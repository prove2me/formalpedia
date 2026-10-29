-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1686_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:35.539986+00:00
-- url     : https://prove2.me/submissions/a3d15a4b-1031-41ff-b78f-bab0223897c4

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
theorem support_rectangle_w1686_s3_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1503743429/10000000000 : ℝ)*x 0 + (5485942699/10000000000 : ℝ)*x 1 + (128363959/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503743429/10000000000 : ℝ)^5111 ≤ (9354362398193/100000000000000 : ℝ)^4087 := by
    have hnat : (1503743429 : ℕ)^5111*100000000000000^4087 ≤ 9354362398193^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503743429 10000000000 9354362398193 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485942699/10000000000 : ℝ)^5111 ≤ (23598833665333/50000000000000 : ℝ)^4087 := by
    have hnat : (5485942699 : ℕ)^5111*50000000000000^4087 ≤ 23598833665333^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485942699 10000000000 23598833665333 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128363959/250000000 : ℝ)^5111 ≤ (43447970257859/100000000000000 : ℝ)^4087 := by
    have hnat : (128363959 : ℕ)^5111*100000000000000^4087 ≤ 43447970257859^4087*250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128363959 250000000 43447970257859 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1503743429/10000000000 : ℝ), (5485942699/10000000000 : ℝ), (128363959/250000000 : ℝ)] ![(9354362398193/100000000000000 : ℝ), (23598833665333/50000000000000 : ℝ), (43447970257859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1503743429/10000000000 : ℝ)|^5111 ≤ (9354362398193/100000000000000 : ℝ)^4087
        have hw : |(-1503743429/10000000000 : ℝ)|=(1503743429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485942699/10000000000 : ℝ)|^5111 ≤ (23598833665333/50000000000000 : ℝ)^4087
        have hw : |(5485942699/10000000000 : ℝ)|=(5485942699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128363959/250000000 : ℝ)|^5111 ≤ (43447970257859/100000000000000 : ℝ)^4087
        have hw : |(128363959/250000000 : ℝ)|=(128363959/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070310543/2000000000 : ℝ)*x 0 + (-843168189/5000000000 : ℝ)*x 1 + (32090989/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070310543/2000000000 : ℝ)^5111 ≤ (45756234888077/100000000000000 : ℝ)^4087 := by
    have hnat : (1070310543 : ℕ)^5111*100000000000000^4087 ≤ 45756234888077^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070310543 2000000000 45756234888077 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843168189/5000000000 : ℝ)^5111 ≤ (1079579610493/10000000000000 : ℝ)^4087 := by
    have hnat : (843168189 : ℕ)^5111*10000000000000^4087 ≤ 1079579610493^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843168189 5000000000 1079579610493 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32090989/62500000 : ℝ)^5111 ≤ (43447968988019/100000000000000 : ℝ)^4087 := by
    have hnat : (32090989 : ℕ)^5111*100000000000000^4087 ≤ 43447968988019^4087*62500000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32090989 62500000 43447968988019 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070310543/2000000000 : ℝ), (-843168189/5000000000 : ℝ), (32090989/62500000 : ℝ)] ![(45756234888077/100000000000000 : ℝ), (1079579610493/10000000000000 : ℝ), (43447968988019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070310543/2000000000 : ℝ)|^5111 ≤ (45756234888077/100000000000000 : ℝ)^4087
        have hw : |(1070310543/2000000000 : ℝ)|=(1070310543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-843168189/5000000000 : ℝ)|^5111 ≤ (1079579610493/10000000000000 : ℝ)^4087
        have hw : |(-843168189/5000000000 : ℝ)|=(843168189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32090989/62500000 : ℝ)|^5111 ≤ (43447968988019/100000000000000 : ℝ)^4087
        have hw : |(32090989/62500000 : ℝ)|=(32090989/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351552267/10000000000 : ℝ)*x 0 + (5134558443/10000000000 : ℝ)*x 1 + (-421584177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351552267/10000000000 : ℝ)^5111 ≤ (45756230097921/100000000000000 : ℝ)^4087 := by
    have hnat : (5351552267 : ℕ)^5111*100000000000000^4087 ≤ 45756230097921^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351552267 10000000000 45756230097921 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134558443/10000000000 : ℝ)^5111 ≤ (8689594227233/20000000000000 : ℝ)^4087 := by
    have hnat : (5134558443 : ℕ)^5111*20000000000000^4087 ≤ 8689594227233^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134558443 10000000000 8689594227233 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421584177/2500000000 : ℝ)^5111 ≤ (10795798746887/100000000000000 : ℝ)^4087 := by
    have hnat : (421584177 : ℕ)^5111*100000000000000^4087 ≤ 10795798746887^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421584177 2500000000 10795798746887 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351552267/10000000000 : ℝ), (5134558443/10000000000 : ℝ), (-421584177/2500000000 : ℝ)] ![(45756230097921/100000000000000 : ℝ), (8689594227233/20000000000000 : ℝ), (10795798746887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351552267/10000000000 : ℝ)|^5111 ≤ (45756230097921/100000000000000 : ℝ)^4087
        have hw : |(5351552267/10000000000 : ℝ)|=(5351552267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134558443/10000000000 : ℝ)|^5111 ≤ (8689594227233/20000000000000 : ℝ)^4087
        have hw : |(5134558443/10000000000 : ℝ)|=(5134558443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421584177/2500000000 : ℝ)|^5111 ≤ (10795798746887/100000000000000 : ℝ)^4087
        have hw : |(-421584177/2500000000 : ℝ)|=(421584177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4136762031/10000000000 : ℝ)*x 0 + (229631151/625000000 : ℝ)*x 1 + (4637255973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136762031/10000000000 : ℝ)^5111 ≤ (33160008632371/100000000000000 : ℝ)^4087 := by
    have hnat : (4136762031 : ℕ)^5111*100000000000000^4087 ≤ 33160008632371^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136762031 10000000000 33160008632371 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229631151/625000000 : ℝ)^5111 ≤ (14294503988393/50000000000000 : ℝ)^4087 := by
    have hnat : (229631151 : ℕ)^5111*50000000000000^4087 ≤ 14294503988393^4087*625000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229631151 625000000 14294503988393 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4637255973/10000000000 : ℝ)^5111 ≤ (38250983369419/100000000000000 : ℝ)^4087 := by
    have hnat : (4637255973 : ℕ)^5111*100000000000000^4087 ≤ 38250983369419^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637255973 10000000000 38250983369419 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136762031/10000000000 : ℝ), (229631151/625000000 : ℝ), (4637255973/10000000000 : ℝ)] ![(33160008632371/100000000000000 : ℝ), (14294503988393/50000000000000 : ℝ), (38250983369419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136762031/10000000000 : ℝ)|^5111 ≤ (33160008632371/100000000000000 : ℝ)^4087
        have hw : |(4136762031/10000000000 : ℝ)|=(4136762031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229631151/625000000 : ℝ)|^5111 ≤ (14294503988393/50000000000000 : ℝ)^4087
        have hw : |(229631151/625000000 : ℝ)|=(229631151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4637255973/10000000000 : ℝ)|^5111 ≤ (38250983369419/100000000000000 : ℝ)^4087
        have hw : |(4637255973/10000000000 : ℝ)|=(4637255973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1503907413/10000000000 : ℝ)*x 0 + (1027673837/2000000000 : ℝ)*x 1 + (1096415059/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503907413/10000000000 : ℝ)^5111 ≤ (9355638099793/100000000000000 : ℝ)^4087 := by
    have hnat : (1503907413 : ℕ)^5111*100000000000000^4087 ≤ 9355638099793^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503907413 10000000000 9355638099793 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027673837/2000000000 : ℝ)^5111 ≤ (43488300146003/100000000000000 : ℝ)^4087 := by
    have hnat : (1027673837 : ℕ)^5111*100000000000000^4087 ≤ 43488300146003^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027673837 2000000000 43488300146003 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096415059/2000000000 : ℝ)^5111 ≤ (11789015435047/25000000000000 : ℝ)^4087 := by
    have hnat : (1096415059 : ℕ)^5111*25000000000000^4087 ≤ 11789015435047^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096415059 2000000000 11789015435047 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1503907413/10000000000 : ℝ), (1027673837/2000000000 : ℝ), (1096415059/2000000000 : ℝ)] ![(9355638099793/100000000000000 : ℝ), (43488300146003/100000000000000 : ℝ), (11789015435047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1503907413/10000000000 : ℝ)|^5111 ≤ (9355638099793/100000000000000 : ℝ)^4087
        have hw : |(-1503907413/10000000000 : ℝ)|=(1503907413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027673837/2000000000 : ℝ)|^5111 ≤ (43488300146003/100000000000000 : ℝ)^4087
        have hw : |(1027673837/2000000000 : ℝ)|=(1027673837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096415059/2000000000 : ℝ)|^5111 ≤ (11789015435047/25000000000000 : ℝ)^4087
        have hw : |(1096415059/2000000000 : ℝ)|=(1096415059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628826207/5000000000 : ℝ)*x 0 + (-334704767/2500000000 : ℝ)*x 1 + (2741037633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628826207/5000000000 : ℝ)^5111 ≤ (71607104079/160000000000 : ℝ)^4087 := by
    have hnat : (2628826207 : ℕ)^5111*160000000000^4087 ≤ 71607104079^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628826207 5000000000 71607104079 160000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334704767/2500000000 : ℝ)^5111 ≤ (4044749252213/50000000000000 : ℝ)^4087 := by
    have hnat : (334704767 : ℕ)^5111*50000000000000^4087 ≤ 4044749252213^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334704767 2500000000 4044749252213 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741037633/5000000000 : ℝ)^5111 ≤ (47156061428233/100000000000000 : ℝ)^4087 := by
    have hnat : (2741037633 : ℕ)^5111*100000000000000^4087 ≤ 47156061428233^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741037633 5000000000 47156061428233 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628826207/5000000000 : ℝ), (-334704767/2500000000 : ℝ), (2741037633/5000000000 : ℝ)] ![(71607104079/160000000000 : ℝ), (4044749252213/50000000000000 : ℝ), (47156061428233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628826207/5000000000 : ℝ)|^5111 ≤ (71607104079/160000000000 : ℝ)^4087
        have hw : |(2628826207/5000000000 : ℝ)|=(2628826207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334704767/2500000000 : ℝ)|^5111 ≤ (4044749252213/50000000000000 : ℝ)^4087
        have hw : |(-334704767/2500000000 : ℝ)|=(334704767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741037633/5000000000 : ℝ)|^5111 ≤ (47156061428233/100000000000000 : ℝ)^4087
        have hw : |(2741037633/5000000000 : ℝ)|=(2741037633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257652421/10000000000 : ℝ)*x 0 + (548207523/1000000000 : ℝ)*x 1 + (-133881911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257652421/10000000000 : ℝ)^5111 ≤ (4475444012389/10000000000000 : ℝ)^4087 := by
    have hnat : (5257652421 : ℕ)^5111*10000000000000^4087 ≤ 4475444012389^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257652421 10000000000 4475444012389 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548207523/1000000000 : ℝ)^5111 ≤ (23578030520489/50000000000000 : ℝ)^4087 := by
    have hnat : (548207523 : ℕ)^5111*50000000000000^4087 ≤ 23578030520489^4087*1000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548207523 1000000000 23578030520489 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133881911/1000000000 : ℝ)^5111 ≤ (1011187352723/12500000000000 : ℝ)^4087 := by
    have hnat : (133881911 : ℕ)^5111*12500000000000^4087 ≤ 1011187352723^4087*1000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133881911 1000000000 1011187352723 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257652421/10000000000 : ℝ), (548207523/1000000000 : ℝ), (-133881911/1000000000 : ℝ)] ![(4475444012389/10000000000000 : ℝ), (23578030520489/50000000000000 : ℝ), (1011187352723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257652421/10000000000 : ℝ)|^5111 ≤ (4475444012389/10000000000000 : ℝ)^4087
        have hw : |(5257652421/10000000000 : ℝ)|=(5257652421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548207523/1000000000 : ℝ)|^5111 ≤ (23578030520489/50000000000000 : ℝ)^4087
        have hw : |(548207523/1000000000 : ℝ)|=(548207523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133881911/1000000000 : ℝ)|^5111 ≤ (1011187352723/12500000000000 : ℝ)^4087
        have hw : |(-133881911/1000000000 : ℝ)|=(133881911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s3_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827442593/2000000000 : ℝ)*x 0 + (1156702551/2500000000 : ℝ)*x 1 + (921175033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827442593/2000000000 : ℝ)^5111 ≤ (829113225129/2500000000000 : ℝ)^4087 := by
    have hnat : (827442593 : ℕ)^5111*2500000000000^4087 ≤ 829113225129^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827442593 2000000000 829113225129 2500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156702551/2500000000 : ℝ)^5111 ≤ (476790779063/1250000000000 : ℝ)^4087 := by
    have hnat : (1156702551 : ℕ)^5111*1250000000000^4087 ≤ 476790779063^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156702551 2500000000 476790779063 1250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921175033/2500000000 : ℝ)^5111 ≤ (3586526082119/12500000000000 : ℝ)^4087 := by
    have hnat : (921175033 : ℕ)^5111*12500000000000^4087 ≤ 3586526082119^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921175033 2500000000 3586526082119 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827442593/2000000000 : ℝ), (1156702551/2500000000 : ℝ), (921175033/2500000000 : ℝ)] ![(829113225129/2500000000000 : ℝ), (476790779063/1250000000000 : ℝ), (3586526082119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827442593/2000000000 : ℝ)|^5111 ≤ (829113225129/2500000000000 : ℝ)^4087
        have hw : |(827442593/2000000000 : ℝ)|=(827442593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1156702551/2500000000 : ℝ)|^5111 ≤ (476790779063/1250000000000 : ℝ)^4087
        have hw : |(1156702551/2500000000 : ℝ)|=(1156702551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921175033/2500000000 : ℝ)|^5111 ≤ (3586526082119/12500000000000 : ℝ)^4087
        have hw : |(921175033/2500000000 : ℝ)|=(921175033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (979/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1079/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1729/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1729/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1729/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1729/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1729/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1729/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9767/100000 : ℝ) ^ (5103/1024 : ℝ) ≤ (461899493175181/50000000000000000000 : ℝ) := by
    have hpowers : (9767/100000 : ℝ)^5103 ≤ (461899493175181/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9767 : ℕ)^5103*50000000000000000000^1024 ≤ 461899493175181^1024*100000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9767 100000 461899493175181 50000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9767/100000 : ℝ)) (X := (461899493175181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1729/10000 : ℝ) ^ (5103/1024 : ℝ) ≤ (3181696543062521/20000000000000000000 : ℝ) := by
    have hpowers : (1729/10000 : ℝ)^5103 ≤ (3181696543062521/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1729 : ℕ)^5103*20000000000000000000^1024 ≤ 3181696543062521^1024*10000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1729 10000 3181696543062521 20000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1729/10000 : ℝ)) (X := (3181696543062521/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000461899493175181/25000000000000000000 : ℝ) ≤ (1250004634348309/1250000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (25000461899493175181/25000000000000000000 : ℝ)^1024 ≤ (1250004634348309/1250000000000000 : ℝ)^5103 := by
      have hnat : (25000461899493175181 : ℕ)^1024*1250000000000000^5103 ≤ 1250004634348309^5103*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000461899493175181 25000000000000000000 1250004634348309 1250000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004634348309/1250000000000000 : ℝ)) (X := (25000461899493175181/25000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016832281701662967/100000000000000000000 : ℝ) ≤ (5000168872203057/5000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (100016832281701662967/100000000000000000000 : ℝ)^1024 ≤ (5000168872203057/5000000000000000 : ℝ)^5103 := by
      have hnat : (100016832281701662967 : ℕ)^1024*5000000000000000^5103 ≤ 5000168872203057^5103*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016832281701662967 100000000000000000000 5000168872203057 5000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000168872203057/5000000000000000 : ℝ)) (X := (100016832281701662967/100000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003181696543062521/10000000000000000000 : ℝ) ≤ (2500159603506439/2500000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (10003181696543062521/10000000000000000000 : ℝ)^1024 ≤ (2500159603506439/2500000000000000 : ℝ)^5103 := by
      have hnat : (10003181696543062521 : ℕ)^1024*2500000000000000^5103 ≤ 2500159603506439^5103*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003181696543062521 10000000000000000000 2500159603506439 2500000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500159603506439/2500000000000000 : ℝ)) (X := (10003181696543062521/10000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461899493175181/50000000000000000000 : ℝ) ≤ ((18806101408317135507/18807500000000000000 : ℝ)+2*(150334809821/376150000000000 : ℝ)*(9767/100000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (18806101408317135507/18807500000000000000 : ℝ)+2*(150334809821/376150000000000 : ℝ)*(9767/100000 : ℝ)=(1250004634348309/1250000000000000 : ℝ) by norm_num, show 1+2*(461899493175181/50000000000000000000 : ℝ)=(25000461899493175181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3181696543062521/20000000000000000000 : ℝ)+(461899493175181/50000000000000000000 : ℝ) ≤ ((18806101408317135507/18807500000000000000 : ℝ)+(150334809821/376150000000000 : ℝ)*((1729/10000 : ℝ)+(9767/100000 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (18806101408317135507/18807500000000000000 : ℝ)+(150334809821/376150000000000 : ℝ)*((1729/10000 : ℝ)+(9767/100000 : ℝ))=(5000168872203057/5000000000000000 : ℝ) by norm_num, show 1+(3181696543062521/20000000000000000000 : ℝ)+(461899493175181/50000000000000000000 : ℝ)=(100016832281701662967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3181696543062521/20000000000000000000 : ℝ) ≤ ((18806101408317135507/18807500000000000000 : ℝ)+2*(150334809821/376150000000000 : ℝ)*(1729/10000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (18806101408317135507/18807500000000000000 : ℝ)+2*(150334809821/376150000000000 : ℝ)*(1729/10000 : ℝ)=(2500159603506439/2500000000000000 : ℝ) by norm_num, show 1+2*(3181696543062521/20000000000000000000 : ℝ)=(10003181696543062521/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18806101408317135507/18807500000000000000 : ℝ)*(X 1 0+X 2 0)+(150334809821/376150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (1729/10000 : ℝ)) (c := (18806101408317135507/18807500000000000000 : ℝ)) (alpha := (150334809821/376150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18806101408317135507/18807500000000000000 : ℝ)*(X 0 1+X 2 1)+(150334809821/376150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (1729/10000 : ℝ)) (c := (18806101408317135507/18807500000000000000 : ℝ)) (alpha := (150334809821/376150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18806101408317135507/18807500000000000000 : ℝ)*(X 0 2+X 1 2)+(150334809821/376150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (1729/10000 : ℝ)) (c := (18806101408317135507/18807500000000000000 : ℝ)) (alpha := (150334809821/376150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1503743429/10000000000 : ℝ)*X 0 0+(5485942699/10000000000 : ℝ)*X 0 1+(128363959/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070310543/2000000000 : ℝ)*X 1 0+(-843168189/5000000000 : ℝ)*X 1 1+(32090989/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351552267/10000000000 : ℝ)*X 2 0+(5134558443/10000000000 : ℝ)*X 2 1+(-421584177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4136762031/10000000000 : ℝ)*X 0 0+(229631151/625000000 : ℝ)*X 0 1+(4637255973/10000000000 : ℝ)*X 0 2+(4136762031/10000000000 : ℝ)*X 1 0+(229631151/625000000 : ℝ)*X 1 1+(4637255973/10000000000 : ℝ)*X 1 2+(4136762031/10000000000 : ℝ)*X 2 0+(229631151/625000000 : ℝ)*X 2 1+(4637255973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1503907413/10000000000 : ℝ)*X 0 0+(1027673837/2000000000 : ℝ)*X 0 1+(1096415059/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628826207/5000000000 : ℝ)*X 1 0+(-334704767/2500000000 : ℝ)*X 1 1+(2741037633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257652421/10000000000 : ℝ)*X 2 0+(548207523/1000000000 : ℝ)*X 2 1+(-133881911/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((827442593/2000000000 : ℝ)*X 0 0+(1156702551/2500000000 : ℝ)*X 0 1+(921175033/2500000000 : ℝ)*X 0 2+(827442593/2000000000 : ℝ)*X 1 0+(1156702551/2500000000 : ℝ)*X 1 1+(921175033/2500000000 : ℝ)*X 1 2+(827442593/2000000000 : ℝ)*X 2 0+(1156702551/2500000000 : ℝ)*X 2 1+(921175033/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1513000259270515221719424027/470187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153309039/50000000000000 : ℝ)*(base19) + (281332023/100000000000000 : ℝ)*(base23) + (64583389/50000000000000 : ℝ)*(upper2) + (115032581/100000000000000 : ℝ)*(upper3) + (160356923/100000000000000 : ℝ)*(upper5) + (971035493759713/50000000000000 : ℝ)*(major0) + (971035493759713/50000000000000 : ℝ)*(major1) + (971035493759713/50000000000000 : ℝ)*(major2) + (711472064279343/25000000000000 : ℝ)*(sp0) + (1422943975249647/50000000000000 : ℝ)*(sp1) + (284588635672389/10000000000000 : ℝ)*(sp2) + (259563279478173/25000000000000 : ℝ)*(sp3) + (809530729/50000000000000 : ℝ)*(sp6) + (492746591/100000000000000 : ℝ)*(sp7) + (1038253610659283/100000000000000 : ℝ)*(f.failure) + (711472064279343/25000000000000 : ℝ)*(f.sum) + (60329047182593/37615000000000000000000000000 : ℝ)*base66 + (1500245719721920509/940375000000000000000000000000000 : ℝ)*base68 + (1246014348899079491/940375000000000000000000000000000 : ℝ)*base69 + (811567272759295509/940375000000000000000000000000000 : ℝ)*base72 + (24828234241117/9403750000000000000000000000 : ℝ)*base74 + (1040963097559079491/940375000000000000000000000000000 : ℝ)*base75 + (2749853616556454491/940375000000000000000000000000000 : ℝ)*base77 + (5778894747604829491/940375000000000000000000000000000 : ℝ)*base79 + (2180021697179/1175468750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2294127/625000000000000000000 : ℝ)*base90 + (2294127/625000000000000000000 : ℝ)*base92 + (2294127/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143464336348225220187/14693359375000000000000000 : ℝ) := by norm_num
    linear_combination (351484739/25000000000000 : ℝ)*(base19) + (152367453/10000000000000 : ℝ)*(base23) + (16750507/4000000000000 : ℝ)*(lower1) + (2599907/1250000000000 : ℝ)*(upper3) + (54110567/100000000000000 : ℝ)*(lower4) + (41207989/20000000000000 : ℝ)*(upper5) + (19854461670933/1000000000000 : ℝ)*(major0) + (19854461670933/1000000000000 : ℝ)*(major1) + (19854461670933/1000000000000 : ℝ)*(major2) + (612790459/100000000000000 : ℝ)*(sp2) + (2909449525414991/100000000000000 : ℝ)*(sp4) + (581889623895207/20000000000000 : ℝ)*(sp5) + (1454723694475001/50000000000000 : ℝ)*(sp6) + (8491539866469/800000000000 : ℝ)*(sp7) + (8491539866469/800000000000 : ℝ)*(f.failure) + (2909449525414991/100000000000000 : ℝ)*(f.sum) + (12978745911677/3761500000000000000000000000 : ℝ)*base65 + (91847843407994469/18807500000000000000000000000000 : ℝ)*base68 + (41429148976069469/18807500000000000000000000000000 : ℝ)*base70 + (166396814779655531/18807500000000000000000000000000 : ℝ)*base71 + (185598207313/94037500000000000000000000 : ℝ)*base74 + (4282424009693031/18807500000000000000000000000000 : ℝ)*base75 + (38375049361131969/18807500000000000000000000000000 : ℝ)*base78 + (46772958305440531/18807500000000000000000000000000 : ℝ)*base79 + (2760412202591/1880750000000000000000000000 : ℝ)*base82 + (1161/5000000000000000000 : ℝ)*base90 + (1161/5000000000000000000 : ℝ)*base92 + (1161/5000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1686_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (979/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1079/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1686_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1686_s4_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1503759251/10000000000 : ℝ)*x 0 + (5485881193/10000000000 : ℝ)*x 1 + (5134609263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503759251/10000000000 : ℝ)^5111 ≤ (2338621370693/25000000000000 : ℝ)^4087 := by
    have hnat : (1503759251 : ℕ)^5111*25000000000000^4087 ≤ 2338621370693^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503759251 10000000000 2338621370693 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485881193/10000000000 : ℝ)^5111 ≤ (47197005590669/100000000000000 : ℝ)^4087 := by
    have hnat : (5485881193 : ℕ)^5111*100000000000000^4087 ≤ 47197005590669^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485881193 10000000000 47197005590669 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5134609263/10000000000 : ℝ)^5111 ≤ (4344850891393/10000000000000 : ℝ)^4087 := by
    have hnat : (5134609263 : ℕ)^5111*10000000000000^4087 ≤ 4344850891393^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134609263 10000000000 4344850891393 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1503759251/10000000000 : ℝ), (5485881193/10000000000 : ℝ), (5134609263/10000000000 : ℝ)] ![(2338621370693/25000000000000 : ℝ), (47197005590669/100000000000000 : ℝ), (4344850891393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1503759251/10000000000 : ℝ)|^5111 ≤ (2338621370693/25000000000000 : ℝ)^4087
        have hw : |(-1503759251/10000000000 : ℝ)|=(1503759251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485881193/10000000000 : ℝ)|^5111 ≤ (47197005590669/100000000000000 : ℝ)^4087
        have hw : |(5485881193/10000000000 : ℝ)|=(5485881193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5134609263/10000000000 : ℝ)|^5111 ≤ (4344850891393/10000000000000 : ℝ)^4087
        have hw : |(5134609263/10000000000 : ℝ)|=(5134609263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351534949/10000000000 : ℝ)*x 0 + (-421572617/2500000000 : ℝ)*x 1 + (205384437/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351534949/10000000000 : ℝ)^5111 ≤ (45756044928501/100000000000000 : ℝ)^4087 := by
    have hnat : (5351534949 : ℕ)^5111*100000000000000^4087 ≤ 45756044928501^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351534949 10000000000 45756044928501 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421572617/2500000000 : ℝ)^5111 ≤ (5397714277003/50000000000000 : ℝ)^4087 := by
    have hnat : (421572617 : ℕ)^5111*50000000000000^4087 ≤ 5397714277003^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421572617 2500000000 5397714277003 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205384437/400000000 : ℝ)^5111 ≤ (21724263250627/50000000000000 : ℝ)^4087 := by
    have hnat : (205384437 : ℕ)^5111*50000000000000^4087 ≤ 21724263250627^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205384437 400000000 21724263250627 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351534949/10000000000 : ℝ), (-421572617/2500000000 : ℝ), (205384437/400000000 : ℝ)] ![(45756044928501/100000000000000 : ℝ), (5397714277003/50000000000000 : ℝ), (21724263250627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351534949/10000000000 : ℝ)|^5111 ≤ (45756044928501/100000000000000 : ℝ)^4087
        have hw : |(5351534949/10000000000 : ℝ)|=(5351534949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421572617/2500000000 : ℝ)|^5111 ≤ (5397714277003/50000000000000 : ℝ)^4087
        have hw : |(-421572617/2500000000 : ℝ)|=(421572617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205384437/400000000 : ℝ)|^5111 ≤ (21724263250627/50000000000000 : ℝ)^4087
        have hw : |(205384437/400000000 : ℝ)|=(205384437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675767801/5000000000 : ℝ)*x 0 + (5134610139/10000000000 : ℝ)*x 1 + (-337258127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675767801/5000000000 : ℝ)^5111 ≤ (2859753244411/6250000000000 : ℝ)^4087 := by
    have hnat : (2675767801 : ℕ)^5111*6250000000000^4087 ≤ 2859753244411^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675767801 5000000000 2859753244411 6250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134610139/10000000000 : ℝ)^5111 ≤ (43448518183783/100000000000000 : ℝ)^4087 := by
    have hnat : (5134610139 : ℕ)^5111*100000000000000^4087 ≤ 43448518183783^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134610139 10000000000 43448518183783 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337258127/2000000000 : ℝ)^5111 ≤ (10795429890987/100000000000000 : ℝ)^4087 := by
    have hnat : (337258127 : ℕ)^5111*100000000000000^4087 ≤ 10795429890987^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337258127 2000000000 10795429890987 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675767801/5000000000 : ℝ), (5134610139/10000000000 : ℝ), (-337258127/2000000000 : ℝ)] ![(2859753244411/6250000000000 : ℝ), (43448518183783/100000000000000 : ℝ), (10795429890987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675767801/5000000000 : ℝ)|^5111 ≤ (2859753244411/6250000000000 : ℝ)^4087
        have hw : |(2675767801/5000000000 : ℝ)|=(2675767801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134610139/10000000000 : ℝ)|^5111 ≤ (43448518183783/100000000000000 : ℝ)^4087
        have hw : |(5134610139/10000000000 : ℝ)|=(5134610139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337258127/2000000000 : ℝ)|^5111 ≤ (10795429890987/100000000000000 : ℝ)^4087
        have hw : |(-337258127/2000000000 : ℝ)|=(337258127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517096717/1250000000 : ℝ)*x 0 + (229640727/625000000 : ℝ)*x 1 + (4637100063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517096717/1250000000 : ℝ)^5111 ≤ (33160125967191/100000000000000 : ℝ)^4087 := by
    have hnat : (517096717 : ℕ)^5111*100000000000000^4087 ≤ 33160125967191^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517096717 1250000000 33160125967191 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229640727/625000000 : ℝ)^5111 ≤ (7147624725563/25000000000000 : ℝ)^4087 := by
    have hnat : (229640727 : ℕ)^5111*25000000000000^4087 ≤ 7147624725563^4087*625000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229640727 625000000 7147624725563 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4637100063/10000000000 : ℝ)^5111 ≤ (1912468755719/5000000000000 : ℝ)^4087 := by
    have hnat : (4637100063 : ℕ)^5111*5000000000000^4087 ≤ 1912468755719^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637100063 10000000000 1912468755719 5000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517096717/1250000000 : ℝ), (229640727/625000000 : ℝ), (4637100063/10000000000 : ℝ)] ![(33160125967191/100000000000000 : ℝ), (7147624725563/25000000000000 : ℝ), (1912468755719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517096717/1250000000 : ℝ)|^5111 ≤ (33160125967191/100000000000000 : ℝ)^4087
        have hw : |(517096717/1250000000 : ℝ)|=(517096717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229640727/625000000 : ℝ)|^5111 ≤ (7147624725563/25000000000000 : ℝ)^4087
        have hw : |(229640727/625000000 : ℝ)|=(229640727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4637100063/10000000000 : ℝ)|^5111 ≤ (1912468755719/5000000000000 : ℝ)^4087
        have hw : |(4637100063/10000000000 : ℝ)|=(4637100063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375980779/2500000000 : ℝ)*x 0 + (5138418069/10000000000 : ℝ)*x 1 + (5482015841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375980779/2500000000 : ℝ)^5111 ≤ (584735016373/6250000000000 : ℝ)^4087 := by
    have hnat : (375980779 : ℕ)^5111*6250000000000^4087 ≤ 584735016373^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375980779 2500000000 584735016373 6250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138418069/10000000000 : ℝ)^5111 ≤ (2718051095821/6250000000000 : ℝ)^4087 := by
    have hnat : (5138418069 : ℕ)^5111*6250000000000^4087 ≤ 2718051095821^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138418069 10000000000 2718051095821 6250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482015841/10000000000 : ℝ)^5111 ≤ (47155422190541/100000000000000 : ℝ)^4087 := by
    have hnat : (5482015841 : ℕ)^5111*100000000000000^4087 ≤ 47155422190541^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482015841 10000000000 47155422190541 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375980779/2500000000 : ℝ), (5138418069/10000000000 : ℝ), (5482015841/10000000000 : ℝ)] ![(584735016373/6250000000000 : ℝ), (2718051095821/6250000000000 : ℝ), (47155422190541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375980779/2500000000 : ℝ)|^5111 ≤ (584735016373/6250000000000 : ℝ)^4087
        have hw : |(-375980779/2500000000 : ℝ)|=(375980779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138418069/10000000000 : ℝ)|^5111 ≤ (2718051095821/6250000000000 : ℝ)^4087
        have hw : |(5138418069/10000000000 : ℝ)|=(5138418069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482015841/10000000000 : ℝ)|^5111 ≤ (47155422190541/100000000000000 : ℝ)^4087
        have hw : |(5482015841/10000000000 : ℝ)|=(5482015841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257666011/10000000000 : ℝ)*x 0 + (-1338884757/10000000000 : ℝ)*x 1 + (5482015669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257666011/10000000000 : ℝ)^5111 ≤ (5594323098679/12500000000000 : ℝ)^4087 := by
    have hnat : (5257666011 : ℕ)^5111*12500000000000^4087 ≤ 5594323098679^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257666011 10000000000 5594323098679 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338884757/10000000000 : ℝ)^5111 ≤ (8089994863851/100000000000000 : ℝ)^4087 := by
    have hnat : (1338884757 : ℕ)^5111*100000000000000^4087 ≤ 8089994863851^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338884757 10000000000 8089994863851 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482015669/10000000000 : ℝ)^5111 ≤ (47155420340331/100000000000000 : ℝ)^4087 := by
    have hnat : (5482015669 : ℕ)^5111*100000000000000^4087 ≤ 47155420340331^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482015669 10000000000 47155420340331 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257666011/10000000000 : ℝ), (-1338884757/10000000000 : ℝ), (5482015669/10000000000 : ℝ)] ![(5594323098679/12500000000000 : ℝ), (8089994863851/100000000000000 : ℝ), (47155420340331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257666011/10000000000 : ℝ)|^5111 ≤ (5594323098679/12500000000000 : ℝ)^4087
        have hw : |(5257666011/10000000000 : ℝ)|=(5257666011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338884757/10000000000 : ℝ)|^5111 ≤ (8089994863851/100000000000000 : ℝ)^4087
        have hw : |(-1338884757/10000000000 : ℝ)|=(1338884757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482015669/10000000000 : ℝ)|^5111 ≤ (47155420340331/100000000000000 : ℝ)^4087
        have hw : |(5482015669/10000000000 : ℝ)|=(5482015669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257666029/10000000000 : ℝ)*x 0 + (5482015671/10000000000 : ℝ)*x 1 + (-167360591/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257666029/10000000000 : ℝ)^5111 ≤ (22377292490521/50000000000000 : ℝ)^4087 := by
    have hnat : (5257666029 : ℕ)^5111*50000000000000^4087 ≤ 22377292490521^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257666029 10000000000 22377292490521 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482015671/10000000000 : ℝ)^5111 ≤ (9431084072369/20000000000000 : ℝ)^4087 := by
    have hnat : (5482015671 : ℕ)^5111*20000000000000^4087 ≤ 9431084072369^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482015671 10000000000 9431084072369 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167360591/1250000000 : ℝ)^5111 ≤ (101124933059/1250000000000 : ℝ)^4087 := by
    have hnat : (167360591 : ℕ)^5111*1250000000000^4087 ≤ 101124933059^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167360591 1250000000 101124933059 1250000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257666029/10000000000 : ℝ), (5482015671/10000000000 : ℝ), (-167360591/1250000000 : ℝ)] ![(22377292490521/50000000000000 : ℝ), (9431084072369/20000000000000 : ℝ), (101124933059/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257666029/10000000000 : ℝ)|^5111 ≤ (22377292490521/50000000000000 : ℝ)^4087
        have hw : |(5257666029/10000000000 : ℝ)|=(5257666029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482015671/10000000000 : ℝ)|^5111 ≤ (9431084072369/20000000000000 : ℝ)^4087
        have hw : |(5482015671/10000000000 : ℝ)|=(5482015671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167360591/1250000000 : ℝ)|^5111 ≤ (101124933059/1250000000000 : ℝ)^4087
        have hw : |(-167360591/1250000000 : ℝ)|=(167360591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_s4_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137223511/10000000000 : ℝ)*x 0 + (925332067/2000000000 : ℝ)*x 1 + (184242397/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137223511/10000000000 : ℝ)^5111 ≤ (33164634724661/100000000000000 : ℝ)^4087 := by
    have hnat : (4137223511 : ℕ)^5111*100000000000000^4087 ≤ 33164634724661^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137223511 10000000000 33164634724661 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925332067/2000000000 : ℝ)^5111 ≤ (11919286643/31250000000 : ℝ)^4087 := by
    have hnat : (925332067 : ℕ)^5111*31250000000^4087 ≤ 11919286643^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925332067 2000000000 11919286643 31250000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184242397/500000000 : ℝ)^5111 ≤ (5738729599259/20000000000000 : ℝ)^4087 := by
    have hnat : (184242397 : ℕ)^5111*20000000000000^4087 ≤ 5738729599259^4087*500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184242397 500000000 5738729599259 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137223511/10000000000 : ℝ), (925332067/2000000000 : ℝ), (184242397/500000000 : ℝ)] ![(33164634724661/100000000000000 : ℝ), (11919286643/31250000000 : ℝ), (5738729599259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137223511/10000000000 : ℝ)|^5111 ≤ (33164634724661/100000000000000 : ℝ)^4087
        have hw : |(4137223511/10000000000 : ℝ)|=(4137223511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925332067/2000000000 : ℝ)|^5111 ≤ (11919286643/31250000000 : ℝ)^4087
        have hw : |(925332067/2000000000 : ℝ)|=(925332067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184242397/500000000 : ℝ)|^5111 ≤ (5738729599259/20000000000000 : ℝ)^4087
        have hw : |(184242397/500000000 : ℝ)|=(184242397/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1079/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (979/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9791/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17263/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1079/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (979/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1079/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (979/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1079/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (979/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1079/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (979/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1079/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (979/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1079/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (979/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (979/10000 : ℝ) ^ (5103/1024 : ℝ) ≤ (467345480932141/50000000000000000000 : ℝ) := by
    have hpowers : (979/10000 : ℝ)^5103 ≤ (467345480932141/50000000000000000000 : ℝ)^1024 := by
      have hnat : (979 : ℕ)^5103*50000000000000000000^1024 ≤ 467345480932141^1024*10000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        979 10000 467345480932141 50000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (979/10000 : ℝ)) (X := (467345480932141/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1079/6250 : ℝ) ^ (5103/1024 : ℝ) ≤ (1578962373591223/10000000000000000000 : ℝ) := by
    have hpowers : (1079/6250 : ℝ)^5103 ≤ (1578962373591223/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1079 : ℕ)^5103*10000000000000000000^1024 ≤ 1578962373591223^1024*6250^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 6250 1578962373591223 10000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/6250 : ℝ)) (X := (1578962373591223/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000467345480932141/25000000000000000000 : ℝ) ≤ (10000037511910409/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (25000467345480932141/25000000000000000000 : ℝ)^1024 ≤ (10000037511910409/10000000000000000 : ℝ)^5103 := by
      have hnat : (25000467345480932141 : ℕ)^1024*10000000000000000^5103 ≤ 10000037511910409^5103*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000467345480932141 25000000000000000000 10000037511910409 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037511910409/10000000000000000 : ℝ)) (X := (25000467345480932141/25000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781380658708576379/781250000000000000 : ℝ) ≤ (10000335578162987/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (781380658708576379/781250000000000000 : ℝ)^1024 ≤ (10000335578162987/10000000000000000 : ℝ)^5103 := by
      have hnat : (781380658708576379 : ℕ)^1024*10000000000000000^5103 ≤ 10000335578162987^5103*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781380658708576379 781250000000000000 10000335578162987 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000335578162987/10000000000000000 : ℝ)) (X := (781380658708576379/781250000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001578962373591223/5000000000000000000 : ℝ) ≤ (2000126728883113/2000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (5001578962373591223/5000000000000000000 : ℝ)^1024 ≤ (2000126728883113/2000000000000000 : ℝ)^5103 := by
      have hnat : (5001578962373591223 : ℕ)^1024*2000000000000000^5103 ≤ 2000126728883113^5103*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001578962373591223 5000000000000000000 2000126728883113 2000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000126728883113/2000000000000000 : ℝ)) (X := (5001578962373591223/5000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(467345480932141/50000000000000000000 : ℝ) ≤ ((37367222113396459813/37370000000000000000 : ℝ)+2*(149033126289/373700000000000 : ℝ)*(979/10000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (37367222113396459813/37370000000000000000 : ℝ)+2*(149033126289/373700000000000 : ℝ)*(979/10000 : ℝ)=(10000037511910409/10000000000000000 : ℝ) by norm_num, show 1+2*(467345480932141/50000000000000000000 : ℝ)=(25000467345480932141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1578962373591223/10000000000000000000 : ℝ)+(467345480932141/50000000000000000000 : ℝ) ≤ ((37367222113396459813/37370000000000000000 : ℝ)+(149033126289/373700000000000 : ℝ)*((1079/6250 : ℝ)+(979/10000 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (37367222113396459813/37370000000000000000 : ℝ)+(149033126289/373700000000000 : ℝ)*((1079/6250 : ℝ)+(979/10000 : ℝ))=(10000335578162987/10000000000000000 : ℝ) by norm_num, show 1+(1578962373591223/10000000000000000000 : ℝ)+(467345480932141/50000000000000000000 : ℝ)=(781380658708576379/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1578962373591223/10000000000000000000 : ℝ) ≤ ((37367222113396459813/37370000000000000000 : ℝ)+2*(149033126289/373700000000000 : ℝ)*(1079/6250 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (37367222113396459813/37370000000000000000 : ℝ)+2*(149033126289/373700000000000 : ℝ)*(1079/6250 : ℝ)=(2000126728883113/2000000000000000 : ℝ) by norm_num, show 1+2*(1578962373591223/10000000000000000000 : ℝ)=(5001578962373591223/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37367222113396459813/37370000000000000000 : ℝ)*(X 1 0+X 2 0)+(149033126289/373700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (979/10000 : ℝ)) (hi := (1079/6250 : ℝ)) (c := (37367222113396459813/37370000000000000000 : ℝ)) (alpha := (149033126289/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37367222113396459813/37370000000000000000 : ℝ)*(X 0 1+X 2 1)+(149033126289/373700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (979/10000 : ℝ)) (hi := (1079/6250 : ℝ)) (c := (37367222113396459813/37370000000000000000 : ℝ)) (alpha := (149033126289/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37367222113396459813/37370000000000000000 : ℝ)*(X 0 2+X 1 2)+(149033126289/373700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (979/10000 : ℝ)) (hi := (1079/6250 : ℝ)) (c := (37367222113396459813/37370000000000000000 : ℝ)) (alpha := (149033126289/373700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1503759251/10000000000 : ℝ)*X 0 0+(5485881193/10000000000 : ℝ)*X 0 1+(5134609263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351534949/10000000000 : ℝ)*X 1 0+(-421572617/2500000000 : ℝ)*X 1 1+(205384437/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675767801/5000000000 : ℝ)*X 2 0+(5134610139/10000000000 : ℝ)*X 2 1+(-337258127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((517096717/1250000000 : ℝ)*X 0 0+(229640727/625000000 : ℝ)*X 0 1+(4637100063/10000000000 : ℝ)*X 0 2+(517096717/1250000000 : ℝ)*X 1 0+(229640727/625000000 : ℝ)*X 1 1+(4637100063/10000000000 : ℝ)*X 1 2+(517096717/1250000000 : ℝ)*X 2 0+(229640727/625000000 : ℝ)*X 2 1+(4637100063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375980779/2500000000 : ℝ)*X 0 0+(5138418069/10000000000 : ℝ)*X 0 1+(5482015841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257666011/10000000000 : ℝ)*X 1 0+(-1338884757/10000000000 : ℝ)*X 1 1+(5482015669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257666029/10000000000 : ℝ)*X 2 0+(5482015671/10000000000 : ℝ)*X 2 1+(-167360591/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4137223511/10000000000 : ℝ)*X 0 0+(925332067/2000000000 : ℝ)*X 0 1+(184242397/500000000 : ℝ)*X 0 2+(4137223511/10000000000 : ℝ)*X 1 0+(925332067/2000000000 : ℝ)*X 1 1+(184242397/500000000 : ℝ)*X 1 2+(4137223511/10000000000 : ℝ)*X 2 0+(925332067/2000000000 : ℝ)*X 2 1+(184242397/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (417896076687553632181005171/93425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85784203/25000000000000 : ℝ)*(base19) + (581375779/100000000000000 : ℝ)*(base23) + (127628517/50000000000000 : ℝ)*(upper3) + (182509/312500000000 : ℝ)*(upper4) + (64093501/50000000000000 : ℝ)*(upper5) + (97135336039011/5000000000000 : ℝ)*(major0) + (97135336039011/5000000000000 : ℝ)*(major1) + (97135336039011/5000000000000 : ℝ)*(major2) + (177925545882031/6250000000000 : ℝ)*(sp0) + (1423409734154241/50000000000000 : ℝ)*(sp1) + (1423409615034757/50000000000000 : ℝ)*(sp2) + (519294298953207/50000000000000 : ℝ)*(sp3) + (11077332797/100000000000000 : ℝ)*(sp4) + (4883106567/100000000000000 : ℝ)*(sp7) + (519296740506491/50000000000000 : ℝ)*(f.failure) + (2846819811445293/100000000000000 : ℝ)*(f.sum) + (143540159099/29896000000000000000000000 : ℝ)*base65 + (259265156591235057/186850000000000000000000000000000 : ℝ)*base68 + (421666791378714943/186850000000000000000000000000000 : ℝ)*base69 + (69162481375514943/186850000000000000000000000000000 : ℝ)*base71 + (3341318928813/3737000000000000000000000000 : ℝ)*base74 + (1020605586277535057/186850000000000000000000000000000 : ℝ)*base76 + (1233294034507014943/186850000000000000000000000000000 : ℝ)*base77 + (1520405283692514943/186850000000000000000000000000000 : ℝ)*base79 + (14298364637/934250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2534921/312500000000000000000 : ℝ)*base89 + (2534921/312500000000000000000 : ℝ)*base91 + (2534921/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24860512885418741783883978747/1868500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1913294563/100000000000000 : ℝ)*(base19) + (63187911/3125000000000 : ℝ)*(base23) + (572073951/100000000000000 : ℝ)*(lower1) + (121145639/50000000000000 : ℝ)*(upper3) + (49381851/100000000000000 : ℝ)*(lower4) + (301589729/100000000000000 : ℝ)*(upper5) + (1986070064810791/100000000000000 : ℝ)*(major0) + (1986070064810791/100000000000000 : ℝ)*(major1) + (1986070064810791/100000000000000 : ℝ)*(major2) + (67649747/25000000000000 : ℝ)*(sp2) + (582072731975087/20000000000000 : ℝ)*(sp4) + (363795218322609/12500000000000 : ℝ)*(sp5) + (1455180683631647/50000000000000 : ℝ)*(sp6) + (132722003280499/12500000000000 : ℝ)*(sp7) + (132722003280499/12500000000000 : ℝ)*(f.failure) + (582072731975087/20000000000000 : ℝ)*(f.sum) + (36800594138979/18685000000000000000000000000 : ℝ)*base65 + (15021483390354857917/3737000000000000000000000000000000 : ℝ)*base68 + (32309779565614857917/3737000000000000000000000000000000 : ℝ)*base70 + (18603566686907857917/3737000000000000000000000000000000 : ℝ)*base72 + (2102487016361/18685000000000000000000000000 : ℝ)*base74 + (94803322386435857917/3737000000000000000000000000000000 : ℝ)*base76 + (1908402256177857917/3737000000000000000000000000000000 : ℝ)*base78 + (20360406921857917/3737000000000000000000000000000000 : ℝ)*base80 + (126025813910981/18685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (886019/78125000000000000000 : ℝ)*base89 + (886019/78125000000000000000 : ℝ)*base91 + (886019/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1686_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1079/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (979/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17263/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1686_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1686_box_0 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291330617/2500000000 : ℝ)*x 0 + (217211799/400000000 : ℝ)*x 1 + (2715148369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291330617/2500000000 : ℝ)^5111 ≤ (3400272386179/50000000000000 : ℝ)^4087 := by
    have hnat : (291330617 : ℕ)^5111*50000000000000^4087 ≤ 3400272386179^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291330617 2500000000 3400272386179 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217211799/400000000 : ℝ)^5111 ≤ (46599718145421/100000000000000 : ℝ)^4087 := by
    have hnat : (217211799 : ℕ)^5111*100000000000000^4087 ≤ 46599718145421^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217211799 400000000 46599718145421 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715148369/5000000000 : ℝ)^5111 ≤ (23299868532543/50000000000000 : ℝ)^4087 := by
    have hnat : (2715148369 : ℕ)^5111*50000000000000^4087 ≤ 23299868532543^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715148369 5000000000 23299868532543 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291330617/2500000000 : ℝ), (217211799/400000000 : ℝ), (2715148369/5000000000 : ℝ)] ![(3400272386179/50000000000000 : ℝ), (46599718145421/100000000000000 : ℝ), (23299868532543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291330617/2500000000 : ℝ)|^5111 ≤ (3400272386179/50000000000000 : ℝ)^4087
        have hw : |(-291330617/2500000000 : ℝ)|=(291330617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217211799/400000000 : ℝ)|^5111 ≤ (46599718145421/100000000000000 : ℝ)^4087
        have hw : |(217211799/400000000 : ℝ)|=(217211799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715148369/5000000000 : ℝ)|^5111 ≤ (23299868532543/50000000000000 : ℝ)^4087
        have hw : |(2715148369/5000000000 : ℝ)|=(2715148369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_1 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226084509/10000000000 : ℝ)*x 0 + (-727816933/5000000000 : ℝ)*x 1 + (5430296283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226084509/10000000000 : ℝ)^5111 ≤ (44418652970503/100000000000000 : ℝ)^4087 := by
    have hnat : (5226084509 : ℕ)^5111*100000000000000^4087 ≤ 44418652970503^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226084509 10000000000 44418652970503 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727816933/5000000000 : ℝ)^5111 ≤ (8981614841267/100000000000000 : ℝ)^4087 := by
    have hnat : (727816933 : ℕ)^5111*100000000000000^4087 ≤ 8981614841267^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727816933 5000000000 8981614841267 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430296283/10000000000 : ℝ)^5111 ≤ (9319946436449/20000000000000 : ℝ)^4087 := by
    have hnat : (5430296283 : ℕ)^5111*20000000000000^4087 ≤ 9319946436449^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430296283 10000000000 9319946436449 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226084509/10000000000 : ℝ), (-727816933/5000000000 : ℝ), (5430296283/10000000000 : ℝ)] ![(44418652970503/100000000000000 : ℝ), (8981614841267/100000000000000 : ℝ), (9319946436449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226084509/10000000000 : ℝ)|^5111 ≤ (44418652970503/100000000000000 : ℝ)^4087
        have hw : |(5226084509/10000000000 : ℝ)|=(5226084509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-727816933/5000000000 : ℝ)|^5111 ≤ (8981614841267/100000000000000 : ℝ)^4087
        have hw : |(-727816933/5000000000 : ℝ)|=(727816933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430296283/10000000000 : ℝ)|^5111 ≤ (9319946436449/20000000000000 : ℝ)^4087
        have hw : |(5430296283/10000000000 : ℝ)|=(5430296283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_2 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226084529/10000000000 : ℝ)*x 0 + (5430296303/10000000000 : ℝ)*x 1 + (-1455633811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226084529/10000000000 : ℝ)^5111 ≤ (22209326591541/50000000000000 : ℝ)^4087 := by
    have hnat : (5226084529 : ℕ)^5111*50000000000000^4087 ≤ 22209326591541^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226084529 10000000000 22209326591541 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430296303/10000000000 : ℝ)^5111 ≤ (14911914367/32000000000 : ℝ)^4087 := by
    have hnat : (5430296303 : ℕ)^5111*32000000000^4087 ≤ 14911914367^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430296303 10000000000 14911914367 32000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455633811/10000000000 : ℝ)^5111 ≤ (2245403604219/25000000000000 : ℝ)^4087 := by
    have hnat : (1455633811 : ℕ)^5111*25000000000000^4087 ≤ 2245403604219^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455633811 10000000000 2245403604219 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226084529/10000000000 : ℝ), (5430296303/10000000000 : ℝ), (-1455633811/10000000000 : ℝ)] ![(22209326591541/50000000000000 : ℝ), (14911914367/32000000000 : ℝ), (2245403604219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226084529/10000000000 : ℝ)|^5111 ≤ (22209326591541/50000000000000 : ℝ)^4087
        have hw : |(5226084529/10000000000 : ℝ)|=(5226084529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430296303/10000000000 : ℝ)|^5111 ≤ (14911914367/32000000000 : ℝ)^4087
        have hw : |(5430296303/10000000000 : ℝ)|=(5430296303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1455633811/10000000000 : ℝ)|^5111 ≤ (2245403604219/25000000000000 : ℝ)^4087
        have hw : |(-1455633811/10000000000 : ℝ)|=(1455633811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_3 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2260824491/5000000000 : ℝ)*x 0 + (991795217/2500000000 : ℝ)*x 1 + (3967181639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260824491/5000000000 : ℝ)^5111 ≤ (9265551975911/25000000000000 : ℝ)^4087 := by
    have hnat : (2260824491 : ℕ)^5111*25000000000000^4087 ≤ 9265551975911^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260824491 5000000000 9265551975911 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991795217/2500000000 : ℝ)^5111 ≤ (7867223054797/25000000000000 : ℝ)^4087 := by
    have hnat : (991795217 : ℕ)^5111*25000000000000^4087 ≤ 7867223054797^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991795217 2500000000 7867223054797 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3967181639/10000000000 : ℝ)^5111 ≤ (6293779973463/20000000000000 : ℝ)^4087 := by
    have hnat : (3967181639 : ℕ)^5111*20000000000000^4087 ≤ 6293779973463^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3967181639 10000000000 6293779973463 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2260824491/5000000000 : ℝ), (991795217/2500000000 : ℝ), (3967181639/10000000000 : ℝ)] ![(9265551975911/25000000000000 : ℝ), (7867223054797/25000000000000 : ℝ), (6293779973463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2260824491/5000000000 : ℝ)|^5111 ≤ (9265551975911/25000000000000 : ℝ)^4087
        have hw : |(2260824491/5000000000 : ℝ)|=(2260824491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(991795217/2500000000 : ℝ)|^5111 ≤ (7867223054797/25000000000000 : ℝ)^4087
        have hw : |(991795217/2500000000 : ℝ)|=(991795217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3967181639/10000000000 : ℝ)|^5111 ≤ (6293779973463/20000000000000 : ℝ)^4087
        have hw : |(3967181639/10000000000 : ℝ)|=(3967181639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_4 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372643011/2000000000 : ℝ)*x 0 + (2587907727/5000000000 : ℝ)*x 1 + (2587907837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372643011/2000000000 : ℝ)^5111 ≤ (6115007527143/50000000000000 : ℝ)^4087 := by
    have hnat : (372643011 : ℕ)^5111*50000000000000^4087 ≤ 6115007527143^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372643011 2000000000 6115007527143 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587907727/5000000000 : ℝ)^5111 ≤ (10971247824711/25000000000000 : ℝ)^4087 := by
    have hnat : (2587907727 : ℕ)^5111*25000000000000^4087 ≤ 10971247824711^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587907727 5000000000 10971247824711 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587907837/5000000000 : ℝ)^5111 ≤ (10971248407889/25000000000000 : ℝ)^4087 := by
    have hnat : (2587907837 : ℕ)^5111*25000000000000^4087 ≤ 10971248407889^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587907837 5000000000 10971248407889 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372643011/2000000000 : ℝ), (2587907727/5000000000 : ℝ), (2587907837/5000000000 : ℝ)] ![(6115007527143/50000000000000 : ℝ), (10971247824711/25000000000000 : ℝ), (10971248407889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372643011/2000000000 : ℝ)|^5111 ≤ (6115007527143/50000000000000 : ℝ)^4087
        have hw : |(-372643011/2000000000 : ℝ)|=(372643011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587907727/5000000000 : ℝ)|^5111 ≤ (10971247824711/25000000000000 : ℝ)^4087
        have hw : |(2587907727/5000000000 : ℝ)|=(2587907727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587907837/5000000000 : ℝ)|^5111 ≤ (10971248407889/25000000000000 : ℝ)^4087
        have hw : |(2587907837/5000000000 : ℝ)|=(2587907837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_5 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399689449/10000000000 : ℝ)*x 0 + (-1566297711/10000000000 : ℝ)*x 1 + (207032617/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399689449/10000000000 : ℝ)^5111 ≤ (11567876663931/25000000000000 : ℝ)^4087 := by
    have hnat : (5399689449 : ℕ)^5111*25000000000000^4087 ≤ 11567876663931^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399689449 10000000000 11567876663931 25000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1566297711/10000000000 : ℝ)^5111 ≤ (4921751170249/50000000000000 : ℝ)^4087 := by
    have hnat : (1566297711 : ℕ)^5111*50000000000000^4087 ≤ 4921751170249^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566297711 10000000000 4921751170249 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207032617/400000000 : ℝ)^5111 ≤ (877699819827/2000000000000 : ℝ)^4087 := by
    have hnat : (207032617 : ℕ)^5111*2000000000000^4087 ≤ 877699819827^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207032617 400000000 877699819827 2000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399689449/10000000000 : ℝ), (-1566297711/10000000000 : ℝ), (207032617/400000000 : ℝ)] ![(11567876663931/25000000000000 : ℝ), (4921751170249/50000000000000 : ℝ), (877699819827/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399689449/10000000000 : ℝ)|^5111 ≤ (11567876663931/25000000000000 : ℝ)^4087
        have hw : |(5399689449/10000000000 : ℝ)|=(5399689449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1566297711/10000000000 : ℝ)|^5111 ≤ (4921751170249/50000000000000 : ℝ)^4087
        have hw : |(-1566297711/10000000000 : ℝ)|=(1566297711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207032617/400000000 : ℝ)|^5111 ≤ (877699819827/2000000000000 : ℝ)^4087
        have hw : |(207032617/400000000 : ℝ)|=(207032617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_6 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079937879/2000000000 : ℝ)*x 0 + (5175815577/10000000000 : ℝ)*x 1 + (-78314879/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079937879/2000000000 : ℝ)^5111 ≤ (23135753038521/50000000000000 : ℝ)^4087 := by
    have hnat : (1079937879 : ℕ)^5111*50000000000000^4087 ≤ 23135753038521^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079937879 2000000000 23135753038521 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175815577/10000000000 : ℝ)^5111 ≤ (21942496301521/50000000000000 : ℝ)^4087 := by
    have hnat : (5175815577 : ℕ)^5111*50000000000000^4087 ≤ 21942496301521^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175815577 10000000000 21942496301521 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78314879/500000000 : ℝ)^5111 ≤ (9843501310947/100000000000000 : ℝ)^4087 := by
    have hnat : (78314879 : ℕ)^5111*100000000000000^4087 ≤ 9843501310947^4087*500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78314879 500000000 9843501310947 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079937879/2000000000 : ℝ), (5175815577/10000000000 : ℝ), (-78314879/500000000 : ℝ)] ![(23135753038521/50000000000000 : ℝ), (21942496301521/50000000000000 : ℝ), (9843501310947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079937879/2000000000 : ℝ)|^5111 ≤ (23135753038521/50000000000000 : ℝ)^4087
        have hw : |(1079937879/2000000000 : ℝ)|=(1079937879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175815577/10000000000 : ℝ)|^5111 ≤ (21942496301521/50000000000000 : ℝ)^4087
        have hw : |(5175815577/10000000000 : ℝ)|=(5175815577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78314879/500000000 : ℝ)|^5111 ≤ (9843501310947/100000000000000 : ℝ)^4087
        have hw : |(-78314879/500000000 : ℝ)|=(78314879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_7 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (467193303/1250000000 : ℝ)*x 0 + (4358363641/10000000000 : ℝ)*x 1 + (4358363951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467193303/1250000000 : ℝ)^5111 ≤ (584154784489/2000000000000 : ℝ)^4087 := by
    have hnat : (467193303 : ℕ)^5111*2000000000000^4087 ≤ 584154784489^4087*1250000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467193303 1250000000 584154784489 2000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4358363641/10000000000 : ℝ)^5111 ≤ (17698064400417/50000000000000 : ℝ)^4087 := by
    have hnat : (4358363641 : ℕ)^5111*50000000000000^4087 ≤ 17698064400417^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358363641 10000000000 17698064400417 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4358363951/10000000000 : ℝ)^5111 ≤ (35396131949273/100000000000000 : ℝ)^4087 := by
    have hnat : (4358363951 : ℕ)^5111*100000000000000^4087 ≤ 35396131949273^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358363951 10000000000 35396131949273 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(467193303/1250000000 : ℝ), (4358363641/10000000000 : ℝ), (4358363951/10000000000 : ℝ)] ![(584154784489/2000000000000 : ℝ), (17698064400417/50000000000000 : ℝ), (35396131949273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(467193303/1250000000 : ℝ)|^5111 ≤ (584154784489/2000000000000 : ℝ)^4087
        have hw : |(467193303/1250000000 : ℝ)|=(467193303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4358363641/10000000000 : ℝ)|^5111 ≤ (17698064400417/50000000000000 : ℝ)^4087
        have hw : |(4358363641/10000000000 : ℝ)|=(4358363641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4358363951/10000000000 : ℝ)|^5111 ≤ (35396131949273/100000000000000 : ℝ)^4087
        have hw : |(4358363951/10000000000 : ℝ)|=(4358363951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_8 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1713551759/10000000000 : ℝ)*x 0 + (4989293097/10000000000 : ℝ)*x 1 + (5474037997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713551759/10000000000 : ℝ)^5111 ≤ (5507059626071/50000000000000 : ℝ)^4087 := by
    have hnat : (1713551759 : ℕ)^5111*50000000000000^4087 ≤ 5507059626071^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713551759 10000000000 5507059626071 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989293097/10000000000 : ℝ)^5111 ≤ (8383252170059/20000000000000 : ℝ)^4087 := by
    have hnat : (4989293097 : ℕ)^5111*20000000000000^4087 ≤ 8383252170059^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989293097 10000000000 8383252170059 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474037997/10000000000 : ℝ)^5111 ≤ (2353480994601/5000000000000 : ℝ)^4087 := by
    have hnat : (5474037997 : ℕ)^5111*5000000000000^4087 ≤ 2353480994601^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474037997 10000000000 2353480994601 5000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1713551759/10000000000 : ℝ), (4989293097/10000000000 : ℝ), (5474037997/10000000000 : ℝ)] ![(5507059626071/50000000000000 : ℝ), (8383252170059/20000000000000 : ℝ), (2353480994601/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1713551759/10000000000 : ℝ)|^5111 ≤ (5507059626071/50000000000000 : ℝ)^4087
        have hw : |(-1713551759/10000000000 : ℝ)|=(1713551759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989293097/10000000000 : ℝ)|^5111 ≤ (8383252170059/20000000000000 : ℝ)^4087
        have hw : |(4989293097/10000000000 : ℝ)|=(4989293097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474037997/10000000000 : ℝ)|^5111 ≤ (2353480994601/5000000000000 : ℝ)^4087
        have hw : |(5474037997/10000000000 : ℝ)|=(5474037997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_9 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598126197/5000000000 : ℝ)*x 0 + (-1435766121/10000000000 : ℝ)*x 1 + (1368509723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598126197/5000000000 : ℝ)^5111 ≤ (44101796106339/100000000000000 : ℝ)^4087 := by
    have hnat : (2598126197 : ℕ)^5111*100000000000000^4087 ≤ 44101796106339^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598126197 5000000000 44101796106339 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435766121/10000000000 : ℝ)^5111 ≤ (8828574359323/100000000000000 : ℝ)^4087 := by
    have hnat : (1435766121 : ℕ)^5111*100000000000000^4087 ≤ 8828574359323^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435766121 10000000000 8828574359323 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368509723/2500000000 : ℝ)^5111 ≤ (23534814758027/50000000000000 : ℝ)^4087 := by
    have hnat : (1368509723 : ℕ)^5111*50000000000000^4087 ≤ 23534814758027^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368509723 2500000000 23534814758027 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598126197/5000000000 : ℝ), (-1435766121/10000000000 : ℝ), (1368509723/2500000000 : ℝ)] ![(44101796106339/100000000000000 : ℝ), (8828574359323/100000000000000 : ℝ), (23534814758027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598126197/5000000000 : ℝ)|^5111 ≤ (44101796106339/100000000000000 : ℝ)^4087
        have hw : |(2598126197/5000000000 : ℝ)|=(2598126197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1435766121/10000000000 : ℝ)|^5111 ≤ (8828574359323/100000000000000 : ℝ)^4087
        have hw : |(-1435766121/10000000000 : ℝ)|=(1435766121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368509723/2500000000 : ℝ)|^5111 ≤ (23534814758027/50000000000000 : ℝ)^4087
        have hw : |(1368509723/2500000000 : ℝ)|=(1368509723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_10 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039250481/2000000000 : ℝ)*x 0 + (1368509729/2500000000 : ℝ)*x 1 + (-1435766073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039250481/2000000000 : ℝ)^5111 ≤ (4410179622309/10000000000000 : ℝ)^4087 := by
    have hnat : (1039250481 : ℕ)^5111*10000000000000^4087 ≤ 4410179622309^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039250481 2000000000 4410179622309 10000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368509729/2500000000 : ℝ)^5111 ≤ (47069629774129/100000000000000 : ℝ)^4087 := by
    have hnat : (1368509729 : ℕ)^5111*100000000000000^4087 ≤ 47069629774129^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368509729 2500000000 47069629774129 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435766073/10000000000 : ℝ)^5111 ≤ (8828573990219/100000000000000 : ℝ)^4087 := by
    have hnat : (1435766073 : ℕ)^5111*100000000000000^4087 ≤ 8828573990219^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435766073 10000000000 8828573990219 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039250481/2000000000 : ℝ), (1368509729/2500000000 : ℝ), (-1435766073/10000000000 : ℝ)] ![(4410179622309/10000000000000 : ℝ), (47069629774129/100000000000000 : ℝ), (8828573990219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039250481/2000000000 : ℝ)|^5111 ≤ (4410179622309/10000000000000 : ℝ)^4087
        have hw : |(1039250481/2000000000 : ℝ)|=(1039250481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368509729/2500000000 : ℝ)|^5111 ≤ (47069629774129/100000000000000 : ℝ)^4087
        have hw : |(1368509729/2500000000 : ℝ)|=(1368509729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1435766073/10000000000 : ℝ)|^5111 ≤ (8828573990219/100000000000000 : ℝ)^4087
        have hw : |(-1435766073/10000000000 : ℝ)|=(1435766073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_11 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4651389201/10000000000 : ℝ)*x 0 + (3899767233/10000000000 : ℝ)*x 1 + (155990613/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4651389201/10000000000 : ℝ)^5111 ≤ (38396827784613/100000000000000 : ℝ)^4087 := by
    have hnat : (4651389201 : ℕ)^5111*100000000000000^4087 ≤ 38396827784613^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651389201 10000000000 38396827784613 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3899767233/10000000000 : ℝ)^5111 ≤ (1540079775999/5000000000000 : ℝ)^4087 := by
    have hnat : (3899767233 : ℕ)^5111*5000000000000^4087 ≤ 1540079775999^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3899767233 10000000000 1540079775999 5000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155990613/400000000 : ℝ)^5111 ≤ (154007883371/500000000000 : ℝ)^4087 := by
    have hnat : (155990613 : ℕ)^5111*500000000000^4087 ≤ 154007883371^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155990613 400000000 154007883371 500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4651389201/10000000000 : ℝ), (3899767233/10000000000 : ℝ), (155990613/400000000 : ℝ)] ![(38396827784613/100000000000000 : ℝ), (1540079775999/5000000000000 : ℝ), (154007883371/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4651389201/10000000000 : ℝ)|^5111 ≤ (38396827784613/100000000000000 : ℝ)^4087
        have hw : |(4651389201/10000000000 : ℝ)|=(4651389201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3899767233/10000000000 : ℝ)|^5111 ≤ (1540079775999/5000000000000 : ℝ)^4087
        have hw : |(3899767233/10000000000 : ℝ)|=(3899767233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155990613/400000000 : ℝ)|^5111 ≤ (154007883371/500000000000 : ℝ)^4087
        have hw : |(155990613/400000000 : ℝ)|=(155990613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_12 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-327579657/2500000000 : ℝ)*x 0 + (5607465597/10000000000 : ℝ)*x 1 + (257524109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327579657/2500000000 : ℝ)^5111 ≤ (393736105477/5000000000000 : ℝ)^4087 := by
    have hnat : (327579657 : ℕ)^5111*5000000000000^4087 ≤ 393736105477^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327579657 2500000000 393736105477 5000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607465597/10000000000 : ℝ)^5111 ≤ (48508736379961/100000000000000 : ℝ)^4087 := by
    have hnat : (5607465597 : ℕ)^5111*100000000000000^4087 ≤ 48508736379961^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607465597 10000000000 48508736379961 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257524109/500000000 : ℝ)^5111 ≤ (43616541492761/100000000000000 : ℝ)^4087 := by
    have hnat : (257524109 : ℕ)^5111*100000000000000^4087 ≤ 43616541492761^4087*500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257524109 500000000 43616541492761 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327579657/2500000000 : ℝ), (5607465597/10000000000 : ℝ), (257524109/500000000 : ℝ)] ![(393736105477/5000000000000 : ℝ), (48508736379961/100000000000000 : ℝ), (43616541492761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327579657/2500000000 : ℝ)|^5111 ≤ (393736105477/5000000000000 : ℝ)^4087
        have hw : |(-327579657/2500000000 : ℝ)|=(327579657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607465597/10000000000 : ℝ)|^5111 ≤ (48508736379961/100000000000000 : ℝ)^4087
        have hw : |(5607465597/10000000000 : ℝ)|=(5607465597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257524109/500000000 : ℝ)|^5111 ≤ (43616541492761/100000000000000 : ℝ)^4087
        have hw : |(257524109/500000000 : ℝ)|=(257524109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_13 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083399701/2000000000 : ℝ)*x 0 + (-788417613/5000000000 : ℝ)*x 1 + (2575241077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083399701/2000000000 : ℝ)^5111 ≤ (46457070650251/100000000000000 : ℝ)^4087 := by
    have hnat : (1083399701 : ℕ)^5111*100000000000000^4087 ≤ 46457070650251^4087*2000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083399701 2000000000 46457070650251 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788417613/5000000000 : ℝ)^5111 ≤ (1985277624721/20000000000000 : ℝ)^4087 := by
    have hnat : (788417613 : ℕ)^5111*20000000000000^4087 ≤ 1985277624721^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788417613 5000000000 1985277624721 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575241077/5000000000 : ℝ)^5111 ≤ (5452067652177/12500000000000 : ℝ)^4087 := by
    have hnat : (2575241077 : ℕ)^5111*12500000000000^4087 ≤ 5452067652177^4087*5000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575241077 5000000000 5452067652177 12500000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083399701/2000000000 : ℝ), (-788417613/5000000000 : ℝ), (2575241077/5000000000 : ℝ)] ![(46457070650251/100000000000000 : ℝ), (1985277624721/20000000000000 : ℝ), (5452067652177/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083399701/2000000000 : ℝ)|^5111 ≤ (46457070650251/100000000000000 : ℝ)^4087
        have hw : |(1083399701/2000000000 : ℝ)|=(1083399701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-788417613/5000000000 : ℝ)|^5111 ≤ (1985277624721/20000000000000 : ℝ)^4087
        have hw : |(-788417613/5000000000 : ℝ)|=(788417613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575241077/5000000000 : ℝ)|^5111 ≤ (5452067652177/12500000000000 : ℝ)^4087
        have hw : |(2575241077/5000000000 : ℝ)|=(2575241077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_14 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216679943/400000000 : ℝ)*x 0 + (5150482021/10000000000 : ℝ)*x 1 + (-1576835309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216679943/400000000 : ℝ)^5111 ≤ (9291414280199/20000000000000 : ℝ)^4087 := by
    have hnat : (216679943 : ℕ)^5111*20000000000000^4087 ≤ 9291414280199^4087*400000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216679943 400000000 9291414280199 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150482021/10000000000 : ℝ)^5111 ≤ (21808269904459/50000000000000 : ℝ)^4087 := by
    have hnat : (5150482021 : ℕ)^5111*50000000000000^4087 ≤ 21808269904459^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150482021 10000000000 21808269904459 50000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576835309/10000000000 : ℝ)^5111 ≤ (9926388777013/100000000000000 : ℝ)^4087 := by
    have hnat : (1576835309 : ℕ)^5111*100000000000000^4087 ≤ 9926388777013^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576835309 10000000000 9926388777013 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216679943/400000000 : ℝ), (5150482021/10000000000 : ℝ), (-1576835309/10000000000 : ℝ)] ![(9291414280199/20000000000000 : ℝ), (21808269904459/50000000000000 : ℝ), (9926388777013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216679943/400000000 : ℝ)|^5111 ≤ (9291414280199/20000000000000 : ℝ)^4087
        have hw : |(216679943/400000000 : ℝ)|=(216679943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150482021/10000000000 : ℝ)|^5111 ≤ (21808269904459/50000000000000 : ℝ)^4087
        have hw : |(5150482021/10000000000 : ℝ)|=(5150482021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576835309/10000000000 : ℝ)|^5111 ≤ (9926388777013/100000000000000 : ℝ)^4087
        have hw : |(-1576835309/10000000000 : ℝ)|=(1576835309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1686_box_15 (p : ℝ) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (914127293/2500000000 : ℝ)*x 0 + (4397202443/10000000000 : ℝ)*x 1 + (4397202169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914127293/2500000000 : ℝ)^5111 ≤ (5683590588227/20000000000000 : ℝ)^4087 := by
    have hnat : (914127293 : ℕ)^5111*20000000000000^4087 ≤ 5683590588227^4087*2500000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914127293 2500000000 5683590588227 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397202443/10000000000 : ℝ)^5111 ≤ (35791024915691/100000000000000 : ℝ)^4087 := by
    have hnat : (4397202443 : ℕ)^5111*100000000000000^4087 ≤ 35791024915691^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397202443 10000000000 35791024915691 100000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4397202169/10000000000 : ℝ)^5111 ≤ (7158204425337/20000000000000 : ℝ)^4087 := by
    have hnat : (4397202169 : ℕ)^5111*20000000000000^4087 ≤ 7158204425337^4087*10000000000^5111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397202169 10000000000 7158204425337 20000000000000 5111 4087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5111/1024 : ℝ)) 5111 4087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(914127293/2500000000 : ℝ), (4397202443/10000000000 : ℝ), (4397202169/10000000000 : ℝ)] ![(5683590588227/20000000000000 : ℝ), (35791024915691/100000000000000 : ℝ), (7158204425337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(914127293/2500000000 : ℝ)|^5111 ≤ (5683590588227/20000000000000 : ℝ)^4087
        have hw : |(914127293/2500000000 : ℝ)|=(914127293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397202443/10000000000 : ℝ)|^5111 ≤ (35791024915691/100000000000000 : ℝ)^4087
        have hw : |(4397202443/10000000000 : ℝ)|=(4397202443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4397202169/10000000000 : ℝ)|^5111 ≤ (7158204425337/20000000000000 : ℝ)^4087
        have hw : |(4397202169/10000000000 : ℝ)|=(4397202169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1686_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66541/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11567/20000 : ℝ) ∧ (80663/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11259/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9791/100000 : ℝ) ^ (5103/1024 : ℝ) ≤ (2337917109767/250000000000000000 : ℝ) := by
    have hpowers : (9791/100000 : ℝ)^5103 ≤ (2337917109767/250000000000000000 : ℝ)^1024 := by
      have hnat : (9791 : ℕ)^5103*250000000000000000^1024 ≤ 2337917109767^1024*100000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9791 100000 2337917109767 250000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9791/100000 : ℝ)) (X := (2337917109767/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17263/100000 : ℝ) ^ (5103/1024 : ℝ) ≤ (3946266613585973/25000000000000000000 : ℝ) := by
    have hpowers : (17263/100000 : ℝ)^5103 ≤ (3946266613585973/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17263 : ℕ)^5103*25000000000000000000^1024 ≤ 3946266613585973^1024*100000^5103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17263 100000 3946266613585973 25000000000000000000 5103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17263/100000 : ℝ)) (X := (3946266613585973/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (125002337917109767/125000000000000000 : ℝ) ≤ (10000037531008819/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (125002337917109767/125000000000000000 : ℝ)^1024 ≤ (10000037531008819/10000000000000000 : ℝ)^5103 := by
      have hnat : (125002337917109767 : ℕ)^1024*10000000000000000^5103 ≤ 10000037531008819^5103*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125002337917109767 125000000000000000 10000037531008819 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037531008819/10000000000000000 : ℝ)) (X := (125002337917109767/125000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004180058324562673/25000000000000000000 : ℝ) ≤ (10000335496274009/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (25004180058324562673/25000000000000000000 : ℝ)^1024 ≤ (10000335496274009/10000000000000000 : ℝ)^5103 := by
      have hnat : (25004180058324562673 : ℕ)^1024*10000000000000000^5103 ≤ 10000335496274009^5103*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004180058324562673 25000000000000000000 10000335496274009 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000335496274009/10000000000000000 : ℝ)) (X := (25004180058324562673/25000000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503946266613585973/12500000000000000000 : ℝ) ≤ (10000633461539199/10000000000000000 : ℝ) ^ (5103/1024 : ℝ) := by
    have hpowers : (12503946266613585973/12500000000000000000 : ℝ)^1024 ≤ (10000633461539199/10000000000000000 : ℝ)^5103 := by
      have hnat : (12503946266613585973 : ℕ)^1024*10000000000000000^5103 ≤ 10000633461539199^5103*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503946266613585973 12500000000000000000 10000633461539199 10000000000000000 1024 5103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000633461539199/10000000000000000 : ℝ)) (X := (12503946266613585973/12500000000000000000 : ℝ)) (by norm_num) 5103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2337917109767/250000000000000000 : ℝ) ≤ ((18678611418968736247/18680000000000000000 : ℝ)+2*(29796526519/74720000000000 : ℝ)*(9791/100000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (18678611418968736247/18680000000000000000 : ℝ)+2*(29796526519/74720000000000 : ℝ)*(9791/100000 : ℝ)=(10000037531008819/10000000000000000 : ℝ) by norm_num, show 1+2*(2337917109767/250000000000000000 : ℝ)=(125002337917109767/125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3946266613585973/25000000000000000000 : ℝ)+(2337917109767/250000000000000000 : ℝ) ≤ ((18678611418968736247/18680000000000000000 : ℝ)+(29796526519/74720000000000 : ℝ)*((17263/100000 : ℝ)+(9791/100000 : ℝ)))^(5103/1024 : ℝ) := by
    rw [show (18678611418968736247/18680000000000000000 : ℝ)+(29796526519/74720000000000 : ℝ)*((17263/100000 : ℝ)+(9791/100000 : ℝ))=(10000335496274009/10000000000000000 : ℝ) by norm_num, show 1+(3946266613585973/25000000000000000000 : ℝ)+(2337917109767/250000000000000000 : ℝ)=(25004180058324562673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3946266613585973/25000000000000000000 : ℝ) ≤ ((18678611418968736247/18680000000000000000 : ℝ)+2*(29796526519/74720000000000 : ℝ)*(17263/100000 : ℝ))^(5103/1024 : ℝ) := by
    rw [show (18678611418968736247/18680000000000000000 : ℝ)+2*(29796526519/74720000000000 : ℝ)*(17263/100000 : ℝ)=(10000633461539199/10000000000000000 : ℝ) by norm_num, show 1+2*(3946266613585973/25000000000000000000 : ℝ)=(12503946266613585973/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18678611418968736247/18680000000000000000 : ℝ)*(X 1 0+X 2 0)+(29796526519/74720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9791/100000 : ℝ)) (hi := (17263/100000 : ℝ)) (c := (18678611418968736247/18680000000000000000 : ℝ)) (alpha := (29796526519/74720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18678611418968736247/18680000000000000000 : ℝ)*(X 0 1+X 2 1)+(29796526519/74720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9791/100000 : ℝ)) (hi := (17263/100000 : ℝ)) (c := (18678611418968736247/18680000000000000000 : ℝ)) (alpha := (29796526519/74720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18678611418968736247/18680000000000000000 : ℝ)*(X 0 2+X 1 2)+(29796526519/74720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5103/1024 : ℝ)) (lo := (9791/100000 : ℝ)) (hi := (17263/100000 : ℝ)) (c := (18678611418968736247/18680000000000000000 : ℝ)) (alpha := (29796526519/74720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-291330617/2500000000 : ℝ)*X 0 0+(217211799/400000000 : ℝ)*X 0 1+(2715148369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5226084509/10000000000 : ℝ)*X 1 0+(-727816933/5000000000 : ℝ)*X 1 1+(5430296283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226084529/10000000000 : ℝ)*X 2 0+(5430296303/10000000000 : ℝ)*X 2 1+(-1455633811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2260824491/5000000000 : ℝ)*X 0 0+(991795217/2500000000 : ℝ)*X 0 1+(3967181639/10000000000 : ℝ)*X 0 2+(2260824491/5000000000 : ℝ)*X 1 0+(991795217/2500000000 : ℝ)*X 1 1+(3967181639/10000000000 : ℝ)*X 1 2+(2260824491/5000000000 : ℝ)*X 2 0+(991795217/2500000000 : ℝ)*X 2 1+(3967181639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372643011/2000000000 : ℝ)*X 0 0+(2587907727/5000000000 : ℝ)*X 0 1+(2587907837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5399689449/10000000000 : ℝ)*X 1 0+(-1566297711/10000000000 : ℝ)*X 1 1+(207032617/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1079937879/2000000000 : ℝ)*X 2 0+(5175815577/10000000000 : ℝ)*X 2 1+(-78314879/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((467193303/1250000000 : ℝ)*X 0 0+(4358363641/10000000000 : ℝ)*X 0 1+(4358363951/10000000000 : ℝ)*X 0 2+(467193303/1250000000 : ℝ)*X 1 0+(4358363641/10000000000 : ℝ)*X 1 1+(4358363951/10000000000 : ℝ)*X 1 2+(467193303/1250000000 : ℝ)*X 2 0+(4358363641/10000000000 : ℝ)*X 2 1+(4358363951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1713551759/10000000000 : ℝ)*X 0 0+(4989293097/10000000000 : ℝ)*X 0 1+(5474037997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598126197/5000000000 : ℝ)*X 1 0+(-1435766121/10000000000 : ℝ)*X 1 1+(1368509723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1039250481/2000000000 : ℝ)*X 2 0+(1368509729/2500000000 : ℝ)*X 2 1+(-1435766073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4651389201/10000000000 : ℝ)*X 0 0+(3899767233/10000000000 : ℝ)*X 0 1+(155990613/400000000 : ℝ)*X 0 2+(4651389201/10000000000 : ℝ)*X 1 0+(3899767233/10000000000 : ℝ)*X 1 1+(155990613/400000000 : ℝ)*X 1 2+(4651389201/10000000000 : ℝ)*X 2 0+(3899767233/10000000000 : ℝ)*X 2 1+(155990613/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-327579657/2500000000 : ℝ)*X 0 0+(5607465597/10000000000 : ℝ)*X 0 1+(257524109/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1083399701/2000000000 : ℝ)*X 1 0+(-788417613/5000000000 : ℝ)*X 1 1+(2575241077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((216679943/400000000 : ℝ)*X 2 0+(5150482021/10000000000 : ℝ)*X 2 1+(-1576835309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((914127293/2500000000 : ℝ)*X 0 0+(4397202443/10000000000 : ℝ)*X 0 1+(4397202169/10000000000 : ℝ)*X 0 2+(914127293/2500000000 : ℝ)*X 1 0+(4397202443/10000000000 : ℝ)*X 1 1+(4397202169/10000000000 : ℝ)*X 1 2+(914127293/2500000000 : ℝ)*X 2 0+(4397202443/10000000000 : ℝ)*X 2 1+(4397202169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1686_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66541/100000 : ℝ) ≤ (-155367515910276398532291376265841/233500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1817993/25000000000000 : ℝ)*(upper1) + (4457409/100000000000000 : ℝ)*(lower4) + (25061583/50000000000000 : ℝ)*(upper5) + (323800791645633/25000000000000 : ℝ)*(major0) + (323800791645633/25000000000000 : ℝ)*(major1) + (323800791645633/25000000000000 : ℝ)*(major2) + (1581346447/100000000000000 : ℝ)*(sp1) + (620418259/50000000000000 : ℝ)*(sp2) + (188961341/25000000000000 : ℝ)*(sp3) + (1920155140241043/100000000000000 : ℝ)*(sp4) + (1920153676388861/100000000000000 : ℝ)*(sp5) + (192015401689879/10000000000000 : ℝ)*(sp6) + (692429836488069/100000000000000 : ℝ)*(sp7) + (23498853/20000000000000 : ℝ)*(sp12) + (692430592333433/100000000000000 : ℝ)*(f.failure) + (480038814433827/25000000000000 : ℝ)*(f.sum) + (4398281741181/934000000000000000000000000 : ℝ)*base65 + (1481130508187890649/467000000000000000000000000000000 : ℝ)*base68 + (1438915104050890649/467000000000000000000000000000000 : ℝ)*base70 + (11844324223890649/467000000000000000000000000000000 : ℝ)*base72 + (333527457709/186800000000000000000000000 : ℝ)*base74 + (2237079628498890649/467000000000000000000000000000000 : ℝ)*base76 + (1738644520543890649/467000000000000000000000000000000 : ℝ)*base78 + (715467689806890649/467000000000000000000000000000000 : ℝ)*base80 + (289062636951/934000000000000000000000000 : ℝ)*base82 + (2509523/625000000000000000000 : ℝ)*base89 + (2509523/625000000000000000000 : ℝ)*base91 + (2509523/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11567/20000 : ℝ) ≤ (270099068647704092238450663077169/467000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (178762309/100000000000000 : ℝ)*(lower0) + (111813581/50000000000000 : ℝ)*(lower1) + (79914047/100000000000000 : ℝ)*(lower3) + (418299/781250000000 : ℝ)*(lower5) + (696549368908509/50000000000000 : ℝ)*(major0) + (696549368908509/50000000000000 : ℝ)*(major1) + (696549368908509/50000000000000 : ℝ)*(major2) + (505535833661429/25000000000000 : ℝ)*(sp0) + (101107587941643/5000000000000 : ℝ)*(sp1) + (1011075201572699/50000000000000 : ℝ)*(sp2) + (744763130584171/100000000000000 : ℝ)*(sp3) + (1783163899/50000000000000 : ℝ)*(sp7) + (677843731/50000000000000 : ℝ)*(sp10) + (1684837429/20000000000000 : ℝ)*(sp12) + (744766696911969/100000000000000 : ℝ)*(f.failure) + (101107587941643/5000000000000 : ℝ)*(f.sum) + (4281901182803/1868000000000000000000000000 : ℝ)*base65 + (6830815388636224277/934000000000000000000000000000000 : ℝ)*base68 + (3422029272412224277/934000000000000000000000000000000 : ℝ)*base70 + (2064728192961775723/934000000000000000000000000000000 : ℝ)*base71 + (13143217625277/1868000000000000000000000000 : ℝ)*base74 + (422216358860224277/934000000000000000000000000000000 : ℝ)*base76 + (3274232123153775723/934000000000000000000000000000000 : ℝ)*base77 + (3071378639650224277/934000000000000000000000000000000 : ℝ)*base80 + (6876658655687/1868000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2240661/625000000000000000000 : ℝ)*base90 + (2240661/625000000000000000000 : ℝ)*base92 + (2240661/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80663/100000 : ℝ) ≤ (188353063106452505908060292596899/233500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8348753/50000000000000 : ℝ)*(upper1) + (30671831/20000000000000 : ℝ)*(upper3) + (83967807/100000000000000 : ℝ)*(upper4) + (19921149/100000000000000 : ℝ)*(lower5) + (713062897991039/50000000000000 : ℝ)*(major0) + (713062897991039/50000000000000 : ℝ)*(major1) + (713062897991039/50000000000000 : ℝ)*(major2) + (2741690019/25000000000000 : ℝ)*(sp1) + (38352863687/100000000000000 : ℝ)*(sp2) + (1634794553/100000000000000 : ℝ)*(sp3) + (103146993666281/5000000000000 : ℝ)*(sp8) + (257866113320693/12500000000000 : ℝ)*(sp9) + (1031450760230967/50000000000000 : ℝ)*(sp10) + (762421709381957/100000000000000 : ℝ)*(sp11) + (76242334417651/10000000000000 : ℝ)*(f.failure) + (103146993666281/5000000000000 : ℝ)*(f.sum) + (1637359825877/1868000000000000000000000000 : ℝ)*base65 + (3276458913979259367/934000000000000000000000000000000 : ℝ)*base68 + (3555224670117259367/934000000000000000000000000000000 : ℝ)*base70 + (1427123711688740633/934000000000000000000000000000000 : ℝ)*base71 + (322507274781/1868000000000000000000000000 : ℝ)*base73 + (2271116279461259367/934000000000000000000000000000000 : ℝ)*base76 + (9130695232893259367/934000000000000000000000000000000 : ℝ)*base78 + (8593186259689259367/934000000000000000000000000000000 : ℝ)*base80 + (6313540608237/1868000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (742881/62500000000000000000 : ℝ)*base89 + (742881/62500000000000000000 : ℝ)*base91 + (742881/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-11259/12500 : ℝ) ≤ (-210312234680282835471834790551003/233500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11650537/100000000000000 : ℝ)*(upper1) + (8701217/25000000000000 : ℝ)*(upper3) + (16044553/100000000000000 : ℝ)*(upper5) + (368202934655583/25000000000000 : ℝ)*(major0) + (368202934655583/25000000000000 : ℝ)*(major1) + (368202934655583/25000000000000 : ℝ)*(major2) + (306636481/25000000000000 : ℝ)*(sp4) + (12612302613/100000000000000 : ℝ)*(sp5) + (21461765613/100000000000000 : ℝ)*(sp6) + (1802741181/25000000000000 : ℝ)*(sp7) + (2188263221487619/100000000000000 : ℝ)*(sp12) + (218825183573093/10000000000000 : ℝ)*(sp13) + (218824298626793/10000000000000 : ℝ)*(sp14) + (787374978086549/100000000000000 : ℝ)*(sp15) + (787382189051273/100000000000000 : ℝ)*(f.failure) + (2188264448033543/100000000000000 : ℝ)*(f.sum) + (1104744104191/934000000000000000000000000 : ℝ)*base66 + (185264337997267001/467000000000000000000000000000000 : ℝ)*base67 + (1250358654859732999/467000000000000000000000000000000 : ℝ)*base70 + (1265822032210267001/467000000000000000000000000000000 : ℝ)*base71 + (289795532947/186800000000000000000000000 : ℝ)*base74 + (1518363673242732999/467000000000000000000000000000000 : ℝ)*base76 + (1514974005144267001/467000000000000000000000000000000 : ℝ)*base77 + (251397519333267001/467000000000000000000000000000000 : ℝ)*base79 + (5314665551353/934000000000000000000000000 : ℝ)*base82 + (2850563/625000000000000000000 : ℝ)*base89 + (2850563/625000000000000000000 : ℝ)*base91 + (2850563/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1686_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66541/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11567/20000 : ℝ) else (80663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11259/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1686_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1686_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66541/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11567/20000 : ℝ) else (80663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11259/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1686_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1686_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1686_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5103/1024 : ℝ) ≤ p) (hpb : p ≤ (5111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11690731/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1729/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66541/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11567/20000 : ℝ) else (80663/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11259/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1686_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

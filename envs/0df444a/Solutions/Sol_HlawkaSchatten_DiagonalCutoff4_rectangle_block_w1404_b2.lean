-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:19.267787+00:00
-- url     : https://prove2.me/submissions/b6b27cb1-5202-4239-afe6-8b11a49d940d

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
theorem support_rectangle_w1404_s6_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991594009/10000000000 : ℝ)*x 0 + (1081903401/2000000000 : ℝ)*x 1 + (2623156369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991594009/10000000000 : ℝ)^1091 ≤ (12143531731461/100000000000000 : ℝ)^835 := by
    have hnat : (1991594009 : ℕ)^1091*100000000000000^835 ≤ 12143531731461^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991594009 10000000000 12143531731461 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081903401/2000000000 : ℝ)^1091 ≤ (11201815296673/25000000000000 : ℝ)^835 := by
    have hnat : (1081903401 : ℕ)^1091*25000000000000^835 ≤ 11201815296673^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081903401 2000000000 11201815296673 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623156369/5000000000 : ℝ)^1091 ≤ (43049207076329/100000000000000 : ℝ)^835 := by
    have hnat : (2623156369 : ℕ)^1091*100000000000000^835 ≤ 43049207076329^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623156369 5000000000 43049207076329 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991594009/10000000000 : ℝ), (1081903401/2000000000 : ℝ), (2623156369/5000000000 : ℝ)] ![(12143531731461/100000000000000 : ℝ), (11201815296673/25000000000000 : ℝ), (43049207076329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991594009/10000000000 : ℝ)|^1091 ≤ (12143531731461/100000000000000 : ℝ)^835
        have hw : |(-1991594009/10000000000 : ℝ)|=(1991594009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081903401/2000000000 : ℝ)|^1091 ≤ (11201815296673/25000000000000 : ℝ)^835
        have hw : |(1081903401/2000000000 : ℝ)|=(1081903401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623156369/5000000000 : ℝ)|^1091 ≤ (43049207076329/100000000000000 : ℝ)^835
        have hw : |(2623156369/5000000000 : ℝ)|=(2623156369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668480413/1250000000 : ℝ)*x 0 + (-2074701647/10000000000 : ℝ)*x 1 + (2623156369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668480413/1250000000 : ℝ)^1091 ≤ (11035241566003/25000000000000 : ℝ)^835 := by
    have hnat : (668480413 : ℕ)^1091*25000000000000^835 ≤ 11035241566003^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668480413 1250000000 11035241566003 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074701647/10000000000 : ℝ)^1091 ≤ (6404913325779/50000000000000 : ℝ)^835 := by
    have hnat : (2074701647 : ℕ)^1091*50000000000000^835 ≤ 6404913325779^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074701647 10000000000 6404913325779 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623156369/5000000000 : ℝ)^1091 ≤ (43049207076329/100000000000000 : ℝ)^835 := by
    have hnat : (2623156369 : ℕ)^1091*100000000000000^835 ≤ 43049207076329^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623156369 5000000000 43049207076329 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668480413/1250000000 : ℝ), (-2074701647/10000000000 : ℝ), (2623156369/5000000000 : ℝ)] ![(11035241566003/25000000000000 : ℝ), (6404913325779/50000000000000 : ℝ), (43049207076329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668480413/1250000000 : ℝ)|^1091 ≤ (11035241566003/25000000000000 : ℝ)^835
        have hw : |(668480413/1250000000 : ℝ)|=(668480413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074701647/10000000000 : ℝ)|^1091 ≤ (6404913325779/50000000000000 : ℝ)^835
        have hw : |(-2074701647/10000000000 : ℝ)|=(2074701647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623156369/5000000000 : ℝ)|^1091 ≤ (43049207076329/100000000000000 : ℝ)^835
        have hw : |(2623156369/5000000000 : ℝ)|=(2623156369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668480413/1250000000 : ℝ)*x 0 + (2623156369/5000000000 : ℝ)*x 1 + (-2074701647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668480413/1250000000 : ℝ)^1091 ≤ (11035241566003/25000000000000 : ℝ)^835 := by
    have hnat : (668480413 : ℕ)^1091*25000000000000^835 ≤ 11035241566003^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668480413 1250000000 11035241566003 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623156369/5000000000 : ℝ)^1091 ≤ (43049207076329/100000000000000 : ℝ)^835 := by
    have hnat : (2623156369 : ℕ)^1091*100000000000000^835 ≤ 43049207076329^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623156369 5000000000 43049207076329 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074701647/10000000000 : ℝ)^1091 ≤ (6404913325779/50000000000000 : ℝ)^835 := by
    have hnat : (2074701647 : ℕ)^1091*50000000000000^835 ≤ 6404913325779^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074701647 10000000000 6404913325779 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668480413/1250000000 : ℝ), (2623156369/5000000000 : ℝ), (-2074701647/10000000000 : ℝ)] ![(11035241566003/25000000000000 : ℝ), (43049207076329/100000000000000 : ℝ), (6404913325779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668480413/1250000000 : ℝ)|^1091 ≤ (11035241566003/25000000000000 : ℝ)^835
        have hw : |(668480413/1250000000 : ℝ)|=(668480413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623156369/5000000000 : ℝ)|^1091 ≤ (43049207076329/100000000000000 : ℝ)^835
        have hw : |(2623156369/5000000000 : ℝ)|=(2623156369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074701647/10000000000 : ℝ)|^1091 ≤ (6404913325779/50000000000000 : ℝ)^835
        have hw : |(-2074701647/10000000000 : ℝ)|=(2074701647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (86213279/200000000 : ℝ)*x 0 + (165558961/400000000 : ℝ)*x 1 + (4488808077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86213279/200000000 : ℝ)^1091 ≤ (4163036672887/12500000000000 : ℝ)^835 := by
    have hnat : (86213279 : ℕ)^1091*12500000000000^835 ≤ 4163036672887^835*200000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86213279 200000000 4163036672887 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165558961/400000000 : ℝ)^1091 ≤ (31581812434751/100000000000000 : ℝ)^835 := by
    have hnat : (165558961 : ℕ)^1091*100000000000000^835 ≤ 31581812434751^835*400000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165558961 400000000 31581812434751 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488808077/10000000000 : ℝ)^1091 ≤ (35113894167311/100000000000000 : ℝ)^835 := by
    have hnat : (4488808077 : ℕ)^1091*100000000000000^835 ≤ 35113894167311^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488808077 10000000000 35113894167311 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86213279/200000000 : ℝ), (165558961/400000000 : ℝ), (4488808077/10000000000 : ℝ)] ![(4163036672887/12500000000000 : ℝ), (31581812434751/100000000000000 : ℝ), (35113894167311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86213279/200000000 : ℝ)|^1091 ≤ (4163036672887/12500000000000 : ℝ)^835
        have hw : |(86213279/200000000 : ℝ)|=(86213279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165558961/400000000 : ℝ)|^1091 ≤ (31581812434751/100000000000000 : ℝ)^835
        have hw : |(165558961/400000000 : ℝ)|=(165558961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488808077/10000000000 : ℝ)|^1091 ≤ (35113894167311/100000000000000 : ℝ)^835
        have hw : |(4488808077/10000000000 : ℝ)|=(4488808077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991605499/10000000000 : ℝ)*x 0 + (2623450091/5000000000 : ℝ)*x 1 + (5408926573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991605499/10000000000 : ℝ)^1091 ≤ (12143623269771/100000000000000 : ℝ)^835 := by
    have hnat : (1991605499 : ℕ)^1091*100000000000000^835 ≤ 12143623269771^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991605499 10000000000 12143623269771 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623450091/5000000000 : ℝ)^1091 ≤ (21527752687001/50000000000000 : ℝ)^835 := by
    have hnat : (2623450091 : ℕ)^1091*50000000000000^835 ≤ 21527752687001^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623450091 5000000000 21527752687001 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408926573/10000000000 : ℝ)^1091 ≤ (22400435667311/50000000000000 : ℝ)^835 := by
    have hnat : (5408926573 : ℕ)^1091*50000000000000^835 ≤ 22400435667311^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408926573 10000000000 22400435667311 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991605499/10000000000 : ℝ), (2623450091/5000000000 : ℝ), (5408926573/10000000000 : ℝ)] ![(12143623269771/100000000000000 : ℝ), (21527752687001/50000000000000 : ℝ), (22400435667311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991605499/10000000000 : ℝ)|^1091 ≤ (12143623269771/100000000000000 : ℝ)^835
        have hw : |(-1991605499/10000000000 : ℝ)|=(1991605499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623450091/5000000000 : ℝ)|^1091 ≤ (21527752687001/50000000000000 : ℝ)^835
        have hw : |(2623450091/5000000000 : ℝ)|=(2623450091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408926573/10000000000 : ℝ)|^1091 ≤ (22400435667311/50000000000000 : ℝ)^835
        have hw : |(5408926573/10000000000 : ℝ)|=(5408926573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331595049/625000000 : ℝ)*x 0 + (-1912087771/10000000000 : ℝ)*x 1 + (1081785319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331595049/625000000 : ℝ)^1091 ≤ (43685092287153/100000000000000 : ℝ)^835 := by
    have hnat : (331595049 : ℕ)^1091*100000000000000^835 ≤ 43685092287153^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331595049 625000000 43685092287153 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912087771/10000000000 : ℝ)^1091 ≤ (11514036129927/100000000000000 : ℝ)^835 := by
    have hnat : (1912087771 : ℕ)^1091*100000000000000^835 ≤ 11514036129927^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912087771 10000000000 11514036129927 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081785319/2000000000 : ℝ)^1091 ≤ (44800871572709/100000000000000 : ℝ)^835 := by
    have hnat : (1081785319 : ℕ)^1091*100000000000000^835 ≤ 44800871572709^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081785319 2000000000 44800871572709 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331595049/625000000 : ℝ), (-1912087771/10000000000 : ℝ), (1081785319/2000000000 : ℝ)] ![(43685092287153/100000000000000 : ℝ), (11514036129927/100000000000000 : ℝ), (44800871572709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331595049/625000000 : ℝ)|^1091 ≤ (43685092287153/100000000000000 : ℝ)^835
        have hw : |(331595049/625000000 : ℝ)|=(331595049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912087771/10000000000 : ℝ)|^1091 ≤ (11514036129927/100000000000000 : ℝ)^835
        have hw : |(-1912087771/10000000000 : ℝ)|=(1912087771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081785319/2000000000 : ℝ)|^1091 ≤ (44800871572709/100000000000000 : ℝ)^835
        have hw : |(1081785319/2000000000 : ℝ)|=(1081785319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305520753/10000000000 : ℝ)*x 0 + (1352231659/2500000000 : ℝ)*x 1 + (-478021939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305520753/10000000000 : ℝ)^1091 ≤ (21842545976823/50000000000000 : ℝ)^835 := by
    have hnat : (5305520753 : ℕ)^1091*50000000000000^835 ≤ 21842545976823^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305520753 10000000000 21842545976823 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352231659/2500000000 : ℝ)^1091 ≤ (22400436008209/50000000000000 : ℝ)^835 := by
    have hnat : (1352231659 : ℕ)^1091*50000000000000^835 ≤ 22400436008209^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352231659 2500000000 22400436008209 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478021939/2500000000 : ℝ)^1091 ≤ (2878509002977/25000000000000 : ℝ)^835 := by
    have hnat : (478021939 : ℕ)^1091*25000000000000^835 ≤ 2878509002977^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478021939 2500000000 2878509002977 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305520753/10000000000 : ℝ), (1352231659/2500000000 : ℝ), (-478021939/2500000000 : ℝ)] ![(21842545976823/50000000000000 : ℝ), (22400436008209/50000000000000 : ℝ), (2878509002977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305520753/10000000000 : ℝ)|^1091 ≤ (21842545976823/50000000000000 : ℝ)^835
        have hw : |(5305520753/10000000000 : ℝ)|=(5305520753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352231659/2500000000 : ℝ)|^1091 ≤ (22400436008209/50000000000000 : ℝ)^835
        have hw : |(1352231659/2500000000 : ℝ)|=(1352231659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478021939/2500000000 : ℝ)|^1091 ≤ (2878509002977/25000000000000 : ℝ)^835
        have hw : |(-478021939/2500000000 : ℝ)|=(478021939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s6_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2155344377/5000000000 : ℝ)*x 0 + (2243774477/5000000000 : ℝ)*x 1 + (4140239633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155344377/5000000000 : ℝ)^1091 ≤ (33304543772783/100000000000000 : ℝ)^835 := by
    have hnat : (2155344377 : ℕ)^1091*100000000000000^835 ≤ 33304543772783^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155344377 5000000000 33304543772783 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243774477/5000000000 : ℝ)^1091 ≤ (35101025436541/100000000000000 : ℝ)^835 := by
    have hnat : (2243774477 : ℕ)^1091*100000000000000^835 ≤ 35101025436541^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243774477 5000000000 35101025436541 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140239633/10000000000 : ℝ)^1091 ≤ (1974651923359/6250000000000 : ℝ)^835 := by
    have hnat : (4140239633 : ℕ)^1091*6250000000000^835 ≤ 1974651923359^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140239633 10000000000 1974651923359 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155344377/5000000000 : ℝ), (2243774477/5000000000 : ℝ), (4140239633/10000000000 : ℝ)] ![(33304543772783/100000000000000 : ℝ), (35101025436541/100000000000000 : ℝ), (1974651923359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155344377/5000000000 : ℝ)|^1091 ≤ (33304543772783/100000000000000 : ℝ)^835
        have hw : |(2155344377/5000000000 : ℝ)|=(2155344377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243774477/5000000000 : ℝ)|^1091 ≤ (35101025436541/100000000000000 : ℝ)^835
        have hw : |(2243774477/5000000000 : ℝ)|=(2243774477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140239633/10000000000 : ℝ)|^1091 ≤ (1974651923359/6250000000000 : ℝ)^835
        have hw : |(4140239633/10000000000 : ℝ)|=(4140239633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1843/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11283/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (9175409729652943/100000000000000000000 : ℝ) := by
    have hpowers : (11283/100000 : ℝ)^4363 ≤ (9175409729652943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11283 : ℕ)^4363*100000000000000000000^1024 ≤ 9175409729652943^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11283 100000 9175409729652943 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11283/100000 : ℝ)) (X := (9175409729652943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (28728413168014003/100000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^4363 ≤ (28728413168014003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14749 : ℕ)^4363*100000000000000000000^1024 ≤ 28728413168014003^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 28728413168014003 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (28728413168014003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009175409729652943/50000000000000000000 : ℝ) ≤ (10000430665133179/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50009175409729652943/50000000000000000000 : ℝ)^1024 ≤ (10000430665133179/10000000000000000 : ℝ)^4363 := by
      have hnat : (50009175409729652943 : ℕ)^1024*10000000000000000^4363 ≤ 10000430665133179^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009175409729652943 50000000000000000000 10000430665133179 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000430665133179/10000000000000000 : ℝ)) (X := (50009175409729652943/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018951911448833473/50000000000000000000 : ℝ) ≤ (10000889477112917/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50018951911448833473/50000000000000000000 : ℝ)^1024 ≤ (10000889477112917/10000000000000000 : ℝ)^4363 := by
      have hnat : (50018951911448833473 : ℕ)^1024*10000000000000000^4363 ≤ 10000889477112917^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018951911448833473 50000000000000000000 10000889477112917 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000889477112917/10000000000000000 : ℝ)) (X := (50018951911448833473/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028728413168014003/50000000000000000000 : ℝ) ≤ (2000269657818531/2000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50028728413168014003/50000000000000000000 : ℝ)^1024 ≤ (2000269657818531/2000000000000000 : ℝ)^4363 := by
      have hnat : (50028728413168014003 : ℕ)^1024*2000000000000000^4363 ≤ 2000269657818531^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028728413168014003 50000000000000000000 2000269657818531 2000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000269657818531/2000000000000000 : ℝ)) (X := (50028728413168014003/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9175409729652943/100000000000000000000 : ℝ) ≤ ((17325569567108415353/17330000000000000000 : ℝ)+2*(229405989869/173300000000000 : ℝ)*(11283/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (17325569567108415353/17330000000000000000 : ℝ)+2*(229405989869/173300000000000 : ℝ)*(11283/100000 : ℝ)=(10000430665133179/10000000000000000 : ℝ) by norm_num, show 1+2*(9175409729652943/100000000000000000000 : ℝ)=(50009175409729652943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28728413168014003/100000000000000000000 : ℝ)+(9175409729652943/100000000000000000000 : ℝ) ≤ ((17325569567108415353/17330000000000000000 : ℝ)+(229405989869/173300000000000 : ℝ)*((14749/100000 : ℝ)+(11283/100000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (17325569567108415353/17330000000000000000 : ℝ)+(229405989869/173300000000000 : ℝ)*((14749/100000 : ℝ)+(11283/100000 : ℝ))=(10000889477112917/10000000000000000 : ℝ) by norm_num, show 1+(28728413168014003/100000000000000000000 : ℝ)+(9175409729652943/100000000000000000000 : ℝ)=(50018951911448833473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28728413168014003/100000000000000000000 : ℝ) ≤ ((17325569567108415353/17330000000000000000 : ℝ)+2*(229405989869/173300000000000 : ℝ)*(14749/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (17325569567108415353/17330000000000000000 : ℝ)+2*(229405989869/173300000000000 : ℝ)*(14749/100000 : ℝ)=(2000269657818531/2000000000000000 : ℝ) by norm_num, show 1+2*(28728413168014003/100000000000000000000 : ℝ)=(50028728413168014003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17325569567108415353/17330000000000000000 : ℝ)*(X 1 0+X 2 0)+(229405989869/173300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (17325569567108415353/17330000000000000000 : ℝ)) (alpha := (229405989869/173300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17325569567108415353/17330000000000000000 : ℝ)*(X 0 1+X 2 1)+(229405989869/173300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (17325569567108415353/17330000000000000000 : ℝ)) (alpha := (229405989869/173300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17325569567108415353/17330000000000000000 : ℝ)*(X 0 2+X 1 2)+(229405989869/173300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (17325569567108415353/17330000000000000000 : ℝ)) (alpha := (229405989869/173300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991594009/10000000000 : ℝ)*X 0 0+(1081903401/2000000000 : ℝ)*X 0 1+(2623156369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668480413/1250000000 : ℝ)*X 1 0+(-2074701647/10000000000 : ℝ)*X 1 1+(2623156369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668480413/1250000000 : ℝ)*X 2 0+(2623156369/5000000000 : ℝ)*X 2 1+(-2074701647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86213279/200000000 : ℝ)*X 0 0+(165558961/400000000 : ℝ)*X 0 1+(4488808077/10000000000 : ℝ)*X 0 2+(86213279/200000000 : ℝ)*X 1 0+(165558961/400000000 : ℝ)*X 1 1+(4488808077/10000000000 : ℝ)*X 1 2+(86213279/200000000 : ℝ)*X 2 0+(165558961/400000000 : ℝ)*X 2 1+(4488808077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1991605499/10000000000 : ℝ)*X 0 0+(2623450091/5000000000 : ℝ)*X 0 1+(5408926573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331595049/625000000 : ℝ)*X 1 0+(-1912087771/10000000000 : ℝ)*X 1 1+(1081785319/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305520753/10000000000 : ℝ)*X 2 0+(1352231659/2500000000 : ℝ)*X 2 1+(-478021939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155344377/5000000000 : ℝ)*X 0 0+(2243774477/5000000000 : ℝ)*X 0 1+(4140239633/10000000000 : ℝ)*X 0 2+(2155344377/5000000000 : ℝ)*X 1 0+(2243774477/5000000000 : ℝ)*X 1 1+(4140239633/10000000000 : ℝ)*X 1 2+(2155344377/5000000000 : ℝ)*X 2 0+(2243774477/5000000000 : ℝ)*X 2 1+(4140239633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112570506894037865873785899/43325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119247559/25000000000000 : ℝ)*(base19) + (222176589/50000000000000 : ℝ)*(base23) + (4363447/25000000000000 : ℝ)*(lower2) + (64964889/100000000000000 : ℝ)*(upper3) + (8226689/20000000000000 : ℝ)*(upper5) + (224645472609239/5000000000000 : ℝ)*(major0) + (224645472609239/5000000000000 : ℝ)*(major1) + (224645472609239/5000000000000 : ℝ)*(major2) + (765912645483407/12500000000000 : ℝ)*(sp0) + (765913829460401/12500000000000 : ℝ)*(sp1) + (3063655334160133/50000000000000 : ℝ)*(sp2) + (89328208725791/3125000000000 : ℝ)*(sp3) + (2487201547/25000000000000 : ℝ)*(sp4) + (1005172287/20000000000000 : ℝ)*(sp7) + (1429253852543373/50000000000000 : ℝ)*(f.failure) + (1531827778168361/25000000000000 : ℝ)*(f.sum) + (152547403539/866500000000000000000000000 : ℝ)*base66 + (856295881064446367/86650000000000000000000000000000 : ℝ)*base67 + (135198021589803633/86650000000000000000000000000000 : ℝ)*base70 + (330493340600046367/86650000000000000000000000000000 : ℝ)*base71 + (5124386524951/866500000000000000000000000 : ℝ)*base73 + (638659017284396367/86650000000000000000000000000000 : ℝ)*base75 + (1016106298487246367/86650000000000000000000000000000 : ℝ)*base77 + (1152661303745353633/86650000000000000000000000000000 : ℝ)*base80 + (1366059941277/1733000000000000000000000000 : ℝ)*base82 + (25727249/1250000000000000000000 : ℝ)*base90 + (25727249/1250000000000000000000 : ℝ)*base92 + (25727249/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312598990981040236871663403/43325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111479883/10000000000000 : ℝ)*(base19) + (1303365873/100000000000000 : ℝ)*(base23) + (138173/100000000000 : ℝ)*(upper3) + (49214817/50000000000000 : ℝ)*(lower4) + (15314093/12500000000000 : ℝ)*(upper5) + (226277714180617/5000000000000 : ℝ)*(major0) + (226277714180617/5000000000000 : ℝ)*(major1) + (226277714180617/5000000000000 : ℝ)*(major2) + (23812076177/100000000000000 : ℝ)*(sp1) + (14357166397/50000000000000 : ℝ)*(sp2) + (3085915558667651/50000000000000 : ℝ)*(sp4) + (3085903095230147/50000000000000 : ℝ)*(sp5) + (1234360219927327/20000000000000 : ℝ)*(sp6) + (2879277209382357/100000000000000 : ℝ)*(sp7) + (2879277209382357/100000000000000 : ℝ)*(f.failure) + (3085915558667651/50000000000000 : ℝ)*(f.sum) + (2036579918463/433250000000000000000000000 : ℝ)*base65 + (59916690800812801/86650000000000000000000000000000 : ℝ)*base67 + (191152159474437199/86650000000000000000000000000000 : ℝ)*base70 + (165096283950187199/86650000000000000000000000000000 : ℝ)*base72 + (9366890801487/1733000000000000000000000000 : ℝ)*base73 + (745466622684062801/86650000000000000000000000000000 : ℝ)*base75 + (88929047319737199/86650000000000000000000000000000 : ℝ)*base78 + (1316727807511387199/86650000000000000000000000000000 : ℝ)*base80 + (8257206158893/1733000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9541241/2500000000000000000000 : ℝ)*base90 + (9541241/2500000000000000000000 : ℝ)*base92 + (9541241/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1404_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_s7_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347833921/10000000000 : ℝ)*x 0 + (5246347783/10000000000 : ℝ)*x 1 + (-64833363/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347833921/10000000000 : ℝ)^1091 ≤ (5517608134093/12500000000000 : ℝ)^835 := by
    have hnat : (5347833921 : ℕ)^1091*12500000000000^835 ≤ 5517608134093^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347833921 10000000000 5517608134093 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246347783/10000000000 : ℝ)^1091 ≤ (10762395701559/25000000000000 : ℝ)^835 := by
    have hnat : (5246347783 : ℕ)^1091*25000000000000^835 ≤ 10762395701559^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246347783 10000000000 10762395701559 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64833363/312500000 : ℝ)^1091 ≤ (3202388028859/25000000000000 : ℝ)^835 := by
    have hnat : (64833363 : ℕ)^1091*25000000000000^835 ≤ 3202388028859^835*312500000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64833363 312500000 3202388028859 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347833921/10000000000 : ℝ), (5246347783/10000000000 : ℝ), (-64833363/312500000 : ℝ)] ![(5517608134093/12500000000000 : ℝ), (10762395701559/25000000000000 : ℝ), (3202388028859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347833921/10000000000 : ℝ)|^1091 ≤ (5517608134093/12500000000000 : ℝ)^835
        have hw : |(5347833921/10000000000 : ℝ)|=(5347833921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246347783/10000000000 : ℝ)|^1091 ≤ (10762395701559/25000000000000 : ℝ)^835
        have hw : |(5246347783/10000000000 : ℝ)|=(5246347783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64833363/312500000 : ℝ)|^1091 ≤ (3202388028859/25000000000000 : ℝ)^835
        have hw : |(-64833363/312500000 : ℝ)|=(64833363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s7_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991609129/10000000000 : ℝ)*x 0 + (2623467349/5000000000 : ℝ)*x 1 + (1081777941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991609129/10000000000 : ℝ)^1091 ≤ (6071826094609/50000000000000 : ℝ)^835 := by
    have hnat : (1991609129 : ℕ)^1091*50000000000000^835 ≤ 6071826094609^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991609129 10000000000 6071826094609 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623467349/5000000000 : ℝ)^1091 ≤ (43055875445009/100000000000000 : ℝ)^835 := by
    have hnat : (2623467349 : ℕ)^1091*100000000000000^835 ≤ 43055875445009^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623467349 5000000000 43055875445009 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081777941/2000000000 : ℝ)^1091 ≤ (560005904299/1250000000000 : ℝ)^835 := by
    have hnat : (1081777941 : ℕ)^1091*1250000000000^835 ≤ 560005904299^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081777941 2000000000 560005904299 1250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991609129/10000000000 : ℝ), (2623467349/5000000000 : ℝ), (1081777941/2000000000 : ℝ)] ![(6071826094609/50000000000000 : ℝ), (43055875445009/100000000000000 : ℝ), (560005904299/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991609129/10000000000 : ℝ)|^1091 ≤ (6071826094609/50000000000000 : ℝ)^835
        have hw : |(-1991609129/10000000000 : ℝ)|=(1991609129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623467349/5000000000 : ℝ)|^1091 ≤ (43055875445009/100000000000000 : ℝ)^835
        have hw : |(2623467349/5000000000 : ℝ)|=(2623467349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081777941/2000000000 : ℝ)|^1091 ≤ (560005904299/1250000000000 : ℝ)^835
        have hw : |(1081777941/2000000000 : ℝ)|=(1081777941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s7_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132638253/250000000 : ℝ)*x 0 + (-956062903/5000000000 : ℝ)*x 1 + (5408889661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132638253/250000000 : ℝ)^1091 ≤ (43685192726637/100000000000000 : ℝ)^835 := by
    have hnat : (132638253 : ℕ)^1091*100000000000000^835 ≤ 43685192726637^835*250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132638253 250000000 43685192726637 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956062903/5000000000 : ℝ)^1091 ≤ (1151433538587/10000000000000 : ℝ)^835 := by
    have hnat : (956062903 : ℕ)^1091*10000000000000^835 ≤ 1151433538587^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956062903 5000000000 1151433538587 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408889661/10000000000 : ℝ)^1091 ≤ (22400235933873/50000000000000 : ℝ)^835 := by
    have hnat : (5408889661 : ℕ)^1091*50000000000000^835 ≤ 22400235933873^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408889661 10000000000 22400235933873 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132638253/250000000 : ℝ), (-956062903/5000000000 : ℝ), (5408889661/10000000000 : ℝ)] ![(43685192726637/100000000000000 : ℝ), (1151433538587/10000000000000 : ℝ), (22400235933873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132638253/250000000 : ℝ)|^1091 ≤ (43685192726637/100000000000000 : ℝ)^835
        have hw : |(132638253/250000000 : ℝ)|=(132638253/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956062903/5000000000 : ℝ)|^1091 ≤ (1151433538587/10000000000000 : ℝ)^835
        have hw : |(-956062903/5000000000 : ℝ)|=(956062903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408889661/10000000000 : ℝ)|^1091 ≤ (22400235933873/50000000000000 : ℝ)^835
        have hw : |(5408889661/10000000000 : ℝ)|=(5408889661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s7_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530553011/1000000000 : ℝ)*x 0 + (5408889691/10000000000 : ℝ)*x 1 + (-956062889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530553011/1000000000 : ℝ)^1091 ≤ (21842596309527/50000000000000 : ℝ)^835 := by
    have hnat : (530553011 : ℕ)^1091*50000000000000^835 ≤ 21842596309527^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530553011 1000000000 21842596309527 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408889691/10000000000 : ℝ)^1091 ≤ (4480047219241/10000000000000 : ℝ)^835 := by
    have hnat : (5408889691 : ℕ)^1091*10000000000000^835 ≤ 4480047219241^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408889691 10000000000 4480047219241 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956062889/5000000000 : ℝ)^1091 ≤ (11514335165567/100000000000000 : ℝ)^835 := by
    have hnat : (956062889 : ℕ)^1091*100000000000000^835 ≤ 11514335165567^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956062889 5000000000 11514335165567 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530553011/1000000000 : ℝ), (5408889691/10000000000 : ℝ), (-956062889/5000000000 : ℝ)] ![(21842596309527/50000000000000 : ℝ), (4480047219241/10000000000000 : ℝ), (11514335165567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530553011/1000000000 : ℝ)|^1091 ≤ (21842596309527/50000000000000 : ℝ)^835
        have hw : |(530553011/1000000000 : ℝ)|=(530553011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408889691/10000000000 : ℝ)|^1091 ≤ (4480047219241/10000000000000 : ℝ)^835
        have hw : |(5408889691/10000000000 : ℝ)|=(5408889691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956062889/5000000000 : ℝ)|^1091 ≤ (11514335165567/100000000000000 : ℝ)^835
        have hw : |(-956062889/5000000000 : ℝ)|=(956062889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s7_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4310691243/10000000000 : ℝ)*x 0 + (1121868003/2500000000 : ℝ)*x 1 + (4140315979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310691243/10000000000 : ℝ)^1091 ≤ (33304568898591/100000000000000 : ℝ)^835 := by
    have hnat : (4310691243 : ℕ)^1091*100000000000000^835 ≤ 33304568898591^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310691243 10000000000 33304568898591 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121868003/2500000000 : ℝ)^1091 ≤ (17550119547509/50000000000000 : ℝ)^835 := by
    have hnat : (1121868003 : ℕ)^1091*50000000000000^835 ≤ 17550119547509^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121868003 2500000000 17550119547509 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140315979/10000000000 : ℝ)^1091 ≤ (1974699499681/6250000000000 : ℝ)^835 := by
    have hnat : (4140315979 : ℕ)^1091*6250000000000^835 ≤ 1974699499681^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140315979 10000000000 1974699499681 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310691243/10000000000 : ℝ), (1121868003/2500000000 : ℝ), (4140315979/10000000000 : ℝ)] ![(33304568898591/100000000000000 : ℝ), (17550119547509/50000000000000 : ℝ), (1974699499681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310691243/10000000000 : ℝ)|^1091 ≤ (33304568898591/100000000000000 : ℝ)^835
        have hw : |(4310691243/10000000000 : ℝ)|=(4310691243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121868003/2500000000 : ℝ)|^1091 ≤ (17550119547509/50000000000000 : ℝ)^835
        have hw : |(1121868003/2500000000 : ℝ)|=(1121868003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140315979/10000000000 : ℝ)|^1091 ≤ (1974699499681/6250000000000 : ℝ)^835
        have hw : |(4140315979/10000000000 : ℝ)|=(4140315979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (4363/1024 : ℝ) ≤ (4596373284090663/50000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^4363 ≤ (4596373284090663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4363*50000000000000000000^1024 ≤ 4596373284090663^1024*12500^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 4596373284090663 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (4596373284090663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1843/12500 : ℝ) ^ (4363/1024 : ℝ) ≤ (14343470139898027/50000000000000000000 : ℝ) := by
    have hpowers : (1843/12500 : ℝ)^4363 ≤ (14343470139898027/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1843 : ℕ)^4363*50000000000000000000^1024 ≤ 14343470139898027^1024*12500^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1843 12500 14343470139898027 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1843/12500 : ℝ)) (X := (14343470139898027/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004596373284090663/25000000000000000000 : ℝ) ≤ (5000215739406551/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25004596373284090663/25000000000000000000 : ℝ)^1024 ≤ (5000215739406551/5000000000000000 : ℝ)^4363 := by
      have hnat : (25004596373284090663 : ℕ)^1024*5000000000000000^4363 ≤ 5000215739406551^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004596373284090663 25000000000000000000 5000215739406551 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215739406551/5000000000000000 : ℝ)) (X := (25004596373284090663/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001893984342398869/5000000000000000000 : ℝ) ≤ (312527778462559/312500000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (5001893984342398869/5000000000000000000 : ℝ)^1024 ≤ (312527778462559/312500000000000 : ℝ)^4363 := by
      have hnat : (5001893984342398869 : ℕ)^1024*312500000000000^4363 ≤ 312527778462559^4363*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001893984342398869 5000000000000000000 312527778462559 312500000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312527778462559/312500000000000 : ℝ)) (X := (5001893984342398869/5000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014343470139898027/25000000000000000000 : ℝ) ≤ (5000673171395337/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25014343470139898027/25000000000000000000 : ℝ)^1024 ≤ (5000673171395337/5000000000000000 : ℝ)^4363 := by
      have hnat : (25014343470139898027 : ℕ)^1024*5000000000000000^4363 ≤ 5000673171395337^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014343470139898027 25000000000000000000 5000673171395337 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000673171395337/5000000000000000 : ℝ)) (X := (25014343470139898027/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4596373284090663/50000000000000000000 : ℝ) ≤ ((1079723881443726493/1080000000000000000 : ℝ)+2*(228715994393/172800000000000 : ℝ)*(1411/12500 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (1079723881443726493/1080000000000000000 : ℝ)+2*(228715994393/172800000000000 : ℝ)*(1411/12500 : ℝ)=(5000215739406551/5000000000000000 : ℝ) by norm_num, show 1+2*(4596373284090663/50000000000000000000 : ℝ)=(25004596373284090663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14343470139898027/50000000000000000000 : ℝ)+(4596373284090663/50000000000000000000 : ℝ) ≤ ((1079723881443726493/1080000000000000000 : ℝ)+(228715994393/172800000000000 : ℝ)*((1843/12500 : ℝ)+(1411/12500 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (1079723881443726493/1080000000000000000 : ℝ)+(228715994393/172800000000000 : ℝ)*((1843/12500 : ℝ)+(1411/12500 : ℝ))=(312527778462559/312500000000000 : ℝ) by norm_num, show 1+(14343470139898027/50000000000000000000 : ℝ)+(4596373284090663/50000000000000000000 : ℝ)=(5001893984342398869/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14343470139898027/50000000000000000000 : ℝ) ≤ ((1079723881443726493/1080000000000000000 : ℝ)+2*(228715994393/172800000000000 : ℝ)*(1843/12500 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (1079723881443726493/1080000000000000000 : ℝ)+2*(228715994393/172800000000000 : ℝ)*(1843/12500 : ℝ)=(5000673171395337/5000000000000000 : ℝ) by norm_num, show 1+2*(14343470139898027/50000000000000000000 : ℝ)=(25014343470139898027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1079723881443726493/1080000000000000000 : ℝ)*(X 1 0+X 2 0)+(228715994393/172800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (1079723881443726493/1080000000000000000 : ℝ)) (alpha := (228715994393/172800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1079723881443726493/1080000000000000000 : ℝ)*(X 0 1+X 2 1)+(228715994393/172800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (1079723881443726493/1080000000000000000 : ℝ)) (alpha := (228715994393/172800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1079723881443726493/1080000000000000000 : ℝ)*(X 0 2+X 1 2)+(228715994393/172800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (1079723881443726493/1080000000000000000 : ℝ)) (alpha := (228715994393/172800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347833921/10000000000 : ℝ)*X 2 0+(5246347783/10000000000 : ℝ)*X 2 1+(-64833363/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1991609129/10000000000 : ℝ)*X 0 0+(2623467349/5000000000 : ℝ)*X 0 1+(1081777941/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132638253/250000000 : ℝ)*X 1 0+(-956062903/5000000000 : ℝ)*X 1 1+(5408889661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530553011/1000000000 : ℝ)*X 2 0+(5408889691/10000000000 : ℝ)*X 2 1+(-956062889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4310691243/10000000000 : ℝ)*X 0 0+(1121868003/2500000000 : ℝ)*X 0 1+(4140315979/10000000000 : ℝ)*X 0 2+(4310691243/10000000000 : ℝ)*X 1 0+(1121868003/2500000000 : ℝ)*X 1 1+(4140315979/10000000000 : ℝ)*X 1 2+(4310691243/10000000000 : ℝ)*X 2 0+(1121868003/2500000000 : ℝ)*X 2 1+(4140315979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1170109899429624892373/240000000000000000000000000 : ℝ) := by norm_num
    linear_combination (844391977/100000000000000 : ℝ)*(base19) + (900024069/100000000000000 : ℝ)*(base23) + (57187817/20000000000000 : ℝ)*(lower1) + (74562629/100000000000000 : ℝ)*(upper3) + (8020471/25000000000000 : ℝ)*(lower4) + (24446357/20000000000000 : ℝ)*(upper5) + (1131884734862697/25000000000000 : ℝ)*(major0) + (1131884734862697/25000000000000 : ℝ)*(major1) + (1131884734862697/25000000000000 : ℝ)*(major2) + (21324467/2500000000000 : ℝ)*(sp0) + (3087268908260481/50000000000000 : ℝ)*(sp1) + (1234907394425797/20000000000000 : ℝ)*(sp2) + (6174536063518213/100000000000000 : ℝ)*(sp3) + (1440269949932667/50000000000000 : ℝ)*(sp4) + (1440269949932667/50000000000000 : ℝ)*(f.failure) + (3087268908260481/50000000000000 : ℝ)*(f.sum) + (1372139813227/720000000000000000000000000 : ℝ)*base65 + (75420357407815319/3000000000000000000000000000000 : ℝ)*base67 + (22669867271815319/3000000000000000000000000000000 : ℝ)*base69 + (74234723226184681/3000000000000000000000000000000 : ℝ)*base72 + (3452534851253/720000000000000000000000000 : ℝ)*base74 + (227130583646815319/3000000000000000000000000000000 : ℝ)*base75 + (14103231756184681/3000000000000000000000000000000 : ℝ)*base78 + (35845350033184681/3000000000000000000000000000000 : ℝ)*base80 + (1292837337067/720000000000000000000000000 : ℝ)*base81 + (4506729/1250000000000000000000 : ℝ)*base89 + (4506729/1250000000000000000000 : ℝ)*base91 + (4506729/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1404_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_box_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-914553133/5000000000 : ℝ)*x 0 + (5387324693/10000000000 : ℝ)*x 1 + (1346831023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914553133/5000000000 : ℝ)^1091 ≤ (10865534991937/100000000000000 : ℝ)^835 := by
    have hnat : (914553133 : ℕ)^1091*100000000000000^835 ≤ 10865534991937^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914553133 5000000000 10865534991937 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387324693/10000000000 : ℝ)^1091 ≤ (8913447149997/20000000000000 : ℝ)^835 := by
    have hnat : (5387324693 : ℕ)^1091*20000000000000^835 ≤ 8913447149997^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387324693 10000000000 8913447149997 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346831023/2500000000 : ℝ)^1091 ≤ (22283614626923/50000000000000 : ℝ)^835 := by
    have hnat : (1346831023 : ℕ)^1091*50000000000000^835 ≤ 22283614626923^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346831023 2500000000 22283614626923 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914553133/5000000000 : ℝ), (5387324693/10000000000 : ℝ), (1346831023/2500000000 : ℝ)] ![(10865534991937/100000000000000 : ℝ), (8913447149997/20000000000000 : ℝ), (22283614626923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914553133/5000000000 : ℝ)|^1091 ≤ (10865534991937/100000000000000 : ℝ)^835
        have hw : |(-914553133/5000000000 : ℝ)|=(914553133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387324693/10000000000 : ℝ)|^1091 ≤ (8913447149997/20000000000000 : ℝ)^835
        have hw : |(5387324693/10000000000 : ℝ)|=(5387324693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346831023/2500000000 : ℝ)|^1091 ≤ (22283614626923/50000000000000 : ℝ)^835
        have hw : |(1346831023/2500000000 : ℝ)|=(1346831023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321465883/2500000000 : ℝ)*x 0 + (-984197367/5000000000 : ℝ)*x 1 + (5387323861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321465883/2500000000 : ℝ)^1091 ≤ (43473733954771/100000000000000 : ℝ)^835 := by
    have hnat : (1321465883 : ℕ)^1091*100000000000000^835 ≤ 43473733954771^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321465883 2500000000 43473733954771 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984197367/5000000000 : ℝ)^1091 ≤ (5979519641563/50000000000000 : ℝ)^835 := by
    have hnat : (984197367 : ℕ)^1091*50000000000000^835 ≤ 5979519641563^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984197367 5000000000 5979519641563 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387323861/10000000000 : ℝ)^1091 ≤ (8913445351399/20000000000000 : ℝ)^835 := by
    have hnat : (5387323861 : ℕ)^1091*20000000000000^835 ≤ 8913445351399^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387323861 10000000000 8913445351399 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321465883/2500000000 : ℝ), (-984197367/5000000000 : ℝ), (5387323861/10000000000 : ℝ)] ![(43473733954771/100000000000000 : ℝ), (5979519641563/50000000000000 : ℝ), (8913445351399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321465883/2500000000 : ℝ)|^1091 ≤ (43473733954771/100000000000000 : ℝ)^835
        have hw : |(1321465883/2500000000 : ℝ)|=(1321465883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984197367/5000000000 : ℝ)|^1091 ≤ (5979519641563/50000000000000 : ℝ)^835
        have hw : |(-984197367/5000000000 : ℝ)|=(984197367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387323861/10000000000 : ℝ)|^1091 ≤ (8913445351399/20000000000000 : ℝ)^835
        have hw : |(5387323861/10000000000 : ℝ)|=(5387323861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (660732971/1250000000 : ℝ)*x 0 + (5387324143/10000000000 : ℝ)*x 1 + (-492098507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660732971/1250000000 : ℝ)^1091 ≤ (43473736490841/100000000000000 : ℝ)^835 := by
    have hnat : (660732971 : ℕ)^1091*100000000000000^835 ≤ 43473736490841^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660732971 1250000000 43473736490841 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387324143/10000000000 : ℝ)^1091 ≤ (44567229805099/100000000000000 : ℝ)^835 := by
    have hnat : (5387324143 : ℕ)^1091*100000000000000^835 ≤ 44567229805099^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387324143 10000000000 44567229805099 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492098507/2500000000 : ℝ)^1091 ≤ (373719802461/3125000000000 : ℝ)^835 := by
    have hnat : (492098507 : ℕ)^1091*3125000000000^835 ≤ 373719802461^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492098507 2500000000 373719802461 3125000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660732971/1250000000 : ℝ), (5387324143/10000000000 : ℝ), (-492098507/2500000000 : ℝ)] ![(43473736490841/100000000000000 : ℝ), (44567229805099/100000000000000 : ℝ), (373719802461/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660732971/1250000000 : ℝ)|^1091 ≤ (43473736490841/100000000000000 : ℝ)^835
        have hw : |(660732971/1250000000 : ℝ)|=(660732971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387324143/10000000000 : ℝ)|^1091 ≤ (44567229805099/100000000000000 : ℝ)^835
        have hw : |(5387324143/10000000000 : ℝ)|=(5387324143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492098507/2500000000 : ℝ)|^1091 ≤ (373719802461/3125000000000 : ℝ)^835
        have hw : |(-492098507/2500000000 : ℝ)|=(492098507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (445747741/1000000000 : ℝ)*x 0 + (4241018767/10000000000 : ℝ)*x 1 + (4241019087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445747741/1000000000 : ℝ)^1091 ≤ (17397005936911/50000000000000 : ℝ)^835 := by
    have hnat : (445747741 : ℕ)^1091*50000000000000^835 ≤ 17397005936911^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445747741 1000000000 17397005936911 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241018767/10000000000 : ℝ)^1091 ≤ (4075374056253/12500000000000 : ℝ)^835 := by
    have hnat : (4241018767 : ℕ)^1091*12500000000000^835 ≤ 4075374056253^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241018767 10000000000 4075374056253 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241019087/10000000000 : ℝ)^1091 ≤ (8150748916061/25000000000000 : ℝ)^835 := by
    have hnat : (4241019087 : ℕ)^1091*25000000000000^835 ≤ 8150748916061^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241019087 10000000000 8150748916061 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445747741/1000000000 : ℝ), (4241018767/10000000000 : ℝ), (4241019087/10000000000 : ℝ)] ![(17397005936911/50000000000000 : ℝ), (4075374056253/12500000000000 : ℝ), (8150748916061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445747741/1000000000 : ℝ)|^1091 ≤ (17397005936911/50000000000000 : ℝ)^835
        have hw : |(445747741/1000000000 : ℝ)|=(445747741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241018767/10000000000 : ℝ)|^1091 ≤ (4075374056253/12500000000000 : ℝ)^835
        have hw : |(4241018767/10000000000 : ℝ)|=(4241018767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241019087/10000000000 : ℝ)|^1091 ≤ (8150748916061/25000000000000 : ℝ)^835
        have hw : |(4241019087/10000000000 : ℝ)|=(4241019087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-53920819/250000000 : ℝ)*x 0 + (263306533/500000000 : ℝ)*x 1 + (5266131259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53920819/250000000 : ℝ)^1091 ≤ (842274000337/6250000000000 : ℝ)^835 := by
    have hnat : (53920819 : ℕ)^1091*6250000000000^835 ≤ 842274000337^835*250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53920819 250000000 842274000337 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263306533/500000000 : ℝ)^1091 ≤ (21630902388617/50000000000000 : ℝ)^835 := by
    have hnat : (263306533 : ℕ)^1091*50000000000000^835 ≤ 21630902388617^835*500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263306533 500000000 21630902388617 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266131259/10000000000 : ℝ)^1091 ≤ (43261811206747/100000000000000 : ℝ)^835 := by
    have hnat : (5266131259 : ℕ)^1091*100000000000000^835 ≤ 43261811206747^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266131259 10000000000 43261811206747 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53920819/250000000 : ℝ), (263306533/500000000 : ℝ), (5266131259/10000000000 : ℝ)] ![(842274000337/6250000000000 : ℝ), (21630902388617/50000000000000 : ℝ), (43261811206747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53920819/250000000 : ℝ)|^1091 ≤ (842274000337/6250000000000 : ℝ)^835
        have hw : |(-53920819/250000000 : ℝ)|=(53920819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263306533/500000000 : ℝ)|^1091 ≤ (21630902388617/50000000000000 : ℝ)^835
        have hw : |(263306533/500000000 : ℝ)|=(263306533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266131259/10000000000 : ℝ)|^1091 ≤ (43261811206747/100000000000000 : ℝ)^835
        have hw : |(5266131259/10000000000 : ℝ)|=(5266131259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342691977/2500000000 : ℝ)*x 0 + (-403487753/2000000000 : ℝ)*x 1 + (5266130289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342691977/2500000000 : ℝ)^1091 ≤ (44388359766283/100000000000000 : ℝ)^835 := by
    have hnat : (1342691977 : ℕ)^1091*100000000000000^835 ≤ 44388359766283^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342691977 2500000000 44388359766283 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403487753/2000000000 : ℝ)^1091 ≤ (3087459855057/25000000000000 : ℝ)^835 := by
    have hnat : (403487753 : ℕ)^1091*25000000000000^835 ≤ 3087459855057^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403487753 2000000000 3087459855057 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266130289/10000000000 : ℝ)^1091 ≤ (21630900397507/50000000000000 : ℝ)^835 := by
    have hnat : (5266130289 : ℕ)^1091*50000000000000^835 ≤ 21630900397507^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266130289 10000000000 21630900397507 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342691977/2500000000 : ℝ), (-403487753/2000000000 : ℝ), (5266130289/10000000000 : ℝ)] ![(44388359766283/100000000000000 : ℝ), (3087459855057/25000000000000 : ℝ), (21630900397507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342691977/2500000000 : ℝ)|^1091 ≤ (44388359766283/100000000000000 : ℝ)^835
        have hw : |(1342691977/2500000000 : ℝ)|=(1342691977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403487753/2000000000 : ℝ)|^1091 ≤ (3087459855057/25000000000000 : ℝ)^835
        have hw : |(-403487753/2000000000 : ℝ)|=(403487753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266130289/10000000000 : ℝ)|^1091 ≤ (21630900397507/50000000000000 : ℝ)^835
        have hw : |(5266130289/10000000000 : ℝ)|=(5266130289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5370767673/10000000000 : ℝ)*x 0 + (1316532759/2500000000 : ℝ)*x 1 + (-3152247/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370767673/10000000000 : ℝ)^1091 ≤ (44388357228591/100000000000000 : ℝ)^835 := by
    have hnat : (5370767673 : ℕ)^1091*100000000000000^835 ≤ 44388357228591^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370767673 10000000000 44388357228591 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316532759/2500000000 : ℝ)^1091 ≤ (21630904406561/50000000000000 : ℝ)^835 := by
    have hnat : (1316532759 : ℕ)^1091*50000000000000^835 ≤ 21630904406561^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316532759 2500000000 21630904406561 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3152247/15625000 : ℝ)^1091 ≤ (12349833941373/100000000000000 : ℝ)^835 := by
    have hnat : (3152247 : ℕ)^1091*100000000000000^835 ≤ 12349833941373^835*15625000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3152247 15625000 12349833941373 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370767673/10000000000 : ℝ), (1316532759/2500000000 : ℝ), (-3152247/15625000 : ℝ)] ![(44388357228591/100000000000000 : ℝ), (21630904406561/50000000000000 : ℝ), (12349833941373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370767673/10000000000 : ℝ)|^1091 ≤ (44388357228591/100000000000000 : ℝ)^835
        have hw : |(5370767673/10000000000 : ℝ)|=(5370767673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316532759/2500000000 : ℝ)|^1091 ≤ (21630904406561/50000000000000 : ℝ)^835
        have hw : |(1316532759/2500000000 : ℝ)|=(1316532759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3152247/15625000 : ℝ)|^1091 ≤ (12349833941373/100000000000000 : ℝ)^835
        have hw : |(-3152247/15625000 : ℝ)|=(3152247/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4162841199/10000000000 : ℝ)*x 0 + (4388285491/10000000000 : ℝ)*x 1 + (4388285323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162841199/10000000000 : ℝ)^1091 ≤ (31819971349193/100000000000000 : ℝ)^835 := by
    have hnat : (4162841199 : ℕ)^1091*100000000000000^835 ≤ 31819971349193^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162841199 10000000000 31819971349193 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388285491/10000000000 : ℝ)^1091 ≤ (17045007588629/50000000000000 : ℝ)^835 := by
    have hnat : (4388285491 : ℕ)^1091*50000000000000^835 ≤ 17045007588629^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388285491 10000000000 17045007588629 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388285323/10000000000 : ℝ)^1091 ≤ (852250336801/2500000000000 : ℝ)^835 := by
    have hnat : (4388285323 : ℕ)^1091*2500000000000^835 ≤ 852250336801^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388285323 10000000000 852250336801 2500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162841199/10000000000 : ℝ), (4388285491/10000000000 : ℝ), (4388285323/10000000000 : ℝ)] ![(31819971349193/100000000000000 : ℝ), (17045007588629/50000000000000 : ℝ), (852250336801/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162841199/10000000000 : ℝ)|^1091 ≤ (31819971349193/100000000000000 : ℝ)^835
        have hw : |(4162841199/10000000000 : ℝ)|=(4162841199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388285491/10000000000 : ℝ)|^1091 ≤ (17045007588629/50000000000000 : ℝ)^835
        have hw : |(4388285491/10000000000 : ℝ)|=(4388285491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388285323/10000000000 : ℝ)|^1091 ≤ (852250336801/2500000000000 : ℝ)^835
        have hw : |(4388285323/10000000000 : ℝ)|=(4388285323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_8 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-8351441/40000000 : ℝ)*x 0 + (5182415013/10000000000 : ℝ)*x 1 + (2700656609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8351441/40000000 : ℝ)^1091 ≤ (6458041768393/50000000000000 : ℝ)^835 := by
    have hnat : (8351441 : ℕ)^1091*50000000000000^835 ≤ 6458041768393^835*40000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8351441 40000000 6458041768393 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182415013/10000000000 : ℝ)^1091 ≤ (42365420221/100000000000 : ℝ)^835 := by
    have hnat : (5182415013 : ℕ)^1091*100000000000^835 ≤ 42365420221^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182415013 10000000000 42365420221 100000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700656609/5000000000 : ℝ)^1091 ≤ (22359248114643/50000000000000 : ℝ)^835 := by
    have hnat : (2700656609 : ℕ)^1091*50000000000000^835 ≤ 22359248114643^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700656609 5000000000 22359248114643 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8351441/40000000 : ℝ), (5182415013/10000000000 : ℝ), (2700656609/5000000000 : ℝ)] ![(6458041768393/50000000000000 : ℝ), (42365420221/100000000000 : ℝ), (22359248114643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8351441/40000000 : ℝ)|^1091 ≤ (6458041768393/50000000000000 : ℝ)^835
        have hw : |(-8351441/40000000 : ℝ)|=(8351441/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182415013/10000000000 : ℝ)|^1091 ≤ (42365420221/100000000000 : ℝ)^835
        have hw : |(5182415013/10000000000 : ℝ)|=(5182415013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700656609/5000000000 : ℝ)|^1091 ≤ (22359248114643/50000000000000 : ℝ)^835
        have hw : |(2700656609/5000000000 : ℝ)|=(2700656609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_9 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276059171/10000000000 : ℝ)*x 0 + (-39252101/200000000 : ℝ)*x 1 + (1350328253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276059171/10000000000 : ℝ)^1091 ≤ (21684202835119/50000000000000 : ℝ)^835 := by
    have hnat : (5276059171 : ℕ)^1091*50000000000000^835 ≤ 21684202835119^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276059171 10000000000 21684202835119 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39252101/200000000 : ℝ)^1091 ≤ (2382620062931/20000000000000 : ℝ)^835 := by
    have hnat : (39252101 : ℕ)^1091*20000000000000^835 ≤ 2382620062931^835*200000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39252101 200000000 2382620062931 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350328253/2500000000 : ℝ)^1091 ≤ (8943698800177/20000000000000 : ℝ)^835 := by
    have hnat : (1350328253 : ℕ)^1091*20000000000000^835 ≤ 8943698800177^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350328253 2500000000 8943698800177 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276059171/10000000000 : ℝ), (-39252101/200000000 : ℝ), (1350328253/2500000000 : ℝ)] ![(21684202835119/50000000000000 : ℝ), (2382620062931/20000000000000 : ℝ), (8943698800177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276059171/10000000000 : ℝ)|^1091 ≤ (21684202835119/50000000000000 : ℝ)^835
        have hw : |(5276059171/10000000000 : ℝ)|=(5276059171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39252101/200000000 : ℝ)|^1091 ≤ (2382620062931/20000000000000 : ℝ)^835
        have hw : |(-39252101/200000000 : ℝ)|=(39252101/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350328253/2500000000 : ℝ)|^1091 ≤ (8943698800177/20000000000000 : ℝ)^835
        have hw : |(1350328253/2500000000 : ℝ)|=(1350328253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_10 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2638029137/5000000000 : ℝ)*x 0 + (2700656853/5000000000 : ℝ)*x 1 + (-981302659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638029137/5000000000 : ℝ)^1091 ≤ (10842099009127/25000000000000 : ℝ)^835 := by
    have hnat : (2638029137 : ℕ)^1091*25000000000000^835 ≤ 10842099009127^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638029137 5000000000 10842099009127 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700656853/5000000000 : ℝ)^1091 ≤ (5589812688527/12500000000000 : ℝ)^835 := by
    have hnat : (2700656853 : ℕ)^1091*12500000000000^835 ≤ 5589812688527^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700656853 5000000000 5589812688527 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981302659/5000000000 : ℝ)^1091 ≤ (5956551220087/50000000000000 : ℝ)^835 := by
    have hnat : (981302659 : ℕ)^1091*50000000000000^835 ≤ 5956551220087^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981302659 5000000000 5956551220087 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638029137/5000000000 : ℝ), (2700656853/5000000000 : ℝ), (-981302659/5000000000 : ℝ)] ![(10842099009127/25000000000000 : ℝ), (5589812688527/12500000000000 : ℝ), (5956551220087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638029137/5000000000 : ℝ)|^1091 ≤ (10842099009127/25000000000000 : ℝ)^835
        have hw : |(2638029137/5000000000 : ℝ)|=(2638029137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700656853/5000000000 : ℝ)|^1091 ≤ (5589812688527/12500000000000 : ℝ)^835
        have hw : |(2700656853/5000000000 : ℝ)|=(2700656853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-981302659/5000000000 : ℝ)|^1091 ≤ (5956551220087/50000000000000 : ℝ)^835
        have hw : |(-981302659/5000000000 : ℝ)|=(981302659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_11 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1122732143/2500000000 : ℝ)*x 0 + (844801379/2000000000 : ℝ)*x 1 + (422400541/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122732143/2500000000 : ℝ)^1091 ≤ (17567784479481/50000000000000 : ℝ)^835 := by
    have hnat : (1122732143 : ℕ)^1091*50000000000000^835 ≤ 17567784479481^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122732143 2500000000 17567784479481 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844801379/2000000000 : ℝ)^1091 ≤ (32432222963703/100000000000000 : ℝ)^835 := by
    have hnat : (844801379 : ℕ)^1091*100000000000000^835 ≤ 32432222963703^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844801379 2000000000 32432222963703 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422400541/1000000000 : ℝ)^1091 ≤ (16216104033043/50000000000000 : ℝ)^835 := by
    have hnat : (422400541 : ℕ)^1091*50000000000000^835 ≤ 16216104033043^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422400541 1000000000 16216104033043 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1122732143/2500000000 : ℝ), (844801379/2000000000 : ℝ), (422400541/1000000000 : ℝ)] ![(17567784479481/50000000000000 : ℝ), (32432222963703/100000000000000 : ℝ), (16216104033043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1122732143/2500000000 : ℝ)|^1091 ≤ (17567784479481/50000000000000 : ℝ)^835
        have hw : |(1122732143/2500000000 : ℝ)|=(1122732143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844801379/2000000000 : ℝ)|^1091 ≤ (32432222963703/100000000000000 : ℝ)^835
        have hw : |(844801379/2000000000 : ℝ)|=(844801379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422400541/1000000000 : ℝ)|^1091 ≤ (16216104033043/50000000000000 : ℝ)^835
        have hw : |(422400541/1000000000 : ℝ)|=(422400541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_12 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-189830221/1000000000 : ℝ)*x 0 + (5468966597/10000000000 : ℝ)*x 1 + (5255018713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189830221/1000000000 : ℝ)^1091 ≤ (11405692986137/100000000000000 : ℝ)^835 := by
    have hnat : (189830221 : ℕ)^1091*100000000000000^835 ≤ 11405692986137^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189830221 1000000000 11405692986137 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468966597/10000000000 : ℝ)^1091 ≤ (4545173643251/10000000000000 : ℝ)^835 := by
    have hnat : (5468966597 : ℕ)^1091*10000000000000^835 ≤ 4545173643251^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468966597 10000000000 4545173643251 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255018713/10000000000 : ℝ)^1091 ≤ (21571285284717/50000000000000 : ℝ)^835 := by
    have hnat : (5255018713 : ℕ)^1091*50000000000000^835 ≤ 21571285284717^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255018713 10000000000 21571285284717 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189830221/1000000000 : ℝ), (5468966597/10000000000 : ℝ), (5255018713/10000000000 : ℝ)] ![(11405692986137/100000000000000 : ℝ), (4545173643251/10000000000000 : ℝ), (21571285284717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189830221/1000000000 : ℝ)|^1091 ≤ (11405692986137/100000000000000 : ℝ)^835
        have hw : |(-189830221/1000000000 : ℝ)|=(189830221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468966597/10000000000 : ℝ)|^1091 ≤ (4545173643251/10000000000000 : ℝ)^835
        have hw : |(5468966597/10000000000 : ℝ)|=(5468966597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255018713/10000000000 : ℝ)|^1091 ≤ (21571285284717/50000000000000 : ℝ)^835
        have hw : |(5255018713/10000000000 : ℝ)|=(5255018713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_13 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1344637783/2500000000 : ℝ)*x 0 + (-1010917393/5000000000 : ℝ)*x 1 + (5255017817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344637783/2500000000 : ℝ)^1091 ≤ (44472427037829/100000000000000 : ℝ)^835 := by
    have hnat : (1344637783 : ℕ)^1091*100000000000000^835 ≤ 44472427037829^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344637783 2500000000 44472427037829 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010917393/5000000000 : ℝ)^1091 ≤ (3096252994507/25000000000000 : ℝ)^835 := by
    have hnat : (1010917393 : ℕ)^1091*25000000000000^835 ≤ 3096252994507^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010917393 5000000000 3096252994507 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255017817/10000000000 : ℝ)^1091 ≤ (1725702438329/4000000000000 : ℝ)^835 := by
    have hnat : (5255017817 : ℕ)^1091*4000000000000^835 ≤ 1725702438329^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255017817 10000000000 1725702438329 4000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344637783/2500000000 : ℝ), (-1010917393/5000000000 : ℝ), (5255017817/10000000000 : ℝ)] ![(44472427037829/100000000000000 : ℝ), (3096252994507/25000000000000 : ℝ), (1725702438329/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344637783/2500000000 : ℝ)|^1091 ≤ (44472427037829/100000000000000 : ℝ)^835
        have hw : |(1344637783/2500000000 : ℝ)|=(1344637783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010917393/5000000000 : ℝ)|^1091 ≤ (3096252994507/25000000000000 : ℝ)^835
        have hw : |(-1010917393/5000000000 : ℝ)|=(1010917393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255017817/10000000000 : ℝ)|^1091 ≤ (1725702438329/4000000000000 : ℝ)^835
        have hw : |(5255017817/10000000000 : ℝ)|=(5255017817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_14 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (84039859/156250000 : ℝ)*x 0 + (656877249/1250000000 : ℝ)*x 1 + (-2021834763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84039859/156250000 : ℝ)^1091 ≤ (22236212676243/50000000000000 : ℝ)^835 := by
    have hnat : (84039859 : ℕ)^1091*50000000000000^835 ≤ 22236212676243^835*156250000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84039859 156250000 22236212676243 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656877249/1250000000 : ℝ)^1091 ≤ (21571281417707/50000000000000 : ℝ)^835 := by
    have hnat : (656877249 : ℕ)^1091*50000000000000^835 ≤ 21571281417707^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656877249 1250000000 21571281417707 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021834763/10000000000 : ℝ)^1091 ≤ (1548126474243/12500000000000 : ℝ)^835 := by
    have hnat : (2021834763 : ℕ)^1091*12500000000000^835 ≤ 1548126474243^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021834763 10000000000 1548126474243 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84039859/156250000 : ℝ), (656877249/1250000000 : ℝ), (-2021834763/10000000000 : ℝ)] ![(22236212676243/50000000000000 : ℝ), (21571281417707/50000000000000 : ℝ), (1548126474243/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84039859/156250000 : ℝ)|^1091 ≤ (22236212676243/50000000000000 : ℝ)^835
        have hw : |(84039859/156250000 : ℝ)|=(84039859/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656877249/1250000000 : ℝ)|^1091 ≤ (21571281417707/50000000000000 : ℝ)^835
        have hw : |(656877249/1250000000 : ℝ)|=(656877249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021834763/10000000000 : ℝ)|^1091 ≤ (1548126474243/12500000000000 : ℝ)^835
        have hw : |(-2021834763/10000000000 : ℝ)|=(2021834763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_box_15 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4135375291/10000000000 : ℝ)*x 0 + (440177849/1000000000 : ℝ)*x 1 + (4401777603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135375291/10000000000 : ℝ)^1091 ≤ (3154593887527/10000000000000 : ℝ)^835 := by
    have hnat : (4135375291 : ℕ)^1091*10000000000000^835 ≤ 3154593887527^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135375291 10000000000 3154593887527 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440177849/1000000000 : ℝ)^1091 ≤ (8556758765049/25000000000000 : ℝ)^835 := by
    have hnat : (440177849 : ℕ)^1091*25000000000000^835 ≤ 8556758765049^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440177849 1000000000 8556758765049 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401777603/10000000000 : ℝ)^1091 ≤ (17113513024287/50000000000000 : ℝ)^835 := by
    have hnat : (4401777603 : ℕ)^1091*50000000000000^835 ≤ 17113513024287^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401777603 10000000000 17113513024287 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135375291/10000000000 : ℝ), (440177849/1000000000 : ℝ), (4401777603/10000000000 : ℝ)] ![(3154593887527/10000000000000 : ℝ), (8556758765049/25000000000000 : ℝ), (17113513024287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135375291/10000000000 : ℝ)|^1091 ≤ (3154593887527/10000000000000 : ℝ)^835
        have hw : |(4135375291/10000000000 : ℝ)|=(4135375291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440177849/1000000000 : ℝ)|^1091 ≤ (8556758765049/25000000000000 : ℝ)^835
        have hw : |(440177849/1000000000 : ℝ)|=(440177849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401777603/10000000000 : ℝ)|^1091 ≤ (17113513024287/50000000000000 : ℝ)^835
        have hw : |(4401777603/10000000000 : ℝ)|=(4401777603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(12577/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59063/100000 : ℝ) ∧ (8031/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84591/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (4363/1024 : ℝ) ≤ (4596373284090663/50000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^4363 ≤ (4596373284090663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4363*50000000000000000000^1024 ≤ 4596373284090663^1024*12500^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 4596373284090663 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (4596373284090663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (2867865120345271/10000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^4363 ≤ (2867865120345271/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14743 : ℕ)^4363*10000000000000000000^1024 ≤ 2867865120345271^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 2867865120345271 10000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (2867865120345271/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004596373284090663/25000000000000000000 : ℝ) ≤ (5000215739406551/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25004596373284090663/25000000000000000000 : ℝ)^1024 ≤ (5000215739406551/5000000000000000 : ℝ)^4363 := by
      have hnat : (25004596373284090663 : ℕ)^1024*5000000000000000^4363 ≤ 5000215739406551^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004596373284090663 25000000000000000000 5000215739406551 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215739406551/5000000000000000 : ℝ)) (X := (25004596373284090663/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009467849442908509/25000000000000000000 : ℝ) ≤ (10000888716312897/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25009467849442908509/25000000000000000000 : ℝ)^1024 ≤ (10000888716312897/10000000000000000 : ℝ)^4363 := by
      have hnat : (25009467849442908509 : ℕ)^1024*10000000000000000^4363 ≤ 10000888716312897^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009467849442908509 25000000000000000000 10000888716312897 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000888716312897/10000000000000000 : ℝ)) (X := (25009467849442908509/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002867865120345271/5000000000000000000 : ℝ) ≤ (2500336488453173/2500000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (5002867865120345271/5000000000000000000 : ℝ)^1024 ≤ (2500336488453173/2500000000000000 : ℝ)^4363 := by
      have hnat : (5002867865120345271 : ℕ)^1024*2500000000000000^4363 ≤ 2500336488453173^4363*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002867865120345271 5000000000000000000 2500336488453173 2500000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500336488453173/2500000000000000 : ℝ)) (X := (5002867865120345271/5000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4596373284090663/50000000000000000000 : ℝ) ≤ ((3454116816550389549/3455000000000000000 : ℝ)+2*(91447499959/69100000000000 : ℝ)*(1411/12500 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (3454116816550389549/3455000000000000000 : ℝ)+2*(91447499959/69100000000000 : ℝ)*(1411/12500 : ℝ)=(5000215739406551/5000000000000000 : ℝ) by norm_num, show 1+2*(4596373284090663/50000000000000000000 : ℝ)=(25004596373284090663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2867865120345271/10000000000000000000 : ℝ)+(4596373284090663/50000000000000000000 : ℝ) ≤ ((3454116816550389549/3455000000000000000 : ℝ)+(91447499959/69100000000000 : ℝ)*((14743/100000 : ℝ)+(1411/12500 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (3454116816550389549/3455000000000000000 : ℝ)+(91447499959/69100000000000 : ℝ)*((14743/100000 : ℝ)+(1411/12500 : ℝ))=(10000888716312897/10000000000000000 : ℝ) by norm_num, show 1+(2867865120345271/10000000000000000000 : ℝ)+(4596373284090663/50000000000000000000 : ℝ)=(25009467849442908509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2867865120345271/10000000000000000000 : ℝ) ≤ ((3454116816550389549/3455000000000000000 : ℝ)+2*(91447499959/69100000000000 : ℝ)*(14743/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (3454116816550389549/3455000000000000000 : ℝ)+2*(91447499959/69100000000000 : ℝ)*(14743/100000 : ℝ)=(2500336488453173/2500000000000000 : ℝ) by norm_num, show 1+2*(2867865120345271/10000000000000000000 : ℝ)=(5002867865120345271/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3454116816550389549/3455000000000000000 : ℝ)*(X 1 0+X 2 0)+(91447499959/69100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (3454116816550389549/3455000000000000000 : ℝ)) (alpha := (91447499959/69100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3454116816550389549/3455000000000000000 : ℝ)*(X 0 1+X 2 1)+(91447499959/69100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (3454116816550389549/3455000000000000000 : ℝ)) (alpha := (91447499959/69100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3454116816550389549/3455000000000000000 : ℝ)*(X 0 2+X 1 2)+(91447499959/69100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (3454116816550389549/3455000000000000000 : ℝ)) (alpha := (91447499959/69100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-914553133/5000000000 : ℝ)*X 0 0+(5387324693/10000000000 : ℝ)*X 0 1+(1346831023/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321465883/2500000000 : ℝ)*X 1 0+(-984197367/5000000000 : ℝ)*X 1 1+(5387323861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660732971/1250000000 : ℝ)*X 2 0+(5387324143/10000000000 : ℝ)*X 2 1+(-492098507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445747741/1000000000 : ℝ)*X 0 0+(4241018767/10000000000 : ℝ)*X 0 1+(4241019087/10000000000 : ℝ)*X 0 2+(445747741/1000000000 : ℝ)*X 1 0+(4241018767/10000000000 : ℝ)*X 1 1+(4241019087/10000000000 : ℝ)*X 1 2+(445747741/1000000000 : ℝ)*X 2 0+(4241018767/10000000000 : ℝ)*X 2 1+(4241019087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53920819/250000000 : ℝ)*X 0 0+(263306533/500000000 : ℝ)*X 0 1+(5266131259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342691977/2500000000 : ℝ)*X 1 0+(-403487753/2000000000 : ℝ)*X 1 1+(5266130289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370767673/10000000000 : ℝ)*X 2 0+(1316532759/2500000000 : ℝ)*X 2 1+(-3152247/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4162841199/10000000000 : ℝ)*X 0 0+(4388285491/10000000000 : ℝ)*X 0 1+(4388285323/10000000000 : ℝ)*X 0 2+(4162841199/10000000000 : ℝ)*X 1 0+(4388285491/10000000000 : ℝ)*X 1 1+(4388285323/10000000000 : ℝ)*X 1 2+(4162841199/10000000000 : ℝ)*X 2 0+(4388285491/10000000000 : ℝ)*X 2 1+(4388285323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-8351441/40000000 : ℝ)*X 0 0+(5182415013/10000000000 : ℝ)*X 0 1+(2700656609/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276059171/10000000000 : ℝ)*X 1 0+(-39252101/200000000 : ℝ)*X 1 1+(1350328253/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638029137/5000000000 : ℝ)*X 2 0+(2700656853/5000000000 : ℝ)*X 2 1+(-981302659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1122732143/2500000000 : ℝ)*X 0 0+(844801379/2000000000 : ℝ)*X 0 1+(422400541/1000000000 : ℝ)*X 0 2+(1122732143/2500000000 : ℝ)*X 1 0+(844801379/2000000000 : ℝ)*X 1 1+(422400541/1000000000 : ℝ)*X 1 2+(1122732143/2500000000 : ℝ)*X 2 0+(844801379/2000000000 : ℝ)*X 2 1+(422400541/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-189830221/1000000000 : ℝ)*X 0 0+(5468966597/10000000000 : ℝ)*X 0 1+(5255018713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344637783/2500000000 : ℝ)*X 1 0+(-1010917393/5000000000 : ℝ)*X 1 1+(5255017817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((84039859/156250000 : ℝ)*X 2 0+(656877249/1250000000 : ℝ)*X 2 1+(-2021834763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4135375291/10000000000 : ℝ)*X 0 0+(440177849/1000000000 : ℝ)*X 0 1+(4401777603/10000000000 : ℝ)*X 0 2+(4135375291/10000000000 : ℝ)*X 1 0+(440177849/1000000000 : ℝ)*X 1 1+(4401777603/10000000000 : ℝ)*X 1 2+(4135375291/10000000000 : ℝ)*X 2 0+(440177849/1000000000 : ℝ)*X 2 1+(4401777603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12577/20000 : ℝ) ≤ (-13578649624816782944968700512833/21593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57150751/100000000000000 : ℝ)*(lower0) + (54325241/25000000000000 : ℝ)*(lower2) + (44805111/25000000000000 : ℝ)*(lower3) + (46400787/50000000000000 : ℝ)*(lower4) + (747351484176089/25000000000000 : ℝ)*(major0) + (747351484176089/25000000000000 : ℝ)*(major1) + (747351484176089/25000000000000 : ℝ)*(major2) + (18009982851/100000000000000 : ℝ)*(sp1) + (2048916800836977/50000000000000 : ℝ)*(sp4) + (2048907795845551/50000000000000 : ℝ)*(sp5) + (4097746381833281/100000000000000 : ℝ)*(sp6) + (475473226961947/25000000000000 : ℝ)*(sp7) + (87219840673/100000000000000 : ℝ)*(sp14) + (46135136073/100000000000000 : ℝ)*(sp15) + (1901939042983861/100000000000000 : ℝ)*(f.failure) + (2048916800836977/50000000000000 : ℝ)*(f.sum) + (23623286134579/3455000000000000000000000000 : ℝ)*base65 + (357051667186593861/86375000000000000000000000000000 : ℝ)*base67 + (368444202551031139/86375000000000000000000000000000 : ℝ)*base70 + (1215991349719718861/86375000000000000000000000000000 : ℝ)*base71 + (7728211391517/1727500000000000000000000000 : ℝ)*base73 + (108210352552343861/86375000000000000000000000000000 : ℝ)*base75 + (155139852146843861/86375000000000000000000000000000 : ℝ)*base77 + (602583998240093861/86375000000000000000000000000000 : ℝ)*base79 + (489715055451/215937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (27883993/2500000000000000000000 : ℝ)*base90 + (27883993/2500000000000000000000 : ℝ)*base92 + (27883993/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59063/100000 : ℝ) ≤ (25508968586748538693012725783657/43187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111269879/50000000000000 : ℝ)*(lower1) + (52672039/50000000000000 : ℝ)*(lower2) + (217932219/100000000000000 : ℝ)*(upper4) + (765046836856723/25000000000000 : ℝ)*(major0) + (765046836856723/25000000000000 : ℝ)*(major1) + (765046836856723/25000000000000 : ℝ)*(major2) + (2076851768021603/50000000000000 : ℝ)*(sp0) + (4153475866381669/100000000000000 : ℝ)*(sp1) + (4153705610682873/100000000000000 : ℝ)*(sp2) + (60842847241411/3125000000000 : ℝ)*(sp3) + (233736521/25000000000000 : ℝ)*(sp7) + (10569091187/100000000000000 : ℝ)*(sp8) + (9529550109/4000000000000 : ℝ)*(sp9) + (8494451521/100000000000000 : ℝ)*(sp10) + (486743011667809/25000000000000 : ℝ)*(f.failure) + (2076857052567197/50000000000000 : ℝ)*(f.sum) + (9916473314739/1727500000000000000000000000 : ℝ)*base65 + (680998325974062927/86375000000000000000000000000000 : ℝ)*base67 + (930046899925687927/86375000000000000000000000000000 : ℝ)*base69 + (1179058523688812927/86375000000000000000000000000000 : ℝ)*base71 + (579465593671/431875000000000000000000000 : ℝ)*base73 + (523865612828062927/86375000000000000000000000000000 : ℝ)*base75 + (1067212025503187927/86375000000000000000000000000000 : ℝ)*base77 + (224431004484562927/86375000000000000000000000000000 : ℝ)*base79 + (4843074019479/1727500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6273717/625000000000000000000 : ℝ)*base90 + (6273717/625000000000000000000 : ℝ)*base92 + (6273717/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8031/10000 : ℝ) ≤ (34684742664379760267786527935381/43187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156288221/100000000000000 : ℝ)*(upper1) + (124457891/100000000000000 : ℝ)*(upper2) + (14743291/20000000000000 : ℝ)*(upper3) + (18960239/5000000000000 : ℝ)*(lower5) + (1684701563814523/50000000000000 : ℝ)*(major0) + (1684701563814523/50000000000000 : ℝ)*(major1) + (1684701563814523/50000000000000 : ℝ)*(major2) + (8246318937/100000000000000 : ℝ)*(sp0) + (72745319127/25000000000000 : ℝ)*(sp2) + (6678198289/50000000000000 : ℝ)*(sp3) + (4568324047943207/100000000000000 : ℝ)*(sp8) + (35690096048923/781250000000 : ℝ)*(sp9) + (4568041312985637/100000000000000 : ℝ)*(sp10) + (535922484933849/25000000000000 : ℝ)*(sp11) + (1071851648065987/50000000000000 : ℝ)*(f.failure) + (35690096048923/781250000000 : ℝ)*(f.sum) + (8384907499193/1727500000000000000000000000 : ℝ)*base66 + (539406560861970127/172750000000000000000000000000000 : ℝ)*base67 + (52815714342529873/172750000000000000000000000000000 : ℝ)*base70 + (447919691777529873/172750000000000000000000000000000 : ℝ)*base72 + (681699590579/863750000000000000000000000 : ℝ)*base74 + (403131534847029873/172750000000000000000000000000000 : ℝ)*base76 + (1870420939297029873/172750000000000000000000000000000 : ℝ)*base78 + (503069783086529873/172750000000000000000000000000000 : ℝ)*base80 + (13181533565817/1727500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6517569/1250000000000000000000 : ℝ)*base89 + (6517569/1250000000000000000000 : ℝ)*base91 + (6517569/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84591/100000 : ℝ) ≤ (-4566431445232338863833949505027/5398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (113180387/50000000000000 : ℝ)*(lower0) + (2664337/10000000000000 : ℝ)*(lower3) + (20307403/50000000000000 : ℝ)*(lower4) + (53228189093389/1562500000000 : ℝ)*(major0) + (53228189093389/1562500000000 : ℝ)*(major1) + (53228189093389/1562500000000 : ℝ)*(major2) + (735236281/10000000000000 : ℝ)*(sp4) + (90061037909/25000000000000 : ℝ)*(sp5) + (159370635421/50000000000000 : ℝ)*(sp6) + (3180333311/12500000000000 : ℝ)*(sp7) + (2337012659824669/50000000000000 : ℝ)*(sp12) + (146052263370641/3125000000000 : ℝ)*(sp13) + (2336856965370653/50000000000000 : ℝ)*(sp14) + (1083673048134673/50000000000000 : ℝ)*(sp15) + (2167371538935833/100000000000000 : ℝ)*(f.failure) + (4674032672012149/100000000000000 : ℝ)*(f.sum) + (2575612192963/1727500000000000000000000000 : ℝ)*base66 + (3314335238937383/674804687500000000000000000000 : ℝ)*base68 + (98852348646969/21087646484375000000000000000 : ℝ)*base70 + (5179399652046641/1349609375000000000000000000000 : ℝ)*base72 + (1404640909477/431875000000000000000000000 : ℝ)*base74 + (23884834138077657/2699218750000000000000000000000 : ℝ)*base76 + (23258687676545939/5398437500000000000000000000000 : ℝ)*base78 + (56776770366952189/5398437500000000000000000000000 : ℝ)*base80 + (894024638291/215937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2902771/2500000000000000000000 : ℝ)*base89 + (2902771/2500000000000000000000 : ℝ)*base91 + (2902771/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1404_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59063/100000 : ℝ) else (8031/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84591/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1404_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1404_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59063/100000 : ℝ) else (8031/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84591/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1404_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1404_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1404_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59063/100000 : ℝ) else (8031/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84591/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

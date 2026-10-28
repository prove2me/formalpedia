-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:19.525879+00:00
-- url     : https://prove2.me/submissions/d23f1677-8f70-47c0-8b37-8e41d1c467b1

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
theorem support_rectangle_w1180_s6_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-537205377/2500000000 : ℝ)*x 0 + (2696309369/5000000000 : ℝ)*x 1 + (5266072713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537205377/2500000000 : ℝ)^8373 ≤ (13060821932761/100000000000000 : ℝ)^6325 := by
    have hnat : (537205377 : ℕ)^8373*100000000000000^6325 ≤ 13060821932761^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537205377 2500000000 13060821932761 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696309369/5000000000 : ℝ)^8373 ≤ (4415276936559/10000000000000 : ℝ)^6325 := by
    have hnat : (2696309369 : ℕ)^8373*10000000000000^6325 ≤ 4415276936559^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696309369 5000000000 4415276936559 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266072713/10000000000 : ℝ)^8373 ≤ (21393204344291/50000000000000 : ℝ)^6325 := by
    have hnat : (5266072713 : ℕ)^8373*50000000000000^6325 ≤ 21393204344291^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266072713 10000000000 21393204344291 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537205377/2500000000 : ℝ), (2696309369/5000000000 : ℝ), (5266072713/10000000000 : ℝ)] ![(13060821932761/100000000000000 : ℝ), (4415276936559/10000000000000 : ℝ), (21393204344291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537205377/2500000000 : ℝ)|^8373 ≤ (13060821932761/100000000000000 : ℝ)^6325
        have hw : |(-537205377/2500000000 : ℝ)|=(537205377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696309369/5000000000 : ℝ)|^8373 ≤ (4415276936559/10000000000000 : ℝ)^6325
        have hw : |(2696309369/5000000000 : ℝ)|=(2696309369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266072713/10000000000 : ℝ)|^8373 ≤ (21393204344291/50000000000000 : ℝ)^6325
        have hw : |(5266072713/10000000000 : ℝ)|=(5266072713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344675801/10000000000 : ℝ)*x 0 + (-276625283/1250000000 : ℝ)*x 1 + (5266072711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344675801/10000000000 : ℝ)^8373 ≤ (272711736179/625000000000 : ℝ)^6325 := by
    have hnat : (5344675801 : ℕ)^8373*625000000000^6325 ≤ 272711736179^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344675801 10000000000 272711736179 625000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276625283/1250000000 : ℝ)^8373 ≤ (13579713533827/100000000000000 : ℝ)^6325 := by
    have hnat : (276625283 : ℕ)^8373*100000000000000^6325 ≤ 13579713533827^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276625283 1250000000 13579713533827 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266072711/10000000000 : ℝ)^8373 ≤ (4278640866707/10000000000000 : ℝ)^6325 := by
    have hnat : (5266072711 : ℕ)^8373*10000000000000^6325 ≤ 4278640866707^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266072711 10000000000 4278640866707 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344675801/10000000000 : ℝ), (-276625283/1250000000 : ℝ), (5266072711/10000000000 : ℝ)] ![(272711736179/625000000000 : ℝ), (13579713533827/100000000000000 : ℝ), (4278640866707/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344675801/10000000000 : ℝ)|^8373 ≤ (272711736179/625000000000 : ℝ)^6325
        have hw : |(5344675801/10000000000 : ℝ)|=(5344675801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276625283/1250000000 : ℝ)|^8373 ≤ (13579713533827/100000000000000 : ℝ)^6325
        have hw : |(-276625283/1250000000 : ℝ)|=(276625283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266072711/10000000000 : ℝ)|^8373 ≤ (4278640866707/10000000000000 : ℝ)^6325
        have hw : |(5266072711/10000000000 : ℝ)|=(5266072711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344675799/10000000000 : ℝ)*x 0 + (658259089/1250000000 : ℝ)*x 1 + (-442600453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344675799/10000000000 : ℝ)^8373 ≤ (1745355110681/4000000000000 : ℝ)^6325 := by
    have hnat : (5344675799 : ℕ)^8373*4000000000000^6325 ≤ 1745355110681^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344675799 10000000000 1745355110681 4000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658259089/1250000000 : ℝ)^8373 ≤ (21393204338913/50000000000000 : ℝ)^6325 := by
    have hnat : (658259089 : ℕ)^8373*50000000000000^6325 ≤ 21393204338913^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658259089 1250000000 21393204338913 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442600453/2000000000 : ℝ)^8373 ≤ (271594270839/2000000000000 : ℝ)^6325 := by
    have hnat : (442600453 : ℕ)^8373*2000000000000^6325 ≤ 271594270839^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442600453 2000000000 271594270839 2000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344675799/10000000000 : ℝ), (658259089/1250000000 : ℝ), (-442600453/2000000000 : ℝ)] ![(1745355110681/4000000000000 : ℝ), (21393204338913/50000000000000 : ℝ), (271594270839/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344675799/10000000000 : ℝ)|^8373 ≤ (1745355110681/4000000000000 : ℝ)^6325
        have hw : |(5344675799/10000000000 : ℝ)|=(5344675799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658259089/1250000000 : ℝ)|^8373 ≤ (21393204338913/50000000000000 : ℝ)^6325
        have hw : |(658259089/1250000000 : ℝ)|=(658259089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442600453/2000000000 : ℝ)|^8373 ≤ (271594270839/2000000000000 : ℝ)^6325
        have hw : |(-442600453/2000000000 : ℝ)|=(442600453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089833377/2500000000 : ℝ)*x 0 + (4234333959/10000000000 : ℝ)*x 1 + (4487971867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089833377/2500000000 : ℝ)^8373 ≤ (33317032924049/100000000000000 : ℝ)^6325 := by
    have hnat : (1089833377 : ℕ)^8373*100000000000000^6325 ≤ 33317032924049^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089833377 2500000000 33317032924049 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234333959/10000000000 : ℝ)^8373 ≤ (64116555989/200000000000 : ℝ)^6325 := by
    have hnat : (4234333959 : ℕ)^8373*200000000000^6325 ≤ 64116555989^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234333959 10000000000 64116555989 200000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487971867/10000000000 : ℝ)^8373 ≤ (3462468906327/10000000000000 : ℝ)^6325 := by
    have hnat : (4487971867 : ℕ)^8373*10000000000000^6325 ≤ 3462468906327^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487971867 10000000000 3462468906327 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089833377/2500000000 : ℝ), (4234333959/10000000000 : ℝ), (4487971867/10000000000 : ℝ)] ![(33317032924049/100000000000000 : ℝ), (64116555989/200000000000 : ℝ), (3462468906327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089833377/2500000000 : ℝ)|^8373 ≤ (33317032924049/100000000000000 : ℝ)^6325
        have hw : |(1089833377/2500000000 : ℝ)|=(1089833377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234333959/10000000000 : ℝ)|^8373 ≤ (64116555989/200000000000 : ℝ)^6325
        have hw : |(4234333959/10000000000 : ℝ)|=(4234333959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487971867/10000000000 : ℝ)|^8373 ≤ (3462468906327/10000000000000 : ℝ)^6325
        have hw : |(4487971867/10000000000 : ℝ)|=(4487971867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074413181/5000000000 : ℝ)*x 0 + (2633196227/5000000000 : ℝ)*x 1 + (1348074459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074413181/5000000000 : ℝ)^8373 ≤ (6530430494511/50000000000000 : ℝ)^6325 := by
    have hnat : (1074413181 : ℕ)^8373*50000000000000^6325 ≤ 6530430494511^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074413181 5000000000 6530430494511 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633196227/5000000000 : ℝ)^8373 ≤ (10697461941877/25000000000000 : ℝ)^6325 := by
    have hnat : (2633196227 : ℕ)^8373*25000000000000^6325 ≤ 10697461941877^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633196227 5000000000 10697461941877 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348074459/2500000000 : ℝ)^8373 ≤ (11037322806449/25000000000000 : ℝ)^6325 := by
    have hnat : (1348074459 : ℕ)^8373*25000000000000^6325 ≤ 11037322806449^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348074459 2500000000 11037322806449 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074413181/5000000000 : ℝ), (2633196227/5000000000 : ℝ), (1348074459/2500000000 : ℝ)] ![(6530430494511/50000000000000 : ℝ), (10697461941877/25000000000000 : ℝ), (11037322806449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074413181/5000000000 : ℝ)|^8373 ≤ (6530430494511/50000000000000 : ℝ)^6325
        have hw : |(-1074413181/5000000000 : ℝ)|=(1074413181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633196227/5000000000 : ℝ)|^8373 ≤ (10697461941877/25000000000000 : ℝ)^6325
        have hw : |(2633196227/5000000000 : ℝ)|=(2633196227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348074459/2500000000 : ℝ)|^8373 ≤ (11037322806449/25000000000000 : ℝ)^6325
        have hw : |(1348074459/2500000000 : ℝ)|=(1348074459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312525963/10000000000 : ℝ)*x 0 + (-1043388563/5000000000 : ℝ)*x 1 + (5392297851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312525963/10000000000 : ℝ)^8373 ≤ (43286759040783/100000000000000 : ℝ)^6325 := by
    have hnat : (5312525963 : ℕ)^8373*100000000000000^6325 ≤ 43286759040783^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312525963 10000000000 43286759040783 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043388563/5000000000 : ℝ)^8373 ≤ (6281974777831/50000000000000 : ℝ)^6325 := by
    have hnat : (1043388563 : ℕ)^8373*50000000000000^6325 ≤ 6281974777831^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043388563 5000000000 6281974777831 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392297851/10000000000 : ℝ)^8373 ≤ (44149291388373/100000000000000 : ℝ)^6325 := by
    have hnat : (5392297851 : ℕ)^8373*100000000000000^6325 ≤ 44149291388373^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392297851 10000000000 44149291388373 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312525963/10000000000 : ℝ), (-1043388563/5000000000 : ℝ), (5392297851/10000000000 : ℝ)] ![(43286759040783/100000000000000 : ℝ), (6281974777831/50000000000000 : ℝ), (44149291388373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312525963/10000000000 : ℝ)|^8373 ≤ (43286759040783/100000000000000 : ℝ)^6325
        have hw : |(5312525963/10000000000 : ℝ)|=(5312525963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043388563/5000000000 : ℝ)|^8373 ≤ (6281974777831/50000000000000 : ℝ)^6325
        have hw : |(-1043388563/5000000000 : ℝ)|=(1043388563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392297851/10000000000 : ℝ)|^8373 ≤ (44149291388373/100000000000000 : ℝ)^6325
        have hw : |(5392297851/10000000000 : ℝ)|=(5392297851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312525967/10000000000 : ℝ)*x 0 + (674037233/1250000000 : ℝ)*x 1 + (-2086777103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312525967/10000000000 : ℝ)^8373 ≤ (5410844885491/12500000000000 : ℝ)^6325 := by
    have hnat : (5312525967 : ℕ)^8373*12500000000000^6325 ≤ 5410844885491^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312525967 10000000000 5410844885491 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674037233/1250000000 : ℝ)^8373 ≤ (22074645764637/50000000000000 : ℝ)^6325 := by
    have hnat : (674037233 : ℕ)^8373*50000000000000^6325 ≤ 22074645764637^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674037233 1250000000 22074645764637 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086777103/10000000000 : ℝ)^8373 ≤ (6281974686173/50000000000000 : ℝ)^6325 := by
    have hnat : (2086777103 : ℕ)^8373*50000000000000^6325 ≤ 6281974686173^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086777103 10000000000 6281974686173 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312525967/10000000000 : ℝ), (674037233/1250000000 : ℝ), (-2086777103/10000000000 : ℝ)] ![(5410844885491/12500000000000 : ℝ), (22074645764637/50000000000000 : ℝ), (6281974686173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312525967/10000000000 : ℝ)|^8373 ≤ (5410844885491/12500000000000 : ℝ)^6325
        have hw : |(5312525967/10000000000 : ℝ)|=(5312525967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674037233/1250000000 : ℝ)|^8373 ≤ (22074645764637/50000000000000 : ℝ)^6325
        have hw : |(674037233/1250000000 : ℝ)|=(674037233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086777103/10000000000 : ℝ)|^8373 ≤ (6281974686173/50000000000000 : ℝ)^6325
        have hw : |(-2086777103/10000000000 : ℝ)|=(2086777103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s6_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179671633/5000000000 : ℝ)*x 0 + (2243665511/5000000000 : ℝ)*x 1 + (4234977109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179671633/5000000000 : ℝ)^8373 ≤ (33317131649189/100000000000000 : ℝ)^6325 := by
    have hnat : (2179671633 : ℕ)^8373*100000000000000^6325 ≤ 33317131649189^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179671633 5000000000 33317131649189 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243665511/5000000000 : ℝ)^8373 ≤ (86545360549/250000000000 : ℝ)^6325 := by
    have hnat : (2243665511 : ℕ)^8373*250000000000^6325 ≤ 86545360549^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243665511 5000000000 86545360549 250000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234977109/10000000000 : ℝ)^8373 ≤ (32064724117637/100000000000000 : ℝ)^6325 := by
    have hnat : (4234977109 : ℕ)^8373*100000000000000^6325 ≤ 32064724117637^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234977109 10000000000 32064724117637 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179671633/5000000000 : ℝ), (2243665511/5000000000 : ℝ), (4234977109/10000000000 : ℝ)] ![(33317131649189/100000000000000 : ℝ), (86545360549/250000000000 : ℝ), (32064724117637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179671633/5000000000 : ℝ)|^8373 ≤ (33317131649189/100000000000000 : ℝ)^6325
        have hw : |(2179671633/5000000000 : ℝ)|=(2179671633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243665511/5000000000 : ℝ)|^8373 ≤ (86545360549/250000000000 : ℝ)^6325
        have hw : |(2243665511/5000000000 : ℝ)|=(2243665511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234977109/10000000000 : ℝ)|^8373 ≤ (32064724117637/100000000000000 : ℝ)^6325
        have hw : |(4234977109/10000000000 : ℝ)|=(4234977109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (1137/10000 : ℝ) ^ (2093/512 : ℝ) ≤ (3451374328821223/25000000000000000000 : ℝ) := by
    have hpowers : (1137/10000 : ℝ)^2093 ≤ (3451374328821223/25000000000000000000 : ℝ)^512 := by
      have hnat : (1137 : ℕ)^2093*25000000000000000000^512 ≤ 3451374328821223^512*10000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1137 10000 3451374328821223 25000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1137/10000 : ℝ)) (X := (3451374328821223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (2093/512 : ℝ) ≤ (33312280150624183/100000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^2093 ≤ (33312280150624183/100000000000000000000 : ℝ)^512 := by
      have hnat : (1763 : ℕ)^2093*100000000000000000000^512 ≤ 33312280150624183^512*12500^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 33312280150624183 100000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (33312280150624183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503451374328821223/12500000000000000000 : ℝ) ≤ (5000337681683087/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (12503451374328821223/12500000000000000000 : ℝ)^512 ≤ (5000337681683087/5000000000000000 : ℝ)^2093 := by
      have hnat : (12503451374328821223 : ℕ)^512*5000000000000000^2093 ≤ 5000337681683087^2093*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503451374328821223 12500000000000000000 5000337681683087 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337681683087/5000000000000000 : ℝ)) (X := (12503451374328821223/12500000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001884711098636363/4000000000000000000 : ℝ) ≤ (1000115241328877/1000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (4001884711098636363/4000000000000000000 : ℝ)^512 ≤ (1000115241328877/1000000000000000 : ℝ)^2093 := by
      have hnat : (4001884711098636363 : ℕ)^512*1000000000000000^2093 ≤ 1000115241328877^2093*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001884711098636363 4000000000000000000 1000115241328877 1000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000115241328877/1000000000000000 : ℝ)) (X := (4001884711098636363/4000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033312280150624183/50000000000000000000 : ℝ) ≤ (5000814731605683/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (50033312280150624183/50000000000000000000 : ℝ)^512 ≤ (5000814731605683/5000000000000000 : ℝ)^2093 := by
      have hnat : (50033312280150624183 : ℕ)^512*5000000000000000^2093 ≤ 5000814731605683^2093*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033312280150624183 50000000000000000000 5000814731605683 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000814731605683/5000000000000000 : ℝ)) (X := (50033312280150624183/50000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3451374328821223/25000000000000000000 : ℝ) ≤ ((6832749582050821669/6835000000000000000 : ℝ)+2*(119262480649/68350000000000 : ℝ)*(1137/10000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (6832749582050821669/6835000000000000000 : ℝ)+2*(119262480649/68350000000000 : ℝ)*(1137/10000 : ℝ)=(5000337681683087/5000000000000000 : ℝ) by norm_num, show 1+2*(3451374328821223/25000000000000000000 : ℝ)=(12503451374328821223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33312280150624183/100000000000000000000 : ℝ)+(3451374328821223/25000000000000000000 : ℝ) ≤ ((6832749582050821669/6835000000000000000 : ℝ)+(119262480649/68350000000000 : ℝ)*((1763/12500 : ℝ)+(1137/10000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (6832749582050821669/6835000000000000000 : ℝ)+(119262480649/68350000000000 : ℝ)*((1763/12500 : ℝ)+(1137/10000 : ℝ))=(1000115241328877/1000000000000000 : ℝ) by norm_num, show 1+(33312280150624183/100000000000000000000 : ℝ)+(3451374328821223/25000000000000000000 : ℝ)=(4001884711098636363/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33312280150624183/100000000000000000000 : ℝ) ≤ ((6832749582050821669/6835000000000000000 : ℝ)+2*(119262480649/68350000000000 : ℝ)*(1763/12500 : ℝ))^(2093/512 : ℝ) := by
    rw [show (6832749582050821669/6835000000000000000 : ℝ)+2*(119262480649/68350000000000 : ℝ)*(1763/12500 : ℝ)=(5000814731605683/5000000000000000 : ℝ) by norm_num, show 1+2*(33312280150624183/100000000000000000000 : ℝ)=(50033312280150624183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6832749582050821669/6835000000000000000 : ℝ)*(X 1 0+X 2 0)+(119262480649/68350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (6832749582050821669/6835000000000000000 : ℝ)) (alpha := (119262480649/68350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6832749582050821669/6835000000000000000 : ℝ)*(X 0 1+X 2 1)+(119262480649/68350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (6832749582050821669/6835000000000000000 : ℝ)) (alpha := (119262480649/68350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6832749582050821669/6835000000000000000 : ℝ)*(X 0 2+X 1 2)+(119262480649/68350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (6832749582050821669/6835000000000000000 : ℝ)) (alpha := (119262480649/68350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-537205377/2500000000 : ℝ)*X 0 0+(2696309369/5000000000 : ℝ)*X 0 1+(5266072713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344675801/10000000000 : ℝ)*X 1 0+(-276625283/1250000000 : ℝ)*X 1 1+(5266072711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344675799/10000000000 : ℝ)*X 2 0+(658259089/1250000000 : ℝ)*X 2 1+(-442600453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089833377/2500000000 : ℝ)*X 0 0+(4234333959/10000000000 : ℝ)*X 0 1+(4487971867/10000000000 : ℝ)*X 0 2+(1089833377/2500000000 : ℝ)*X 1 0+(4234333959/10000000000 : ℝ)*X 1 1+(4487971867/10000000000 : ℝ)*X 1 2+(1089833377/2500000000 : ℝ)*X 2 0+(4234333959/10000000000 : ℝ)*X 2 1+(4487971867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074413181/5000000000 : ℝ)*X 0 0+(2633196227/5000000000 : ℝ)*X 0 1+(1348074459/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312525963/10000000000 : ℝ)*X 1 0+(-1043388563/5000000000 : ℝ)*X 1 1+(5392297851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312525967/10000000000 : ℝ)*X 2 0+(674037233/1250000000 : ℝ)*X 2 1+(-2086777103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179671633/5000000000 : ℝ)*X 0 0+(2243665511/5000000000 : ℝ)*X 0 1+(4234977109/10000000000 : ℝ)*X 0 2+(2179671633/5000000000 : ℝ)*X 1 0+(2243665511/5000000000 : ℝ)*X 1 1+(4234977109/10000000000 : ℝ)*X 1 2+(2179671633/5000000000 : ℝ)*X 2 0+(2243665511/5000000000 : ℝ)*X 2 1+(4234977109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2918861014822458584986752669/341750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (832066353/50000000000000 : ℝ)*(base19) + (772882197/50000000000000 : ℝ)*(base23) + (61683557/100000000000000 : ℝ)*(lower2) + (2143423/1000000000000 : ℝ)*(upper3) + (126775693/100000000000000 : ℝ)*(upper5) + (5922515693250333/100000000000000 : ℝ)*(major0) + (5922515693250333/100000000000000 : ℝ)*(major1) + (5922515693250333/100000000000000 : ℝ)*(major2) + (1580462171594911/20000000000000 : ℝ)*(sp0) + (7902354499050483/100000000000000 : ℝ)*(sp1) + (1975588654354699/25000000000000 : ℝ)*(sp2) + (788530074929181/20000000000000 : ℝ)*(sp3) + (22652604317/50000000000000 : ℝ)*(sp4) + (2456397407/10000000000000 : ℝ)*(sp7) + (157706997544799/4000000000000 : ℝ)*(f.failure) + (790235616318319/10000000000000 : ℝ)*(f.sum) + (9226903474357/3417500000000000000000000000 : ℝ)*base65 + (10000131181076065777/683500000000000000000000000000000 : ℝ)*base67 + (1319179134164434223/683500000000000000000000000000000 : ℝ)*base70 + (3713074482020934223/683500000000000000000000000000000 : ℝ)*base72 + (8047963648529/6835000000000000000000000000 : ℝ)*base73 + (9099318632656565777/683500000000000000000000000000000 : ℝ)*base75 + (10735120259275565777/683500000000000000000000000000000 : ℝ)*base77 + (1471394035755065777/683500000000000000000000000000000 : ℝ)*base79 + (15445816315859/6835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2565273/400000000000000000000 : ℝ)*base90 + (2565273/400000000000000000000 : ℝ)*base92 + (2565273/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136486996519958027396900847/17087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1443739849/100000000000000 : ℝ)*(base19) + (1616259389/100000000000000 : ℝ)*(base23) + (10770131/6250000000000 : ℝ)*(upper3) + (8654629/12500000000000 : ℝ)*(lower4) + (77519747/50000000000000 : ℝ)*(upper5) + (297628963305121/5000000000000 : ℝ)*(major0) + (297628963305121/5000000000000 : ℝ)*(major1) + (297628963305121/5000000000000 : ℝ)*(major2) + (4999241117/12500000000000 : ℝ)*(sp1) + (45977617419/100000000000000 : ℝ)*(sp2) + (3971234860697603/50000000000000 : ℝ)*(sp4) + (397121414186321/5000000000000 : ℝ)*(sp5) + (3971211063759199/50000000000000 : ℝ)*(sp6) + (990672136139619/25000000000000 : ℝ)*(sp7) + (990672136139619/25000000000000 : ℝ)*(f.failure) + (3971234860697603/50000000000000 : ℝ)*(f.sum) + (1015049458521/341750000000000000000000000 : ℝ)*base65 + (122499106654933051/34175000000000000000000000000000 : ℝ)*base68 + (52552522559133051/34175000000000000000000000000000 : ℝ)*base70 + (171196577758266949/34175000000000000000000000000000 : ℝ)*base71 + (604232517273/170875000000000000000000000 : ℝ)*base74 + (263282909931633051/34175000000000000000000000000000 : ℝ)*base76 + (107512714320341949/34175000000000000000000000000000 : ℝ)*base77 + (153177890557233051/34175000000000000000000000000000 : ℝ)*base80 + (4747695950553/1367000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9951413/2500000000000000000000 : ℝ)*base90 + (9951413/2500000000000000000000 : ℝ)*base92 + (9951413/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s7_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074421699/5000000000 : ℝ)*x 0 + (5392356941/10000000000 : ℝ)*x 1 + (5266320151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074421699/5000000000 : ℝ)^8373 ≤ (13060998064331/100000000000000 : ℝ)^6325 := by
    have hnat : (1074421699 : ℕ)^8373*100000000000000^6325 ≤ 13060998064331^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074421699 5000000000 13060998064331 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392356941/10000000000 : ℝ)^8373 ≤ (44149931838309/100000000000000 : ℝ)^6325 := by
    have hnat : (5392356941 : ℕ)^8373*100000000000000^6325 ≤ 44149931838309^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392356941 10000000000 44149931838309 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266320151/10000000000 : ℝ)^8373 ≤ (21394535041511/50000000000000 : ℝ)^6325 := by
    have hnat : (5266320151 : ℕ)^8373*50000000000000^6325 ≤ 21394535041511^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266320151 10000000000 21394535041511 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074421699/5000000000 : ℝ), (5392356941/10000000000 : ℝ), (5266320151/10000000000 : ℝ)] ![(13060998064331/100000000000000 : ℝ), (44149931838309/100000000000000 : ℝ), (21394535041511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074421699/5000000000 : ℝ)|^8373 ≤ (13060998064331/100000000000000 : ℝ)^6325
        have hw : |(-1074421699/5000000000 : ℝ)|=(1074421699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392356941/10000000000 : ℝ)|^8373 ≤ (44149931838309/100000000000000 : ℝ)^6325
        have hw : |(5392356941/10000000000 : ℝ)|=(5392356941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266320151/10000000000 : ℝ)|^8373 ≤ (21394535041511/50000000000000 : ℝ)^6325
        have hw : |(5266320151/10000000000 : ℝ)|=(5266320151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068921989/2000000000 : ℝ)*x 0 + (-276595281/1250000000 : ℝ)*x 1 + (105326403/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068921989/2000000000 : ℝ)^8373 ≤ (43633166055009/100000000000000 : ℝ)^6325 := by
    have hnat : (1068921989 : ℕ)^8373*100000000000000^6325 ≤ 43633166055009^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068921989 2000000000 43633166055009 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276595281/1250000000 : ℝ)^8373 ≤ (13577763860369/100000000000000 : ℝ)^6325 := by
    have hnat : (276595281 : ℕ)^8373*100000000000000^6325 ≤ 13577763860369^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276595281 1250000000 13577763860369 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105326403/200000000 : ℝ)^8373 ≤ (42789070072267/100000000000000 : ℝ)^6325 := by
    have hnat : (105326403 : ℕ)^8373*100000000000000^6325 ≤ 42789070072267^6325*200000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105326403 200000000 42789070072267 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068921989/2000000000 : ℝ), (-276595281/1250000000 : ℝ), (105326403/200000000 : ℝ)] ![(43633166055009/100000000000000 : ℝ), (13577763860369/100000000000000 : ℝ), (42789070072267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068921989/2000000000 : ℝ)|^8373 ≤ (43633166055009/100000000000000 : ℝ)^6325
        have hw : |(1068921989/2000000000 : ℝ)|=(1068921989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276595281/1250000000 : ℝ)|^8373 ≤ (13577763860369/100000000000000 : ℝ)^6325
        have hw : |(-276595281/1250000000 : ℝ)|=(276595281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105326403/200000000 : ℝ)|^8373 ≤ (42789070072267/100000000000000 : ℝ)^6325
        have hw : |(105326403/200000000 : ℝ)|=(105326403/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344609943/10000000000 : ℝ)*x 0 + (5266320151/10000000000 : ℝ)*x 1 + (-2212762249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344609943/10000000000 : ℝ)^8373 ≤ (21816583016697/50000000000000 : ℝ)^6325 := by
    have hnat : (5344609943 : ℕ)^8373*50000000000000^6325 ≤ 21816583016697^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344609943 10000000000 21816583016697 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266320151/10000000000 : ℝ)^8373 ≤ (21394535041511/50000000000000 : ℝ)^6325 := by
    have hnat : (5266320151 : ℕ)^8373*50000000000000^6325 ≤ 21394535041511^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266320151 10000000000 21394535041511 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212762249/10000000000 : ℝ)^8373 ≤ (3394440967123/25000000000000 : ℝ)^6325 := by
    have hnat : (2212762249 : ℕ)^8373*25000000000000^6325 ≤ 3394440967123^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212762249 10000000000 3394440967123 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344609943/10000000000 : ℝ), (5266320151/10000000000 : ℝ), (-2212762249/10000000000 : ℝ)] ![(21816583016697/50000000000000 : ℝ), (21394535041511/50000000000000 : ℝ), (3394440967123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344609943/10000000000 : ℝ)|^8373 ≤ (21816583016697/50000000000000 : ℝ)^6325
        have hw : |(5344609943/10000000000 : ℝ)|=(5344609943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266320151/10000000000 : ℝ)|^8373 ≤ (21394535041511/50000000000000 : ℝ)^6325
        have hw : |(5266320151/10000000000 : ℝ)|=(5266320151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212762249/10000000000 : ℝ)|^8373 ≤ (3394440967123/25000000000000 : ℝ)^6325
        have hw : |(-2212762249/10000000000 : ℝ)|=(2212762249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359346443/10000000000 : ℝ)*x 0 + (2117421313/5000000000 : ℝ)*x 1 + (4487459859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359346443/10000000000 : ℝ)^8373 ≤ (33317163792037/100000000000000 : ℝ)^6325 := by
    have hnat : (4359346443 : ℕ)^8373*100000000000000^6325 ≤ 33317163792037^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359346443 10000000000 33317163792037 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117421313/5000000000 : ℝ)^8373 ≤ (801584405093/2500000000000 : ℝ)^6325 := by
    have hnat : (2117421313 : ℕ)^8373*2500000000000^6325 ≤ 801584405093^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117421313 5000000000 801584405093 2500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487459859/10000000000 : ℝ)^8373 ≤ (34619459986203/100000000000000 : ℝ)^6325 := by
    have hnat : (4487459859 : ℕ)^8373*100000000000000^6325 ≤ 34619459986203^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487459859 10000000000 34619459986203 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359346443/10000000000 : ℝ), (2117421313/5000000000 : ℝ), (4487459859/10000000000 : ℝ)] ![(33317163792037/100000000000000 : ℝ), (801584405093/2500000000000 : ℝ), (34619459986203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359346443/10000000000 : ℝ)|^8373 ≤ (33317163792037/100000000000000 : ℝ)^6325
        have hw : |(4359346443/10000000000 : ℝ)|=(4359346443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117421313/5000000000 : ℝ)|^8373 ≤ (801584405093/2500000000000 : ℝ)^6325
        have hw : |(2117421313/5000000000 : ℝ)|=(2117421313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487459859/10000000000 : ℝ)|^8373 ≤ (34619459986203/100000000000000 : ℝ)^6325
        have hw : |(4487459859/10000000000 : ℝ)|=(4487459859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074424103/5000000000 : ℝ)*x 0 + (526663729/1000000000 : ℝ)*x 1 + (2696019323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074424103/5000000000 : ℝ)^8373 ≤ (6530518375297/50000000000000 : ℝ)^6325 := by
    have hnat : (1074424103 : ℕ)^8373*50000000000000^6325 ≤ 6530518375297^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074424103 5000000000 6530518375297 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526663729/1000000000 : ℝ)^8373 ≤ (42792481226909/100000000000000 : ℝ)^6325 := by
    have hnat : (526663729 : ℕ)^8373*100000000000000^6325 ≤ 42792481226909^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526663729 1000000000 42792481226909 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696019323/5000000000 : ℝ)^8373 ≤ (44146482008799/100000000000000 : ℝ)^6325 := by
    have hnat : (2696019323 : ℕ)^8373*100000000000000^6325 ≤ 44146482008799^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696019323 5000000000 44146482008799 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074424103/5000000000 : ℝ), (526663729/1000000000 : ℝ), (2696019323/5000000000 : ℝ)] ![(6530518375297/50000000000000 : ℝ), (42792481226909/100000000000000 : ℝ), (44146482008799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074424103/5000000000 : ℝ)|^8373 ≤ (6530518375297/50000000000000 : ℝ)^6325
        have hw : |(-1074424103/5000000000 : ℝ)|=(1074424103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526663729/1000000000 : ℝ)|^8373 ≤ (42792481226909/100000000000000 : ℝ)^6325
        have hw : |(526663729/1000000000 : ℝ)|=(526663729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696019323/5000000000 : ℝ)|^8373 ≤ (44146482008799/100000000000000 : ℝ)^6325
        have hw : |(2696019323/5000000000 : ℝ)|=(2696019323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312589387/10000000000 : ℝ)*x 0 + (-2087043771/10000000000 : ℝ)*x 1 + (2696019323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312589387/10000000000 : ℝ)^8373 ≤ (43287443155659/100000000000000 : ℝ)^6325 := by
    have hnat : (5312589387 : ℕ)^8373*100000000000000^6325 ≤ 43287443155659^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312589387 10000000000 43287443155659 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087043771/10000000000 : ℝ)^8373 ≤ (628303741037/5000000000000 : ℝ)^6325 := by
    have hnat : (2087043771 : ℕ)^8373*5000000000000^6325 ≤ 628303741037^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087043771 10000000000 628303741037 5000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696019323/5000000000 : ℝ)^8373 ≤ (44146482008799/100000000000000 : ℝ)^6325 := by
    have hnat : (2696019323 : ℕ)^8373*100000000000000^6325 ≤ 44146482008799^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696019323 5000000000 44146482008799 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312589387/10000000000 : ℝ), (-2087043771/10000000000 : ℝ), (2696019323/5000000000 : ℝ)] ![(43287443155659/100000000000000 : ℝ), (628303741037/5000000000000 : ℝ), (44146482008799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312589387/10000000000 : ℝ)|^8373 ≤ (43287443155659/100000000000000 : ℝ)^6325
        have hw : |(5312589387/10000000000 : ℝ)|=(5312589387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087043771/10000000000 : ℝ)|^8373 ≤ (628303741037/5000000000000 : ℝ)^6325
        have hw : |(-2087043771/10000000000 : ℝ)|=(2087043771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696019323/5000000000 : ℝ)|^8373 ≤ (44146482008799/100000000000000 : ℝ)^6325
        have hw : |(2696019323/5000000000 : ℝ)|=(2696019323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062517879/2000000000 : ℝ)*x 0 + (5392038639/10000000000 : ℝ)*x 1 + (-2087043769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062517879/2000000000 : ℝ)^8373 ≤ (865748864839/2000000000000 : ℝ)^6325 := by
    have hnat : (1062517879 : ℕ)^8373*2000000000000^6325 ≤ 865748864839^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062517879 2000000000 865748864839 2000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392038639/10000000000 : ℝ)^8373 ≤ (44146481932931/100000000000000 : ℝ)^6325 := by
    have hnat : (5392038639 : ℕ)^8373*100000000000000^6325 ≤ 44146481932931^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392038639 10000000000 44146481932931 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087043769/10000000000 : ℝ)^8373 ≤ (12566074804799/100000000000000 : ℝ)^6325 := by
    have hnat : (2087043769 : ℕ)^8373*100000000000000^6325 ≤ 12566074804799^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087043769 10000000000 12566074804799 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062517879/2000000000 : ℝ), (5392038639/10000000000 : ℝ), (-2087043769/10000000000 : ℝ)] ![(865748864839/2000000000000 : ℝ), (44146481932931/100000000000000 : ℝ), (12566074804799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062517879/2000000000 : ℝ)|^8373 ≤ (865748864839/2000000000000 : ℝ)^6325
        have hw : |(1062517879/2000000000 : ℝ)|=(1062517879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392038639/10000000000 : ℝ)|^8373 ≤ (44146481932931/100000000000000 : ℝ)^6325
        have hw : |(5392038639/10000000000 : ℝ)|=(5392038639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087043769/10000000000 : ℝ)|^8373 ≤ (12566074804799/100000000000000 : ℝ)^6325
        have hw : |(-2087043769/10000000000 : ℝ)|=(2087043769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s7_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871871217/2000000000 : ℝ)*x 0 + (448682413/1000000000 : ℝ)*x 1 + (529435079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871871217/2000000000 : ℝ)^8373 ≤ (33317261343657/100000000000000 : ℝ)^6325 := by
    have hnat : (871871217 : ℕ)^8373*100000000000000^6325 ≤ 33317261343657^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871871217 2000000000 33317261343657 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448682413/1000000000 : ℝ)^8373 ≤ (4326620953757/12500000000000 : ℝ)^6325 := by
    have hnat : (448682413 : ℕ)^8373*12500000000000^6325 ≤ 4326620953757^6325*1000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448682413 1000000000 4326620953757 12500000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529435079/1250000000 : ℝ)^8373 ≤ (32069771017343/100000000000000 : ℝ)^6325 := by
    have hnat : (529435079 : ℕ)^8373*100000000000000^6325 ≤ 32069771017343^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529435079 1250000000 32069771017343 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871871217/2000000000 : ℝ), (448682413/1000000000 : ℝ), (529435079/1250000000 : ℝ)] ![(33317261343657/100000000000000 : ℝ), (4326620953757/12500000000000 : ℝ), (32069771017343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871871217/2000000000 : ℝ)|^8373 ≤ (33317261343657/100000000000000 : ℝ)^6325
        have hw : |(871871217/2000000000 : ℝ)|=(871871217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448682413/1000000000 : ℝ)|^8373 ≤ (4326620953757/12500000000000 : ℝ)^6325
        have hw : |(448682413/1000000000 : ℝ)|=(448682413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529435079/1250000000 : ℝ)|^8373 ≤ (32069771017343/100000000000000 : ℝ)^6325
        have hw : |(529435079/1250000000 : ℝ)|=(529435079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2849/25000 : ℝ) ^ (2093/512 : ℝ) ≤ (1393500550900627/10000000000000000000 : ℝ) := by
    have hpowers : (2849/25000 : ℝ)^2093 ≤ (1393500550900627/10000000000000000000 : ℝ)^512 := by
      have hnat : (2849 : ℕ)^2093*10000000000000000000^512 ≤ 1393500550900627^512*25000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 25000 1393500550900627 10000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/25000 : ℝ)) (X := (1393500550900627/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (6610471840506409/20000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^2093 ≤ (6610471840506409/20000000000000000000 : ℝ)^512 := by
      have hnat : (14077 : ℕ)^2093*20000000000000000000^512 ≤ 6610471840506409^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 6610471840506409 20000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (6610471840506409/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001393500550900627/5000000000000000000 : ℝ) ≤ (10000681698225613/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (5001393500550900627/5000000000000000000 : ℝ)^512 ≤ (10000681698225613/10000000000000000 : ℝ)^2093 := by
      have hnat : (5001393500550900627 : ℕ)^512*10000000000000000^2093 ≤ 10000681698225613^2093*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001393500550900627 5000000000000000000 10000681698225613 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000681698225613/10000000000000000 : ℝ)) (X := (5001393500550900627/5000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009397472942307663/20000000000000000000 : ℝ) ≤ (2500287306050239/2500000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (20009397472942307663/20000000000000000000 : ℝ)^512 ≤ (2500287306050239/2500000000000000 : ℝ)^2093 := by
      have hnat : (20009397472942307663 : ℕ)^512*2500000000000000^2093 ≤ 2500287306050239^2093*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009397472942307663 20000000000000000000 2500287306050239 2500000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500287306050239/2500000000000000 : ℝ)) (X := (20009397472942307663/20000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006610471840506409/10000000000000000000 : ℝ) ≤ (10001616750176299/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (10006610471840506409/10000000000000000000 : ℝ)^512 ≤ (10001616750176299/10000000000000000 : ℝ)^2093 := by
      have hnat : (10006610471840506409 : ℕ)^512*10000000000000000^2093 ≤ 10001616750176299^2093*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006610471840506409 10000000000000000000 10001616750176299 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001616750176299/10000000000000000 : ℝ)) (X := (10006610471840506409/10000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1393500550900627/10000000000000000000 : ℝ) ≤ ((3828738825844692971/3830000000000000000 : ℝ)+2*(66789425049/38300000000000 : ℝ)*(2849/25000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (3828738825844692971/3830000000000000000 : ℝ)+2*(66789425049/38300000000000 : ℝ)*(2849/25000 : ℝ)=(10000681698225613/10000000000000000 : ℝ) by norm_num, show 1+2*(1393500550900627/10000000000000000000 : ℝ)=(5001393500550900627/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6610471840506409/20000000000000000000 : ℝ)+(1393500550900627/10000000000000000000 : ℝ) ≤ ((3828738825844692971/3830000000000000000 : ℝ)+(66789425049/38300000000000 : ℝ)*((14077/100000 : ℝ)+(2849/25000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (3828738825844692971/3830000000000000000 : ℝ)+(66789425049/38300000000000 : ℝ)*((14077/100000 : ℝ)+(2849/25000 : ℝ))=(2500287306050239/2500000000000000 : ℝ) by norm_num, show 1+(6610471840506409/20000000000000000000 : ℝ)+(1393500550900627/10000000000000000000 : ℝ)=(20009397472942307663/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6610471840506409/20000000000000000000 : ℝ) ≤ ((3828738825844692971/3830000000000000000 : ℝ)+2*(66789425049/38300000000000 : ℝ)*(14077/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (3828738825844692971/3830000000000000000 : ℝ)+2*(66789425049/38300000000000 : ℝ)*(14077/100000 : ℝ)=(10001616750176299/10000000000000000 : ℝ) by norm_num, show 1+2*(6610471840506409/20000000000000000000 : ℝ)=(10006610471840506409/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3828738825844692971/3830000000000000000 : ℝ)*(X 1 0+X 2 0)+(66789425049/38300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (3828738825844692971/3830000000000000000 : ℝ)) (alpha := (66789425049/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3828738825844692971/3830000000000000000 : ℝ)*(X 0 1+X 2 1)+(66789425049/38300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (3828738825844692971/3830000000000000000 : ℝ)) (alpha := (66789425049/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3828738825844692971/3830000000000000000 : ℝ)*(X 0 2+X 1 2)+(66789425049/38300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (3828738825844692971/3830000000000000000 : ℝ)) (alpha := (66789425049/38300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074421699/5000000000 : ℝ)*X 0 0+(5392356941/10000000000 : ℝ)*X 0 1+(5266320151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068921989/2000000000 : ℝ)*X 1 0+(-276595281/1250000000 : ℝ)*X 1 1+(105326403/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344609943/10000000000 : ℝ)*X 2 0+(5266320151/10000000000 : ℝ)*X 2 1+(-2212762249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359346443/10000000000 : ℝ)*X 0 0+(2117421313/5000000000 : ℝ)*X 0 1+(4487459859/10000000000 : ℝ)*X 0 2+(4359346443/10000000000 : ℝ)*X 1 0+(2117421313/5000000000 : ℝ)*X 1 1+(4487459859/10000000000 : ℝ)*X 1 2+(4359346443/10000000000 : ℝ)*X 2 0+(2117421313/5000000000 : ℝ)*X 2 1+(4487459859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074424103/5000000000 : ℝ)*X 0 0+(526663729/1000000000 : ℝ)*X 0 1+(2696019323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312589387/10000000000 : ℝ)*X 1 0+(-2087043771/10000000000 : ℝ)*X 1 1+(2696019323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062517879/2000000000 : ℝ)*X 2 0+(5392038639/10000000000 : ℝ)*X 2 1+(-2087043769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871871217/2000000000 : ℝ)*X 0 0+(448682413/1000000000 : ℝ)*X 0 1+(529435079/1250000000 : ℝ)*X 0 2+(871871217/2000000000 : ℝ)*X 1 0+(448682413/1000000000 : ℝ)*X 1 1+(529435079/1250000000 : ℝ)*X 1 2+(871871217/2000000000 : ℝ)*X 2 0+(448682413/1000000000 : ℝ)*X 2 1+(529435079/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132372355915567054818330381/11968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (541908751/25000000000000 : ℝ)*(base19) + (20163063/1000000000000 : ℝ)*(base23) + (79292429/100000000000000 : ℝ)*(lower2) + (55772323/20000000000000 : ℝ)*(upper3) + (83518279/50000000000000 : ℝ)*(upper5) + (743308271718763/12500000000000 : ℝ)*(major0) + (743308271718763/12500000000000 : ℝ)*(major1) + (743308271718763/12500000000000 : ℝ)*(major2) + (7934253604469679/100000000000000 : ℝ)*(sp0) + (7934310810275991/100000000000000 : ℝ)*(sp1) + (991788870200587/12500000000000 : ℝ)*(sp2) + (395858694688801/10000000000000 : ℝ)*(sp3) + (59373441317/100000000000000 : ℝ)*(sp4) + (6410808029/20000000000000 : ℝ)*(sp7) + (1979309500464077/50000000000000 : ℝ)*(f.failure) + (1983578244477749/25000000000000 : ℝ)*(f.sum) + (1575614408969/1915000000000000000000000000 : ℝ)*base66 + (562512069138989873/47875000000000000000000000000000 : ℝ)*base67 + (267334708233239873/47875000000000000000000000000000 : ℝ)*base69 + (251539841960135127/47875000000000000000000000000000 : ℝ)*base72 + (3171837212583/957500000000000000000000000 : ℝ)*base73 + (889653199503614873/47875000000000000000000000000000 : ℝ)*base75 + (237562560284989873/47875000000000000000000000000000 : ℝ)*base77 + (566225913521364873/47875000000000000000000000000000 : ℝ)*base79 + (2138472709097/957500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (61121179/5000000000000000000000 : ℝ)*base90 + (61121179/5000000000000000000000 : ℝ)*base92 + (61121179/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (607606582557804433438831143/191500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286747477/50000000000000 : ℝ)*(base19) + (315202523/50000000000000 : ℝ)*(base23) + (12453593/25000000000000 : ℝ)*(upper3) + (24890839/100000000000000 : ℝ)*(lower4) + (95687231/100000000000000 : ℝ)*(upper5) + (5976507514083763/100000000000000 : ℝ)*(major0) + (5976507514083763/100000000000000 : ℝ)*(major1) + (5976507514083763/100000000000000 : ℝ)*(major2) + (3411588479/20000000000000 : ℝ)*(sp1) + (16734292617/100000000000000 : ℝ)*(sp2) + (7974397115936827/100000000000000 : ℝ)*(sp4) + (3987189742249739/50000000000000 : ℝ)*(sp5) + (1594875950247833/20000000000000 : ℝ)*(sp6) + (3978617806468013/100000000000000 : ℝ)*(sp7) + (3978617806468013/100000000000000 : ℝ)*(f.failure) + (7974397115936827/100000000000000 : ℝ)*(f.sum) + (3259419333271/957500000000000000000000000 : ℝ)*base65 + (4955594095890029873/383000000000000000000000000000000 : ℝ)*base67 + (6329143955636029873/383000000000000000000000000000000 : ℝ)*base69 + (3992833649872029873/383000000000000000000000000000000 : ℝ)*base71 + (859793158293/1915000000000000000000000000 : ℝ)*base74 + (5566219523768029873/383000000000000000000000000000000 : ℝ)*base75 + (2999566143537029873/383000000000000000000000000000000 : ℝ)*base77 + (709946114214029873/383000000000000000000000000000000 : ℝ)*base79 + (7477645382283/1915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (25767749/10000000000000000000000 : ℝ)*base89 + (25767749/10000000000000000000000 : ℝ)*base91 + (25767749/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1180_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1180_s8_0 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148850361/10000000000 : ℝ)*x 0 + (5392301943/10000000000 : ℝ)*x 1 + (5266370363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148850361/10000000000 : ℝ)^8373 ≤ (13061054090223/100000000000000 : ℝ)^6325 := by
    have hnat : (2148850361 : ℕ)^8373*100000000000000^6325 ≤ 13061054090223^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148850361 10000000000 13061054090223 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392301943/10000000000 : ℝ)^8373 ≤ (172458342733/390625000000 : ℝ)^6325 := by
    have hnat : (5392301943 : ℕ)^8373*390625000000^6325 ≤ 172458342733^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392301943 10000000000 172458342733 390625000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266370363/10000000000 : ℝ)^8373 ≤ (10697402539589/25000000000000 : ℝ)^6325 := by
    have hnat : (5266370363 : ℕ)^8373*25000000000000^6325 ≤ 10697402539589^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266370363 10000000000 10697402539589 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148850361/10000000000 : ℝ), (5392301943/10000000000 : ℝ), (5266370363/10000000000 : ℝ)] ![(13061054090223/100000000000000 : ℝ), (172458342733/390625000000 : ℝ), (10697402539589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148850361/10000000000 : ℝ)|^8373 ≤ (13061054090223/100000000000000 : ℝ)^6325
        have hw : |(-2148850361/10000000000 : ℝ)|=(2148850361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392301943/10000000000 : ℝ)|^8373 ≤ (172458342733/390625000000 : ℝ)^6325
        have hw : |(5392301943/10000000000 : ℝ)|=(5392301943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266370363/10000000000 : ℝ)|^8373 ≤ (10697402539589/25000000000000 : ℝ)^6325
        have hw : |(5266370363/10000000000 : ℝ)|=(5266370363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_1 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344595379/10000000000 : ℝ)*x 0 + (-2212715207/10000000000 : ℝ)*x 1 + (5266370311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344595379/10000000000 : ℝ)^8373 ≤ (43633008634473/100000000000000 : ℝ)^6325 := by
    have hnat : (5344595379 : ℕ)^8373*100000000000000^6325 ≤ 43633008634473^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344595379 10000000000 43633008634473 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212715207/10000000000 : ℝ)^8373 ≤ (3394345437437/25000000000000 : ℝ)^6325 := by
    have hnat : (2212715207 : ℕ)^8373*25000000000000^6325 ≤ 3394345437437^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212715207 10000000000 3394345437437 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266370311/10000000000 : ℝ)^8373 ≤ (42789609599049/100000000000000 : ℝ)^6325 := by
    have hnat : (5266370311 : ℕ)^8373*100000000000000^6325 ≤ 42789609599049^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266370311 10000000000 42789609599049 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344595379/10000000000 : ℝ), (-2212715207/10000000000 : ℝ), (5266370311/10000000000 : ℝ)] ![(43633008634473/100000000000000 : ℝ), (3394345437437/25000000000000 : ℝ), (42789609599049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344595379/10000000000 : ℝ)|^8373 ≤ (43633008634473/100000000000000 : ℝ)^6325
        have hw : |(5344595379/10000000000 : ℝ)|=(5344595379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212715207/10000000000 : ℝ)|^8373 ≤ (3394345437437/25000000000000 : ℝ)^6325
        have hw : |(-2212715207/10000000000 : ℝ)|=(2212715207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266370311/10000000000 : ℝ)|^8373 ≤ (42789609599049/100000000000000 : ℝ)^6325
        have hw : |(5266370311/10000000000 : ℝ)|=(5266370311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_2 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672297709/5000000000 : ℝ)*x 0 + (658296293/1250000000 : ℝ)*x 1 + (-2212715111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672297709/5000000000 : ℝ)^8373 ≤ (43633009055961/100000000000000 : ℝ)^6325 := by
    have hnat : (2672297709 : ℕ)^8373*100000000000000^6325 ≤ 43633009055961^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672297709 5000000000 43633009055961 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658296293/1250000000 : ℝ)^8373 ≤ (21394804976997/50000000000000 : ℝ)^6325 := by
    have hnat : (658296293 : ℕ)^8373*50000000000000^6325 ≤ 21394804976997^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658296293 1250000000 21394804976997 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212715111/10000000000 : ℝ)^8373 ≤ (13577380969949/100000000000000 : ℝ)^6325 := by
    have hnat : (2212715111 : ℕ)^8373*100000000000000^6325 ≤ 13577380969949^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212715111 10000000000 13577380969949 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672297709/5000000000 : ℝ), (658296293/1250000000 : ℝ), (-2212715111/10000000000 : ℝ)] ![(43633009055961/100000000000000 : ℝ), (21394804976997/50000000000000 : ℝ), (13577380969949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672297709/5000000000 : ℝ)|^8373 ≤ (43633009055961/100000000000000 : ℝ)^6325
        have hw : |(2672297709/5000000000 : ℝ)|=(2672297709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658296293/1250000000 : ℝ)|^8373 ≤ (21394804976997/50000000000000 : ℝ)^6325
        have hw : |(658296293/1250000000 : ℝ)|=(658296293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2212715111/10000000000 : ℝ)|^8373 ≤ (13577380969949/100000000000000 : ℝ)^6325
        have hw : |(-2212715111/10000000000 : ℝ)|=(2212715111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_3 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179674569/5000000000 : ℝ)*x 0 + (1058736917/2500000000 : ℝ)*x 1 + (4487354099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179674569/5000000000 : ℝ)^8373 ≤ (1332687642333/4000000000000 : ℝ)^6325 := by
    have hnat : (2179674569 : ℕ)^8373*4000000000000^6325 ≤ 1332687642333^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179674569 5000000000 1332687642333 4000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058736917/2500000000 : ℝ)^8373 ≤ (16032214515661/50000000000000 : ℝ)^6325 := by
    have hnat : (1058736917 : ℕ)^8373*50000000000000^6325 ≤ 16032214515661^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058736917 2500000000 16032214515661 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487354099/10000000000 : ℝ)^8373 ≤ (432729748699/1250000000000 : ℝ)^6325 := by
    have hnat : (4487354099 : ℕ)^8373*1250000000000^6325 ≤ 432729748699^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487354099 10000000000 432729748699 1250000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179674569/5000000000 : ℝ), (1058736917/2500000000 : ℝ), (4487354099/10000000000 : ℝ)] ![(1332687642333/4000000000000 : ℝ), (16032214515661/50000000000000 : ℝ), (432729748699/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179674569/5000000000 : ℝ)|^8373 ≤ (1332687642333/4000000000000 : ℝ)^6325
        have hw : |(2179674569/5000000000 : ℝ)|=(2179674569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058736917/2500000000 : ℝ)|^8373 ≤ (16032214515661/50000000000000 : ℝ)^6325
        have hw : |(1058736917/2500000000 : ℝ)|=(1058736917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487354099/10000000000 : ℝ)|^8373 ≤ (432729748699/1250000000000 : ℝ)^6325
        have hw : |(4487354099/10000000000 : ℝ)|=(4487354099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_4 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074427683/5000000000 : ℝ)*x 0 + (1053337379/2000000000 : ℝ)*x 1 + (5391984101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074427683/5000000000 : ℝ)^8373 ≤ (3265273590409/25000000000000 : ℝ)^6325 := by
    have hnat : (1074427683 : ℕ)^8373*25000000000000^6325 ≤ 3265273590409^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074427683 5000000000 3265273590409 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053337379/2000000000 : ℝ)^8373 ≤ (10698253695951/25000000000000 : ℝ)^6325 := by
    have hnat : (1053337379 : ℕ)^8373*25000000000000^6325 ≤ 10698253695951^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053337379 2000000000 10698253695951 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391984101/10000000000 : ℝ)^8373 ≤ (44145890831293/100000000000000 : ℝ)^6325 := by
    have hnat : (5391984101 : ℕ)^8373*100000000000000^6325 ≤ 44145890831293^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391984101 10000000000 44145890831293 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074427683/5000000000 : ℝ), (1053337379/2000000000 : ℝ), (5391984101/10000000000 : ℝ)] ![(3265273590409/25000000000000 : ℝ), (10698253695951/25000000000000 : ℝ), (44145890831293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074427683/5000000000 : ℝ)|^8373 ≤ (3265273590409/25000000000000 : ℝ)^6325
        have hw : |(-1074427683/5000000000 : ℝ)|=(1074427683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053337379/2000000000 : ℝ)|^8373 ≤ (10698253695951/25000000000000 : ℝ)^6325
        have hw : |(1053337379/2000000000 : ℝ)|=(1053337379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391984101/10000000000 : ℝ)|^8373 ≤ (44145890831293/100000000000000 : ℝ)^6325
        have hw : |(5391984101/10000000000 : ℝ)|=(5391984101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_5 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664075207/1250000000 : ℝ)*x 0 + (-41742027/200000000 : ℝ)*x 1 + (1347996023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664075207/1250000000 : ℝ)^8373 ≤ (21643787746983/50000000000000 : ℝ)^6325 := by
    have hnat : (664075207 : ℕ)^8373*50000000000000^6325 ≤ 21643787746983^6325*1250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664075207 1250000000 21643787746983 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41742027/200000000 : ℝ)^8373 ≤ (12566533759463/100000000000000 : ℝ)^6325 := by
    have hnat : (41742027 : ℕ)^8373*100000000000000^6325 ≤ 12566533759463^6325*200000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41742027 200000000 12566533759463 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347996023/2500000000 : ℝ)^8373 ≤ (44145890733749/100000000000000 : ℝ)^6325 := by
    have hnat : (1347996023 : ℕ)^8373*100000000000000^6325 ≤ 44145890733749^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347996023 2500000000 44145890733749 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664075207/1250000000 : ℝ), (-41742027/200000000 : ℝ), (1347996023/2500000000 : ℝ)] ![(21643787746983/50000000000000 : ℝ), (12566533759463/100000000000000 : ℝ), (44145890733749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664075207/1250000000 : ℝ)|^8373 ≤ (21643787746983/50000000000000 : ℝ)^6325
        have hw : |(664075207/1250000000 : ℝ)|=(664075207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41742027/200000000 : ℝ)|^8373 ≤ (12566533759463/100000000000000 : ℝ)^6325
        have hw : |(-41742027/200000000 : ℝ)|=(41742027/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347996023/2500000000 : ℝ)|^8373 ≤ (44145890733749/100000000000000 : ℝ)^6325
        have hw : |(1347996023/2500000000 : ℝ)|=(1347996023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_6 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656300843/5000000000 : ℝ)*x 0 + (5391984091/10000000000 : ℝ)*x 1 + (-16305479/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656300843/5000000000 : ℝ)^8373 ≤ (21643787908779/50000000000000 : ℝ)^6325 := by
    have hnat : (2656300843 : ℕ)^8373*50000000000000^6325 ≤ 21643787908779^6325*5000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656300843 5000000000 21643787908779 50000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391984091/10000000000 : ℝ)^8373 ≤ (4414589072291/10000000000000 : ℝ)^6325 := by
    have hnat : (5391984091 : ℕ)^8373*10000000000000^6325 ≤ 4414589072291^6325*10000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391984091 10000000000 4414589072291 10000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16305479/78125000 : ℝ)^8373 ≤ (12566533456579/100000000000000 : ℝ)^6325 := by
    have hnat : (16305479 : ℕ)^8373*100000000000000^6325 ≤ 12566533456579^6325*78125000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16305479 78125000 12566533456579 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656300843/5000000000 : ℝ), (5391984091/10000000000 : ℝ), (-16305479/78125000 : ℝ)] ![(21643787908779/50000000000000 : ℝ), (4414589072291/10000000000000 : ℝ), (12566533456579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656300843/5000000000 : ℝ)|^8373 ≤ (21643787908779/50000000000000 : ℝ)^6325
        have hw : |(2656300843/5000000000 : ℝ)|=(2656300843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391984091/10000000000 : ℝ)|^8373 ≤ (4414589072291/10000000000000 : ℝ)^6325
        have hw : |(5391984091/10000000000 : ℝ)|=(5391984091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16305479/78125000 : ℝ)|^8373 ≤ (12566533456579/100000000000000 : ℝ)^6325
        have hw : |(-16305479/78125000 : ℝ)|=(16305479/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1180_s8_7 (p : ℝ) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871871753/2000000000 : ℝ)*x 0 + (112167987/250000000 : ℝ)*x 1 + (1058896137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871871753/2000000000 : ℝ)^8373 ≤ (8329322114551/25000000000000 : ℝ)^6325 := by
    have hnat : (871871753 : ℕ)^8373*25000000000000^6325 ≤ 8329322114551^6325*2000000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871871753 2000000000 8329322114551 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112167987/250000000 : ℝ)^8373 ≤ (8652974731201/25000000000000 : ℝ)^6325 := by
    have hnat : (112167987 : ℕ)^8373*25000000000000^6325 ≤ 8652974731201^6325*250000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112167987 250000000 8652974731201 25000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058896137/2500000000 : ℝ)^8373 ≤ (32070812609897/100000000000000 : ℝ)^6325 := by
    have hnat : (1058896137 : ℕ)^8373*100000000000000^6325 ≤ 32070812609897^6325*2500000000^8373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058896137 2500000000 32070812609897 100000000000000 8373 6325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8373/2048 : ℝ)) 8373 6325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871871753/2000000000 : ℝ), (112167987/250000000 : ℝ), (1058896137/2500000000 : ℝ)] ![(8329322114551/25000000000000 : ℝ), (8652974731201/25000000000000 : ℝ), (32070812609897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871871753/2000000000 : ℝ)|^8373 ≤ (8329322114551/25000000000000 : ℝ)^6325
        have hw : |(871871753/2000000000 : ℝ)|=(871871753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112167987/250000000 : ℝ)|^8373 ≤ (8652974731201/25000000000000 : ℝ)^6325
        have hw : |(112167987/250000000 : ℝ)|=(112167987/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058896137/2500000000 : ℝ)|^8373 ≤ (32070812609897/100000000000000 : ℝ)^6325
        have hw : |(1058896137/2500000000 : ℝ)|=(1058896137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1180_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11401/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (111680126130617/800000000000000000 : ℝ) := by
    have hpowers : (11401/100000 : ℝ)^2093 ≤ (111680126130617/800000000000000000 : ℝ)^512 := by
      have hnat : (11401 : ℕ)^2093*800000000000000000^512 ≤ 111680126130617^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11401 100000 111680126130617 800000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11401/100000 : ℝ)) (X := (111680126130617/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (2093/512 : ℝ) ≤ (6598961529439427/20000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^2093 ≤ (6598961529439427/20000000000000000000 : ℝ)^512 := by
      have hnat : (14071 : ℕ)^2093*20000000000000000000^512 ≤ 6598961529439427^512*100000^2093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 6598961529439427 20000000000000000000 2093 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (6598961529439427/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (400111680126130617/400000000000000000 : ℝ) ≤ (625042682599649/625000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (400111680126130617/400000000000000000 : ℝ)^512 ≤ (625042682599649/625000000000000 : ℝ)^2093 := by
      have hnat : (400111680126130617 : ℕ)^512*625000000000000^2093 ≤ 625042682599649^2093*400000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400111680126130617 400000000000000000 625042682599649 625000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625042682599649/625000000000000 : ℝ)) (X := (400111680126130617/400000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002347741170676213/5000000000000000000 : ℝ) ≤ (10001148428441973/10000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (5002347741170676213/5000000000000000000 : ℝ)^512 ≤ (10001148428441973/10000000000000000 : ℝ)^2093 := by
      have hnat : (5002347741170676213 : ℕ)^512*10000000000000000^2093 ≤ 10001148428441973^2093*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002347741170676213 5000000000000000000 10001148428441973 10000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001148428441973/10000000000000000 : ℝ)) (X := (5002347741170676213/5000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006598961529439427/10000000000000000000 : ℝ) ≤ (5000806967644781/5000000000000000 : ℝ) ^ (2093/512 : ℝ) := by
    have hpowers : (10006598961529439427/10000000000000000000 : ℝ)^512 ≤ (5000806967644781/5000000000000000 : ℝ)^2093 := by
      have hnat : (10006598961529439427 : ℕ)^512*5000000000000000^2093 ≤ 5000806967644781^2093*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006598961529439427 10000000000000000000 5000806967644781 5000000000000000 512 2093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000806967644781/5000000000000000 : ℝ)) (X := (10006598961529439427/10000000000000000000 : ℝ)) (by norm_num) 2093 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(111680126130617/800000000000000000 : ℝ) ≤ ((13345604456759140451/13350000000000000000 : ℝ)+2*(465506847589/267000000000000 : ℝ)*(11401/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (13345604456759140451/13350000000000000000 : ℝ)+2*(465506847589/267000000000000 : ℝ)*(11401/100000 : ℝ)=(625042682599649/625000000000000 : ℝ) by norm_num, show 1+2*(111680126130617/800000000000000000 : ℝ)=(400111680126130617/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6598961529439427/20000000000000000000 : ℝ)+(111680126130617/800000000000000000 : ℝ) ≤ ((13345604456759140451/13350000000000000000 : ℝ)+(465506847589/267000000000000 : ℝ)*((14071/100000 : ℝ)+(11401/100000 : ℝ)))^(2093/512 : ℝ) := by
    rw [show (13345604456759140451/13350000000000000000 : ℝ)+(465506847589/267000000000000 : ℝ)*((14071/100000 : ℝ)+(11401/100000 : ℝ))=(10001148428441973/10000000000000000 : ℝ) by norm_num, show 1+(6598961529439427/20000000000000000000 : ℝ)+(111680126130617/800000000000000000 : ℝ)=(5002347741170676213/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6598961529439427/20000000000000000000 : ℝ) ≤ ((13345604456759140451/13350000000000000000 : ℝ)+2*(465506847589/267000000000000 : ℝ)*(14071/100000 : ℝ))^(2093/512 : ℝ) := by
    rw [show (13345604456759140451/13350000000000000000 : ℝ)+2*(465506847589/267000000000000 : ℝ)*(14071/100000 : ℝ)=(5000806967644781/5000000000000000 : ℝ) by norm_num, show 1+2*(6598961529439427/20000000000000000000 : ℝ)=(10006598961529439427/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13345604456759140451/13350000000000000000 : ℝ)*(X 1 0+X 2 0)+(465506847589/267000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (13345604456759140451/13350000000000000000 : ℝ)) (alpha := (465506847589/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13345604456759140451/13350000000000000000 : ℝ)*(X 0 1+X 2 1)+(465506847589/267000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (13345604456759140451/13350000000000000000 : ℝ)) (alpha := (465506847589/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13345604456759140451/13350000000000000000 : ℝ)*(X 0 2+X 1 2)+(465506847589/267000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2093/512 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (13345604456759140451/13350000000000000000 : ℝ)) (alpha := (465506847589/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2148850361/10000000000 : ℝ)*X 0 0+(5392301943/10000000000 : ℝ)*X 0 1+(5266370363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344595379/10000000000 : ℝ)*X 1 0+(-2212715207/10000000000 : ℝ)*X 1 1+(5266370311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672297709/5000000000 : ℝ)*X 2 0+(658296293/1250000000 : ℝ)*X 2 1+(-2212715111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179674569/5000000000 : ℝ)*X 0 0+(1058736917/2500000000 : ℝ)*X 0 1+(4487354099/10000000000 : ℝ)*X 0 2+(2179674569/5000000000 : ℝ)*X 1 0+(1058736917/2500000000 : ℝ)*X 1 1+(4487354099/10000000000 : ℝ)*X 1 2+(2179674569/5000000000 : ℝ)*X 2 0+(1058736917/2500000000 : ℝ)*X 2 1+(4487354099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074427683/5000000000 : ℝ)*X 0 0+(1053337379/2000000000 : ℝ)*X 0 1+(5391984101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664075207/1250000000 : ℝ)*X 1 0+(-41742027/200000000 : ℝ)*X 1 1+(1347996023/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656300843/5000000000 : ℝ)*X 2 0+(5391984091/10000000000 : ℝ)*X 2 1+(-16305479/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871871753/2000000000 : ℝ)*X 0 0+(112167987/250000000 : ℝ)*X 0 1+(1058896137/2500000000 : ℝ)*X 0 2+(871871753/2000000000 : ℝ)*X 1 0+(112167987/250000000 : ℝ)*X 1 1+(1058896137/2500000000 : ℝ)*X 1 2+(871871753/2000000000 : ℝ)*X 2 0+(112167987/250000000 : ℝ)*X 2 1+(1058896137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1180_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54076470744687371285604361/22250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112004749/25000000000000 : ℝ)*(base19) + (101781207/25000000000000 : ℝ)*(base23) + (53778679/100000000000000 : ℝ)*(lower2) + (4228919/5000000000000 : ℝ)*(upper5) + (1190271718845589/20000000000000 : ℝ)*(major0) + (1190271718845589/20000000000000 : ℝ)*(major1) + (1190271718845589/20000000000000 : ℝ)*(major2) + (7940827281929849/100000000000000 : ℝ)*(sp0) + (3970420214907331/50000000000000 : ℝ)*(sp1) + (7940840768617763/100000000000000 : ℝ)*(sp2) + (3961870465190777/100000000000000 : ℝ)*(sp3) + (6946906371/50000000000000 : ℝ)*(sp4) + (297908933/100000000000000 : ℝ)*(sp5) + (5466509069/100000000000000 : ℝ)*(sp7) + (1980937965849923/50000000000000 : ℝ)*(f.failure) + (7940841175742591/100000000000000 : ℝ)*(f.sum) + (4056099401579/2670000000000000000000000000 : ℝ)*base66 + (6066079360627870639/267000000000000000000000000000000 : ℝ)*base67 + (4481125705690870639/267000000000000000000000000000000 : ℝ)*base69 + (527844782140129361/267000000000000000000000000000000 : ℝ)*base72 + (18109021417681/2670000000000000000000000000 : ℝ)*base73 + (6233683377427870639/267000000000000000000000000000000 : ℝ)*base75 + (225477031063870639/267000000000000000000000000000000 : ℝ)*base77 + (3527708284702870639/267000000000000000000000000000000 : ℝ)*base79 + (211486842781/2670000000000000000000000000 : ℝ)*base81 + (49556821/5000000000000000000000 : ℝ)*base90 + (49556821/5000000000000000000000 : ℝ)*base92 + (49556821/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2842856013494778788509179/890000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1109797429/100000000000000 : ℝ)*(base19) + (698874779/50000000000000 : ℝ)*(base23) + (345772261/100000000000000 : ℝ)*(lower1) + (50834087/50000000000000 : ℝ)*(upper2) + (79220631/50000000000000 : ℝ)*(upper3) + (150434451/100000000000000 : ℝ)*(upper5) + (23925805758871/400000000000 : ℝ)*(major0) + (23925805758871/400000000000 : ℝ)*(major1) + (23925805758871/400000000000 : ℝ)*(major2) + (8553657813/100000000000000 : ℝ)*(sp2) + (3990496874125111/50000000000000 : ℝ)*(sp4) + (7980992638452793/100000000000000 : ℝ)*(sp5) + (7980983796842851/100000000000000 : ℝ)*(sp6) + (497738628088907/12500000000000 : ℝ)*(sp7) + (497738628088907/12500000000000 : ℝ)*(f.failure) + (3990496874125111/50000000000000 : ℝ)*(f.sum) + (692516414099/267000000000000000000000000 : ℝ)*base65 + (17643405094659179/5340000000000000000000000000000 : ℝ)*base68 + (227976382257740821/5340000000000000000000000000000 : ℝ)*base69 + (6484815487179179/5340000000000000000000000000000 : ℝ)*base72 + (112825352003/53400000000000000000000000 : ℝ)*base74 + (47723355086180821/5340000000000000000000000000000 : ℝ)*base75 + (53164466832740821/5340000000000000000000000000000 : ℝ)*base77 + (172791993046520821/5340000000000000000000000000000 : ℝ)*base79 + (204071812799/16687500000000000000000000 : ℝ)*base81 + (6160589/1250000000000000000000 : ℝ)*base90 + (6160589/1250000000000000000000 : ℝ)*base92 + (6160589/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1180_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1180_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1180_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1180_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1180_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1180_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2093/512 : ℝ) ≤ p) (hpb : p ≤ (8373/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150215673/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1180_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

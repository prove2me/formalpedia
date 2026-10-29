-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1737_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:05.93898+00:00
-- url     : https://prove2.me/submissions/bb1b7ca7-589d-4d61-b68c-7065c34bbc41

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
theorem support_rectangle_w1737_s3_0 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-649353739/5000000000 : ℝ)*x 0 + (5515209377/10000000000 : ℝ)*x 1 + (5076692829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649353739/5000000000 : ℝ)^5567 ≤ (2049440357991/25000000000000 : ℝ)^4543 := by
    have hnat : (649353739 : ℕ)^5567*25000000000000^4543 ≤ 2049440357991^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649353739 5000000000 2049440357991 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515209377/10000000000 : ℝ)^5567 ≤ (9645830636149/20000000000000 : ℝ)^4543 := by
    have hnat : (5515209377 : ℕ)^5567*20000000000000^4543 ≤ 9645830636149^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515209377 10000000000 9645830636149 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076692829/10000000000 : ℝ)^5567 ≤ (21786542688981/50000000000000 : ℝ)^4543 := by
    have hnat : (5076692829 : ℕ)^5567*50000000000000^4543 ≤ 21786542688981^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076692829 10000000000 21786542688981 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-649353739/5000000000 : ℝ), (5515209377/10000000000 : ℝ), (5076692829/10000000000 : ℝ)] ![(2049440357991/25000000000000 : ℝ), (9645830636149/20000000000000 : ℝ), (21786542688981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-649353739/5000000000 : ℝ)|^5567 ≤ (2049440357991/25000000000000 : ℝ)^4543
        have hw : |(-649353739/5000000000 : ℝ)|=(649353739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515209377/10000000000 : ℝ)|^5567 ≤ (9645830636149/20000000000000 : ℝ)^4543
        have hw : |(5515209377/10000000000 : ℝ)|=(5515209377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076692829/10000000000 : ℝ)|^5567 ≤ (21786542688981/50000000000000 : ℝ)^4543
        have hw : |(5076692829/10000000000 : ℝ)|=(5076692829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_1 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672729993/5000000000 : ℝ)*x 0 + (-1528656479/10000000000 : ℝ)*x 1 + (5076692427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672729993/5000000000 : ℝ)^5567 ≤ (46416506827863/100000000000000 : ℝ)^4543 := by
    have hnat : (2672729993 : ℕ)^5567*100000000000000^4543 ≤ 46416506827863^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672729993 5000000000 46416506827863 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528656479/10000000000 : ℝ)^5567 ≤ (5005206005309/50000000000000 : ℝ)^4543 := by
    have hnat : (1528656479 : ℕ)^5567*50000000000000^4543 ≤ 5005206005309^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528656479 10000000000 5005206005309 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076692427/10000000000 : ℝ)^5567 ≤ (21786540574947/50000000000000 : ℝ)^4543 := by
    have hnat : (5076692427 : ℕ)^5567*50000000000000^4543 ≤ 21786540574947^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076692427 10000000000 21786540574947 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672729993/5000000000 : ℝ), (-1528656479/10000000000 : ℝ), (5076692427/10000000000 : ℝ)] ![(46416506827863/100000000000000 : ℝ), (5005206005309/50000000000000 : ℝ), (21786540574947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672729993/5000000000 : ℝ)|^5567 ≤ (46416506827863/100000000000000 : ℝ)^4543
        have hw : |(2672729993/5000000000 : ℝ)|=(2672729993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1528656479/10000000000 : ℝ)|^5567 ≤ (5005206005309/50000000000000 : ℝ)^4543
        have hw : |(-1528656479/10000000000 : ℝ)|=(1528656479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076692427/10000000000 : ℝ)|^5567 ≤ (21786540574947/50000000000000 : ℝ)^4543
        have hw : |(5076692427/10000000000 : ℝ)|=(5076692427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_2 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668182509/1250000000 : ℝ)*x 0 + (1269173137/2500000000 : ℝ)*x 1 + (-764328103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668182509/1250000000 : ℝ)^5567 ≤ (23208253871477/50000000000000 : ℝ)^4543 := by
    have hnat : (668182509 : ℕ)^5567*50000000000000^4543 ≤ 23208253871477^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668182509 1250000000 23208253871477 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269173137/2500000000 : ℝ)^5567 ≤ (43573082422521/100000000000000 : ℝ)^4543 := by
    have hnat : (1269173137 : ℕ)^5567*100000000000000^4543 ≤ 43573082422521^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269173137 2500000000 43573082422521 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764328103/5000000000 : ℝ)^5567 ≤ (10010409819917/100000000000000 : ℝ)^4543 := by
    have hnat : (764328103 : ℕ)^5567*100000000000000^4543 ≤ 10010409819917^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764328103 5000000000 10010409819917 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668182509/1250000000 : ℝ), (1269173137/2500000000 : ℝ), (-764328103/5000000000 : ℝ)] ![(23208253871477/50000000000000 : ℝ), (43573082422521/100000000000000 : ℝ), (10010409819917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668182509/1250000000 : ℝ)|^5567 ≤ (23208253871477/50000000000000 : ℝ)^4543
        have hw : |(668182509/1250000000 : ℝ)|=(668182509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269173137/2500000000 : ℝ)|^5567 ≤ (43573082422521/100000000000000 : ℝ)^4543
        have hw : |(1269173137/2500000000 : ℝ)|=(1269173137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764328103/5000000000 : ℝ)|^5567 ≤ (10010409819917/100000000000000 : ℝ)^4543
        have hw : |(-764328103/5000000000 : ℝ)|=(764328103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_3 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1012259411/2500000000 : ℝ)*x 0 + (3400028117/10000000000 : ℝ)*x 1 + (19058309/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012259411/2500000000 : ℝ)^5567 ≤ (3302541162049/10000000000000 : ℝ)^4543 := by
    have hnat : (1012259411 : ℕ)^5567*10000000000000^4543 ≤ 3302541162049^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012259411 2500000000 3302541162049 10000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3400028117/10000000000 : ℝ)^5567 ≤ (26661087580217/100000000000000 : ℝ)^4543 := by
    have hnat : (3400028117 : ℕ)^5567*100000000000000^4543 ≤ 26661087580217^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3400028117 10000000000 26661087580217 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19058309/40000000 : ℝ)^5567 ≤ (40313500788489/100000000000000 : ℝ)^4543 := by
    have hnat : (19058309 : ℕ)^5567*100000000000000^4543 ≤ 40313500788489^4543*40000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19058309 40000000 40313500788489 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1012259411/2500000000 : ℝ), (3400028117/10000000000 : ℝ), (19058309/40000000 : ℝ)] ![(3302541162049/10000000000000 : ℝ), (26661087580217/100000000000000 : ℝ), (40313500788489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1012259411/2500000000 : ℝ)|^5567 ≤ (3302541162049/10000000000000 : ℝ)^4543
        have hw : |(1012259411/2500000000 : ℝ)|=(1012259411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3400028117/10000000000 : ℝ)|^5567 ≤ (26661087580217/100000000000000 : ℝ)^4543
        have hw : |(3400028117/10000000000 : ℝ)|=(3400028117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19058309/40000000 : ℝ)|^5567 ≤ (40313500788489/100000000000000 : ℝ)^4543
        have hw : |(19058309/40000000 : ℝ)|=(19058309/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_4 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-649543787/5000000000 : ℝ)*x 0 + (508367333/1000000000 : ℝ)*x 1 + (1377020387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649543787/5000000000 : ℝ)^5567 ≤ (4100350792857/50000000000000 : ℝ)^4543 := by
    have hnat : (649543787 : ℕ)^5567*50000000000000^4543 ≤ 4100350792857^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649543787 5000000000 4100350792857 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508367333/1000000000 : ℝ)^5567 ≤ (8729302948701/20000000000000 : ℝ)^4543 := by
    have hnat : (508367333 : ℕ)^5567*20000000000000^4543 ≤ 8729302948701^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508367333 1000000000 8729302948701 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377020387/2500000000 : ℝ)^5567 ≤ (48152783652769/100000000000000 : ℝ)^4543 := by
    have hnat : (1377020387 : ℕ)^5567*100000000000000^4543 ≤ 48152783652769^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377020387 2500000000 48152783652769 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-649543787/5000000000 : ℝ), (508367333/1000000000 : ℝ), (1377020387/2500000000 : ℝ)] ![(4100350792857/50000000000000 : ℝ), (8729302948701/20000000000000 : ℝ), (48152783652769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-649543787/5000000000 : ℝ)|^5567 ≤ (4100350792857/50000000000000 : ℝ)^4543
        have hw : |(-649543787/5000000000 : ℝ)|=(649543787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508367333/1000000000 : ℝ)|^5567 ≤ (8729302948701/20000000000000 : ℝ)^4543
        have hw : |(508367333/1000000000 : ℝ)|=(508367333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377020387/2500000000 : ℝ)|^5567 ≤ (48152783652769/100000000000000 : ℝ)^4543
        have hw : |(1377020387/2500000000 : ℝ)|=(1377020387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_5 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045777887/2000000000 : ℝ)*x 0 + (-219453421/2000000000 : ℝ)*x 1 + (1377020389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045777887/2000000000 : ℝ)^5567 ≤ (2823699550121/6250000000000 : ℝ)^4543 := by
    have hnat : (1045777887 : ℕ)^5567*6250000000000^4543 ≤ 2823699550121^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045777887 2000000000 2823699550121 6250000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219453421/2000000000 : ℝ)^5567 ≤ (3334011719979/50000000000000 : ℝ)^4543 := by
    have hnat : (219453421 : ℕ)^5567*50000000000000^4543 ≤ 3334011719979^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219453421 2000000000 3334011719979 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377020389/2500000000 : ℝ)^5567 ≤ (48152783738471/100000000000000 : ℝ)^4543 := by
    have hnat : (1377020389 : ℕ)^5567*100000000000000^4543 ≤ 48152783738471^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377020389 2500000000 48152783738471 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045777887/2000000000 : ℝ), (-219453421/2000000000 : ℝ), (1377020389/2500000000 : ℝ)] ![(2823699550121/6250000000000 : ℝ), (3334011719979/50000000000000 : ℝ), (48152783738471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045777887/2000000000 : ℝ)|^5567 ≤ (2823699550121/6250000000000 : ℝ)^4543
        have hw : |(1045777887/2000000000 : ℝ)|=(1045777887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219453421/2000000000 : ℝ)|^5567 ≤ (3334011719979/50000000000000 : ℝ)^4543
        have hw : |(-219453421/2000000000 : ℝ)|=(219453421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377020389/2500000000 : ℝ)|^5567 ≤ (48152783738471/100000000000000 : ℝ)^4543
        have hw : |(1377020389/2500000000 : ℝ)|=(1377020389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_6 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653611179/1250000000 : ℝ)*x 0 + (5508081553/10000000000 : ℝ)*x 1 + (-548633557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653611179/1250000000 : ℝ)^5567 ≤ (45179192770173/100000000000000 : ℝ)^4543 := by
    have hnat : (653611179 : ℕ)^5567*100000000000000^4543 ≤ 45179192770173^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653611179 1250000000 45179192770173 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508081553/10000000000 : ℝ)^5567 ≤ (12038195926583/25000000000000 : ℝ)^4543 := by
    have hnat : (5508081553 : ℕ)^5567*25000000000000^4543 ≤ 12038195926583^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508081553 10000000000 12038195926583 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548633557/5000000000 : ℝ)^5567 ≤ (3334011753489/50000000000000 : ℝ)^4543 := by
    have hnat : (548633557 : ℕ)^5567*50000000000000^4543 ≤ 3334011753489^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548633557 5000000000 3334011753489 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653611179/1250000000 : ℝ), (5508081553/10000000000 : ℝ), (-548633557/5000000000 : ℝ)] ![(45179192770173/100000000000000 : ℝ), (12038195926583/25000000000000 : ℝ), (3334011753489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653611179/1250000000 : ℝ)|^5567 ≤ (45179192770173/100000000000000 : ℝ)^4543
        have hw : |(653611179/1250000000 : ℝ)|=(653611179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508081553/10000000000 : ℝ)|^5567 ≤ (12038195926583/25000000000000 : ℝ)^4543
        have hw : |(5508081553/10000000000 : ℝ)|=(5508081553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548633557/5000000000 : ℝ)|^5567 ≤ (3334011753489/50000000000000 : ℝ)^4543
        have hw : |(-548633557/5000000000 : ℝ)|=(548633557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s3_7 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31642347/78125000 : ℝ)*x 0 + (2371427613/5000000000 : ℝ)*x 1 + (3422208033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31642347/78125000 : ℝ)^5567 ≤ (8259308400259/25000000000000 : ℝ)^4543 := by
    have hnat : (31642347 : ℕ)^5567*25000000000000^4543 ≤ 8259308400259^4543*78125000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31642347 78125000 8259308400259 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2371427613/5000000000 : ℝ)^5567 ≤ (40088397702617/100000000000000 : ℝ)^4543 := by
    have hnat : (2371427613 : ℕ)^5567*100000000000000^4543 ≤ 40088397702617^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371427613 5000000000 40088397702617 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3422208033/10000000000 : ℝ)^5567 ≤ (13437184340619/50000000000000 : ℝ)^4543 := by
    have hnat : (3422208033 : ℕ)^5567*50000000000000^4543 ≤ 13437184340619^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422208033 10000000000 13437184340619 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31642347/78125000 : ℝ), (2371427613/5000000000 : ℝ), (3422208033/10000000000 : ℝ)] ![(8259308400259/25000000000000 : ℝ), (40088397702617/100000000000000 : ℝ), (13437184340619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31642347/78125000 : ℝ)|^5567 ≤ (8259308400259/25000000000000 : ℝ)^4543
        have hw : |(31642347/78125000 : ℝ)|=(31642347/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2371427613/5000000000 : ℝ)|^5567 ≤ (40088397702617/100000000000000 : ℝ)^4543
        have hw : |(2371427613/5000000000 : ℝ)|=(2371427613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3422208033/10000000000 : ℝ)|^5567 ≤ (13437184340619/50000000000000 : ℝ)^4543
        have hw : |(3422208033/10000000000 : ℝ)|=(3422208033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1737_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2213/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18231/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8849/100000 : ℝ) ^ (5551/1024 : ℝ) ≤ (97766572969611/50000000000000000000 : ℝ) := by
    have hpowers : (8849/100000 : ℝ)^5551 ≤ (97766572969611/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8849 : ℕ)^5551*50000000000000000000^1024 ≤ 97766572969611^1024*100000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8849 100000 97766572969611 50000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8849/100000 : ℝ)) (X := (97766572969611/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9117/50000 : ℝ) ^ (5551/1024 : ℝ) ≤ (4923638109063163/50000000000000000000 : ℝ) := by
    have hpowers : (9117/50000 : ℝ)^5551 ≤ (4923638109063163/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9117 : ℕ)^5551*50000000000000000000^1024 ≤ 4923638109063163^1024*50000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9117 50000 4923638109063163 50000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9117/50000 : ℝ)) (X := (4923638109063163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000097766572969611/25000000000000000000 : ℝ) ≤ (10000007214037909/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25000097766572969611/25000000000000000000 : ℝ)^1024 ≤ (10000007214037909/10000000000000000 : ℝ)^5551 := by
      have hnat : (25000097766572969611 : ℕ)^1024*10000000000000000^5551 ≤ 10000007214037909^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000097766572969611 25000000000000000000 10000007214037909 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007214037909/10000000000000000 : ℝ)) (X := (25000097766572969611/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002510702341016387/25000000000000000000 : ℝ) ≤ (10000185253390039/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25002510702341016387/25000000000000000000 : ℝ)^1024 ≤ (10000185253390039/10000000000000000 : ℝ)^5551 := by
      have hnat : (25002510702341016387 : ℕ)^1024*10000000000000000^5551 ≤ 10000185253390039^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002510702341016387 25000000000000000000 10000185253390039 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000185253390039/10000000000000000 : ℝ)) (X := (25002510702341016387/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004923638109063163/25000000000000000000 : ℝ) ≤ (10000363292742169/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25004923638109063163/25000000000000000000 : ℝ)^1024 ≤ (10000363292742169/10000000000000000 : ℝ)^5551 := by
      have hnat : (25004923638109063163 : ℕ)^1024*10000000000000000^5551 ≤ 10000363292742169^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004923638109063163 25000000000000000000 10000363292742169 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000363292742169/10000000000000000 : ℝ)) (X := (25004923638109063163/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(97766572969611/50000000000000000000 : ℝ) ≤ ((3753876670531671169/3754000000000000000 : ℝ)+2*(17803935213/93850000000000 : ℝ)*(8849/100000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (3753876670531671169/3754000000000000000 : ℝ)+2*(17803935213/93850000000000 : ℝ)*(8849/100000 : ℝ)=(10000007214037909/10000000000000000 : ℝ) by norm_num, show 1+2*(97766572969611/50000000000000000000 : ℝ)=(25000097766572969611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4923638109063163/50000000000000000000 : ℝ)+(97766572969611/50000000000000000000 : ℝ) ≤ ((3753876670531671169/3754000000000000000 : ℝ)+(17803935213/93850000000000 : ℝ)*((9117/50000 : ℝ)+(8849/100000 : ℝ)))^(5551/1024 : ℝ) := by
    rw [show (3753876670531671169/3754000000000000000 : ℝ)+(17803935213/93850000000000 : ℝ)*((9117/50000 : ℝ)+(8849/100000 : ℝ))=(10000185253390039/10000000000000000 : ℝ) by norm_num, show 1+(4923638109063163/50000000000000000000 : ℝ)+(97766572969611/50000000000000000000 : ℝ)=(25002510702341016387/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4923638109063163/50000000000000000000 : ℝ) ≤ ((3753876670531671169/3754000000000000000 : ℝ)+2*(17803935213/93850000000000 : ℝ)*(9117/50000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (3753876670531671169/3754000000000000000 : ℝ)+2*(17803935213/93850000000000 : ℝ)*(9117/50000 : ℝ)=(10000363292742169/10000000000000000 : ℝ) by norm_num, show 1+2*(4923638109063163/50000000000000000000 : ℝ)=(25004923638109063163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3753876670531671169/3754000000000000000 : ℝ)*(X 1 0+X 2 0)+(17803935213/93850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (9117/50000 : ℝ)) (c := (3753876670531671169/3754000000000000000 : ℝ)) (alpha := (17803935213/93850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3753876670531671169/3754000000000000000 : ℝ)*(X 0 1+X 2 1)+(17803935213/93850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (9117/50000 : ℝ)) (c := (3753876670531671169/3754000000000000000 : ℝ)) (alpha := (17803935213/93850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3753876670531671169/3754000000000000000 : ℝ)*(X 0 2+X 1 2)+(17803935213/93850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (9117/50000 : ℝ)) (c := (3753876670531671169/3754000000000000000 : ℝ)) (alpha := (17803935213/93850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-649353739/5000000000 : ℝ)*X 0 0+(5515209377/10000000000 : ℝ)*X 0 1+(5076692829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672729993/5000000000 : ℝ)*X 1 0+(-1528656479/10000000000 : ℝ)*X 1 1+(5076692427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668182509/1250000000 : ℝ)*X 2 0+(1269173137/2500000000 : ℝ)*X 2 1+(-764328103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1012259411/2500000000 : ℝ)*X 0 0+(3400028117/10000000000 : ℝ)*X 0 1+(19058309/40000000 : ℝ)*X 0 2+(1012259411/2500000000 : ℝ)*X 1 0+(3400028117/10000000000 : ℝ)*X 1 1+(19058309/40000000 : ℝ)*X 1 2+(1012259411/2500000000 : ℝ)*X 2 0+(3400028117/10000000000 : ℝ)*X 2 1+(19058309/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-649543787/5000000000 : ℝ)*X 0 0+(508367333/1000000000 : ℝ)*X 0 1+(1377020387/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1045777887/2000000000 : ℝ)*X 1 0+(-219453421/2000000000 : ℝ)*X 1 1+(1377020389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653611179/1250000000 : ℝ)*X 2 0+(5508081553/10000000000 : ℝ)*X 2 1+(-548633557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((31642347/78125000 : ℝ)*X 0 0+(2371427613/5000000000 : ℝ)*X 0 1+(3422208033/10000000000 : ℝ)*X 0 2+(31642347/78125000 : ℝ)*X 1 0+(2371427613/5000000000 : ℝ)*X 1 1+(3422208033/10000000000 : ℝ)*X 1 2+(31642347/78125000 : ℝ)*X 2 0+(2371427613/5000000000 : ℝ)*X 2 1+(3422208033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425183994103359269502008301/93850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214499919/50000000000000 : ℝ)*(base19) + (107877049/25000000000000 : ℝ)*(base23) + (18270763/100000000000000 : ℝ)*(lower2) + (14744161/100000000000000 : ℝ)*(upper3) + (128585653/100000000000000 : ℝ)*(upper5) + (1506631339922543/100000000000000 : ℝ)*(major0) + (1506631339922543/100000000000000 : ℝ)*(major1) + (1506631339922543/100000000000000 : ℝ)*(major2) + (2280416065020147/100000000000000 : ℝ)*(sp0) + (1140209032608809/50000000000000 : ℝ)*(sp1) + (114020903135463/5000000000000 : ℝ)*(sp2) + (732843595155337/100000000000000 : ℝ)*(sp3) + (2429197309/100000000000000 : ℝ)*(sp4) + (439456841/100000000000000 : ℝ)*(sp7) + (366422017306089/50000000000000 : ℝ)*(f.failure) + (142526155888591/6250000000000 : ℝ)*(f.sum) + (4002280279149/4692500000000000000000000000 : ℝ)*base65 + (1668981347980977233/375400000000000000000000000000000 : ℝ)*base68 + (2634160393056577233/375400000000000000000000000000000 : ℝ)*base70 + (1698715411020177233/375400000000000000000000000000000 : ℝ)*base72 + (15987161665787/9385000000000000000000000000 : ℝ)*base74 + (655094898342022767/375400000000000000000000000000000 : ℝ)*base75 + (224682298868977233/375400000000000000000000000000000 : ℝ)*base78 + (705407289942377233/375400000000000000000000000000000 : ℝ)*base80 + (48087193059237/9385000000000000000000000000 : ℝ)*base82 + (55940189/5000000000000000000000 : ℝ)*base89 + (55940189/5000000000000000000000 : ℝ)*base91 + (55940189/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60118846579717827811689/9385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214557031/25000000000000 : ℝ)*(base19) + (458849703/50000000000000 : ℝ)*(base23) + (49590367/20000000000000 : ℝ)*(lower1) + (13944221/10000000000000 : ℝ)*(upper3) + (13682851/50000000000000 : ℝ)*(lower4) + (2085973/1562500000000 : ℝ)*(upper5) + (778354657610469/50000000000000 : ℝ)*(major0) + (778354657610469/50000000000000 : ℝ)*(major1) + (778354657610469/50000000000000 : ℝ)*(major2) + (76143347/20000000000000 : ℝ)*(sp2) + (294526979814443/12500000000000 : ℝ)*(sp4) + (117810749014371/5000000000000 : ℝ)*(sp5) + (2356214540099403/100000000000000 : ℝ)*(sp6) + (47325161149887/6250000000000 : ℝ)*(sp7) + (47325161149887/6250000000000 : ℝ)*(f.failure) + (294526979814443/12500000000000 : ℝ)*(f.sum) + (1353316788357/2346250000000000000000000000 : ℝ)*base65 + (429545004986651739/187700000000000000000000000000000 : ℝ)*base68 + (369631753906148261/187700000000000000000000000000000 : ℝ)*base69 + (1717104315731348261/187700000000000000000000000000000 : ℝ)*base71 + (828284138763/146640625000000000000000000 : ℝ)*base74 + (2645439033775451739/187700000000000000000000000000000 : ℝ)*base76 + (264915019781851739/187700000000000000000000000000000 : ℝ)*base78 + (677741945277048261/187700000000000000000000000000000 : ℝ)*base79 + (3448749257563/2346250000000000000000000000 : ℝ)*base82 + (2330187/625000000000000000000 : ℝ)*base89 + (2330187/625000000000000000000 : ℝ)*base91 + (2330187/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1737_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18231/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1737_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1737_box_0 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2778819/31250000 : ℝ)*x 0 + (1359969761/2500000000 : ℝ)*x 1 + (5439879027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2778819/31250000 : ℝ)^5567 ≤ (2576827493219/50000000000000 : ℝ)^4543 := by
    have hnat : (2778819 : ℕ)^5567*50000000000000^4543 ≤ 2576827493219^4543*31250000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778819 31250000 2576827493219 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359969761/2500000000 : ℝ)^5567 ≤ (47423172586557/100000000000000 : ℝ)^4543 := by
    have hnat : (1359969761 : ℕ)^5567*100000000000000^4543 ≤ 47423172586557^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359969761 2500000000 47423172586557 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439879027/10000000000 : ℝ)^5567 ≤ (47423172404951/100000000000000 : ℝ)^4543 := by
    have hnat : (5439879027 : ℕ)^5567*100000000000000^4543 ≤ 47423172404951^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439879027 10000000000 47423172404951 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2778819/31250000 : ℝ), (1359969761/2500000000 : ℝ), (5439879027/10000000000 : ℝ)] ![(2576827493219/50000000000000 : ℝ), (47423172586557/100000000000000 : ℝ), (47423172404951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2778819/31250000 : ℝ)|^5567 ≤ (2576827493219/50000000000000 : ℝ)^4543
        have hw : |(-2778819/31250000 : ℝ)|=(2778819/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359969761/2500000000 : ℝ)|^5567 ≤ (47423172586557/100000000000000 : ℝ)^4543
        have hw : |(1359969761/2500000000 : ℝ)|=(1359969761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439879027/10000000000 : ℝ)|^5567 ≤ (47423172404951/100000000000000 : ℝ)^4543
        have hw : |(5439879027/10000000000 : ℝ)|=(5439879027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_1 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597653407/5000000000 : ℝ)*x 0 + (-310226853/2500000000 : ℝ)*x 1 + (5439879021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597653407/5000000000 : ℝ)^5567 ≤ (5602985384879/12500000000000 : ℝ)^4543 := by
    have hnat : (2597653407 : ℕ)^5567*12500000000000^4543 ≤ 5602985384879^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597653407 5000000000 5602985384879 12500000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310226853/2500000000 : ℝ)^5567 ≤ (7752944563183/100000000000000 : ℝ)^4543 := by
    have hnat : (310226853 : ℕ)^5567*100000000000000^4543 ≤ 7752944563183^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310226853 2500000000 7752944563183 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439879021/10000000000 : ℝ)^5567 ≤ (9484634468171/20000000000000 : ℝ)^4543 := by
    have hnat : (5439879021 : ℕ)^5567*20000000000000^4543 ≤ 9484634468171^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439879021 10000000000 9484634468171 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597653407/5000000000 : ℝ), (-310226853/2500000000 : ℝ), (5439879021/10000000000 : ℝ)] ![(5602985384879/12500000000000 : ℝ), (7752944563183/100000000000000 : ℝ), (9484634468171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597653407/5000000000 : ℝ)|^5567 ≤ (5602985384879/12500000000000 : ℝ)^4543
        have hw : |(2597653407/5000000000 : ℝ)|=(2597653407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310226853/2500000000 : ℝ)|^5567 ≤ (7752944563183/100000000000000 : ℝ)^4543
        have hw : |(-310226853/2500000000 : ℝ)|=(310226853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439879021/10000000000 : ℝ)|^5567 ≤ (9484634468171/20000000000000 : ℝ)^4543
        have hw : |(5439879021/10000000000 : ℝ)|=(5439879021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_2 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039061353/2000000000 : ℝ)*x 0 + (5439879047/10000000000 : ℝ)*x 1 + (-310226861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039061353/2000000000 : ℝ)^5567 ≤ (44823882560981/100000000000000 : ℝ)^4543 := by
    have hnat : (1039061353 : ℕ)^5567*100000000000000^4543 ≤ 44823882560981^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039061353 2000000000 44823882560981 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439879047/10000000000 : ℝ)^5567 ≤ (9484634523721/20000000000000 : ℝ)^4543 := by
    have hnat : (5439879047 : ℕ)^5567*20000000000000^4543 ≤ 9484634523721^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439879047 10000000000 9484634523721 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310226861/2500000000 : ℝ)^5567 ≤ (7752944808177/100000000000000 : ℝ)^4543 := by
    have hnat : (310226861 : ℕ)^5567*100000000000000^4543 ≤ 7752944808177^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310226861 2500000000 7752944808177 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039061353/2000000000 : ℝ), (5439879047/10000000000 : ℝ), (-310226861/2500000000 : ℝ)] ![(44823882560981/100000000000000 : ℝ), (9484634523721/20000000000000 : ℝ), (7752944808177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039061353/2000000000 : ℝ)|^5567 ≤ (44823882560981/100000000000000 : ℝ)^4543
        have hw : |(1039061353/2000000000 : ℝ)|=(1039061353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439879047/10000000000 : ℝ)|^5567 ≤ (9484634523721/20000000000000 : ℝ)^4543
        have hw : |(5439879047/10000000000 : ℝ)|=(5439879047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310226861/2500000000 : ℝ)|^5567 ≤ (7752944808177/100000000000000 : ℝ)^4543
        have hw : |(-310226861/2500000000 : ℝ)|=(310226861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_3 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2289013221/5000000000 : ℝ)*x 0 + (765115013/2000000000 : ℝ)*x 1 + (1912787587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2289013221/5000000000 : ℝ)^5567 ≤ (38387921873791/100000000000000 : ℝ)^4543 := by
    have hnat : (2289013221 : ℕ)^5567*100000000000000^4543 ≤ 38387921873791^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289013221 5000000000 38387921873791 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765115013/2000000000 : ℝ)^5567 ≤ (3080603851717/10000000000000 : ℝ)^4543 := by
    have hnat : (765115013 : ℕ)^5567*10000000000000^4543 ≤ 3080603851717^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765115013 2000000000 3080603851717 10000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912787587/5000000000 : ℝ)^5567 ≤ (30806039592753/100000000000000 : ℝ)^4543 := by
    have hnat : (1912787587 : ℕ)^5567*100000000000000^4543 ≤ 30806039592753^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912787587 5000000000 30806039592753 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2289013221/5000000000 : ℝ), (765115013/2000000000 : ℝ), (1912787587/5000000000 : ℝ)] ![(38387921873791/100000000000000 : ℝ), (3080603851717/10000000000000 : ℝ), (30806039592753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2289013221/5000000000 : ℝ)|^5567 ≤ (38387921873791/100000000000000 : ℝ)^4543
        have hw : |(2289013221/5000000000 : ℝ)|=(2289013221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(765115013/2000000000 : ℝ)|^5567 ≤ (3080603851717/10000000000000 : ℝ)^4543
        have hw : |(765115013/2000000000 : ℝ)|=(765115013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1912787587/5000000000 : ℝ)|^5567 ≤ (30806039592753/100000000000000 : ℝ)^4543
        have hw : |(1912787587/5000000000 : ℝ)|=(1912787587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_4 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437212973/2500000000 : ℝ)*x 0 + (512649563/1000000000 : ℝ)*x 1 + (2563247911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437212973/2500000000 : ℝ)^5567 ≤ (2951265445399/25000000000000 : ℝ)^4543 := by
    have hnat : (437212973 : ℕ)^5567*25000000000000^4543 ≤ 2951265445399^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437212973 2500000000 2951265445399 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512649563/1000000000 : ℝ)^5567 ≤ (44097468087461/100000000000000 : ℝ)^4543 := by
    have hnat : (512649563 : ℕ)^5567*100000000000000^4543 ≤ 44097468087461^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512649563 1000000000 44097468087461 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563247911/5000000000 : ℝ)^5567 ≤ (8819494022257/20000000000000 : ℝ)^4543 := by
    have hnat : (2563247911 : ℕ)^5567*20000000000000^4543 ≤ 8819494022257^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563247911 5000000000 8819494022257 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437212973/2500000000 : ℝ), (512649563/1000000000 : ℝ), (2563247911/5000000000 : ℝ)] ![(2951265445399/25000000000000 : ℝ), (44097468087461/100000000000000 : ℝ), (8819494022257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437212973/2500000000 : ℝ)|^5567 ≤ (2951265445399/25000000000000 : ℝ)^4543
        have hw : |(-437212973/2500000000 : ℝ)|=(437212973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512649563/1000000000 : ℝ)|^5567 ≤ (44097468087461/100000000000000 : ℝ)^4543
        have hw : |(512649563/1000000000 : ℝ)|=(512649563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2563247911/5000000000 : ℝ)|^5567 ≤ (8819494022257/20000000000000 : ℝ)^4543
        have hw : |(2563247911/5000000000 : ℝ)|=(2563247911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_5 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406280977/10000000000 : ℝ)*x 0 + (-345226549/2500000000 : ℝ)*x 1 + (5126494811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406280977/10000000000 : ℝ)^5567 ≤ (47064505727269/100000000000000 : ℝ)^4543 := by
    have hnat : (5406280977 : ℕ)^5567*100000000000000^4543 ≤ 47064505727269^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406280977 10000000000 47064505727269 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345226549/2500000000 : ℝ)^5567 ≤ (2209508702471/25000000000000 : ℝ)^4543 := by
    have hnat : (345226549 : ℕ)^5567*25000000000000^4543 ≤ 2209508702471^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345226549 2500000000 2209508702471 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126494811/10000000000 : ℝ)^5567 ≤ (22048729727293/50000000000000 : ℝ)^4543 := by
    have hnat : (5126494811 : ℕ)^5567*50000000000000^4543 ≤ 22048729727293^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126494811 10000000000 22048729727293 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406280977/10000000000 : ℝ), (-345226549/2500000000 : ℝ), (5126494811/10000000000 : ℝ)] ![(47064505727269/100000000000000 : ℝ), (2209508702471/25000000000000 : ℝ), (22048729727293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406280977/10000000000 : ℝ)|^5567 ≤ (47064505727269/100000000000000 : ℝ)^4543
        have hw : |(5406280977/10000000000 : ℝ)|=(5406280977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345226549/2500000000 : ℝ)|^5567 ≤ (2209508702471/25000000000000 : ℝ)^4543
        have hw : |(-345226549/2500000000 : ℝ)|=(345226549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126494811/10000000000 : ℝ)|^5567 ≤ (22048729727293/50000000000000 : ℝ)^4543
        have hw : |(5126494811/10000000000 : ℝ)|=(5126494811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_6 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168946263/312500000 : ℝ)*x 0 + (5126494981/10000000000 : ℝ)*x 1 + (-138090673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168946263/312500000 : ℝ)^5567 ≤ (23532249871327/50000000000000 : ℝ)^4543 := by
    have hnat : (168946263 : ℕ)^5567*50000000000000^4543 ≤ 23532249871327^4543*312500000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168946263 312500000 23532249871327 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126494981/10000000000 : ℝ)^5567 ≤ (22048730623257/50000000000000 : ℝ)^4543 := by
    have hnat : (5126494981 : ℕ)^5567*50000000000000^4543 ≤ 22048730623257^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126494981 10000000000 22048730623257 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138090673/1000000000 : ℝ)^5567 ≤ (1104754874741/12500000000000 : ℝ)^4543 := by
    have hnat : (138090673 : ℕ)^5567*12500000000000^4543 ≤ 1104754874741^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138090673 1000000000 1104754874741 12500000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168946263/312500000 : ℝ), (5126494981/10000000000 : ℝ), (-138090673/1000000000 : ℝ)] ![(23532249871327/50000000000000 : ℝ), (22048730623257/50000000000000 : ℝ), (1104754874741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168946263/312500000 : ℝ)|^5567 ≤ (23532249871327/50000000000000 : ℝ)^4543
        have hw : |(168946263/312500000 : ℝ)|=(168946263/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126494981/10000000000 : ℝ)|^5567 ≤ (22048730623257/50000000000000 : ℝ)^4543
        have hw : |(5126494981/10000000000 : ℝ)|=(5126494981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138090673/1000000000 : ℝ)|^5567 ≤ (1104754874741/12500000000000 : ℝ)^4543
        have hw : |(-138090673/1000000000 : ℝ)|=(138090673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_7 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1742888689/5000000000 : ℝ)*x 0 + (4369493963/10000000000 : ℝ)*x 1 + (873898629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742888689/5000000000 : ℝ)^5567 ≤ (13743685421029/50000000000000 : ℝ)^4543 := by
    have hnat : (1742888689 : ℕ)^5567*50000000000000^4543 ≤ 13743685421029^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742888689 5000000000 13743685421029 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4369493963/10000000000 : ℝ)^5567 ≤ (18128159364423/50000000000000 : ℝ)^4543 := by
    have hnat : (4369493963 : ℕ)^5567*50000000000000^4543 ≤ 18128159364423^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369493963 10000000000 18128159364423 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873898629/2000000000 : ℝ)^5567 ≤ (9064077602877/25000000000000 : ℝ)^4543 := by
    have hnat : (873898629 : ℕ)^5567*25000000000000^4543 ≤ 9064077602877^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873898629 2000000000 9064077602877 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1742888689/5000000000 : ℝ), (4369493963/10000000000 : ℝ), (873898629/2000000000 : ℝ)] ![(13743685421029/50000000000000 : ℝ), (18128159364423/50000000000000 : ℝ), (9064077602877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1742888689/5000000000 : ℝ)|^5567 ≤ (13743685421029/50000000000000 : ℝ)^4543
        have hw : |(1742888689/5000000000 : ℝ)|=(1742888689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4369493963/10000000000 : ℝ)|^5567 ≤ (18128159364423/50000000000000 : ℝ)^4543
        have hw : |(4369493963/10000000000 : ℝ)|=(4369493963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873898629/2000000000 : ℝ)|^5567 ≤ (9064077602877/25000000000000 : ℝ)^4543
        have hw : |(873898629/2000000000 : ℝ)|=(873898629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_8 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390590737/2500000000 : ℝ)*x 0 + (4889335023/10000000000 : ℝ)*x 1 + (1375966573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390590737/2500000000 : ℝ)^5567 ≤ (10281559519449/100000000000000 : ℝ)^4543 := by
    have hnat : (390590737 : ℕ)^5567*100000000000000^4543 ≤ 10281559519449^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390590737 2500000000 10281559519449 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4889335023/10000000000 : ℝ)^5567 ≤ (41610809749973/100000000000000 : ℝ)^4543 := by
    have hnat : (4889335023 : ℕ)^5567*100000000000000^4543 ≤ 41610809749973^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889335023 10000000000 41610809749973 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375966573/2500000000 : ℝ)^5567 ≤ (24053815357583/50000000000000 : ℝ)^4543 := by
    have hnat : (1375966573 : ℕ)^5567*50000000000000^4543 ≤ 24053815357583^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375966573 2500000000 24053815357583 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390590737/2500000000 : ℝ), (4889335023/10000000000 : ℝ), (1375966573/2500000000 : ℝ)] ![(10281559519449/100000000000000 : ℝ), (41610809749973/100000000000000 : ℝ), (24053815357583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390590737/2500000000 : ℝ)|^5567 ≤ (10281559519449/100000000000000 : ℝ)^4543
        have hw : |(-390590737/2500000000 : ℝ)|=(390590737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4889335023/10000000000 : ℝ)|^5567 ≤ (41610809749973/100000000000000 : ℝ)^4543
        have hw : |(4889335023/10000000000 : ℝ)|=(4889335023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375966573/2500000000 : ℝ)|^5567 ≤ (24053815357583/50000000000000 : ℝ)^4543
        have hw : |(1375966573/2500000000 : ℝ)|=(1375966573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_9 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030456669/2000000000 : ℝ)*x 0 + (-121078021/1000000000 : ℝ)*x 1 + (1375966611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030456669/2000000000 : ℝ)^5567 ≤ (44369443866697/100000000000000 : ℝ)^4543 := by
    have hnat : (1030456669 : ℕ)^5567*100000000000000^4543 ≤ 44369443866697^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030456669 2000000000 44369443866697 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121078021/1000000000 : ℝ)^5567 ≤ (1880730943303/25000000000000 : ℝ)^4543 := by
    have hnat : (121078021 : ℕ)^5567*25000000000000^4543 ≤ 1880730943303^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121078021 1000000000 1880730943303 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375966611/2500000000 : ℝ)^5567 ≤ (24053816171609/50000000000000 : ℝ)^4543 := by
    have hnat : (1375966611 : ℕ)^5567*50000000000000^4543 ≤ 24053816171609^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375966611 2500000000 24053816171609 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030456669/2000000000 : ℝ), (-121078021/1000000000 : ℝ), (1375966611/2500000000 : ℝ)] ![(44369443866697/100000000000000 : ℝ), (1880730943303/25000000000000 : ℝ), (24053816171609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030456669/2000000000 : ℝ)|^5567 ≤ (44369443866697/100000000000000 : ℝ)^4543
        have hw : |(1030456669/2000000000 : ℝ)|=(1030456669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121078021/1000000000 : ℝ)|^5567 ≤ (1880730943303/25000000000000 : ℝ)^4543
        have hw : |(-121078021/1000000000 : ℝ)|=(121078021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375966611/2500000000 : ℝ)|^5567 ≤ (24053816171609/50000000000000 : ℝ)^4543
        have hw : |(1375966611/2500000000 : ℝ)|=(1375966611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_10 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (322017729/625000000 : ℝ)*x 0 + (1100773247/2000000000 : ℝ)*x 1 + (-1210780063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322017729/625000000 : ℝ)^5567 ≤ (44369447233001/100000000000000 : ℝ)^4543 := by
    have hnat : (322017729 : ℕ)^5567*100000000000000^4543 ≤ 44369447233001^4543*625000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322017729 625000000 44369447233001 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100773247/2000000000 : ℝ)^5567 ≤ (48107630104647/100000000000000 : ℝ)^4543 := by
    have hnat : (1100773247 : ℕ)^5567*100000000000000^4543 ≤ 48107630104647^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100773247 2000000000 48107630104647 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1210780063/10000000000 : ℝ)^5567 ≤ (7522922653987/100000000000000 : ℝ)^4543 := by
    have hnat : (1210780063 : ℕ)^5567*100000000000000^4543 ≤ 7522922653987^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210780063 10000000000 7522922653987 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322017729/625000000 : ℝ), (1100773247/2000000000 : ℝ), (-1210780063/10000000000 : ℝ)] ![(44369447233001/100000000000000 : ℝ), (48107630104647/100000000000000 : ℝ), (7522922653987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322017729/625000000 : ℝ)|^5567 ≤ (44369447233001/100000000000000 : ℝ)^4543
        have hw : |(322017729/625000000 : ℝ)|=(322017729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100773247/2000000000 : ℝ)|^5567 ≤ (48107630104647/100000000000000 : ℝ)^4543
        have hw : |(1100773247/2000000000 : ℝ)|=(1100773247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1210780063/10000000000 : ℝ)|^5567 ≤ (7522922653987/100000000000000 : ℝ)^4543
        have hw : |(-1210780063/10000000000 : ℝ)|=(1210780063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_11 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (958065223/2000000000 : ℝ)*x 0 + (371410113/1000000000 : ℝ)*x 1 + (3714101227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958065223/2000000000 : ℝ)^5567 ≤ (20290316659747/50000000000000 : ℝ)^4543 := by
    have hnat : (958065223 : ℕ)^5567*50000000000000^4543 ≤ 20290316659747^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958065223 2000000000 20290316659747 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371410113/1000000000 : ℝ)^5567 ≤ (464213794659/1562500000000 : ℝ)^4543 := by
    have hnat : (371410113 : ℕ)^5567*1562500000000^4543 ≤ 464213794659^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371410113 1000000000 464213794659 1562500000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3714101227/10000000000 : ℝ)^5567 ≤ (29709683808987/100000000000000 : ℝ)^4543 := by
    have hnat : (3714101227 : ℕ)^5567*100000000000000^4543 ≤ 29709683808987^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714101227 10000000000 29709683808987 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(958065223/2000000000 : ℝ), (371410113/1000000000 : ℝ), (3714101227/10000000000 : ℝ)] ![(20290316659747/50000000000000 : ℝ), (464213794659/1562500000000 : ℝ), (29709683808987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(958065223/2000000000 : ℝ)|^5567 ≤ (20290316659747/50000000000000 : ℝ)^4543
        have hw : |(958065223/2000000000 : ℝ)|=(958065223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371410113/1000000000 : ℝ)|^5567 ≤ (464213794659/1562500000000 : ℝ)^4543
        have hw : |(371410113/1000000000 : ℝ)|=(371410113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3714101227/10000000000 : ℝ)|^5567 ≤ (29709683808987/100000000000000 : ℝ)^4543
        have hw : |(3714101227/10000000000 : ℝ)|=(3714101227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_12 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-531444951/5000000000 : ℝ)*x 0 + (5662412433/10000000000 : ℝ)*x 1 + (2547978851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531444951/5000000000 : ℝ)^5567 ≤ (6412938398019/100000000000000 : ℝ)^4543 := by
    have hnat : (531444951 : ℕ)^5567*100000000000000^4543 ≤ 6412938398019^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531444951 5000000000 6412938398019 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5662412433/10000000000 : ℝ)^5567 ≤ (49811269758871/100000000000000 : ℝ)^4543 := by
    have hnat : (5662412433 : ℕ)^5567*100000000000000^4543 ≤ 49811269758871^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662412433 10000000000 49811269758871 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547978851/5000000000 : ℝ)^5567 ≤ (43775791831839/100000000000000 : ℝ)^4543 := by
    have hnat : (2547978851 : ℕ)^5567*100000000000000^4543 ≤ 43775791831839^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547978851 5000000000 43775791831839 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531444951/5000000000 : ℝ), (5662412433/10000000000 : ℝ), (2547978851/5000000000 : ℝ)] ![(6412938398019/100000000000000 : ℝ), (49811269758871/100000000000000 : ℝ), (43775791831839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531444951/5000000000 : ℝ)|^5567 ≤ (6412938398019/100000000000000 : ℝ)^4543
        have hw : |(-531444951/5000000000 : ℝ)|=(531444951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5662412433/10000000000 : ℝ)|^5567 ≤ (49811269758871/100000000000000 : ℝ)^4543
        have hw : |(5662412433/10000000000 : ℝ)|=(5662412433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547978851/5000000000 : ℝ)|^5567 ≤ (43775791831839/100000000000000 : ℝ)^4543
        have hw : |(2547978851/5000000000 : ℝ)|=(2547978851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_13 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5426907439/10000000000 : ℝ)*x 0 + (-1393838191/10000000000 : ℝ)*x 1 + (1019191641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5426907439/10000000000 : ℝ)^5567 ≤ (47284638462951/100000000000000 : ℝ)^4543 := by
    have hnat : (5426907439 : ℕ)^5567*100000000000000^4543 ≤ 47284638462951^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426907439 10000000000 47284638462951 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393838191/10000000000 : ℝ)^5567 ≤ (4469782191973/50000000000000 : ℝ)^4543 := by
    have hnat : (1393838191 : ℕ)^5567*50000000000000^4543 ≤ 4469782191973^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393838191 10000000000 4469782191973 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019191641/2000000000 : ℝ)^5567 ≤ (43775797126701/100000000000000 : ℝ)^4543 := by
    have hnat : (1019191641 : ℕ)^5567*100000000000000^4543 ≤ 43775797126701^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019191641 2000000000 43775797126701 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5426907439/10000000000 : ℝ), (-1393838191/10000000000 : ℝ), (1019191641/2000000000 : ℝ)] ![(47284638462951/100000000000000 : ℝ), (4469782191973/50000000000000 : ℝ), (43775797126701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5426907439/10000000000 : ℝ)|^5567 ≤ (47284638462951/100000000000000 : ℝ)^4543
        have hw : |(5426907439/10000000000 : ℝ)|=(5426907439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1393838191/10000000000 : ℝ)|^5567 ≤ (4469782191973/50000000000000 : ℝ)^4543
        have hw : |(-1393838191/10000000000 : ℝ)|=(1393838191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019191641/2000000000 : ℝ)|^5567 ≤ (43775797126701/100000000000000 : ℝ)^4543
        have hw : |(1019191641/2000000000 : ℝ)|=(1019191641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_14 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2713453619/5000000000 : ℝ)*x 0 + (5095957977/10000000000 : ℝ)*x 1 + (-1393838771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2713453619/5000000000 : ℝ)^5567 ≤ (47284636316889/100000000000000 : ℝ)^4543 := by
    have hnat : (2713453619 : ℕ)^5567*100000000000000^4543 ≤ 47284636316889^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713453619 5000000000 47284636316889 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5095957977/10000000000 : ℝ)^5567 ≤ (10943948681661/25000000000000 : ℝ)^4543 := by
    have hnat : (5095957977 : ℕ)^5567*25000000000000^4543 ≤ 10943948681661^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095957977 10000000000 10943948681661 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393838771/10000000000 : ℝ)^5567 ≤ (4469784471163/50000000000000 : ℝ)^4543 := by
    have hnat : (1393838771 : ℕ)^5567*50000000000000^4543 ≤ 4469784471163^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393838771 10000000000 4469784471163 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2713453619/5000000000 : ℝ), (5095957977/10000000000 : ℝ), (-1393838771/10000000000 : ℝ)] ![(47284636316889/100000000000000 : ℝ), (10943948681661/25000000000000 : ℝ), (4469784471163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2713453619/5000000000 : ℝ)|^5567 ≤ (47284636316889/100000000000000 : ℝ)^4543
        have hw : |(2713453619/5000000000 : ℝ)|=(2713453619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5095957977/10000000000 : ℝ)|^5567 ≤ (10943948681661/25000000000000 : ℝ)^4543
        have hw : |(5095957977/10000000000 : ℝ)|=(5095957977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1393838771/10000000000 : ℝ)|^5567 ≤ (4469784471163/50000000000000 : ℝ)^4543
        have hw : |(-1393838771/10000000000 : ℝ)|=(1393838771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_box_15 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210882617/625000000 : ℝ)*x 0 + (884456889/2000000000 : ℝ)*x 1 + (1105571063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210882617/625000000 : ℝ)^5567 ≤ (6603092787807/25000000000000 : ℝ)^4543 := by
    have hnat : (210882617 : ℕ)^5567*25000000000000^4543 ≤ 6603092787807^4543*625000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210882617 625000000 6603092787807 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884456889/2000000000 : ℝ)^5567 ≤ (36793815398859/100000000000000 : ℝ)^4543 := by
    have hnat : (884456889 : ℕ)^5567*100000000000000^4543 ≤ 36793815398859^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884456889 2000000000 36793815398859 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105571063/2500000000 : ℝ)^5567 ≤ (1149806669723/3125000000000 : ℝ)^4543 := by
    have hnat : (1105571063 : ℕ)^5567*3125000000000^4543 ≤ 1149806669723^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105571063 2500000000 1149806669723 3125000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210882617/625000000 : ℝ), (884456889/2000000000 : ℝ), (1105571063/2500000000 : ℝ)] ![(6603092787807/25000000000000 : ℝ), (36793815398859/100000000000000 : ℝ), (1149806669723/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210882617/625000000 : ℝ)|^5567 ≤ (6603092787807/25000000000000 : ℝ)^4543
        have hw : |(210882617/625000000 : ℝ)|=(210882617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884456889/2000000000 : ℝ)|^5567 ≤ (36793815398859/100000000000000 : ℝ)^4543
        have hw : |(884456889/2000000000 : ℝ)|=(884456889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105571063/2500000000 : ℝ)|^5567 ≤ (1149806669723/3125000000000 : ℝ)^4543
        have hw : |(1105571063/2500000000 : ℝ)|=(1105571063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1737_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68681/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57459/100000 : ℝ) ∧ (3231/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92651/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2213/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2213/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2213/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2213/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2213/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2213/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2213/25000 : ℝ) ^ (5551/1024 : ℝ) ≤ (19589276622151/10000000000000000000 : ℝ) := by
    have hpowers : (2213/25000 : ℝ)^5551 ≤ (19589276622151/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2213 : ℕ)^5551*10000000000000000000^1024 ≤ 19589276622151^1024*25000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2213 25000 19589276622151 10000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2213/25000 : ℝ)) (X := (19589276622151/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18231/100000 : ℝ) ^ (5551/1024 : ℝ) ≤ (9838496738979491/100000000000000000000 : ℝ) := by
    have hpowers : (18231/100000 : ℝ)^5551 ≤ (9838496738979491/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18231 : ℕ)^5551*100000000000000000000^1024 ≤ 9838496738979491^1024*100000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18231 100000 9838496738979491 100000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18231/100000 : ℝ)) (X := (9838496738979491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000019589276622151/5000000000000000000 : ℝ) ≤ (10000007227305789/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (5000019589276622151/5000000000000000000 : ℝ)^1024 ≤ (10000007227305789/10000000000000000 : ℝ)^5551 := by
      have hnat : (5000019589276622151 : ℕ)^1024*10000000000000000^5551 ≤ 10000007227305789^5551*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000019589276622151 5000000000000000000 10000007227305789 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007227305789/10000000000000000 : ℝ)) (X := (5000019589276622151/5000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010034389505201001/100000000000000000000 : ℝ) ≤ (10000185098080551/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (100010034389505201001/100000000000000000000 : ℝ)^1024 ≤ (10000185098080551/10000000000000000 : ℝ)^5551 := by
      have hnat : (100010034389505201001 : ℕ)^1024*10000000000000000^5551 ≤ 10000185098080551^5551*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010034389505201001 100000000000000000000 10000185098080551 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000185098080551/10000000000000000 : ℝ)) (X := (100010034389505201001/100000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009838496738979491/50000000000000000000 : ℝ) ≤ (10000362968855313/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (50009838496738979491/50000000000000000000 : ℝ)^1024 ≤ (10000362968855313/10000000000000000 : ℝ)^5551 := by
      have hnat : (50009838496738979491 : ℕ)^1024*10000000000000000^5551 ≤ 10000362968855313^5551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009838496738979491 50000000000000000000 10000362968855313 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000362968855313/10000000000000000 : ℝ)) (X := (50009838496738979491/50000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19589276622151/10000000000000000000 : ℝ) ≤ ((93786918760704608583/93790000000000000000 : ℝ)+2*(88935387381/468950000000000 : ℝ)*(2213/25000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (93786918760704608583/93790000000000000000 : ℝ)+2*(88935387381/468950000000000 : ℝ)*(2213/25000 : ℝ)=(10000007227305789/10000000000000000 : ℝ) by norm_num, show 1+2*(19589276622151/10000000000000000000 : ℝ)=(5000019589276622151/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9838496738979491/100000000000000000000 : ℝ)+(19589276622151/10000000000000000000 : ℝ) ≤ ((93786918760704608583/93790000000000000000 : ℝ)+(88935387381/468950000000000 : ℝ)*((18231/100000 : ℝ)+(2213/25000 : ℝ)))^(5551/1024 : ℝ) := by
    rw [show (93786918760704608583/93790000000000000000 : ℝ)+(88935387381/468950000000000 : ℝ)*((18231/100000 : ℝ)+(2213/25000 : ℝ))=(10000185098080551/10000000000000000 : ℝ) by norm_num, show 1+(9838496738979491/100000000000000000000 : ℝ)+(19589276622151/10000000000000000000 : ℝ)=(100010034389505201001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9838496738979491/100000000000000000000 : ℝ) ≤ ((93786918760704608583/93790000000000000000 : ℝ)+2*(88935387381/468950000000000 : ℝ)*(18231/100000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (93786918760704608583/93790000000000000000 : ℝ)+2*(88935387381/468950000000000 : ℝ)*(18231/100000 : ℝ)=(10000362968855313/10000000000000000 : ℝ) by norm_num, show 1+2*(9838496738979491/100000000000000000000 : ℝ)=(50009838496738979491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93786918760704608583/93790000000000000000 : ℝ)*(X 1 0+X 2 0)+(88935387381/468950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (18231/100000 : ℝ)) (c := (93786918760704608583/93790000000000000000 : ℝ)) (alpha := (88935387381/468950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93786918760704608583/93790000000000000000 : ℝ)*(X 0 1+X 2 1)+(88935387381/468950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (18231/100000 : ℝ)) (c := (93786918760704608583/93790000000000000000 : ℝ)) (alpha := (88935387381/468950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93786918760704608583/93790000000000000000 : ℝ)*(X 0 2+X 1 2)+(88935387381/468950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (18231/100000 : ℝ)) (c := (93786918760704608583/93790000000000000000 : ℝ)) (alpha := (88935387381/468950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2778819/31250000 : ℝ)*X 0 0+(1359969761/2500000000 : ℝ)*X 0 1+(5439879027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597653407/5000000000 : ℝ)*X 1 0+(-310226853/2500000000 : ℝ)*X 1 1+(5439879021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1039061353/2000000000 : ℝ)*X 2 0+(5439879047/10000000000 : ℝ)*X 2 1+(-310226861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2289013221/5000000000 : ℝ)*X 0 0+(765115013/2000000000 : ℝ)*X 0 1+(1912787587/5000000000 : ℝ)*X 0 2+(2289013221/5000000000 : ℝ)*X 1 0+(765115013/2000000000 : ℝ)*X 1 1+(1912787587/5000000000 : ℝ)*X 1 2+(2289013221/5000000000 : ℝ)*X 2 0+(765115013/2000000000 : ℝ)*X 2 1+(1912787587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437212973/2500000000 : ℝ)*X 0 0+(512649563/1000000000 : ℝ)*X 0 1+(2563247911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5406280977/10000000000 : ℝ)*X 1 0+(-345226549/2500000000 : ℝ)*X 1 1+(5126494811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((168946263/312500000 : ℝ)*X 2 0+(5126494981/10000000000 : ℝ)*X 2 1+(-138090673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1742888689/5000000000 : ℝ)*X 0 0+(4369493963/10000000000 : ℝ)*X 0 1+(873898629/2000000000 : ℝ)*X 0 2+(1742888689/5000000000 : ℝ)*X 1 0+(4369493963/10000000000 : ℝ)*X 1 1+(873898629/2000000000 : ℝ)*X 1 2+(1742888689/5000000000 : ℝ)*X 2 0+(4369493963/10000000000 : ℝ)*X 2 1+(873898629/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-390590737/2500000000 : ℝ)*X 0 0+(4889335023/10000000000 : ℝ)*X 0 1+(1375966573/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1030456669/2000000000 : ℝ)*X 1 0+(-121078021/1000000000 : ℝ)*X 1 1+(1375966611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((322017729/625000000 : ℝ)*X 2 0+(1100773247/2000000000 : ℝ)*X 2 1+(-1210780063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((958065223/2000000000 : ℝ)*X 0 0+(371410113/1000000000 : ℝ)*X 0 1+(3714101227/10000000000 : ℝ)*X 0 2+(958065223/2000000000 : ℝ)*X 1 0+(371410113/1000000000 : ℝ)*X 1 1+(3714101227/10000000000 : ℝ)*X 1 2+(958065223/2000000000 : ℝ)*X 2 0+(371410113/1000000000 : ℝ)*X 2 1+(3714101227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-531444951/5000000000 : ℝ)*X 0 0+(5662412433/10000000000 : ℝ)*X 0 1+(2547978851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5426907439/10000000000 : ℝ)*X 1 0+(-1393838191/10000000000 : ℝ)*X 1 1+(1019191641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2713453619/5000000000 : ℝ)*X 2 0+(5095957977/10000000000 : ℝ)*X 2 1+(-1393838771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((210882617/625000000 : ℝ)*X 0 0+(884456889/2000000000 : ℝ)*X 0 1+(1105571063/2500000000 : ℝ)*X 0 2+(210882617/625000000 : ℝ)*X 1 0+(884456889/2000000000 : ℝ)*X 1 1+(1105571063/2500000000 : ℝ)*X 1 2+(210882617/625000000 : ℝ)*X 2 0+(884456889/2000000000 : ℝ)*X 2 1+(1105571063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68681/100000 : ℝ) ≤ (-322068647969615306828346196708029/468950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4076143/4000000000000 : ℝ)*(lower0) + (45962327/50000000000000 : ℝ)*(lower2) + (1235037/50000000000000 : ℝ)*(lower3) + (209557977/100000000000000 : ℝ)*(lower4) + (1201707/50000000000000 : ℝ)*(lower5) + (100486973085907/10000000000000 : ℝ)*(major0) + (100486973085907/10000000000000 : ℝ)*(major1) + (100486973085907/10000000000000 : ℝ)*(major2) + (612719513/12500000000000 : ℝ)*(sp1) + (6372248439/100000000000000 : ℝ)*(sp2) + (771925671814971/50000000000000 : ℝ)*(sp4) + (771923220936919/50000000000000 : ℝ)*(sp5) + (1543844971381503/100000000000000 : ℝ)*(sp6) + (488781009865541/100000000000000 : ℝ)*(sp7) + (488781009865541/100000000000000 : ℝ)*(f.failure) + (771925671814971/50000000000000 : ℝ)*(f.sum) + (29452376017709/4689500000000000000000000000 : ℝ)*base66 + (4683215854692239781/937900000000000000000000000000000 : ℝ)*base67 + (2812540234536839781/937900000000000000000000000000000 : ℝ)*base69 + (2382339468929939781/937900000000000000000000000000000 : ℝ)*base71 + (3155843155181/1875800000000000000000000000 : ℝ)*base74 + (6700279722820639781/937900000000000000000000000000000 : ℝ)*base75 + (3094897081662039781/937900000000000000000000000000000 : ℝ)*base77 + (10910739970945839781/937900000000000000000000000000000 : ℝ)*base79 + (54060874680213/9379000000000000000000000000 : ℝ)*base82 + (878441/10000000000000000000000 : ℝ)*base89 + (878441/10000000000000000000000 : ℝ)*base91 + (878441/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57459/100000 : ℝ) ≤ (33683319402337470990669166588011/58618750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81043/6250000000000 : ℝ)*(lower1) + (4753687/100000000000000 : ℝ)*(upper2) + (901369/20000000000000 : ℝ)*(lower4) + (14008780400837/1250000000000 : ℝ)*(major0) + (14008780400837/1250000000000 : ℝ)*(major1) + (14008780400837/1250000000000 : ℝ)*(major2) + (335425486289671/20000000000000 : ℝ)*(sp0) + (838563748720721/50000000000000 : ℝ)*(sp1) + (838563659762933/50000000000000 : ℝ)*(sp2) + (136280860171361/25000000000000 : ℝ)*(sp3) + (5455933/50000000000000 : ℝ)*(sp5) + (21274303/100000000000000 : ℝ)*(sp7) + (94413721/50000000000000 : ℝ)*(sp10) + (38452477/50000000000000 : ℝ)*(sp12) + (136280865489937/25000000000000 : ℝ)*(f.failure) + (419281877088327/25000000000000 : ℝ)*(f.sum) + (1730480334729/4689500000000000000000000000 : ℝ)*base65 + (901350080759621471/117237500000000000000000000000000 : ℝ)*base67 + (639819698342033971/117237500000000000000000000000000 : ℝ)*base69 + (1499280756896133971/117237500000000000000000000000000 : ℝ)*base71 + (30503225641093/9379000000000000000000000000 : ℝ)*base73 + (1028730565024721471/117237500000000000000000000000000 : ℝ)*base75 + (539594265134483971/117237500000000000000000000000000 : ℝ)*base77 + (1596394373312996471/117237500000000000000000000000000 : ℝ)*base79 + (3053242897793/1875800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5484763/2500000000000000000000 : ℝ)*base90 + (5484763/2500000000000000000000 : ℝ)*base92 + (5484763/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (3231/4000 : ℝ) ≤ (757613785836329002168106419175817/937900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1204029/20000000000000 : ℝ)*(upper0) + (10457817/100000000000000 : ℝ)*(lower1) + (9401187/50000000000000 : ℝ)*(lower3) + (21525383/50000000000000 : ℝ)*(upper4) + (218577724751067/20000000000000 : ℝ)*(major0) + (218577724751067/20000000000000 : ℝ)*(major1) + (218577724751067/20000000000000 : ℝ)*(major2) + (5169588093/100000000000000 : ℝ)*(sp1) + (1555284641/50000000000000 : ℝ)*(sp2) + (140374801/12500000000000 : ℝ)*(sp3) + (1627256873708047/100000000000000 : ℝ)*(sp8) + (813625852059977/50000000000000 : ℝ)*(sp9) + (325450752627753/20000000000000 : ℝ)*(sp10) + (531593360132273/100000000000000 : ℝ)*(sp11) + (531594483130681/100000000000000 : ℝ)*(f.failure) + (1627256873708047/100000000000000 : ℝ)*(f.sum) + (46195676420729/9379000000000000000000000000 : ℝ)*base65 + (7054109778754208061/1875800000000000000000000000000000 : ℝ)*base67 + (896803531622591939/1875800000000000000000000000000000 : ℝ)*base70 + (15854518383376608061/1875800000000000000000000000000000 : ℝ)*base71 + (1255027953757/586187500000000000000000000 : ℝ)*base74 + (8930383603958408061/1875800000000000000000000000000000 : ℝ)*base75 + (4528633332940208061/1875800000000000000000000000000000 : ℝ)*base77 + (3492958286904191939/1875800000000000000000000000000000 : ℝ)*base80 + (1103739071407/4689500000000000000000000000 : ℝ)*base81 + (15190419/10000000000000000000000 : ℝ)*base90 + (15190419/10000000000000000000000 : ℝ)*base92 + (15190419/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-92651/100000 : ℝ) ≤ (-4344759913142372692652741903247711/4689500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6773473/10000000000000 : ℝ)*(lower0) + (47919/25000000000000 : ℝ)*(upper3) + (53808067/50000000000000 : ℝ)*(lower4) + (1145944060681539/100000000000000 : ℝ)*(major0) + (1145944060681539/100000000000000 : ℝ)*(major1) + (1145944060681539/100000000000000 : ℝ)*(major2) + (3595434259/100000000000000 : ℝ)*(sp0) + (11477448191/100000000000000 : ℝ)*(sp5) + (23223673847/50000000000000 : ℝ)*(sp6) + (3095871553/50000000000000 : ℝ)*(sp7) + (882683059403761/50000000000000 : ℝ)*(sp12) + (176535823679359/10000000000000 : ℝ)*(sp13) + (1765323266894087/100000000000000 : ℝ)*(sp14) + (139348777292573/25000000000000 : ℝ)*(sp15) + (278700650456699/50000000000000 : ℝ)*(f.failure) + (1765369714241781/100000000000000 : ℝ)*(f.sum) + (46268147310579/23447500000000000000000000000 : ℝ)*base65 + (5166965036320849237/9379000000000000000000000000000000 : ℝ)*base67 + (48507286979891849237/9379000000000000000000000000000000 : ℝ)*base69 + (54064429659969849237/9379000000000000000000000000000000 : ℝ)*base71 + (249105699016689/23447500000000000000000000000 : ℝ)*base73 + (750493341014150763/9379000000000000000000000000000000 : ℝ)*base76 + (24522607465422849237/9379000000000000000000000000000000 : ℝ)*base77 + (82941390494868150763/9379000000000000000000000000000000 : ℝ)*base80 + (173447936776703/46895000000000000000000000000 : ℝ)*base81 + (32099799/5000000000000000000000 : ℝ)*base89 + (32099799/5000000000000000000000 : ℝ)*base91 + (32099799/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1737_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68681/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57459/100000 : ℝ) else (3231/4000 : ℝ) ≤ X j i ∧ X j i ≤ (92651/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1737_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1737_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68681/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57459/100000 : ℝ) else (3231/4000 : ℝ) ≤ X j i ∧ X j i ≤ (92651/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1737_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1737_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68681/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57459/100000 : ℝ) else (3231/4000 : ℝ) ≤ X j i ∧ X j i ≤ (92651/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1737_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

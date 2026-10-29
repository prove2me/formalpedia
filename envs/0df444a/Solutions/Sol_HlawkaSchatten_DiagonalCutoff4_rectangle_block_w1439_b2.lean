-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:39.335112+00:00
-- url     : https://prove2.me/submissions/9e6350f1-e9c5-4bff-afd7-611b54477c87

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
theorem support_rectangle_w1439_s6_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-981521811/5000000000 : ℝ)*x 0 + (5407708709/10000000000 : ℝ)*x 1 + (5247121709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981521811/5000000000 : ℝ)^4399 ≤ (748651462257/6250000000000 : ℝ)^3375 := by
    have hnat : (981521811 : ℕ)^4399*6250000000000^3375 ≤ 748651462257^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981521811 5000000000 748651462257 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407708709/10000000000 : ℝ)^4399 ≤ (44875318542321/100000000000000 : ℝ)^3375 := by
    have hnat : (5407708709 : ℕ)^4399*100000000000000^3375 ≤ 44875318542321^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407708709 10000000000 44875318542321 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247121709/10000000000 : ℝ)^4399 ≤ (10786564511353/25000000000000 : ℝ)^3375 := by
    have hnat : (5247121709 : ℕ)^4399*25000000000000^3375 ≤ 10786564511353^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247121709 10000000000 10786564511353 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981521811/5000000000 : ℝ), (5407708709/10000000000 : ℝ), (5247121709/10000000000 : ℝ)] ![(748651462257/6250000000000 : ℝ), (44875318542321/100000000000000 : ℝ), (10786564511353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981521811/5000000000 : ℝ)|^4399 ≤ (748651462257/6250000000000 : ℝ)^3375
        have hw : |(-981521811/5000000000 : ℝ)|=(981521811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407708709/10000000000 : ℝ)|^4399 ≤ (44875318542321/100000000000000 : ℝ)^3375
        have hw : |(5407708709/10000000000 : ℝ)|=(5407708709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247121709/10000000000 : ℝ)|^4399 ≤ (10786564511353/25000000000000 : ℝ)^3375
        have hw : |(5247121709/10000000000 : ℝ)|=(5247121709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334194783/625000000 : ℝ)*x 0 + (-2044794261/10000000000 : ℝ)*x 1 + (524712171/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334194783/625000000 : ℝ)^4399 ≤ (22110529363607/50000000000000 : ℝ)^3375 := by
    have hnat : (334194783 : ℕ)^4399*50000000000000^3375 ≤ 22110529363607^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334194783 625000000 22110529363607 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044794261/10000000000 : ℝ)^4399 ≤ (1579085400441/12500000000000 : ℝ)^3375 := by
    have hnat : (2044794261 : ℕ)^4399*12500000000000^3375 ≤ 1579085400441^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044794261 10000000000 1579085400441 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524712171/1000000000 : ℝ)^4399 ≤ (4314625805613/10000000000000 : ℝ)^3375 := by
    have hnat : (524712171 : ℕ)^4399*10000000000000^3375 ≤ 4314625805613^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524712171 1000000000 4314625805613 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334194783/625000000 : ℝ), (-2044794261/10000000000 : ℝ), (524712171/1000000000 : ℝ)] ![(22110529363607/50000000000000 : ℝ), (1579085400441/12500000000000 : ℝ), (4314625805613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334194783/625000000 : ℝ)|^4399 ≤ (22110529363607/50000000000000 : ℝ)^3375
        have hw : |(334194783/625000000 : ℝ)|=(334194783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044794261/10000000000 : ℝ)|^4399 ≤ (1579085400441/12500000000000 : ℝ)^3375
        have hw : |(-2044794261/10000000000 : ℝ)|=(2044794261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524712171/1000000000 : ℝ)|^4399 ≤ (4314625805613/10000000000000 : ℝ)^3375
        have hw : |(524712171/1000000000 : ℝ)|=(524712171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334194783/625000000 : ℝ)*x 0 + (524712171/1000000000 : ℝ)*x 1 + (-1022397131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334194783/625000000 : ℝ)^4399 ≤ (22110529363607/50000000000000 : ℝ)^3375 := by
    have hnat : (334194783 : ℕ)^4399*50000000000000^3375 ≤ 22110529363607^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334194783 625000000 22110529363607 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524712171/1000000000 : ℝ)^4399 ≤ (4314625805613/10000000000000 : ℝ)^3375 := by
    have hnat : (524712171 : ℕ)^4399*10000000000000^3375 ≤ 4314625805613^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524712171 1000000000 4314625805613 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022397131/5000000000 : ℝ)^4399 ≤ (12632683211581/100000000000000 : ℝ)^3375 := by
    have hnat : (1022397131 : ℕ)^4399*100000000000000^3375 ≤ 12632683211581^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022397131 5000000000 12632683211581 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334194783/625000000 : ℝ), (524712171/1000000000 : ℝ), (-1022397131/5000000000 : ℝ)] ![(22110529363607/50000000000000 : ℝ), (4314625805613/10000000000000 : ℝ), (12632683211581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334194783/625000000 : ℝ)|^4399 ≤ (22110529363607/50000000000000 : ℝ)^3375
        have hw : |(334194783/625000000 : ℝ)|=(334194783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524712171/1000000000 : ℝ)|^4399 ≤ (4314625805613/10000000000000 : ℝ)^3375
        have hw : |(524712171/1000000000 : ℝ)|=(524712171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022397131/5000000000 : ℝ)|^4399 ≤ (12632683211581/100000000000000 : ℝ)^3375
        have hw : |(-1022397131/5000000000 : ℝ)|=(1022397131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301878757/10000000000 : ℝ)*x 0 + (2065352137/5000000000 : ℝ)*x 1 + (895876181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301878757/10000000000 : ℝ)^4399 ≤ (33304839122749/100000000000000 : ℝ)^3375 := by
    have hnat : (4301878757 : ℕ)^4399*100000000000000^3375 ≤ 33304839122749^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301878757 10000000000 33304839122749 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065352137/5000000000 : ℝ)^4399 ≤ (31588061355943/100000000000000 : ℝ)^3375 := by
    have hnat : (2065352137 : ℕ)^4399*100000000000000^3375 ≤ 31588061355943^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065352137 5000000000 31588061355943 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895876181/2000000000 : ℝ)^4399 ≤ (7021419901597/20000000000000 : ℝ)^3375 := by
    have hnat : (895876181 : ℕ)^4399*20000000000000^3375 ≤ 7021419901597^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895876181 2000000000 7021419901597 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301878757/10000000000 : ℝ), (2065352137/5000000000 : ℝ), (895876181/2000000000 : ℝ)] ![(33304839122749/100000000000000 : ℝ), (31588061355943/100000000000000 : ℝ), (7021419901597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301878757/10000000000 : ℝ)|^4399 ≤ (33304839122749/100000000000000 : ℝ)^3375
        have hw : |(4301878757/10000000000 : ℝ)|=(4301878757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065352137/5000000000 : ℝ)|^4399 ≤ (31588061355943/100000000000000 : ℝ)^3375
        have hw : |(2065352137/5000000000 : ℝ)|=(2065352137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895876181/2000000000 : ℝ)|^4399 ≤ (7021419901597/20000000000000 : ℝ)^3375
        have hw : |(895876181/2000000000 : ℝ)|=(895876181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98152741/500000000 : ℝ)*x 0 + (5247701559/10000000000 : ℝ)*x 1 + (2703562943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98152741/500000000 : ℝ)^4399 ≤ (11978512457761/100000000000000 : ℝ)^3375 := by
    have hnat : (98152741 : ℕ)^4399*100000000000000^3375 ≤ 11978512457761^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98152741 500000000 11978512457761 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247701559/10000000000 : ℝ)^4399 ≤ (21576236408169/50000000000000 : ℝ)^3375 := by
    have hnat : (5247701559 : ℕ)^4399*50000000000000^3375 ≤ 21576236408169^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247701559 10000000000 21576236408169 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703562943/5000000000 : ℝ)^4399 ≤ (44869014719177/100000000000000 : ℝ)^3375 := by
    have hnat : (2703562943 : ℕ)^4399*100000000000000^3375 ≤ 44869014719177^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703562943 5000000000 44869014719177 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98152741/500000000 : ℝ), (5247701559/10000000000 : ℝ), (2703562943/5000000000 : ℝ)] ![(11978512457761/100000000000000 : ℝ), (21576236408169/50000000000000 : ℝ), (44869014719177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98152741/500000000 : ℝ)|^4399 ≤ (11978512457761/100000000000000 : ℝ)^3375
        have hw : |(-98152741/500000000 : ℝ)|=(98152741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247701559/10000000000 : ℝ)|^4399 ≤ (21576236408169/50000000000000 : ℝ)^3375
        have hw : |(5247701559/10000000000 : ℝ)|=(5247701559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703562943/5000000000 : ℝ)|^4399 ≤ (44869014719177/100000000000000 : ℝ)^3375
        have hw : |(2703562943/5000000000 : ℝ)|=(2703562943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82895743/156250000 : ℝ)*x 0 + (-376958011/2000000000 : ℝ)*x 1 + (2703563017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82895743/156250000 : ℝ)^4399 ≤ (43771138769827/100000000000000 : ℝ)^3375 := by
    have hnat : (82895743 : ℕ)^4399*100000000000000^3375 ≤ 43771138769827^3375*156250000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82895743 156250000 43771138769827 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376958011/2000000000 : ℝ)^4399 ≤ (11359844898183/100000000000000 : ℝ)^3375 := by
    have hnat : (376958011 : ℕ)^4399*100000000000000^3375 ≤ 11359844898183^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376958011 2000000000 11359844898183 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703563017/5000000000 : ℝ)^4399 ≤ (44869016319921/100000000000000 : ℝ)^3375 := by
    have hnat : (2703563017 : ℕ)^4399*100000000000000^3375 ≤ 44869016319921^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703563017 5000000000 44869016319921 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82895743/156250000 : ℝ), (-376958011/2000000000 : ℝ), (2703563017/5000000000 : ℝ)] ![(43771138769827/100000000000000 : ℝ), (11359844898183/100000000000000 : ℝ), (44869016319921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82895743/156250000 : ℝ)|^4399 ≤ (43771138769827/100000000000000 : ℝ)^3375
        have hw : |(82895743/156250000 : ℝ)|=(82895743/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376958011/2000000000 : ℝ)|^4399 ≤ (11359844898183/100000000000000 : ℝ)^3375
        have hw : |(-376958011/2000000000 : ℝ)|=(376958011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703563017/5000000000 : ℝ)|^4399 ≤ (44869016319921/100000000000000 : ℝ)^3375
        have hw : |(2703563017/5000000000 : ℝ)|=(2703563017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331583/625000 : ℝ)*x 0 + (5407125689/10000000000 : ℝ)*x 1 + (-471197479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331583/625000 : ℝ)^4399 ≤ (21885571793731/50000000000000 : ℝ)^3375 := by
    have hnat : (331583 : ℕ)^4399*50000000000000^3375 ≤ 21885571793731^3375*625000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331583 625000 21885571793731 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407125689/10000000000 : ℝ)^4399 ≤ (5608626573557/12500000000000 : ℝ)^3375 := by
    have hnat : (5407125689 : ℕ)^4399*12500000000000^3375 ≤ 5608626573557^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407125689 10000000000 5608626573557 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471197479/2500000000 : ℝ)^4399 ≤ (11359843806229/100000000000000 : ℝ)^3375 := by
    have hnat : (471197479 : ℕ)^4399*100000000000000^3375 ≤ 11359843806229^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471197479 2500000000 11359843806229 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331583/625000 : ℝ), (5407125689/10000000000 : ℝ), (-471197479/2500000000 : ℝ)] ![(21885571793731/50000000000000 : ℝ), (5608626573557/12500000000000 : ℝ), (11359843806229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331583/625000 : ℝ)|^4399 ≤ (21885571793731/50000000000000 : ℝ)^3375
        have hw : |(331583/625000 : ℝ)|=(331583/625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407125689/10000000000 : ℝ)|^4399 ≤ (5608626573557/12500000000000 : ℝ)^3375
        have hw : |(5407125689/10000000000 : ℝ)|=(5407125689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471197479/2500000000 : ℝ)|^4399 ≤ (11359843806229/100000000000000 : ℝ)^3375
        have hw : |(-471197479/2500000000 : ℝ)|=(471197479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s6_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301902931/10000000000 : ℝ)*x 0 + (4478122401/10000000000 : ℝ)*x 1 + (4131969517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301902931/10000000000 : ℝ)^4399 ≤ (8326270765017/25000000000000 : ℝ)^3375 := by
    have hnat : (4301902931 : ℕ)^4399*25000000000000^3375 ≤ 8326270765017^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301902931 10000000000 8326270765017 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478122401/10000000000 : ℝ)^4399 ≤ (35094243881997/100000000000000 : ℝ)^3375 := by
    have hnat : (4478122401 : ℕ)^4399*100000000000000^3375 ≤ 35094243881997^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478122401 10000000000 35094243881997 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131969517/10000000000 : ℝ)^4399 ≤ (31600673042701/100000000000000 : ℝ)^3375 := by
    have hnat : (4131969517 : ℕ)^4399*100000000000000^3375 ≤ 31600673042701^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131969517 10000000000 31600673042701 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301902931/10000000000 : ℝ), (4478122401/10000000000 : ℝ), (4131969517/10000000000 : ℝ)] ![(8326270765017/25000000000000 : ℝ), (35094243881997/100000000000000 : ℝ), (31600673042701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301902931/10000000000 : ℝ)|^4399 ≤ (8326270765017/25000000000000 : ℝ)^3375
        have hw : |(4301902931/10000000000 : ℝ)|=(4301902931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478122401/10000000000 : ℝ)|^4399 ≤ (35094243881997/100000000000000 : ℝ)^3375
        have hw : |(4478122401/10000000000 : ℝ)|=(4478122401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131969517/10000000000 : ℝ)|^4399 ≤ (31600673042701/100000000000000 : ℝ)^3375
        have hw : |(4131969517/10000000000 : ℝ)|=(4131969517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (71/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (2189631786095707/25000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^2199 ≤ (2189631786095707/25000000000000000000 : ℝ)^512 := by
      have hnat : (11357 : ℕ)^2199*25000000000000000000^512 ≤ 2189631786095707^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 2189631786095707 25000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (2189631786095707/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (2199/512 : ℝ) ≤ (27042628533848177/100000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^2199 ≤ (27042628533848177/100000000000000000000 : ℝ)^512 := by
      have hnat : (7383 : ℕ)^2199*100000000000000000000^512 ≤ 27042628533848177^512*50000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 27042628533848177 100000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (27042628533848177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502189631786095707/12500000000000000000 : ℝ) ≤ (10000407827613749/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12502189631786095707/12500000000000000000 : ℝ)^512 ≤ (10000407827613749/10000000000000000 : ℝ)^2199 := by
      have hnat : (12502189631786095707 : ℕ)^512*10000000000000000^2199 ≤ 10000407827613749^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502189631786095707 12500000000000000000 10000407827613749 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000407827613749/10000000000000000 : ℝ)) (X := (12502189631786095707/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007160231135646201/20000000000000000000 : ℝ) ≤ (10000833454979633/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (20007160231135646201/20000000000000000000 : ℝ)^512 ≤ (10000833454979633/10000000000000000 : ℝ)^2199 := by
      have hnat : (20007160231135646201 : ℕ)^512*10000000000000000^2199 ≤ 10000833454979633^2199*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007160231135646201 20000000000000000000 10000833454979633 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000833454979633/10000000000000000 : ℝ)) (X := (20007160231135646201/20000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027042628533848177/50000000000000000000 : ℝ) ≤ (10001259082345517/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50027042628533848177/50000000000000000000 : ℝ)^512 ≤ (10001259082345517/10000000000000000 : ℝ)^2199 := by
      have hnat : (50027042628533848177 : ℕ)^512*10000000000000000^2199 ≤ 10001259082345517^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027042628533848177 50000000000000000000 10001259082345517 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259082345517/10000000000000000 : ℝ)) (X := (50027042628533848177/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2189631786095707/25000000000000000000 : ℝ) ≤ ((973763502409902319/974000000000000000 : ℝ)+2*(15200977353/12175000000000 : ℝ)*(11357/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (973763502409902319/974000000000000000 : ℝ)+2*(15200977353/12175000000000 : ℝ)*(11357/100000 : ℝ)=(10000407827613749/10000000000000000 : ℝ) by norm_num, show 1+2*(2189631786095707/25000000000000000000 : ℝ)=(12502189631786095707/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27042628533848177/100000000000000000000 : ℝ)+(2189631786095707/25000000000000000000 : ℝ) ≤ ((973763502409902319/974000000000000000 : ℝ)+(15200977353/12175000000000 : ℝ)*((7383/50000 : ℝ)+(11357/100000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (973763502409902319/974000000000000000 : ℝ)+(15200977353/12175000000000 : ℝ)*((7383/50000 : ℝ)+(11357/100000 : ℝ))=(10000833454979633/10000000000000000 : ℝ) by norm_num, show 1+(27042628533848177/100000000000000000000 : ℝ)+(2189631786095707/25000000000000000000 : ℝ)=(20007160231135646201/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27042628533848177/100000000000000000000 : ℝ) ≤ ((973763502409902319/974000000000000000 : ℝ)+2*(15200977353/12175000000000 : ℝ)*(7383/50000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (973763502409902319/974000000000000000 : ℝ)+2*(15200977353/12175000000000 : ℝ)*(7383/50000 : ℝ)=(10001259082345517/10000000000000000 : ℝ) by norm_num, show 1+2*(27042628533848177/100000000000000000000 : ℝ)=(50027042628533848177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (973763502409902319/974000000000000000 : ℝ)*(X 1 0+X 2 0)+(15200977353/12175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (973763502409902319/974000000000000000 : ℝ)) (alpha := (15200977353/12175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (973763502409902319/974000000000000000 : ℝ)*(X 0 1+X 2 1)+(15200977353/12175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (973763502409902319/974000000000000000 : ℝ)) (alpha := (15200977353/12175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (973763502409902319/974000000000000000 : ℝ)*(X 0 2+X 1 2)+(15200977353/12175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (973763502409902319/974000000000000000 : ℝ)) (alpha := (15200977353/12175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-981521811/5000000000 : ℝ)*X 0 0+(5407708709/10000000000 : ℝ)*X 0 1+(5247121709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334194783/625000000 : ℝ)*X 1 0+(-2044794261/10000000000 : ℝ)*X 1 1+(524712171/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334194783/625000000 : ℝ)*X 2 0+(524712171/1000000000 : ℝ)*X 2 1+(-1022397131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301878757/10000000000 : ℝ)*X 0 0+(2065352137/5000000000 : ℝ)*X 0 1+(895876181/2000000000 : ℝ)*X 0 2+(4301878757/10000000000 : ℝ)*X 1 0+(2065352137/5000000000 : ℝ)*X 1 1+(895876181/2000000000 : ℝ)*X 1 2+(4301878757/10000000000 : ℝ)*X 2 0+(2065352137/5000000000 : ℝ)*X 2 1+(895876181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98152741/500000000 : ℝ)*X 0 0+(5247701559/10000000000 : ℝ)*X 0 1+(2703562943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82895743/156250000 : ℝ)*X 1 0+(-376958011/2000000000 : ℝ)*X 1 1+(2703563017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331583/625000 : ℝ)*X 2 0+(5407125689/10000000000 : ℝ)*X 2 1+(-471197479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301902931/10000000000 : ℝ)*X 0 0+(4478122401/10000000000 : ℝ)*X 0 1+(4131969517/10000000000 : ℝ)*X 0 2+(4301902931/10000000000 : ℝ)*X 1 0+(4478122401/10000000000 : ℝ)*X 1 1+(4131969517/10000000000 : ℝ)*X 1 2+(4301902931/10000000000 : ℝ)*X 2 0+(4478122401/10000000000 : ℝ)*X 2 1+(4131969517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22599293530909477767333/2435000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840918037/50000000000000 : ℝ)*(base19) + (48972767/3125000000000 : ℝ)*(base23) + (61335453/100000000000000 : ℝ)*(lower2) + (231717103/100000000000000 : ℝ)*(upper3) + (14767637/10000000000000 : ℝ)*(upper5) + (4547623741105117/100000000000000 : ℝ)*(major0) + (4547623741105117/100000000000000 : ℝ)*(major1) + (4547623741105117/100000000000000 : ℝ)*(major2) + (124543824499011/2000000000000 : ℝ)*(sp0) + (1245445011710411/20000000000000 : ℝ)*(sp1) + (1245445034651917/20000000000000 : ℝ)*(sp2) + (2868002727889719/100000000000000 : ℝ)*(sp3) + (1775771879/5000000000000 : ℝ)*(sp4) + (1106535307/6250000000000 : ℝ)*(sp7) + (358502554056829/12500000000000 : ℝ)*(f.failure) + (6227226740388129/100000000000000 : ℝ)*(f.sum) + (4031527386279/2435000000000000000000000000 : ℝ)*base65 + (319211150786053677/97400000000000000000000000000000 : ℝ)*base68 + (127727338880546323/97400000000000000000000000000000 : ℝ)*base69 + (694361033567853677/97400000000000000000000000000000 : ℝ)*base72 + (1519463482701/2435000000000000000000000000 : ℝ)*base74 + (696160730252546323/97400000000000000000000000000000 : ℝ)*base75 + (650439072383853677/97400000000000000000000000000000 : ℝ)*base78 + (123319595481946323/97400000000000000000000000000000 : ℝ)*base79 + (2143493464089/2435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1149153/1250000000000000000000 : ℝ)*base89 + (1149153/1250000000000000000000 : ℝ)*base91 + (1149153/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117274833875945540239300779/24350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39435449/6250000000000 : ℝ)*(base19) + (634054791/50000000000000 : ℝ)*(base23) + (68966893/25000000000000 : ℝ)*(lower1) + (8269501/100000000000000 : ℝ)*(upper2) + (106761463/100000000000000 : ℝ)*(upper3) + (2290361660713447/50000000000000 : ℝ)*(major0) + (2290361660713447/50000000000000 : ℝ)*(major1) + (2290361660713447/50000000000000 : ℝ)*(major2) + (2916181133/25000000000000 : ℝ)*(sp2) + (1245944011/100000000000000 : ℝ)*(sp3) + (6272551351758521/100000000000000 : ℝ)*(sp4) + (6272550720791337/100000000000000 : ℝ)*(sp5) + (6272538418924407/100000000000000 : ℝ)*(sp6) + (1444446942305373/50000000000000 : ℝ)*(sp7) + (722223782638689/25000000000000 : ℝ)*(f.failure) + (6272551351758521/100000000000000 : ℝ)*(f.sum) + (143944669973/2435000000000000000000000000 : ℝ)*base65 + (710577321648236407/48700000000000000000000000000000 : ℝ)*base68 + (207702288748963593/48700000000000000000000000000000 : ℝ)*base69 + (197378157226836407/48700000000000000000000000000000 : ℝ)*base72 + (3031102945547/2435000000000000000000000000 : ℝ)*base74 + (68703096856563593/48700000000000000000000000000000 : ℝ)*base75 + (28668883793236407/48700000000000000000000000000000 : ℝ)*base78 + (1188925615873036407/48700000000000000000000000000000 : ℝ)*base80 + (11071312012493/2435000000000000000000000000 : ℝ)*base81 + (31818827/2500000000000000000000 : ℝ)*base90 + (31818827/2500000000000000000000 : ℝ)*base92 + (31818827/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1439_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_s7_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963048521/10000000000 : ℝ)*x 0 + (2703841417/5000000000 : ℝ)*x 1 + (5247144187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963048521/10000000000 : ℝ)^4399 ≤ (1197846235957/10000000000000 : ℝ)^3375 := by
    have hnat : (1963048521 : ℕ)^4399*10000000000000^3375 ≤ 1197846235957^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963048521 10000000000 1197846235957 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703841417/5000000000 : ℝ)^4399 ≤ (44875038673523/100000000000000 : ℝ)^3375 := by
    have hnat : (2703841417 : ℕ)^4399*100000000000000^3375 ≤ 44875038673523^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703841417 5000000000 44875038673523 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247144187/10000000000 : ℝ)^4399 ≤ (8629299791671/20000000000000 : ℝ)^3375 := by
    have hnat : (5247144187 : ℕ)^4399*20000000000000^3375 ≤ 8629299791671^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247144187 10000000000 8629299791671 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963048521/10000000000 : ℝ), (2703841417/5000000000 : ℝ), (5247144187/10000000000 : ℝ)] ![(1197846235957/10000000000000 : ℝ), (44875038673523/100000000000000 : ℝ), (8629299791671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963048521/10000000000 : ℝ)|^4399 ≤ (1197846235957/10000000000000 : ℝ)^3375
        have hw : |(-1963048521/10000000000 : ℝ)|=(1963048521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703841417/5000000000 : ℝ)|^4399 ≤ (44875038673523/100000000000000 : ℝ)^3375
        have hw : |(2703841417/5000000000 : ℝ)|=(2703841417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247144187/10000000000 : ℝ)|^4399 ≤ (8629299791671/20000000000000 : ℝ)^3375
        have hw : |(5247144187/10000000000 : ℝ)|=(5247144187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s7_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336777333/2500000000 : ℝ)*x 0 + (-2044773737/10000000000 : ℝ)*x 1 + (5247144367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336777333/2500000000 : ℝ)^4399 ≤ (22110490579773/50000000000000 : ℝ)^3375 := by
    have hnat : (1336777333 : ℕ)^4399*50000000000000^3375 ≤ 22110490579773^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336777333 2500000000 22110490579773 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044773737/10000000000 : ℝ)^4399 ≤ (6316258968003/50000000000000 : ℝ)^3375 := by
    have hnat : (2044773737 : ℕ)^4399*50000000000000^3375 ≤ 6316258968003^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044773737 10000000000 6316258968003 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247144367/10000000000 : ℝ)^4399 ≤ (21573250443773/50000000000000 : ℝ)^3375 := by
    have hnat : (5247144367 : ℕ)^4399*50000000000000^3375 ≤ 21573250443773^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247144367 10000000000 21573250443773 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336777333/2500000000 : ℝ), (-2044773737/10000000000 : ℝ), (5247144367/10000000000 : ℝ)] ![(22110490579773/50000000000000 : ℝ), (6316258968003/50000000000000 : ℝ), (21573250443773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336777333/2500000000 : ℝ)|^4399 ≤ (22110490579773/50000000000000 : ℝ)^3375
        have hw : |(1336777333/2500000000 : ℝ)|=(1336777333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044773737/10000000000 : ℝ)|^4399 ≤ (6316258968003/50000000000000 : ℝ)^3375
        have hw : |(-2044773737/10000000000 : ℝ)|=(2044773737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247144367/10000000000 : ℝ)|^4399 ≤ (21573250443773/50000000000000 : ℝ)^3375
        have hw : |(5247144367/10000000000 : ℝ)|=(5247144367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s7_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347109311/10000000000 : ℝ)*x 0 + (1049428879/2000000000 : ℝ)*x 1 + (-63899179/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347109311/10000000000 : ℝ)^4399 ≤ (44220980933181/100000000000000 : ℝ)^3375 := by
    have hnat : (5347109311 : ℕ)^4399*100000000000000^3375 ≤ 44220980933181^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347109311 10000000000 44220980933181 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049428879/2000000000 : ℝ)^4399 ≤ (21573250593821/50000000000000 : ℝ)^3375 := by
    have hnat : (1049428879 : ℕ)^4399*50000000000000^3375 ≤ 21573250593821^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049428879 2000000000 21573250593821 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63899179/312500000 : ℝ)^4399 ≤ (6316258931767/50000000000000 : ℝ)^3375 := by
    have hnat : (63899179 : ℕ)^4399*50000000000000^3375 ≤ 6316258931767^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63899179 312500000 6316258931767 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347109311/10000000000 : ℝ), (1049428879/2000000000 : ℝ), (-63899179/312500000 : ℝ)] ![(44220980933181/100000000000000 : ℝ), (21573250593821/50000000000000 : ℝ), (6316258931767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347109311/10000000000 : ℝ)|^4399 ≤ (44220980933181/100000000000000 : ℝ)^3375
        have hw : |(5347109311/10000000000 : ℝ)|=(5347109311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049428879/2000000000 : ℝ)|^4399 ≤ (21573250593821/50000000000000 : ℝ)^3375
        have hw : |(1049428879/2000000000 : ℝ)|=(1049428879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63899179/312500000 : ℝ)|^4399 ≤ (6316258931767/50000000000000 : ℝ)^3375
        have hw : |(-63899179/312500000 : ℝ)|=(63899179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s7_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150940201/5000000000 : ℝ)*x 0 + (206537861/500000000 : ℝ)*x 1 + (223966381/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150940201/5000000000 : ℝ)^4399 ≤ (1665242786113/5000000000000 : ℝ)^3375 := by
    have hnat : (2150940201 : ℕ)^4399*5000000000000^3375 ≤ 1665242786113^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150940201 5000000000 1665242786113 5000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206537861/500000000 : ℝ)^4399 ≤ (15794294543743/50000000000000 : ℝ)^3375 := by
    have hnat : (206537861 : ℕ)^4399*50000000000000^3375 ≤ 15794294543743^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206537861 500000000 15794294543743 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223966381/500000000 : ℝ)^4399 ≤ (35106555179167/100000000000000 : ℝ)^3375 := by
    have hnat : (223966381 : ℕ)^4399*100000000000000^3375 ≤ 35106555179167^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223966381 500000000 35106555179167 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150940201/5000000000 : ℝ), (206537861/500000000 : ℝ), (223966381/500000000 : ℝ)] ![(1665242786113/5000000000000 : ℝ), (15794294543743/50000000000000 : ℝ), (35106555179167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150940201/5000000000 : ℝ)|^4399 ≤ (1665242786113/5000000000000 : ℝ)^3375
        have hw : |(2150940201/5000000000 : ℝ)|=(2150940201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206537861/500000000 : ℝ)|^4399 ≤ (15794294543743/50000000000000 : ℝ)^3375
        have hw : |(206537861/500000000 : ℝ)|=(206537861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223966381/500000000 : ℝ)|^4399 ≤ (35106555179167/100000000000000 : ℝ)^3375
        have hw : |(223966381/500000000 : ℝ)|=(223966381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s7_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1963059747/10000000000 : ℝ)*x 0 + (524772367/1000000000 : ℝ)*x 1 + (84485943/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963059747/10000000000 : ℝ)^4399 ≤ (11978551643981/100000000000000 : ℝ)^3375 := by
    have hnat : (1963059747 : ℕ)^4399*100000000000000^3375 ≤ 11978551643981^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963059747 10000000000 11978551643981 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524772367/1000000000 : ℝ)^4399 ≤ (2157635490191/5000000000000 : ℝ)^3375 := by
    have hnat : (524772367 : ℕ)^4399*5000000000000^3375 ≤ 2157635490191^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524772367 1000000000 2157635490191 5000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84485943/156250000 : ℝ)^4399 ≤ (44868738547727/100000000000000 : ℝ)^3375 := by
    have hnat : (84485943 : ℕ)^4399*100000000000000^3375 ≤ 44868738547727^3375*156250000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84485943 156250000 44868738547727 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1963059747/10000000000 : ℝ), (524772367/1000000000 : ℝ), (84485943/156250000 : ℝ)] ![(11978551643981/100000000000000 : ℝ), (2157635490191/5000000000000 : ℝ), (44868738547727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1963059747/10000000000 : ℝ)|^4399 ≤ (11978551643981/100000000000000 : ℝ)^3375
        have hw : |(-1963059747/10000000000 : ℝ)|=(1963059747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524772367/1000000000 : ℝ)|^4399 ≤ (2157635490191/5000000000000 : ℝ)^3375
        have hw : |(524772367/1000000000 : ℝ)|=(524772367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84485943/156250000 : ℝ)|^4399 ≤ (44868738547727/100000000000000 : ℝ)^3375
        have hw : |(84485943/156250000 : ℝ)|=(84485943/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s7_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301905343/10000000000 : ℝ)*x 0 + (4478069341/10000000000 : ℝ)*x 1 + (2066010723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301905343/10000000000 : ℝ)^4399 ≤ (8326276849833/25000000000000 : ℝ)^3375 := by
    have hnat : (4301905343 : ℕ)^4399*25000000000000^3375 ≤ 8326276849833^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301905343 10000000000 8326276849833 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478069341/10000000000 : ℝ)^4399 ≤ (7018740379571/20000000000000 : ℝ)^3375 := by
    have hnat : (4478069341 : ℕ)^4399*20000000000000^3375 ≤ 7018740379571^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478069341 10000000000 7018740379571 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066010723/5000000000 : ℝ)^4399 ≤ (31601190685523/100000000000000 : ℝ)^3375 := by
    have hnat : (2066010723 : ℕ)^4399*100000000000000^3375 ≤ 31601190685523^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066010723 5000000000 31601190685523 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301905343/10000000000 : ℝ), (4478069341/10000000000 : ℝ), (2066010723/5000000000 : ℝ)] ![(8326276849833/25000000000000 : ℝ), (7018740379571/20000000000000 : ℝ), (31601190685523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301905343/10000000000 : ℝ)|^4399 ≤ (8326276849833/25000000000000 : ℝ)^3375
        have hw : |(4301905343/10000000000 : ℝ)|=(4301905343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478069341/10000000000 : ℝ)|^4399 ≤ (7018740379571/20000000000000 : ℝ)^3375
        have hw : |(4478069341/10000000000 : ℝ)|=(4478069341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066010723/5000000000 : ℝ)|^4399 ≤ (31601190685523/100000000000000 : ℝ)^3375
        have hw : |(2066010723/5000000000 : ℝ)|=(2066010723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/625 : ℝ) ^ (2199/512 : ℝ) ≤ (274014631585517/3125000000000000000 : ℝ) := by
    have hpowers : (71/625 : ℝ)^2199 ≤ (274014631585517/3125000000000000000 : ℝ)^512 := by
      have hnat : (71 : ℕ)^2199*3125000000000000000^512 ≤ 274014631585517^512*625^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 625 274014631585517 3125000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/625 : ℝ)) (X := (274014631585517/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (2199/512 : ℝ) ≤ (6752794871956891/25000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^2199 ≤ (6752794871956891/25000000000000000000 : ℝ)^512 := by
      have hnat : (7381 : ℕ)^2199*25000000000000000000^512 ≤ 6752794871956891^512*50000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 6752794871956891 25000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (6752794871956891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562774014631585517/1562500000000000000 : ℝ) ≤ (2000081658094677/2000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (1562774014631585517/1562500000000000000 : ℝ)^512 ≤ (2000081658094677/2000000000000000 : ℝ)^2199 := by
      have hnat : (1562774014631585517 : ℕ)^512*2000000000000000^2199 ≤ 2000081658094677^2199*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562774014631585517 1562500000000000000 2000081658094677 2000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081658094677/2000000000000000 : ℝ)) (X := (1562774014631585517/1562500000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008944911924641027/25000000000000000000 : ℝ) ≤ (5000416477170059/5000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (25008944911924641027/25000000000000000000 : ℝ)^512 ≤ (5000416477170059/5000000000000000 : ℝ)^2199 := by
      have hnat : (25008944911924641027 : ℕ)^512*5000000000000000^2199 ≤ 5000416477170059^2199*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008944911924641027 25000000000000000000 5000416477170059 5000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000416477170059/5000000000000000 : ℝ)) (X := (25008944911924641027/25000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506752794871956891/12500000000000000000 : ℝ) ≤ (10001257618206851/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12506752794871956891/12500000000000000000 : ℝ)^512 ≤ (10001257618206851/10000000000000000 : ℝ)^2199 := by
      have hnat : (12506752794871956891 : ℕ)^512*10000000000000000^2199 ≤ 10001257618206851^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506752794871956891 12500000000000000000 10001257618206851 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001257618206851/10000000000000000 : ℝ)) (X := (12506752794871956891/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(274014631585517/3125000000000000000 : ℝ) ≤ ((3401174064113828201/3402000000000000000 : ℝ)+2*(424663866733/340200000000000 : ℝ)*(71/625 : ℝ))^(2199/512 : ℝ) := by
    rw [show (3401174064113828201/3402000000000000000 : ℝ)+2*(424663866733/340200000000000 : ℝ)*(71/625 : ℝ)=(2000081658094677/2000000000000000 : ℝ) by norm_num, show 1+2*(274014631585517/3125000000000000000 : ℝ)=(1562774014631585517/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6752794871956891/25000000000000000000 : ℝ)+(274014631585517/3125000000000000000 : ℝ) ≤ ((3401174064113828201/3402000000000000000 : ℝ)+(424663866733/340200000000000 : ℝ)*((7381/50000 : ℝ)+(71/625 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (3401174064113828201/3402000000000000000 : ℝ)+(424663866733/340200000000000 : ℝ)*((7381/50000 : ℝ)+(71/625 : ℝ))=(5000416477170059/5000000000000000 : ℝ) by norm_num, show 1+(6752794871956891/25000000000000000000 : ℝ)+(274014631585517/3125000000000000000 : ℝ)=(25008944911924641027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6752794871956891/25000000000000000000 : ℝ) ≤ ((3401174064113828201/3402000000000000000 : ℝ)+2*(424663866733/340200000000000 : ℝ)*(7381/50000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (3401174064113828201/3402000000000000000 : ℝ)+2*(424663866733/340200000000000 : ℝ)*(7381/50000 : ℝ)=(10001257618206851/10000000000000000 : ℝ) by norm_num, show 1+2*(6752794871956891/25000000000000000000 : ℝ)=(12506752794871956891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3401174064113828201/3402000000000000000 : ℝ)*(X 1 0+X 2 0)+(424663866733/340200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (3401174064113828201/3402000000000000000 : ℝ)) (alpha := (424663866733/340200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3401174064113828201/3402000000000000000 : ℝ)*(X 0 1+X 2 1)+(424663866733/340200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (3401174064113828201/3402000000000000000 : ℝ)) (alpha := (424663866733/340200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3401174064113828201/3402000000000000000 : ℝ)*(X 0 2+X 1 2)+(424663866733/340200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (3401174064113828201/3402000000000000000 : ℝ)) (alpha := (424663866733/340200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1963048521/10000000000 : ℝ)*X 0 0+(2703841417/5000000000 : ℝ)*X 0 1+(5247144187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336777333/2500000000 : ℝ)*X 1 0+(-2044773737/10000000000 : ℝ)*X 1 1+(5247144367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347109311/10000000000 : ℝ)*X 2 0+(1049428879/2000000000 : ℝ)*X 2 1+(-63899179/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150940201/5000000000 : ℝ)*X 0 0+(206537861/500000000 : ℝ)*X 0 1+(223966381/500000000 : ℝ)*X 0 2+(2150940201/5000000000 : ℝ)*X 1 0+(206537861/500000000 : ℝ)*X 1 1+(223966381/500000000 : ℝ)*X 1 2+(2150940201/5000000000 : ℝ)*X 2 0+(206537861/500000000 : ℝ)*X 2 1+(223966381/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1963059747/10000000000 : ℝ)*X 0 0+(524772367/1000000000 : ℝ)*X 0 1+(84485943/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4301905343/10000000000 : ℝ)*X 0 0+(4478069341/10000000000 : ℝ)*X 0 1+(2066010723/5000000000 : ℝ)*X 0 2+(4301905343/10000000000 : ℝ)*X 1 0+(4478069341/10000000000 : ℝ)*X 1 1+(2066010723/5000000000 : ℝ)*X 1 2+(4301905343/10000000000 : ℝ)*X 2 0+(4478069341/10000000000 : ℝ)*X 2 1+(2066010723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61876896106389831669325289/18900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (563442839/50000000000000 : ℝ)*(base19) + (796424781/100000000000000 : ℝ)*(base23) + (30890313/12500000000000 : ℝ)*(upper3) + (163619981/100000000000000 : ℝ)*(upper4) + (38959617/100000000000000 : ℝ)*(upper5) + (4548979824504511/100000000000000 : ℝ)*(major0) + (4548979824504511/100000000000000 : ℝ)*(major1) + (4548979824504511/100000000000000 : ℝ)*(major2) + (3114529415564073/50000000000000 : ℝ)*(sp0) + (6229082748197493/100000000000000 : ℝ)*(sp1) + (622908307865839/10000000000000 : ℝ)*(sp2) + (179304135198307/6250000000000 : ℝ)*(sp3) + (1001758201/4000000000000 : ℝ)*(sp4) + (1900324521/20000000000000 : ℝ)*(sp5) + (1434437832397759/50000000000000 : ℝ)*(f.failure) + (6229083875083171/100000000000000 : ℝ)*(f.sum) + (24307923582583/17010000000000000000000000000 : ℝ)*base65 + (26382490113206891/16200000000000000000000000000000 : ℝ)*base67 + (99334218122606891/16200000000000000000000000000000 : ℝ)*base69 + (15829998746006891/16200000000000000000000000000000 : ℝ)*base71 + (42792040698523/17010000000000000000000000000 : ℝ)*base73 + (136386601692806891/16200000000000000000000000000000 : ℝ)*base75 + (152590971999206891/16200000000000000000000000000000 : ℝ)*base77 + (24408738230006891/16200000000000000000000000000000 : ℝ)*base79 + (41478838999063/17010000000000000000000000000 : ℝ)*base81 + (3234837/5000000000000000000000 : ℝ)*base90 + (3234837/5000000000000000000000 : ℝ)*base92 + (3234837/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1439_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_box_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180310241/1000000000 : ℝ)*x 0 + (5385828679/10000000000 : ℝ)*x 1 + (1077165783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180310241/1000000000 : ℝ)^4399 ≤ (1340298351391/12500000000000 : ℝ)^3375 := by
    have hnat : (180310241 : ℕ)^4399*12500000000000^3375 ≤ 1340298351391^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180310241 1000000000 1340298351391 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385828679/10000000000 : ℝ)^4399 ≤ (1115970132699/2500000000000 : ℝ)^3375 := by
    have hnat : (5385828679 : ℕ)^4399*2500000000000^3375 ≤ 1115970132699^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385828679 10000000000 1115970132699 2500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077165783/2000000000 : ℝ)^4399 ≤ (44638807857443/100000000000000 : ℝ)^3375 := by
    have hnat : (1077165783 : ℕ)^4399*100000000000000^3375 ≤ 44638807857443^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077165783 2000000000 44638807857443 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180310241/1000000000 : ℝ), (5385828679/10000000000 : ℝ), (1077165783/2000000000 : ℝ)] ![(1340298351391/12500000000000 : ℝ), (1115970132699/2500000000000 : ℝ), (44638807857443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180310241/1000000000 : ℝ)|^4399 ≤ (1340298351391/12500000000000 : ℝ)^3375
        have hw : |(-180310241/1000000000 : ℝ)|=(180310241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385828679/10000000000 : ℝ)|^4399 ≤ (1115970132699/2500000000000 : ℝ)^3375
        have hw : |(5385828679/10000000000 : ℝ)|=(5385828679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077165783/2000000000 : ℝ)|^4399 ≤ (44638807857443/100000000000000 : ℝ)^3375
        have hw : |(1077165783/2000000000 : ℝ)|=(1077165783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165191647/312500000 : ℝ)*x 0 + (-242513903/1250000000 : ℝ)*x 1 + (2692914291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165191647/312500000 : ℝ)^4399 ≤ (10891209378891/25000000000000 : ℝ)^3375 := by
    have hnat : (165191647 : ℕ)^4399*25000000000000^3375 ≤ 10891209378891^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165191647 312500000 10891209378891 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242513903/1250000000 : ℝ)^4399 ≤ (11796358206367/100000000000000 : ℝ)^3375 := by
    have hnat : (242513903 : ℕ)^4399*100000000000000^3375 ≤ 11796358206367^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242513903 1250000000 11796358206367 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692914291/5000000000 : ℝ)^4399 ≤ (44638804260079/100000000000000 : ℝ)^3375 := by
    have hnat : (2692914291 : ℕ)^4399*100000000000000^3375 ≤ 44638804260079^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692914291 5000000000 44638804260079 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165191647/312500000 : ℝ), (-242513903/1250000000 : ℝ), (2692914291/5000000000 : ℝ)] ![(10891209378891/25000000000000 : ℝ), (11796358206367/100000000000000 : ℝ), (44638804260079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165191647/312500000 : ℝ)|^4399 ≤ (10891209378891/25000000000000 : ℝ)^3375
        have hw : |(165191647/312500000 : ℝ)|=(165191647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242513903/1250000000 : ℝ)|^4399 ≤ (11796358206367/100000000000000 : ℝ)^3375
        have hw : |(-242513903/1250000000 : ℝ)|=(242513903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692914291/5000000000 : ℝ)|^4399 ≤ (44638804260079/100000000000000 : ℝ)^3375
        have hw : |(2692914291/5000000000 : ℝ)|=(2692914291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286132487/10000000000 : ℝ)*x 0 + (2692914283/5000000000 : ℝ)*x 1 + (-97005577/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286132487/10000000000 : ℝ)^4399 ≤ (43564835184587/100000000000000 : ℝ)^3375 := by
    have hnat : (5286132487 : ℕ)^4399*100000000000000^3375 ≤ 43564835184587^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286132487 10000000000 43564835184587 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692914283/5000000000 : ℝ)^4399 ≤ (697481313863/1562500000000 : ℝ)^3375 := by
    have hnat : (2692914283 : ℕ)^4399*1562500000000^3375 ≤ 697481313863^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692914283 5000000000 697481313863 1562500000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97005577/500000000 : ℝ)^4399 ≤ (294909017767/2500000000000 : ℝ)^3375 := by
    have hnat : (97005577 : ℕ)^4399*2500000000000^3375 ≤ 294909017767^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97005577 500000000 294909017767 2500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286132487/10000000000 : ℝ), (2692914283/5000000000 : ℝ), (-97005577/500000000 : ℝ)] ![(43564835184587/100000000000000 : ℝ), (697481313863/1562500000000 : ℝ), (294909017767/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286132487/10000000000 : ℝ)|^4399 ≤ (43564835184587/100000000000000 : ℝ)^3375
        have hw : |(5286132487/10000000000 : ℝ)|=(5286132487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692914283/5000000000 : ℝ)|^4399 ≤ (697481313863/1562500000000 : ℝ)^3375
        have hw : |(2692914283/5000000000 : ℝ)|=(2692914283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97005577/500000000 : ℝ)|^4399 ≤ (294909017767/2500000000000 : ℝ)^3375
        have hw : |(-97005577/500000000 : ℝ)|=(97005577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4447981301/10000000000 : ℝ)*x 0 + (4232519557/10000000000 : ℝ)*x 1 + (1058129801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4447981301/10000000000 : ℝ)^4399 ≤ (8696670087217/25000000000000 : ℝ)^3375 := by
    have hnat : (4447981301 : ℕ)^4399*25000000000000^3375 ≤ 8696670087217^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447981301 10000000000 8696670087217 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232519557/10000000000 : ℝ)^4399 ≤ (127369771833/390625000000 : ℝ)^3375 := by
    have hnat : (4232519557 : ℕ)^4399*390625000000^3375 ≤ 127369771833^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232519557 10000000000 127369771833 390625000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058129801/2500000000 : ℝ)^4399 ≤ (2037916127793/6250000000000 : ℝ)^3375 := by
    have hnat : (1058129801 : ℕ)^4399*6250000000000^3375 ≤ 2037916127793^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058129801 2500000000 2037916127793 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4447981301/10000000000 : ℝ), (4232519557/10000000000 : ℝ), (1058129801/2500000000 : ℝ)] ![(8696670087217/25000000000000 : ℝ), (127369771833/390625000000 : ℝ), (2037916127793/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4447981301/10000000000 : ℝ)|^4399 ≤ (8696670087217/25000000000000 : ℝ)^3375
        have hw : |(4447981301/10000000000 : ℝ)|=(4447981301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232519557/10000000000 : ℝ)|^4399 ≤ (127369771833/390625000000 : ℝ)^3375
        have hw : |(4232519557/10000000000 : ℝ)|=(4232519557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058129801/2500000000 : ℝ)|^4399 ≤ (2037916127793/6250000000000 : ℝ)^3375
        have hw : |(1058129801/2500000000 : ℝ)|=(1058129801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-425144503/2000000000 : ℝ)*x 0 + (5266669581/10000000000 : ℝ)*x 1 + (658333719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425144503/2000000000 : ℝ)^4399 ≤ (332205710697/2500000000000 : ℝ)^3375 := by
    have hnat : (425144503 : ℕ)^4399*2500000000000^3375 ≤ 332205710697^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425144503 2000000000 332205710697 2500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266669581/10000000000 : ℝ)^4399 ≤ (43355884860687/100000000000000 : ℝ)^3375 := by
    have hnat : (5266669581 : ℕ)^4399*100000000000000^3375 ≤ 43355884860687^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266669581 10000000000 43355884860687 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658333719/1250000000 : ℝ)^4399 ≤ (8671177339097/20000000000000 : ℝ)^3375 := by
    have hnat : (658333719 : ℕ)^4399*20000000000000^3375 ≤ 8671177339097^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658333719 1250000000 8671177339097 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425144503/2000000000 : ℝ), (5266669581/10000000000 : ℝ), (658333719/1250000000 : ℝ)] ![(332205710697/2500000000000 : ℝ), (43355884860687/100000000000000 : ℝ), (8671177339097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425144503/2000000000 : ℝ)|^4399 ≤ (332205710697/2500000000000 : ℝ)^3375
        have hw : |(-425144503/2000000000 : ℝ)|=(425144503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266669581/10000000000 : ℝ)|^4399 ≤ (43355884860687/100000000000000 : ℝ)^3375
        have hw : |(5266669581/10000000000 : ℝ)|=(5266669581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658333719/1250000000 : ℝ)|^4399 ≤ (8671177339097/20000000000000 : ℝ)^3375
        have hw : |(658333719/1250000000 : ℝ)|=(658333719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342372983/2500000000 : ℝ)*x 0 + (-497138407/2500000000 : ℝ)*x 1 + (5266669641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342372983/2500000000 : ℝ)^4399 ≤ (8892480478031/20000000000000 : ℝ)^3375 := by
    have hnat : (1342372983 : ℕ)^4399*20000000000000^3375 ≤ 8892480478031^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342372983 2500000000 8892480478031 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497138407/2500000000 : ℝ)^4399 ≤ (6090856043709/50000000000000 : ℝ)^3375 := by
    have hnat : (497138407 : ℕ)^4399*50000000000000^3375 ≤ 6090856043709^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497138407 2500000000 6090856043709 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266669641/10000000000 : ℝ)^4399 ≤ (1734235420179/4000000000000 : ℝ)^3375 := by
    have hnat : (5266669641 : ℕ)^4399*4000000000000^3375 ≤ 1734235420179^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266669641 10000000000 1734235420179 4000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342372983/2500000000 : ℝ), (-497138407/2500000000 : ℝ), (5266669641/10000000000 : ℝ)] ![(8892480478031/20000000000000 : ℝ), (6090856043709/50000000000000 : ℝ), (1734235420179/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342372983/2500000000 : ℝ)|^4399 ≤ (8892480478031/20000000000000 : ℝ)^3375
        have hw : |(1342372983/2500000000 : ℝ)|=(1342372983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497138407/2500000000 : ℝ)|^4399 ≤ (6090856043709/50000000000000 : ℝ)^3375
        have hw : |(-497138407/2500000000 : ℝ)|=(497138407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266669641/10000000000 : ℝ)|^4399 ≤ (1734235420179/4000000000000 : ℝ)^3375
        have hw : |(5266669641/10000000000 : ℝ)|=(5266669641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369491751/10000000000 : ℝ)*x 0 + (658333709/1250000000 : ℝ)*x 1 + (-198855383/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369491751/10000000000 : ℝ)^4399 ≤ (5557800054579/12500000000000 : ℝ)^3375 := by
    have hnat : (5369491751 : ℕ)^4399*12500000000000^3375 ≤ 5557800054579^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369491751 10000000000 5557800054579 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658333709/1250000000 : ℝ)^4399 ≤ (433558858371/1000000000000 : ℝ)^3375 := by
    have hnat : (658333709 : ℕ)^4399*1000000000000^3375 ≤ 433558858371^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658333709 1250000000 433558858371 1000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198855383/1000000000 : ℝ)^4399 ≤ (121817137003/1000000000000 : ℝ)^3375 := by
    have hnat : (198855383 : ℕ)^4399*1000000000000^3375 ≤ 121817137003^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198855383 1000000000 121817137003 1000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369491751/10000000000 : ℝ), (658333709/1250000000 : ℝ), (-198855383/1000000000 : ℝ)] ![(5557800054579/12500000000000 : ℝ), (433558858371/1000000000000 : ℝ), (121817137003/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369491751/10000000000 : ℝ)|^4399 ≤ (5557800054579/12500000000000 : ℝ)^3375
        have hw : |(5369491751/10000000000 : ℝ)|=(5369491751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658333709/1250000000 : ℝ)|^4399 ≤ (433558858371/1000000000000 : ℝ)^3375
        have hw : |(658333709/1250000000 : ℝ)|=(658333709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198855383/1000000000 : ℝ)|^4399 ≤ (121817137003/1000000000000 : ℝ)^3375
        have hw : |(-198855383/1000000000 : ℝ)|=(198855383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154717601/10000000000 : ℝ)*x 0 + (437910041/1000000000 : ℝ)*x 1 + (437910083/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154717601/10000000000 : ℝ)^4399 ≤ (15913810514939/50000000000000 : ℝ)^3375 := by
    have hnat : (4154717601 : ℕ)^4399*50000000000000^3375 ≤ 15913810514939^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154717601 10000000000 15913810514939 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437910041/1000000000 : ℝ)^4399 ≤ (17043093674277/50000000000000 : ℝ)^3375 := by
    have hnat : (437910041 : ℕ)^4399*50000000000000^3375 ≤ 17043093674277^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437910041 1000000000 17043093674277 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437910083/1000000000 : ℝ)^4399 ≤ (34086191609667/100000000000000 : ℝ)^3375 := by
    have hnat : (437910083 : ℕ)^4399*100000000000000^3375 ≤ 34086191609667^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437910083 1000000000 34086191609667 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154717601/10000000000 : ℝ), (437910041/1000000000 : ℝ), (437910083/1000000000 : ℝ)] ![(15913810514939/50000000000000 : ℝ), (17043093674277/50000000000000 : ℝ), (34086191609667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154717601/10000000000 : ℝ)|^4399 ≤ (15913810514939/50000000000000 : ℝ)^3375
        have hw : |(4154717601/10000000000 : ℝ)|=(4154717601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(437910041/1000000000 : ℝ)|^4399 ≤ (17043093674277/50000000000000 : ℝ)^3375
        have hw : |(437910041/1000000000 : ℝ)|=(437910041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(437910083/1000000000 : ℝ)|^4399 ≤ (34086191609667/100000000000000 : ℝ)^3375
        have hw : |(437910083/1000000000 : ℝ)|=(437910083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_8 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411549561/2000000000 : ℝ)*x 0 + (1036840621/2000000000 : ℝ)*x 1 + (1349949293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411549561/2000000000 : ℝ)^4399 ≤ (3184272654033/25000000000000 : ℝ)^3375 := by
    have hnat : (411549561 : ℕ)^4399*25000000000000^3375 ≤ 3184272654033^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411549561 2000000000 3184272654033 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036840621/2000000000 : ℝ)^4399 ≤ (5309143067071/12500000000000 : ℝ)^3375 := by
    have hnat : (1036840621 : ℕ)^4399*12500000000000^3375 ≤ 5309143067071^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036840621 2000000000 5309143067071 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349949293/2500000000 : ℝ)^4399 ≤ (44789764827809/100000000000000 : ℝ)^3375 := by
    have hnat : (1349949293 : ℕ)^4399*100000000000000^3375 ≤ 44789764827809^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349949293 2500000000 44789764827809 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411549561/2000000000 : ℝ), (1036840621/2000000000 : ℝ), (1349949293/2500000000 : ℝ)] ![(3184272654033/25000000000000 : ℝ), (5309143067071/12500000000000 : ℝ), (44789764827809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411549561/2000000000 : ℝ)|^4399 ≤ (3184272654033/25000000000000 : ℝ)^3375
        have hw : |(-411549561/2000000000 : ℝ)|=(411549561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036840621/2000000000 : ℝ)|^4399 ≤ (5309143067071/12500000000000 : ℝ)^3375
        have hw : |(1036840621/2000000000 : ℝ)|=(1036840621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349949293/2500000000 : ℝ)|^4399 ≤ (44789764827809/100000000000000 : ℝ)^3375
        have hw : |(1349949293/2500000000 : ℝ)|=(1349949293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_9 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527635717/1000000000 : ℝ)*x 0 + (-967153601/5000000000 : ℝ)*x 1 + (674974569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527635717/1000000000 : ℝ)^4399 ≤ (43459859875631/100000000000000 : ℝ)^3375 := by
    have hnat : (527635717 : ℕ)^4399*100000000000000^3375 ≤ 43459859875631^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527635717 1000000000 43459859875631 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967153601/5000000000 : ℝ)^4399 ≤ (5875190992341/50000000000000 : ℝ)^3375 := by
    have hnat : (967153601 : ℕ)^4399*50000000000000^3375 ≤ 5875190992341^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967153601 5000000000 5875190992341 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674974569/1250000000 : ℝ)^4399 ≤ (11197439531187/25000000000000 : ℝ)^3375 := by
    have hnat : (674974569 : ℕ)^4399*25000000000000^3375 ≤ 11197439531187^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674974569 1250000000 11197439531187 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527635717/1000000000 : ℝ), (-967153601/5000000000 : ℝ), (674974569/1250000000 : ℝ)] ![(43459859875631/100000000000000 : ℝ), (5875190992341/50000000000000 : ℝ), (11197439531187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527635717/1000000000 : ℝ)|^4399 ≤ (43459859875631/100000000000000 : ℝ)^3375
        have hw : |(527635717/1000000000 : ℝ)|=(527635717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-967153601/5000000000 : ℝ)|^4399 ≤ (5875190992341/50000000000000 : ℝ)^3375
        have hw : |(-967153601/5000000000 : ℝ)|=(967153601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674974569/1250000000 : ℝ)|^4399 ≤ (11197439531187/25000000000000 : ℝ)^3375
        have hw : |(674974569/1250000000 : ℝ)|=(674974569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_10 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638178557/5000000000 : ℝ)*x 0 + (337487257/625000000 : ℝ)*x 1 + (-1934307879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638178557/5000000000 : ℝ)^4399 ≤ (43459859274427/100000000000000 : ℝ)^3375 := by
    have hnat : (2638178557 : ℕ)^4399*100000000000000^3375 ≤ 43459859274427^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638178557 5000000000 43459859274427 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337487257/625000000 : ℝ)^4399 ≤ (5598719170967/12500000000000 : ℝ)^3375 := by
    have hnat : (337487257 : ℕ)^4399*12500000000000^3375 ≤ 5598719170967^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337487257 625000000 5598719170967 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934307879/10000000000 : ℝ)^4399 ≤ (587519367253/5000000000000 : ℝ)^3375 := by
    have hnat : (1934307879 : ℕ)^4399*5000000000000^3375 ≤ 587519367253^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934307879 10000000000 587519367253 5000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638178557/5000000000 : ℝ), (337487257/625000000 : ℝ), (-1934307879/10000000000 : ℝ)] ![(43459859274427/100000000000000 : ℝ), (5598719170967/12500000000000 : ℝ), (587519367253/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638178557/5000000000 : ℝ)|^4399 ≤ (43459859274427/100000000000000 : ℝ)^3375
        have hw : |(2638178557/5000000000 : ℝ)|=(2638178557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337487257/625000000 : ℝ)|^4399 ≤ (5598719170967/12500000000000 : ℝ)^3375
        have hw : |(337487257/625000000 : ℝ)|=(337487257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934307879/10000000000 : ℝ)|^4399 ≤ (587519367253/5000000000000 : ℝ)^3375
        have hw : |(-1934307879/10000000000 : ℝ)|=(1934307879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_11 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240900649/5000000000 : ℝ)*x 0 + (4215321793/10000000000 : ℝ)*x 1 + (4215322861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240900649/5000000000 : ℝ)^4399 ≤ (3513182691759/10000000000000 : ℝ)^3375 := by
    have hnat : (2240900649 : ℕ)^4399*10000000000000^3375 ≤ 3513182691759^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240900649 5000000000 3513182691759 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4215321793/10000000000 : ℝ)^4399 ≤ (6486816236079/20000000000000 : ℝ)^3375 := by
    have hnat : (4215321793 : ℕ)^4399*20000000000000^3375 ≤ 6486816236079^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215321793 10000000000 6486816236079 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4215322861/10000000000 : ℝ)^4399 ≤ (6486818378241/20000000000000 : ℝ)^3375 := by
    have hnat : (4215322861 : ℕ)^4399*20000000000000^3375 ≤ 6486818378241^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215322861 10000000000 6486818378241 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240900649/5000000000 : ℝ), (4215321793/10000000000 : ℝ), (4215322861/10000000000 : ℝ)] ![(3513182691759/10000000000000 : ℝ), (6486816236079/20000000000000 : ℝ), (6486818378241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240900649/5000000000 : ℝ)|^4399 ≤ (3513182691759/10000000000000 : ℝ)^3375
        have hw : |(2240900649/5000000000 : ℝ)|=(2240900649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4215321793/10000000000 : ℝ)|^4399 ≤ (6486816236079/20000000000000 : ℝ)^3375
        have hw : |(4215321793/10000000000 : ℝ)|=(4215321793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4215322861/10000000000 : ℝ)|^4399 ≤ (6486818378241/20000000000000 : ℝ)^3375
        have hw : |(4215322861/10000000000 : ℝ)|=(4215322861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_12 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871240291/10000000000 : ℝ)*x 0 + (5466290247/10000000000 : ℝ)*x 1 + (5255539209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871240291/10000000000 : ℝ)^4399 ≤ (11253517143571/100000000000000 : ℝ)^3375 := by
    have hnat : (1871240291 : ℕ)^4399*100000000000000^3375 ≤ 11253517143571^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871240291 10000000000 11253517143571 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466290247/10000000000 : ℝ)^4399 ≤ (11377496619959/25000000000000 : ℝ)^3375 := by
    have hnat : (5466290247 : ℕ)^4399*25000000000000^3375 ≤ 11377496619959^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466290247 10000000000 11377496619959 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255539209/10000000000 : ℝ)^4399 ≤ (43236496354413/100000000000000 : ℝ)^3375 := by
    have hnat : (5255539209 : ℕ)^4399*100000000000000^3375 ≤ 43236496354413^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255539209 10000000000 43236496354413 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871240291/10000000000 : ℝ), (5466290247/10000000000 : ℝ), (5255539209/10000000000 : ℝ)] ![(11253517143571/100000000000000 : ℝ), (11377496619959/25000000000000 : ℝ), (43236496354413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871240291/10000000000 : ℝ)|^4399 ≤ (11253517143571/100000000000000 : ℝ)^3375
        have hw : |(-1871240291/10000000000 : ℝ)|=(1871240291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466290247/10000000000 : ℝ)|^4399 ≤ (11377496619959/25000000000000 : ℝ)^3375
        have hw : |(5466290247/10000000000 : ℝ)|=(5466290247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255539209/10000000000 : ℝ)|^4399 ≤ (43236496354413/100000000000000 : ℝ)^3375
        have hw : |(5255539209/10000000000 : ℝ)|=(5255539209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_13 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688638583/5000000000 : ℝ)*x 0 + (-996489927/5000000000 : ℝ)*x 1 + (5255538433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688638583/5000000000 : ℝ)^4399 ≤ (44546446458809/100000000000000 : ℝ)^3375 := by
    have hnat : (2688638583 : ℕ)^4399*100000000000000^3375 ≤ 44546446458809^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688638583 5000000000 44546446458809 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996489927/5000000000 : ℝ)^4399 ≤ (12217065499923/100000000000000 : ℝ)^3375 := by
    have hnat : (996489927 : ℕ)^4399*100000000000000^3375 ≤ 12217065499923^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996489927 5000000000 12217065499923 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255538433/10000000000 : ℝ)^4399 ≤ (43236488033421/100000000000000 : ℝ)^3375 := by
    have hnat : (5255538433 : ℕ)^4399*100000000000000^3375 ≤ 43236488033421^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255538433 10000000000 43236488033421 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688638583/5000000000 : ℝ), (-996489927/5000000000 : ℝ), (5255538433/10000000000 : ℝ)] ![(44546446458809/100000000000000 : ℝ), (12217065499923/100000000000000 : ℝ), (43236488033421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688638583/5000000000 : ℝ)|^4399 ≤ (44546446458809/100000000000000 : ℝ)^3375
        have hw : |(2688638583/5000000000 : ℝ)|=(2688638583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996489927/5000000000 : ℝ)|^4399 ≤ (12217065499923/100000000000000 : ℝ)^3375
        have hw : |(-996489927/5000000000 : ℝ)|=(996489927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255538433/10000000000 : ℝ)|^4399 ≤ (43236488033421/100000000000000 : ℝ)^3375
        have hw : |(5255538433/10000000000 : ℝ)|=(5255538433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_14 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215091079/400000000 : ℝ)*x 0 + (656942431/1250000000 : ℝ)*x 1 + (-1992978749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215091079/400000000 : ℝ)^4399 ≤ (44546444396451/100000000000000 : ℝ)^3375 := by
    have hnat : (215091079 : ℕ)^4399*100000000000000^3375 ≤ 44546444396451^3375*400000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215091079 400000000 44546444396451 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656942431/1250000000 : ℝ)^4399 ≤ (43236498917193/100000000000000 : ℝ)^3375 := by
    have hnat : (656942431 : ℕ)^4399*100000000000000^3375 ≤ 43236498917193^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656942431 1250000000 43236498917193 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1992978749/10000000000 : ℝ)^4399 ≤ (12217056671027/100000000000000 : ℝ)^3375 := by
    have hnat : (1992978749 : ℕ)^4399*100000000000000^3375 ≤ 12217056671027^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992978749 10000000000 12217056671027 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215091079/400000000 : ℝ), (656942431/1250000000 : ℝ), (-1992978749/10000000000 : ℝ)] ![(44546444396451/100000000000000 : ℝ), (43236498917193/100000000000000 : ℝ), (12217056671027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215091079/400000000 : ℝ)|^4399 ≤ (44546444396451/100000000000000 : ℝ)^3375
        have hw : |(215091079/400000000 : ℝ)|=(215091079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656942431/1250000000 : ℝ)|^4399 ≤ (43236498917193/100000000000000 : ℝ)^3375
        have hw : |(656942431/1250000000 : ℝ)|=(656942431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1992978749/10000000000 : ℝ)|^4399 ≤ (12217056671027/100000000000000 : ℝ)^3375
        have hw : |(-1992978749/10000000000 : ℝ)|=(1992978749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_box_15 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825374663/2000000000 : ℝ)*x 0 + (4392781433/10000000000 : ℝ)*x 1 + (549097799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825374663/2000000000 : ℝ)^4399 ≤ (31549882277867/100000000000000 : ℝ)^3375 := by
    have hnat : (825374663 : ℕ)^4399*100000000000000^3375 ≤ 31549882277867^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825374663 2000000000 31549882277867 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392781433/10000000000 : ℝ)^4399 ≤ (2139065874053/6250000000000 : ℝ)^3375 := by
    have hnat : (4392781433 : ℕ)^4399*6250000000000^3375 ≤ 2139065874053^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392781433 10000000000 2139065874053 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549097799/1250000000 : ℝ)^4399 ≤ (34225063723601/100000000000000 : ℝ)^3375 := by
    have hnat : (549097799 : ℕ)^4399*100000000000000^3375 ≤ 34225063723601^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549097799 1250000000 34225063723601 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825374663/2000000000 : ℝ), (4392781433/10000000000 : ℝ), (549097799/1250000000 : ℝ)] ![(31549882277867/100000000000000 : ℝ), (2139065874053/6250000000000 : ℝ), (34225063723601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825374663/2000000000 : ℝ)|^4399 ≤ (31549882277867/100000000000000 : ℝ)^3375
        have hw : |(825374663/2000000000 : ℝ)|=(825374663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392781433/10000000000 : ℝ)|^4399 ≤ (2139065874053/6250000000000 : ℝ)^3375
        have hw : |(4392781433/10000000000 : ℝ)|=(4392781433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549097799/1250000000 : ℝ)|^4399 ≤ (34225063723601/100000000000000 : ℝ)^3375
        have hw : |(549097799/1250000000 : ℝ)|=(549097799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31453/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59133/100000 : ℝ) ∧ (80503/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42361/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (4385891911171301/50000000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^2199 ≤ (4385891911171301/50000000000000000000 : ℝ)^512 := by
      have hnat : (11361 : ℕ)^2199*50000000000000000000^512 ≤ 4385891911171301^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 4385891911171301 50000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (4385891911171301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (2199/512 : ℝ) ≤ (6752794871956891/25000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^2199 ≤ (6752794871956891/25000000000000000000 : ℝ)^512 := by
      have hnat : (7381 : ℕ)^2199*25000000000000000000^512 ≤ 6752794871956891^512*50000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 6752794871956891 25000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (6752794871956891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004385891911171301/25000000000000000000 : ℝ) ≤ (10000408444849441/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (25004385891911171301/25000000000000000000 : ℝ)^512 ≤ (10000408444849441/10000000000000000 : ℝ)^2199 := by
      have hnat : (25004385891911171301 : ℕ)^512*10000000000000000^2199 ≤ 10000408444849441^2199*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004385891911171301 25000000000000000000 10000408444849441 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000408444849441/10000000000000000 : ℝ)) (X := (25004385891911171301/25000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017891481655085083/50000000000000000000 : ℝ) ≤ (2500208257879337/2500000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50017891481655085083/50000000000000000000 : ℝ)^512 ≤ (2500208257879337/2500000000000000 : ℝ)^2199 := by
      have hnat : (50017891481655085083 : ℕ)^512*2500000000000000^2199 ≤ 2500208257879337^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017891481655085083 50000000000000000000 2500208257879337 2500000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500208257879337/2500000000000000 : ℝ)) (X := (50017891481655085083/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506752794871956891/12500000000000000000 : ℝ) ≤ (2000251523637051/2000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12506752794871956891/12500000000000000000 : ℝ)^512 ≤ (2000251523637051/2000000000000000 : ℝ)^2199 := by
      have hnat : (12506752794871956891 : ℕ)^512*2000000000000000^2199 ≤ 2000251523637051^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506752794871956891 12500000000000000000 2000251523637051 2000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000251523637051/2000000000000000 : ℝ)) (X := (12506752794871956891/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4385891911171301/50000000000000000000 : ℝ) ≤ ((34001741662664765987/34010000000000000000 : ℝ)+2*(424586667907/340100000000000 : ℝ)*(11361/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (34001741662664765987/34010000000000000000 : ℝ)+2*(424586667907/340100000000000 : ℝ)*(11361/100000 : ℝ)=(10000408444849441/10000000000000000 : ℝ) by norm_num, show 1+2*(4385891911171301/50000000000000000000 : ℝ)=(25004385891911171301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6752794871956891/25000000000000000000 : ℝ)+(4385891911171301/50000000000000000000 : ℝ) ≤ ((34001741662664765987/34010000000000000000 : ℝ)+(424586667907/340100000000000 : ℝ)*((7381/50000 : ℝ)+(11361/100000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (34001741662664765987/34010000000000000000 : ℝ)+(424586667907/340100000000000 : ℝ)*((7381/50000 : ℝ)+(11361/100000 : ℝ))=(2500208257879337/2500000000000000 : ℝ) by norm_num, show 1+(6752794871956891/25000000000000000000 : ℝ)+(4385891911171301/50000000000000000000 : ℝ)=(50017891481655085083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6752794871956891/25000000000000000000 : ℝ) ≤ ((34001741662664765987/34010000000000000000 : ℝ)+2*(424586667907/340100000000000 : ℝ)*(7381/50000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (34001741662664765987/34010000000000000000 : ℝ)+2*(424586667907/340100000000000 : ℝ)*(7381/50000 : ℝ)=(2000251523637051/2000000000000000 : ℝ) by norm_num, show 1+2*(6752794871956891/25000000000000000000 : ℝ)=(12506752794871956891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34001741662664765987/34010000000000000000 : ℝ)*(X 1 0+X 2 0)+(424586667907/340100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34001741662664765987/34010000000000000000 : ℝ)) (alpha := (424586667907/340100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34001741662664765987/34010000000000000000 : ℝ)*(X 0 1+X 2 1)+(424586667907/340100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34001741662664765987/34010000000000000000 : ℝ)) (alpha := (424586667907/340100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34001741662664765987/34010000000000000000 : ℝ)*(X 0 2+X 1 2)+(424586667907/340100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (34001741662664765987/34010000000000000000 : ℝ)) (alpha := (424586667907/340100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-180310241/1000000000 : ℝ)*X 0 0+(5385828679/10000000000 : ℝ)*X 0 1+(1077165783/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165191647/312500000 : ℝ)*X 1 0+(-242513903/1250000000 : ℝ)*X 1 1+(2692914291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286132487/10000000000 : ℝ)*X 2 0+(2692914283/5000000000 : ℝ)*X 2 1+(-97005577/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4447981301/10000000000 : ℝ)*X 0 0+(4232519557/10000000000 : ℝ)*X 0 1+(1058129801/2500000000 : ℝ)*X 0 2+(4447981301/10000000000 : ℝ)*X 1 0+(4232519557/10000000000 : ℝ)*X 1 1+(1058129801/2500000000 : ℝ)*X 1 2+(4447981301/10000000000 : ℝ)*X 2 0+(4232519557/10000000000 : ℝ)*X 2 1+(1058129801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425144503/2000000000 : ℝ)*X 0 0+(5266669581/10000000000 : ℝ)*X 0 1+(658333719/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342372983/2500000000 : ℝ)*X 1 0+(-497138407/2500000000 : ℝ)*X 1 1+(5266669641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369491751/10000000000 : ℝ)*X 2 0+(658333709/1250000000 : ℝ)*X 2 1+(-198855383/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4154717601/10000000000 : ℝ)*X 0 0+(437910041/1000000000 : ℝ)*X 0 1+(437910083/1000000000 : ℝ)*X 0 2+(4154717601/10000000000 : ℝ)*X 1 0+(437910041/1000000000 : ℝ)*X 1 1+(437910083/1000000000 : ℝ)*X 1 2+(4154717601/10000000000 : ℝ)*X 2 0+(437910041/1000000000 : ℝ)*X 2 1+(437910083/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-411549561/2000000000 : ℝ)*X 0 0+(1036840621/2000000000 : ℝ)*X 0 1+(1349949293/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527635717/1000000000 : ℝ)*X 1 0+(-967153601/5000000000 : ℝ)*X 1 1+(674974569/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638178557/5000000000 : ℝ)*X 2 0+(337487257/625000000 : ℝ)*X 2 1+(-1934307879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2240900649/5000000000 : ℝ)*X 0 0+(4215321793/10000000000 : ℝ)*X 0 1+(4215322861/10000000000 : ℝ)*X 0 2+(2240900649/5000000000 : ℝ)*X 1 0+(4215321793/10000000000 : ℝ)*X 1 1+(4215322861/10000000000 : ℝ)*X 1 2+(2240900649/5000000000 : ℝ)*X 2 0+(4215321793/10000000000 : ℝ)*X 2 1+(4215322861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1871240291/10000000000 : ℝ)*X 0 0+(5466290247/10000000000 : ℝ)*X 0 1+(5255539209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688638583/5000000000 : ℝ)*X 1 0+(-996489927/5000000000 : ℝ)*X 1 1+(5255538433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215091079/400000000 : ℝ)*X 2 0+(656942431/1250000000 : ℝ)*X 2 1+(-1992978749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((825374663/2000000000 : ℝ)*X 0 0+(4392781433/10000000000 : ℝ)*X 0 1+(549097799/1250000000 : ℝ)*X 0 2+(825374663/2000000000 : ℝ)*X 1 0+(4392781433/10000000000 : ℝ)*X 1 1+(549097799/1250000000 : ℝ)*X 1 2+(825374663/2000000000 : ℝ)*X 2 0+(4392781433/10000000000 : ℝ)*X 2 1+(549097799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31453/50000 : ℝ) ≤ (-267417362965678849705668899618193/425125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16074699/50000000000000 : ℝ)*(upper1) + (3737553/2500000000000 : ℝ)*(lower4) + (71226261/100000000000000 : ℝ)*(upper5) + (756910231447287/25000000000000 : ℝ)*(major0) + (756910231447287/25000000000000 : ℝ)*(major1) + (756910231447287/25000000000000 : ℝ)*(major2) + (12488357/1562500000000 : ℝ)*(sp1) + (4843197763/50000000000000 : ℝ)*(sp2) + (4175159001/100000000000000 : ℝ)*(sp3) + (2083411387114491/50000000000000 : ℝ)*(sp4) + (1041706522117541/25000000000000 : ℝ)*(sp5) + (4166817201329487/100000000000000 : ℝ)*(sp6) + (119338658283227/6250000000000 : ℝ)*(sp7) + (4113496031/100000000000000 : ℝ)*(sp12) + (238677838461329/12500000000000 : ℝ)*(f.failure) + (4166826887725013/100000000000000 : ℝ)*(f.sum) + (35326819961337/8502500000000000000000000000 : ℝ)*base66 + (7632375924057072731/850250000000000000000000000000000 : ℝ)*base68 + (2632706073635177269/850250000000000000000000000000000 : ℝ)*base69 + (952134357281322731/850250000000000000000000000000000 : ℝ)*base72 + (61850191401429/17005000000000000000000000000 : ℝ)*base74 + (6096603558005927269/850250000000000000000000000000000 : ℝ)*base75 + (4298334944696072731/850250000000000000000000000000000 : ℝ)*base78 + (5261120314852322731/850250000000000000000000000000000 : ℝ)*base80 + (42850462268667/8502500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1344347/1250000000000000000000 : ℝ)*base90 + (1344347/1250000000000000000000 : ℝ)*base92 + (1344347/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59133/100000 : ℝ) ≤ (10056033154506641181368918859/17005000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33699291/100000000000000 : ℝ)*(lower0) + (1747527/25000000000000 : ℝ)*(lower1) + (21987457/25000000000000 : ℝ)*(lower4) + (44489863/25000000000000 : ℝ)*(lower5) + (1549795022643923/50000000000000 : ℝ)*(major0) + (1549795022643923/50000000000000 : ℝ)*(major1) + (1549795022643923/50000000000000 : ℝ)*(major2) + (422465844880513/10000000000000 : ℝ)*(sp0) + (2112334891450879/50000000000000 : ℝ)*(sp1) + (2112334667990069/50000000000000 : ℝ)*(sp2) + (1954794454840941/100000000000000 : ℝ)*(sp3) + (446921621/100000000000000 : ℝ)*(sp6) + (196919361/5000000000000 : ℝ)*(sp7) + (2833524157/25000000000000 : ℝ)*(sp12) + (1954798393228161/100000000000000 : ℝ)*(f.failure) + (2112334891450879/50000000000000 : ℝ)*(f.sum) + (2965998830257/17005000000000000000000000000 : ℝ)*base65 + (48894847612777247001/1700500000000000000000000000000000 : ℝ)*base67 + (1008860405844252999/1700500000000000000000000000000000 : ℝ)*base70 + (12171456062092247001/1700500000000000000000000000000000 : ℝ)*base71 + (21639017035597/17005000000000000000000000000 : ℝ)*base73 + (552150240621252999/1700500000000000000000000000000000 : ℝ)*base76 + (12530775206619747001/1700500000000000000000000000000000 : ℝ)*base77 + (48548036690039752999/1700500000000000000000000000000000 : ℝ)*base80 + (775648985687/4251250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (29464277/10000000000000000000000 : ℝ)*base89 + (29464277/10000000000000000000000 : ℝ)*base91 + (29464277/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80503/100000 : ℝ) ≤ (10695334702745211825602919274581/13285156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (402260779/100000000000000 : ℝ)*(upper0) + (18605329/20000000000000 : ℝ)*(upper2) + (11175041/2500000000000 : ℝ)*(lower5) + (106465576564441/3125000000000 : ℝ)*(major0) + (106465576564441/3125000000000 : ℝ)*(major1) + (106465576564441/3125000000000 : ℝ)*(major2) + (4286968929/6250000000000 : ℝ)*(sp1) + (42715430713/100000000000000 : ℝ)*(sp3) + (11815320117/100000000000000 : ℝ)*(sp4) + (4638327515837029/100000000000000 : ℝ)*(sp8) + (4638286412418729/100000000000000 : ℝ)*(sp9) + (4638355003921593/100000000000000 : ℝ)*(sp10) + (2148563880527837/100000000000000 : ℝ)*(sp11) + (489773889/3125000000000 : ℝ)*(sp12) + (42972131919171/2000000000000 : ℝ)*(f.failure) + (4638355003921593/100000000000000 : ℝ)*(f.sum) + (11415209417771/17005000000000000000000000000 : ℝ)*base66 + (206415991453331733/106281250000000000000000000000000 : ℝ)*base68 + (108131146401862983/106281250000000000000000000000000 : ℝ)*base70 + (714027389432137017/106281250000000000000000000000000 : ℝ)*base71 + (22473150146643/2125625000000000000000000000 : ℝ)*base73 + (380001985677762017/106281250000000000000000000000000 : ℝ)*base75 + (562867668312887017/106281250000000000000000000000000 : ℝ)*base77 + (366814934142355767/106281250000000000000000000000000 : ℝ)*base79 + (6249352285637/8502500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1417153/200000000000000000000 : ℝ)*base90 + (1417153/200000000000000000000 : ℝ)*base92 + (1417153/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42361/50000 : ℝ) ≤ (-360164838173293963235128872995967/425125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45006957/20000000000000 : ℝ)*(lower1) + (310430271/100000000000000 : ℝ)*(lower2) + (8471001/20000000000000 : ℝ)*(lower3) + (237227381/100000000000000 : ℝ)*(upper5) + (1722260597318847/50000000000000 : ℝ)*(major0) + (1722260597318847/50000000000000 : ℝ)*(major1) + (1722260597318847/50000000000000 : ℝ)*(major2) + (20250507601/100000000000000 : ℝ)*(sp4) + (515153154097/100000000000000 : ℝ)*(sp5) + (29762175349/20000000000000 : ℝ)*(sp7) + (2372464083363579/50000000000000 : ℝ)*(sp12) + (4744433264080661/100000000000000 : ℝ)*(sp13) + (4744948417234759/100000000000000 : ℝ)*(sp14) + (271523134738479/12500000000000 : ℝ)*(sp15) + (33942717012259/1562500000000 : ℝ)*(f.failure) + (4744948417234759/100000000000000 : ℝ)*(f.sum) + (6969557509601/8502500000000000000000000000 : ℝ)*base66 + (4614499981853943011/1700500000000000000000000000000000 : ℝ)*base68 + (2848053197868556989/1700500000000000000000000000000000 : ℝ)*base69 + (17007762165725056989/1700500000000000000000000000000000 : ℝ)*base71 + (54769753451011/8502500000000000000000000000 : ℝ)*base74 + (24180331845460556989/1700500000000000000000000000000000 : ℝ)*base75 + (20121986623277556989/1700500000000000000000000000000000 : ℝ)*base77 + (6745078385733556989/1700500000000000000000000000000000 : ℝ)*base79 + (19194062544557/17005000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2133337/156250000000000000000 : ℝ)*base90 + (2133337/156250000000000000000 : ℝ)*base92 + (2133337/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1439_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59133/100000 : ℝ) else (80503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42361/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1439_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1439_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59133/100000 : ℝ) else (80503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42361/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1439_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1439_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1439_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59133/100000 : ℝ) else (80503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42361/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

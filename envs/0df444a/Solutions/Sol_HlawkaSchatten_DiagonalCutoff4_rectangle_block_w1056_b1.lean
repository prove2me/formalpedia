-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:59:38.298739+00:00
-- url     : https://prove2.me/submissions/6a67e238-b896-4401-89c9-8f418bcd9351

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
theorem support_rectangle_w1056_s3_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203824377/10000000000 : ℝ)*x 0 + (5438717529/10000000000 : ℝ)*x 1 + (1305817459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203824377/10000000000 : ℝ)^8249 ≤ (6686802578347/50000000000000 : ℝ)^6201 := by
    have hnat : (2203824377 : ℕ)^8249*50000000000000^6201 ≤ 6686802578347^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203824377 10000000000 6686802578347 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438717529/10000000000 : ℝ)^8249 ≤ (22238685858339/50000000000000 : ℝ)^6201 := by
    have hnat : (5438717529 : ℕ)^8249*50000000000000^6201 ≤ 22238685858339^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438717529 10000000000 22238685858339 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305817459/2500000000 : ℝ)^8249 ≤ (21074511556791/50000000000000 : ℝ)^6201 := by
    have hnat : (1305817459 : ℕ)^8249*50000000000000^6201 ≤ 21074511556791^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305817459 2500000000 21074511556791 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203824377/10000000000 : ℝ), (5438717529/10000000000 : ℝ), (1305817459/2500000000 : ℝ)] ![(6686802578347/50000000000000 : ℝ), (22238685858339/50000000000000 : ℝ), (21074511556791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203824377/10000000000 : ℝ)|^8249 ≤ (6686802578347/50000000000000 : ℝ)^6201
        have hw : |(-2203824377/10000000000 : ℝ)|=(2203824377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438717529/10000000000 : ℝ)|^8249 ≤ (22238685858339/50000000000000 : ℝ)^6201
        have hw : |(5438717529/10000000000 : ℝ)|=(5438717529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305817459/2500000000 : ℝ)|^8249 ≤ (21074511556791/50000000000000 : ℝ)^6201
        have hw : |(1305817459/2500000000 : ℝ)|=(1305817459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535595133/1000000000 : ℝ)*x 0 + (-2314178721/10000000000 : ℝ)*x 1 + (5223269987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535595133/1000000000 : ℝ)^8249 ≤ (21789621385741/50000000000000 : ℝ)^6201 := by
    have hnat : (535595133 : ℕ)^8249*50000000000000^6201 ≤ 21789621385741^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535595133 1000000000 21789621385741 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314178721/10000000000 : ℝ)^8249 ≤ (14271732480801/100000000000000 : ℝ)^6201 := by
    have hnat : (2314178721 : ℕ)^8249*100000000000000^6201 ≤ 14271732480801^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314178721 10000000000 14271732480801 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223269987/10000000000 : ℝ)^8249 ≤ (21074512367251/50000000000000 : ℝ)^6201 := by
    have hnat : (5223269987 : ℕ)^8249*50000000000000^6201 ≤ 21074512367251^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223269987 10000000000 21074512367251 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535595133/1000000000 : ℝ), (-2314178721/10000000000 : ℝ), (5223269987/10000000000 : ℝ)] ![(21789621385741/50000000000000 : ℝ), (14271732480801/100000000000000 : ℝ), (21074512367251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535595133/1000000000 : ℝ)|^8249 ≤ (21789621385741/50000000000000 : ℝ)^6201
        have hw : |(535595133/1000000000 : ℝ)|=(535595133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2314178721/10000000000 : ℝ)|^8249 ≤ (14271732480801/100000000000000 : ℝ)^6201
        have hw : |(-2314178721/10000000000 : ℝ)|=(2314178721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223269987/10000000000 : ℝ)|^8249 ≤ (21074512367251/50000000000000 : ℝ)^6201
        have hw : |(5223269987/10000000000 : ℝ)|=(5223269987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338987839/2500000000 : ℝ)*x 0 + (1044654047/2000000000 : ℝ)*x 1 + (-1157089181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338987839/2500000000 : ℝ)^8249 ≤ (43579243052903/100000000000000 : ℝ)^6201 := by
    have hnat : (1338987839 : ℕ)^8249*100000000000000^6201 ≤ 43579243052903^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338987839 2500000000 43579243052903 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044654047/2000000000 : ℝ)^8249 ≤ (1685961095867/4000000000000 : ℝ)^6201 := by
    have hnat : (1044654047 : ℕ)^8249*4000000000000^6201 ≤ 1685961095867^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044654047 2000000000 1685961095867 4000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157089181/5000000000 : ℝ)^8249 ≤ (1783966191951/12500000000000 : ℝ)^6201 := by
    have hnat : (1157089181 : ℕ)^8249*12500000000000^6201 ≤ 1783966191951^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157089181 5000000000 1783966191951 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338987839/2500000000 : ℝ), (1044654047/2000000000 : ℝ), (-1157089181/5000000000 : ℝ)] ![(43579243052903/100000000000000 : ℝ), (1685961095867/4000000000000 : ℝ), (1783966191951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338987839/2500000000 : ℝ)|^8249 ≤ (43579243052903/100000000000000 : ℝ)^6201
        have hw : |(1338987839/2500000000 : ℝ)|=(1338987839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044654047/2000000000 : ℝ)|^8249 ≤ (1685961095867/4000000000000 : ℝ)^6201
        have hw : |(1044654047/2000000000 : ℝ)|=(1044654047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1157089181/5000000000 : ℝ)|^8249 ≤ (1783966191951/12500000000000 : ℝ)^6201
        have hw : |(-1157089181/5000000000 : ℝ)|=(1157089181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374048913/10000000000 : ℝ)*x 0 + (1042122493/2500000000 : ℝ)*x 1 + (2294949047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374048913/10000000000 : ℝ)^8249 ≤ (8321824054599/25000000000000 : ℝ)^6201 := by
    have hnat : (4374048913 : ℕ)^8249*25000000000000^6201 ≤ 8321824054599^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374048913 10000000000 8321824054599 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042122493/2500000000 : ℝ)^8249 ≤ (1248904986147/4000000000000 : ℝ)^6201 := by
    have hnat : (1042122493 : ℕ)^8249*4000000000000^6201 ≤ 1248904986147^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042122493 2500000000 1248904986147 4000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294949047/5000000000 : ℝ)^8249 ≤ (17745039551617/50000000000000 : ℝ)^6201 := by
    have hnat : (2294949047 : ℕ)^8249*50000000000000^6201 ≤ 17745039551617^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294949047 5000000000 17745039551617 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374048913/10000000000 : ℝ), (1042122493/2500000000 : ℝ), (2294949047/5000000000 : ℝ)] ![(8321824054599/25000000000000 : ℝ), (1248904986147/4000000000000 : ℝ), (17745039551617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374048913/10000000000 : ℝ)|^8249 ≤ (8321824054599/25000000000000 : ℝ)^6201
        have hw : |(4374048913/10000000000 : ℝ)|=(4374048913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042122493/2500000000 : ℝ)|^8249 ≤ (1248904986147/4000000000000 : ℝ)^6201
        have hw : |(1042122493/2500000000 : ℝ)|=(1042122493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2294949047/5000000000 : ℝ)|^8249 ≤ (17745039551617/50000000000000 : ℝ)^6201
        have hw : |(2294949047/5000000000 : ℝ)|=(2294949047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203847599/10000000000 : ℝ)*x 0 + (653019969/1250000000 : ℝ)*x 1 + (5437822133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203847599/10000000000 : ℝ)^8249 ≤ (3343448154481/25000000000000 : ℝ)^6201 := by
    have hnat : (2203847599 : ℕ)^8249*25000000000000^6201 ≤ 3343448154481^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203847599 10000000000 3343448154481 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653019969/1250000000 : ℝ)^8249 ≤ (42158576247301/100000000000000 : ℝ)^6201 := by
    have hnat : (653019969 : ℕ)^8249*100000000000000^6201 ≤ 42158576247301^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653019969 1250000000 42158576247301 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437822133/10000000000 : ℝ)^8249 ≤ (4446763112077/10000000000000 : ℝ)^6201 := by
    have hnat : (5437822133 : ℕ)^8249*10000000000000^6201 ≤ 4446763112077^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437822133 10000000000 4446763112077 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203847599/10000000000 : ℝ), (653019969/1250000000 : ℝ), (5437822133/10000000000 : ℝ)] ![(3343448154481/25000000000000 : ℝ), (42158576247301/100000000000000 : ℝ), (4446763112077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203847599/10000000000 : ℝ)|^8249 ≤ (3343448154481/25000000000000 : ℝ)^6201
        have hw : |(-2203847599/10000000000 : ℝ)|=(2203847599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653019969/1250000000 : ℝ)|^8249 ≤ (42158576247301/100000000000000 : ℝ)^6201
        have hw : |(653019969/1250000000 : ℝ)|=(653019969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437822133/10000000000 : ℝ)|^8249 ≤ (4446763112077/10000000000000 : ℝ)^6201
        have hw : |(5437822133/10000000000 : ℝ)|=(5437822133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212068931/400000000 : ℝ)*x 0 + (-419925253/2000000000 : ℝ)*x 1 + (1087564461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212068931/400000000 : ℝ)^8249 ≤ (42993268865771/100000000000000 : ℝ)^6201 := by
    have hnat : (212068931 : ℕ)^8249*100000000000000^6201 ≤ 42993268865771^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212068931 400000000 42993268865771 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419925253/2000000000 : ℝ)^8249 ≤ (12539098124627/100000000000000 : ℝ)^6201 := by
    have hnat : (419925253 : ℕ)^8249*100000000000000^6201 ≤ 12539098124627^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419925253 2000000000 12539098124627 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087564461/2000000000 : ℝ)^8249 ≤ (44467632991827/100000000000000 : ℝ)^6201 := by
    have hnat : (1087564461 : ℕ)^8249*100000000000000^6201 ≤ 44467632991827^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087564461 2000000000 44467632991827 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212068931/400000000 : ℝ), (-419925253/2000000000 : ℝ), (1087564461/2000000000 : ℝ)] ![(42993268865771/100000000000000 : ℝ), (12539098124627/100000000000000 : ℝ), (44467632991827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212068931/400000000 : ℝ)|^8249 ≤ (42993268865771/100000000000000 : ℝ)^6201
        have hw : |(212068931/400000000 : ℝ)|=(212068931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419925253/2000000000 : ℝ)|^8249 ≤ (12539098124627/100000000000000 : ℝ)^6201
        have hw : |(-419925253/2000000000 : ℝ)|=(419925253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087564461/2000000000 : ℝ)|^8249 ≤ (44467632991827/100000000000000 : ℝ)^6201
        have hw : |(1087564461/2000000000 : ℝ)|=(1087564461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301722967/10000000000 : ℝ)*x 0 + (5437822357/10000000000 : ℝ)*x 1 + (-524906653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301722967/10000000000 : ℝ)^8249 ≤ (10748316385801/25000000000000 : ℝ)^6201 := by
    have hnat : (5301722967 : ℕ)^8249*25000000000000^6201 ≤ 10748316385801^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301722967 10000000000 10748316385801 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437822357/10000000000 : ℝ)^8249 ≤ (5558454194687/12500000000000 : ℝ)^6201 := by
    have hnat : (5437822357 : ℕ)^8249*12500000000000^6201 ≤ 5558454194687^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437822357 10000000000 5558454194687 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524906653/2500000000 : ℝ)^8249 ≤ (1567387610169/12500000000000 : ℝ)^6201 := by
    have hnat : (524906653 : ℕ)^8249*12500000000000^6201 ≤ 1567387610169^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524906653 2500000000 1567387610169 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301722967/10000000000 : ℝ), (5437822357/10000000000 : ℝ), (-524906653/2500000000 : ℝ)] ![(10748316385801/25000000000000 : ℝ), (5558454194687/12500000000000 : ℝ), (1567387610169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301722967/10000000000 : ℝ)|^8249 ≤ (10748316385801/25000000000000 : ℝ)^6201
        have hw : |(5301722967/10000000000 : ℝ)|=(5301722967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437822357/10000000000 : ℝ)|^8249 ≤ (5558454194687/12500000000000 : ℝ)^6201
        have hw : |(5437822357/10000000000 : ℝ)|=(5437822357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524906653/2500000000 : ℝ)|^8249 ≤ (1567387610169/12500000000000 : ℝ)^6201
        have hw : |(-524906653/2500000000 : ℝ)|=(524906653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s3_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109352339/250000000 : ℝ)*x 0 + (229407917/500000000 : ℝ)*x 1 + (2085120177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109352339/250000000 : ℝ)^8249 ≤ (16643874103493/50000000000000 : ℝ)^6201 := by
    have hnat : (109352339 : ℕ)^8249*50000000000000^6201 ≤ 16643874103493^6201*250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109352339 250000000 16643874103493 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229407917/500000000 : ℝ)^8249 ≤ (3547218523837/10000000000000 : ℝ)^6201 := by
    have hnat : (229407917 : ℕ)^8249*10000000000000^6201 ≤ 3547218523837^6201*500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229407917 500000000 3547218523837 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085120177/5000000000 : ℝ)^8249 ≤ (31240066528633/100000000000000 : ℝ)^6201 := by
    have hnat : (2085120177 : ℕ)^8249*100000000000000^6201 ≤ 31240066528633^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085120177 5000000000 31240066528633 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109352339/250000000 : ℝ), (229407917/500000000 : ℝ), (2085120177/5000000000 : ℝ)] ![(16643874103493/50000000000000 : ℝ), (3547218523837/10000000000000 : ℝ), (31240066528633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109352339/250000000 : ℝ)|^8249 ≤ (16643874103493/50000000000000 : ℝ)^6201
        have hw : |(109352339/250000000 : ℝ)|=(109352339/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229407917/500000000 : ℝ)|^8249 ≤ (3547218523837/10000000000000 : ℝ)^6201
        have hw : |(229407917/500000000 : ℝ)|=(229407917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085120177/5000000000 : ℝ)|^8249 ≤ (31240066528633/100000000000000 : ℝ)^6201
        have hw : |(2085120177/5000000000 : ℝ)|=(2085120177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5181/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14921/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4331/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (2632650568165367/50000000000000000000 : ℝ) := by
    have hpowers : (4331/50000 : ℝ)^1031 ≤ (2632650568165367/50000000000000000000 : ℝ)^256 := by
      have hnat : (4331 : ℕ)^1031*50000000000000000000^256 ≤ 2632650568165367^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4331 50000 2632650568165367 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4331/50000 : ℝ)) (X := (2632650568165367/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (8387/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (75395463048343073/100000000000000000000 : ℝ) := by
    have hpowers : (8387/50000 : ℝ)^1031 ≤ (75395463048343073/100000000000000000000 : ℝ)^256 := by
      have hnat : (8387 : ℕ)^1031*100000000000000000000^256 ≤ 75395463048343073^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8387 50000 75395463048343073 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8387/50000 : ℝ)) (X := (75395463048343073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002632650568165367/25000000000000000000 : ℝ) ≤ (5000130733631891/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25002632650568165367/25000000000000000000 : ℝ)^256 ≤ (5000130733631891/5000000000000000 : ℝ)^1031 := by
      have hnat : (25002632650568165367 : ℕ)^256*5000000000000000^1031 ≤ 5000130733631891^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002632650568165367 25000000000000000000 5000130733631891 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000130733631891/5000000000000000 : ℝ)) (X := (25002632650568165367/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100080660764184673807/100000000000000000000 : ℝ) ≤ (10002002221001927/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (100080660764184673807/100000000000000000000 : ℝ)^256 ≤ (10002002221001927/10000000000000000 : ℝ)^1031 := by
      have hnat : (100080660764184673807 : ℕ)^256*10000000000000000^1031 ≤ 10002002221001927^1031*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100080660764184673807 100000000000000000000 10002002221001927 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002002221001927/10000000000000000 : ℝ)) (X := (100080660764184673807/100000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075395463048343073/50000000000000000000 : ℝ) ≤ (1250467871842509/1250000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50075395463048343073/50000000000000000000 : ℝ)^256 ≤ (1250467871842509/1250000000000000 : ℝ)^1031 := by
      have hnat : (50075395463048343073 : ℕ)^256*1250000000000000^1031 ≤ 1250467871842509^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075395463048343073 50000000000000000000 1250467871842509 1250000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250467871842509/1250000000000000 : ℝ)) (X := (50075395463048343073/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2632650568165367/50000000000000000000 : ℝ) ≤ ((20272991051171043901/20280000000000000000 : ℝ)+2*(348150747629/162240000000000 : ℝ)*(4331/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (20272991051171043901/20280000000000000000 : ℝ)+2*(348150747629/162240000000000 : ℝ)*(4331/50000 : ℝ)=(5000130733631891/5000000000000000 : ℝ) by norm_num, show 1+2*(2632650568165367/50000000000000000000 : ℝ)=(25002632650568165367/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75395463048343073/100000000000000000000 : ℝ)+(2632650568165367/50000000000000000000 : ℝ) ≤ ((20272991051171043901/20280000000000000000 : ℝ)+(348150747629/162240000000000 : ℝ)*((8387/50000 : ℝ)+(4331/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (20272991051171043901/20280000000000000000 : ℝ)+(348150747629/162240000000000 : ℝ)*((8387/50000 : ℝ)+(4331/50000 : ℝ))=(10002002221001927/10000000000000000 : ℝ) by norm_num, show 1+(75395463048343073/100000000000000000000 : ℝ)+(2632650568165367/50000000000000000000 : ℝ)=(100080660764184673807/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75395463048343073/100000000000000000000 : ℝ) ≤ ((20272991051171043901/20280000000000000000 : ℝ)+2*(348150747629/162240000000000 : ℝ)*(8387/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (20272991051171043901/20280000000000000000 : ℝ)+2*(348150747629/162240000000000 : ℝ)*(8387/50000 : ℝ)=(1250467871842509/1250000000000000 : ℝ) by norm_num, show 1+2*(75395463048343073/100000000000000000000 : ℝ)=(50075395463048343073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20272991051171043901/20280000000000000000 : ℝ)*(X 1 0+X 2 0)+(348150747629/162240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (4331/50000 : ℝ)) (hi := (8387/50000 : ℝ)) (c := (20272991051171043901/20280000000000000000 : ℝ)) (alpha := (348150747629/162240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20272991051171043901/20280000000000000000 : ℝ)*(X 0 1+X 2 1)+(348150747629/162240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (4331/50000 : ℝ)) (hi := (8387/50000 : ℝ)) (c := (20272991051171043901/20280000000000000000 : ℝ)) (alpha := (348150747629/162240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20272991051171043901/20280000000000000000 : ℝ)*(X 0 2+X 1 2)+(348150747629/162240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (4331/50000 : ℝ)) (hi := (8387/50000 : ℝ)) (c := (20272991051171043901/20280000000000000000 : ℝ)) (alpha := (348150747629/162240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2203824377/10000000000 : ℝ)*X 0 0+(5438717529/10000000000 : ℝ)*X 0 1+(1305817459/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535595133/1000000000 : ℝ)*X 1 0+(-2314178721/10000000000 : ℝ)*X 1 1+(5223269987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338987839/2500000000 : ℝ)*X 2 0+(1044654047/2000000000 : ℝ)*X 2 1+(-1157089181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374048913/10000000000 : ℝ)*X 0 0+(1042122493/2500000000 : ℝ)*X 0 1+(2294949047/5000000000 : ℝ)*X 0 2+(4374048913/10000000000 : ℝ)*X 1 0+(1042122493/2500000000 : ℝ)*X 1 1+(2294949047/5000000000 : ℝ)*X 1 2+(4374048913/10000000000 : ℝ)*X 2 0+(1042122493/2500000000 : ℝ)*X 2 1+(2294949047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2203847599/10000000000 : ℝ)*X 0 0+(653019969/1250000000 : ℝ)*X 0 1+(5437822133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212068931/400000000 : ℝ)*X 1 0+(-419925253/2000000000 : ℝ)*X 1 1+(1087564461/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301722967/10000000000 : ℝ)*X 2 0+(5437822357/10000000000 : ℝ)*X 2 1+(-524906653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((109352339/250000000 : ℝ)*X 0 0+(229407917/500000000 : ℝ)*X 0 1+(2085120177/5000000000 : ℝ)*X 0 2+(109352339/250000000 : ℝ)*X 1 0+(229407917/500000000 : ℝ)*X 1 1+(2085120177/5000000000 : ℝ)*X 1 2+(109352339/250000000 : ℝ)*X 2 0+(229407917/500000000 : ℝ)*X 2 1+(2085120177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116800349621019181408419933/13000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2210254249/100000000000000 : ℝ)*(base19) + (375016133/20000000000000 : ℝ)*(base23) + (47896363/25000000000000 : ℝ)*(lower2) + (74036557/50000000000000 : ℝ)*(upper3) + (22097171/10000000000000 : ℝ)*(upper5) + (1753654117463971/50000000000000 : ℝ)*(major0) + (1753654117463971/50000000000000 : ℝ)*(major1) + (1753654117463971/50000000000000 : ℝ)*(major2) + (4641537556271089/100000000000000 : ℝ)*(sp0) + (2320790459843761/50000000000000 : ℝ)*(sp1) + (928316250972221/20000000000000 : ℝ)*(sp2) + (2373014503292643/100000000000000 : ℝ)*(sp3) + (22786835341/50000000000000 : ℝ)*(sp4) + (9268566693/50000000000000 : ℝ)*(sp7) + (237303304042603/10000000000000 : ℝ)*(f.failure) + (464158312994177/10000000000000 : ℝ)*(f.sum) + (1782399297529/4056000000000000000000000000 : ℝ)*base66 + (1039999884137665871/1014000000000000000000000000000000 : ℝ)*base67 + (5224625979072334129/1014000000000000000000000000000000 : ℝ)*base70 + (1715971298034334129/1014000000000000000000000000000000 : ℝ)*base72 + (3443275261963/811200000000000000000000000 : ℝ)*base73 + (2242849151471665871/1014000000000000000000000000000000 : ℝ)*base75 + (8144059124285665871/1014000000000000000000000000000000 : ℝ)*base77 + (15865998357917665871/1014000000000000000000000000000000 : ℝ)*base79 + (11181960090503/4056000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4642413/500000000000000000000 : ℝ)*base89 + (4642413/500000000000000000000 : ℝ)*base91 + (4642413/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (835153261201402285523145941/84500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2293071829/100000000000000 : ℝ)*(base19) + (1991736413/100000000000000 : ℝ)*(base23) + (289903767/100000000000000 : ℝ)*(upper3) + (2784519/20000000000000 : ℝ)*(lower4) + (162134957/100000000000000 : ℝ)*(upper5) + (1768272423508541/50000000000000 : ℝ)*(major0) + (1768272423508541/50000000000000 : ℝ)*(major1) + (1768272423508541/50000000000000 : ℝ)*(major2) + (19499604703/50000000000000 : ℝ)*(sp1) + (33553502613/100000000000000 : ℝ)*(sp2) + (234013746502209/5000000000000 : ℝ)*(sp4) + (936046727552589/20000000000000 : ℝ)*(sp5) + (2340119692402577/50000000000000 : ℝ)*(sp6) + (14955090215881/625000000000 : ℝ)*(sp7) + (14955090215881/625000000000 : ℝ)*(f.failure) + (234013746502209/5000000000000 : ℝ)*(f.sum) + (9232334572391/4056000000000000000000000000 : ℝ)*base66 + (3920469484230583441/1014000000000000000000000000000000 : ℝ)*base67 + (11065726540049416559/1014000000000000000000000000000000 : ℝ)*base70 + (10760042728499416559/1014000000000000000000000000000000 : ℝ)*base72 + (1636572410669/811200000000000000000000000 : ℝ)*base73 + (1979830247147416559/1014000000000000000000000000000000 : ℝ)*base76 + (3637108763573416559/1014000000000000000000000000000000 : ℝ)*base78 + (6472836510191416559/1014000000000000000000000000000000 : ℝ)*base80 + (13833411919127/4056000000000000000000000000 : ℝ)*base82 + (397751/31250000000000000000 : ℝ)*base89 + (397751/31250000000000000000 : ℝ)*base91 + (397751/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14921/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s4_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-275950007/1250000000 : ℝ)*x 0 + (1081276599/2000000000 : ℝ)*x 1 + (5253138357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275950007/1250000000 : ℝ)^8249 ≤ (6702046579029/50000000000000 : ℝ)^6201 := by
    have hnat : (275950007 : ℕ)^8249*50000000000000^6201 ≤ 6702046579029^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275950007 1250000000 6702046579029 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081276599/2000000000 : ℝ)^8249 ≤ (44125955630377/100000000000000 : ℝ)^6201 := by
    have hnat : (1081276599 : ℕ)^8249*100000000000000^6201 ≤ 44125955630377^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081276599 2000000000 44125955630377 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253138357/10000000000 : ℝ)^8249 ≤ (21234975601319/50000000000000 : ℝ)^6201 := by
    have hnat : (5253138357 : ℕ)^8249*50000000000000^6201 ≤ 21234975601319^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253138357 10000000000 21234975601319 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275950007/1250000000 : ℝ), (1081276599/2000000000 : ℝ), (5253138357/10000000000 : ℝ)] ![(6702046579029/50000000000000 : ℝ), (44125955630377/100000000000000 : ℝ), (21234975601319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275950007/1250000000 : ℝ)|^8249 ≤ (6702046579029/50000000000000 : ℝ)^6201
        have hw : |(-275950007/1250000000 : ℝ)|=(275950007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081276599/2000000000 : ℝ)|^8249 ≤ (44125955630377/100000000000000 : ℝ)^6201
        have hw : |(1081276599/2000000000 : ℝ)|=(1081276599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253138357/10000000000 : ℝ)|^8249 ≤ (21234975601319/50000000000000 : ℝ)^6201
        have hw : |(5253138357/10000000000 : ℝ)|=(5253138357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069590113/2000000000 : ℝ)*x 0 + (-142847109/625000000 : ℝ)*x 1 + (1050627789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069590113/2000000000 : ℝ)^8249 ≤ (43492664888139/100000000000000 : ℝ)^6201 := by
    have hnat : (1069590113 : ℕ)^8249*100000000000000^6201 ≤ 43492664888139^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069590113 2000000000 43492664888139 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142847109/625000000 : ℝ)^8249 ≤ (7018688787759/50000000000000 : ℝ)^6201 := by
    have hnat : (142847109 : ℕ)^8249*50000000000000^6201 ≤ 7018688787759^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142847109 625000000 7018688787759 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050627789/2000000000 : ℝ)^8249 ≤ (42469957526463/100000000000000 : ℝ)^6201 := by
    have hnat : (1050627789 : ℕ)^8249*100000000000000^6201 ≤ 42469957526463^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050627789 2000000000 42469957526463 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069590113/2000000000 : ℝ), (-142847109/625000000 : ℝ), (1050627789/2000000000 : ℝ)] ![(43492664888139/100000000000000 : ℝ), (7018688787759/50000000000000 : ℝ), (42469957526463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069590113/2000000000 : ℝ)|^8249 ≤ (43492664888139/100000000000000 : ℝ)^6201
        have hw : |(1069590113/2000000000 : ℝ)|=(1069590113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142847109/625000000 : ℝ)|^8249 ≤ (7018688787759/50000000000000 : ℝ)^6201
        have hw : |(-142847109/625000000 : ℝ)|=(142847109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050627789/2000000000 : ℝ)|^8249 ≤ (42469957526463/100000000000000 : ℝ)^6201
        have hw : |(1050627789/2000000000 : ℝ)|=(1050627789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673975053/5000000000 : ℝ)*x 0 + (5253139411/10000000000 : ℝ)*x 1 + (-1142776869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673975053/5000000000 : ℝ)^8249 ≤ (21746329961217/50000000000000 : ℝ)^6201 := by
    have hnat : (2673975053 : ℕ)^8249*50000000000000^6201 ≤ 21746329961217^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673975053 5000000000 21746329961217 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253139411/10000000000 : ℝ)^8249 ≤ (21234981269101/50000000000000 : ℝ)^6201 := by
    have hnat : (5253139411 : ℕ)^8249*50000000000000^6201 ≤ 21234981269101^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253139411 10000000000 21234981269101 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142776869/5000000000 : ℝ)^8249 ≤ (14037377526497/100000000000000 : ℝ)^6201 := by
    have hnat : (1142776869 : ℕ)^8249*100000000000000^6201 ≤ 14037377526497^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142776869 5000000000 14037377526497 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673975053/5000000000 : ℝ), (5253139411/10000000000 : ℝ), (-1142776869/5000000000 : ℝ)] ![(21746329961217/50000000000000 : ℝ), (21234981269101/50000000000000 : ℝ), (14037377526497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673975053/5000000000 : ℝ)|^8249 ≤ (21746329961217/50000000000000 : ℝ)^6201
        have hw : |(2673975053/5000000000 : ℝ)|=(2673975053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253139411/10000000000 : ℝ)|^8249 ≤ (21234981269101/50000000000000 : ℝ)^6201
        have hw : |(5253139411/10000000000 : ℝ)|=(5253139411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1142776869/5000000000 : ℝ)|^8249 ≤ (14037377526497/100000000000000 : ℝ)^6201
        have hw : |(-1142776869/5000000000 : ℝ)|=(1142776869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875258829/2000000000 : ℝ)*x 0 + (4229028983/10000000000 : ℝ)*x 1 + (566096161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875258829/2000000000 : ℝ)^8249 ≤ (8327506987089/25000000000000 : ℝ)^6201 := by
    have hnat : (875258829 : ℕ)^8249*25000000000000^6201 ≤ 8327506987089^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875258829 2000000000 8327506987089 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229028983/10000000000 : ℝ)^8249 ≤ (7956818119043/25000000000000 : ℝ)^6201 := by
    have hnat : (4229028983 : ℕ)^8249*25000000000000^6201 ≤ 7956818119043^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229028983 10000000000 7956818119043 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566096161/1250000000 : ℝ)^8249 ≤ (1743134977617/5000000000000 : ℝ)^6201 := by
    have hnat : (566096161 : ℕ)^8249*5000000000000^6201 ≤ 1743134977617^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566096161 1250000000 1743134977617 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875258829/2000000000 : ℝ), (4229028983/10000000000 : ℝ), (566096161/1250000000 : ℝ)] ![(8327506987089/25000000000000 : ℝ), (7956818119043/25000000000000 : ℝ), (1743134977617/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875258829/2000000000 : ℝ)|^8249 ≤ (8327506987089/25000000000000 : ℝ)^6201
        have hw : |(875258829/2000000000 : ℝ)|=(875258829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229028983/10000000000 : ℝ)|^8249 ≤ (7956818119043/25000000000000 : ℝ)^6201
        have hw : |(4229028983/10000000000 : ℝ)|=(4229028983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566096161/1250000000 : ℝ)|^8249 ≤ (1743134977617/5000000000000 : ℝ)^6201
        have hw : |(566096161/1250000000 : ℝ)|=(566096161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-44152167/200000000 : ℝ)*x 0 + (2626794879/5000000000 : ℝ)*x 1 + (5405929677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44152167/200000000 : ℝ)^8249 ≤ (2680832029949/20000000000000 : ℝ)^6201 := by
    have hnat : (44152167 : ℕ)^8249*20000000000000^6201 ≤ 2680832029949^6201*200000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44152167 200000000 2680832029949 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626794879/5000000000 : ℝ)^8249 ≤ (10618701500187/25000000000000 : ℝ)^6201 := by
    have hnat : (2626794879 : ℕ)^8249*25000000000000^6201 ≤ 10618701500187^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626794879 5000000000 10618701500187 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405929677/10000000000 : ℝ)^8249 ≤ (22060516915889/50000000000000 : ℝ)^6201 := by
    have hnat : (5405929677 : ℕ)^8249*50000000000000^6201 ≤ 22060516915889^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405929677 10000000000 22060516915889 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44152167/200000000 : ℝ), (2626794879/5000000000 : ℝ), (5405929677/10000000000 : ℝ)] ![(2680832029949/20000000000000 : ℝ), (10618701500187/25000000000000 : ℝ), (22060516915889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44152167/200000000 : ℝ)|^8249 ≤ (2680832029949/20000000000000 : ℝ)^6201
        have hw : |(-44152167/200000000 : ℝ)|=(44152167/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626794879/5000000000 : ℝ)|^8249 ≤ (10618701500187/25000000000000 : ℝ)^6201
        have hw : |(2626794879/5000000000 : ℝ)|=(2626794879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405929677/10000000000 : ℝ)|^8249 ≤ (22060516915889/50000000000000 : ℝ)^6201
        have hw : |(5405929677/10000000000 : ℝ)|=(5405929677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327346071/2500000000 : ℝ)*x 0 + (-266595353/1250000000 : ℝ)*x 1 + (5405929719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327346071/2500000000 : ℝ)^8249 ≤ (2153796606409/5000000000000 : ℝ)^6201 := by
    have hnat : (1327346071 : ℕ)^8249*5000000000000^6201 ≤ 2153796606409^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327346071 2500000000 2153796606409 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266595353/1250000000 : ℝ)^8249 ≤ (12803033563997/100000000000000 : ℝ)^6201 := by
    have hnat : (266595353 : ℕ)^8249*100000000000000^6201 ≤ 12803033563997^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266595353 1250000000 12803033563997 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405929719/10000000000 : ℝ)^8249 ≤ (22060517143889/50000000000000 : ℝ)^6201 := by
    have hnat : (5405929719 : ℕ)^8249*50000000000000^6201 ≤ 22060517143889^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405929719 10000000000 22060517143889 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327346071/2500000000 : ℝ), (-266595353/1250000000 : ℝ), (5405929719/10000000000 : ℝ)] ![(2153796606409/5000000000000 : ℝ), (12803033563997/100000000000000 : ℝ), (22060517143889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327346071/2500000000 : ℝ)|^8249 ≤ (2153796606409/5000000000000 : ℝ)^6201
        have hw : |(1327346071/2500000000 : ℝ)|=(1327346071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266595353/1250000000 : ℝ)|^8249 ≤ (12803033563997/100000000000000 : ℝ)^6201
        have hw : |(-266595353/1250000000 : ℝ)|=(266595353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405929719/10000000000 : ℝ)|^8249 ≤ (22060517143889/50000000000000 : ℝ)^6201
        have hw : |(5405929719/10000000000 : ℝ)|=(5405929719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309384343/10000000000 : ℝ)*x 0 + (5405929663/10000000000 : ℝ)*x 1 + (-2132762821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309384343/10000000000 : ℝ)^8249 ≤ (43075932764949/100000000000000 : ℝ)^6201 := by
    have hnat : (5309384343 : ℕ)^8249*100000000000000^6201 ≤ 43075932764949^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309384343 10000000000 43075932764949 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405929663/10000000000 : ℝ)^8249 ≤ (22060516839889/50000000000000 : ℝ)^6201 := by
    have hnat : (5405929663 : ℕ)^8249*50000000000000^6201 ≤ 22060516839889^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405929663 10000000000 22060516839889 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132762821/10000000000 : ℝ)^8249 ≤ (320075838501/2500000000000 : ℝ)^6201 := by
    have hnat : (2132762821 : ℕ)^8249*2500000000000^6201 ≤ 320075838501^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132762821 10000000000 320075838501 2500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309384343/10000000000 : ℝ), (5405929663/10000000000 : ℝ), (-2132762821/10000000000 : ℝ)] ![(43075932764949/100000000000000 : ℝ), (22060516839889/50000000000000 : ℝ), (320075838501/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309384343/10000000000 : ℝ)|^8249 ≤ (43075932764949/100000000000000 : ℝ)^6201
        have hw : |(5309384343/10000000000 : ℝ)|=(5309384343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405929663/10000000000 : ℝ)|^8249 ≤ (22060516839889/50000000000000 : ℝ)^6201
        have hw : |(5405929663/10000000000 : ℝ)|=(5405929663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132762821/10000000000 : ℝ)|^8249 ≤ (320075838501/2500000000000 : ℝ)^6201
        have hw : |(-2132762821/10000000000 : ℝ)|=(2132762821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s4_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875262063/2000000000 : ℝ)*x 0 + (4527887229/10000000000 : ℝ)*x 1 + (2114957403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875262063/2000000000 : ℝ)^8249 ≤ (33310191674619/100000000000000 : ℝ)^6201 := by
    have hnat : (875262063 : ℕ)^8249*100000000000000^6201 ≤ 33310191674619^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875262063 2000000000 33310191674619 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527887229/10000000000 : ℝ)^8249 ≤ (34853667133763/100000000000000 : ℝ)^6201 := by
    have hnat : (4527887229 : ℕ)^8249*100000000000000^6201 ≤ 34853667133763^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527887229 10000000000 34853667133763 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114957403/5000000000 : ℝ)^8249 ≤ (7959035295789/25000000000000 : ℝ)^6201 := by
    have hnat : (2114957403 : ℕ)^8249*25000000000000^6201 ≤ 7959035295789^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114957403 5000000000 7959035295789 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875262063/2000000000 : ℝ), (4527887229/10000000000 : ℝ), (2114957403/5000000000 : ℝ)] ![(33310191674619/100000000000000 : ℝ), (34853667133763/100000000000000 : ℝ), (7959035295789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875262063/2000000000 : ℝ)|^8249 ≤ (33310191674619/100000000000000 : ℝ)^6201
        have hw : |(875262063/2000000000 : ℝ)|=(875262063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527887229/10000000000 : ℝ)|^8249 ≤ (34853667133763/100000000000000 : ℝ)^6201
        have hw : |(4527887229/10000000000 : ℝ)|=(4527887229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114957403/5000000000 : ℝ)|^8249 ≤ (7959035295789/25000000000000 : ℝ)^6201
        have hw : |(2114957403/5000000000 : ℝ)|=(2114957403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14921/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2849/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14921/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14921/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14921/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14921/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14921/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14921/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5181/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (5417799038051487/50000000000000000000 : ℝ) := by
    have hpowers : (5181/50000 : ℝ)^1031 ≤ (5417799038051487/50000000000000000000 : ℝ)^256 := by
      have hnat : (5181 : ℕ)^1031*50000000000000000000^256 ≤ 5417799038051487^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5181 50000 5417799038051487 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5181/50000 : ℝ)) (X := (5417799038051487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14921/100000 : ℝ) ^ (1031/256 : ℝ) ≤ (47054402018161141/100000000000000000000 : ℝ) := by
    have hpowers : (14921/100000 : ℝ)^1031 ≤ (47054402018161141/100000000000000000000 : ℝ)^256 := by
      have hnat : (14921 : ℕ)^1031*100000000000000000000^256 ≤ 47054402018161141^256*100000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14921 100000 47054402018161141 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14921/100000 : ℝ)) (X := (47054402018161141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005417799038051487/25000000000000000000 : ℝ) ≤ (10000538057652441/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25005417799038051487/25000000000000000000 : ℝ)^256 ≤ (10000538057652441/10000000000000000 : ℝ)^1031 := by
      have hnat : (25005417799038051487 : ℕ)^256*10000000000000000^1031 ≤ 10000538057652441^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005417799038051487 25000000000000000000 10000538057652441 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538057652441/10000000000000000 : ℝ)) (X := (25005417799038051487/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011578000018852823/20000000000000000000 : ℝ) ≤ (625089819450961/625000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (20011578000018852823/20000000000000000000 : ℝ)^256 ≤ (625089819450961/625000000000000 : ℝ)^1031 := by
      have hnat : (20011578000018852823 : ℕ)^256*625000000000000^1031 ≤ 625089819450961^1031*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011578000018852823 20000000000000000000 625089819450961 625000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625089819450961/625000000000000 : ℝ)) (X := (20011578000018852823/20000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047054402018161141/50000000000000000000 : ℝ) ≤ (10002336164778311/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50047054402018161141/50000000000000000000 : ℝ)^256 ≤ (10002336164778311/10000000000000000 : ℝ)^1031 := by
      have hnat : (50047054402018161141 : ℕ)^256*10000000000000000^1031 ≤ 10002336164778311^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047054402018161141 50000000000000000000 10002336164778311 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002336164778311/10000000000000000 : ℝ)) (X := (50047054402018161141/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5417799038051487/50000000000000000000 : ℝ) ≤ ((45573821018799213579/45590000000000000000 : ℝ)+2*(179810712587/91180000000000 : ℝ)*(5181/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (45573821018799213579/45590000000000000000 : ℝ)+2*(179810712587/91180000000000 : ℝ)*(5181/50000 : ℝ)=(10000538057652441/10000000000000000 : ℝ) by norm_num, show 1+2*(5417799038051487/50000000000000000000 : ℝ)=(25005417799038051487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47054402018161141/100000000000000000000 : ℝ)+(5417799038051487/50000000000000000000 : ℝ) ≤ ((45573821018799213579/45590000000000000000 : ℝ)+(179810712587/91180000000000 : ℝ)*((14921/100000 : ℝ)+(5181/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (45573821018799213579/45590000000000000000 : ℝ)+(179810712587/91180000000000 : ℝ)*((14921/100000 : ℝ)+(5181/50000 : ℝ))=(625089819450961/625000000000000 : ℝ) by norm_num, show 1+(47054402018161141/100000000000000000000 : ℝ)+(5417799038051487/50000000000000000000 : ℝ)=(20011578000018852823/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47054402018161141/100000000000000000000 : ℝ) ≤ ((45573821018799213579/45590000000000000000 : ℝ)+2*(179810712587/91180000000000 : ℝ)*(14921/100000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (45573821018799213579/45590000000000000000 : ℝ)+2*(179810712587/91180000000000 : ℝ)*(14921/100000 : ℝ)=(10002336164778311/10000000000000000 : ℝ) by norm_num, show 1+2*(47054402018161141/100000000000000000000 : ℝ)=(50047054402018161141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45573821018799213579/45590000000000000000 : ℝ)*(X 1 0+X 2 0)+(179810712587/91180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (14921/100000 : ℝ)) (c := (45573821018799213579/45590000000000000000 : ℝ)) (alpha := (179810712587/91180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45573821018799213579/45590000000000000000 : ℝ)*(X 0 1+X 2 1)+(179810712587/91180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (14921/100000 : ℝ)) (c := (45573821018799213579/45590000000000000000 : ℝ)) (alpha := (179810712587/91180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45573821018799213579/45590000000000000000 : ℝ)*(X 0 2+X 1 2)+(179810712587/91180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (14921/100000 : ℝ)) (c := (45573821018799213579/45590000000000000000 : ℝ)) (alpha := (179810712587/91180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-275950007/1250000000 : ℝ)*X 0 0+(1081276599/2000000000 : ℝ)*X 0 1+(5253138357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069590113/2000000000 : ℝ)*X 1 0+(-142847109/625000000 : ℝ)*X 1 1+(1050627789/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673975053/5000000000 : ℝ)*X 2 0+(5253139411/10000000000 : ℝ)*X 2 1+(-1142776869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875258829/2000000000 : ℝ)*X 0 0+(4229028983/10000000000 : ℝ)*X 0 1+(566096161/1250000000 : ℝ)*X 0 2+(875258829/2000000000 : ℝ)*X 1 0+(4229028983/10000000000 : ℝ)*X 1 1+(566096161/1250000000 : ℝ)*X 1 2+(875258829/2000000000 : ℝ)*X 2 0+(4229028983/10000000000 : ℝ)*X 2 1+(566096161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44152167/200000000 : ℝ)*X 0 0+(2626794879/5000000000 : ℝ)*X 0 1+(5405929677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327346071/2500000000 : ℝ)*X 1 0+(-266595353/1250000000 : ℝ)*X 1 1+(5405929719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309384343/10000000000 : ℝ)*X 2 0+(5405929663/10000000000 : ℝ)*X 2 1+(-2132762821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875262063/2000000000 : ℝ)*X 0 0+(4527887229/10000000000 : ℝ)*X 0 1+(2114957403/5000000000 : ℝ)*X 0 2+(875262063/2000000000 : ℝ)*X 1 0+(4527887229/10000000000 : ℝ)*X 1 1+(2114957403/5000000000 : ℝ)*X 1 2+(875262063/2000000000 : ℝ)*X 2 0+(4527887229/10000000000 : ℝ)*X 2 1+(2114957403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12912360007941909092306694321/1139750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274558603/20000000000000 : ℝ)*(base19) + (751947701/100000000000000 : ℝ)*(base23) + (16249569/50000000000000 : ℝ)*(lower2) + (154783397/50000000000000 : ℝ)*(upper3) + (81188593/50000000000000 : ℝ)*(upper5) + (2465468736900033/50000000000000 : ℝ)*(major0) + (2465468736900033/50000000000000 : ℝ)*(major1) + (2465468736900033/50000000000000 : ℝ)*(major2) + (6525571238446007/100000000000000 : ℝ)*(sp0) + (407851085462071/6250000000000 : ℝ)*(sp1) + (130512359764769/2000000000000 : ℝ)*(sp2) + (333623837649313/10000000000000 : ℝ)*(sp3) + (9500348029/20000000000000 : ℝ)*(sp4) + (17453283639/100000000000000 : ℝ)*(sp7) + (26064498670131/781250000000 : ℝ)*(f.failure) + (6525618740186151/100000000000000 : ℝ)*(f.sum) + (2013050511131/911800000000000000000000000 : ℝ)*base65 + (13470447714957351893/2279500000000000000000000000000000 : ℝ)*base68 + (21954302536146351893/2279500000000000000000000000000000 : ℝ)*base70 + (9380940324412148107/2279500000000000000000000000000000 : ℝ)*base71 + (26035913570041/4559000000000000000000000000 : ℝ)*base74 + (9198922293898351893/2279500000000000000000000000000000 : ℝ)*base76 + (16109463249457851893/2279500000000000000000000000000000 : ℝ)*base78 + (7636201687580148107/2279500000000000000000000000000000 : ℝ)*base79 + (2484968422581/1139750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (406749/39062500000000000000 : ℝ)*base90 + (406749/39062500000000000000 : ℝ)*base92 + (406749/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28180120073055488159685801/4559000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1065195283/100000000000000 : ℝ)*(base19) + (1192428083/100000000000000 : ℝ)*(base23) + (23399669/100000000000000 : ℝ)*(upper2) + (31783489/25000000000000 : ℝ)*(upper3) + (132210209/100000000000000 : ℝ)*(upper5) + (19840567024073/400000000000 : ℝ)*(major0) + (19840567024073/400000000000 : ℝ)*(major1) + (19840567024073/400000000000 : ℝ)*(major2) + (12755814971/50000000000000 : ℝ)*(sp1) + (26918386027/100000000000000 : ℝ)*(sp2) + (6564267956387313/100000000000000 : ℝ)*(sp4) + (820530172445261/12500000000000 : ℝ)*(sp5) + (1641059961393301/25000000000000 : ℝ)*(sp6) + (839003837402241/25000000000000 : ℝ)*(sp7) + (839003837402241/25000000000000 : ℝ)*(f.failure) + (6564267956387313/100000000000000 : ℝ)*(f.sum) + (732818749437/227950000000000000000000000 : ℝ)*base66 + (113159582791372733/18236000000000000000000000000000 : ℝ)*base68 + (162452363839872733/18236000000000000000000000000000 : ℝ)*base70 + (124748278522835267/18236000000000000000000000000000 : ℝ)*base71 + (11239584475807/2279500000000000000000000000 : ℝ)*base74 + (206587068326268733/18236000000000000000000000000000 : ℝ)*base76 + (101419546593596733/18236000000000000000000000000000 : ℝ)*base78 + (175691193243792733/18236000000000000000000000000000 : ℝ)*base80 + (9266253882779/1139750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (18666311/1250000000000000000000 : ℝ)*base89 + (18666311/1250000000000000000000 : ℝ)*base91 + (18666311/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14921/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s5_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-138028757/625000000 : ℝ)*x 0 + (5397290667/10000000000 : ℝ)*x 1 + (5261666643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138028757/625000000 : ℝ)^8249 ≤ (13411040381707/100000000000000 : ℝ)^6201 := by
    have hnat : (138028757 : ℕ)^8249*100000000000000^6201 ≤ 13411040381707^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138028757 625000000 13411040381707 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397290667/10000000000 : ℝ)^8249 ≤ (8805452755263/20000000000000 : ℝ)^6201 := by
    have hnat : (5397290667 : ℕ)^8249*20000000000000^6201 ≤ 8805452755263^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397290667 10000000000 8805452755263 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261666643/10000000000 : ℝ)^8249 ≤ (21280847913141/50000000000000 : ℝ)^6201 := by
    have hnat : (5261666643 : ℕ)^8249*50000000000000^6201 ≤ 21280847913141^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261666643 10000000000 21280847913141 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138028757/625000000 : ℝ), (5397290667/10000000000 : ℝ), (5261666643/10000000000 : ℝ)] ![(13411040381707/100000000000000 : ℝ), (8805452755263/20000000000000 : ℝ), (21280847913141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138028757/625000000 : ℝ)|^8249 ≤ (13411040381707/100000000000000 : ℝ)^6201
        have hw : |(-138028757/625000000 : ℝ)|=(138028757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397290667/10000000000 : ℝ)|^8249 ≤ (8805452755263/20000000000000 : ℝ)^6201
        have hw : |(5397290667/10000000000 : ℝ)|=(5397290667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261666643/10000000000 : ℝ)|^8249 ≤ (21280847913141/50000000000000 : ℝ)^6201
        have hw : |(5261666643/10000000000 : ℝ)|=(5261666643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5220399/9765625 : ℝ)*x 0 + (-1138657759/5000000000 : ℝ)*x 1 + (164427081/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5220399/9765625 : ℝ)^8249 ≤ (43468195204317/100000000000000 : ℝ)^6201 := by
    have hnat : (5220399 : ℕ)^8249*100000000000000^6201 ≤ 43468195204317^6201*9765625^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220399 9765625 43468195204317 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138657759/5000000000 : ℝ)^8249 ≤ (1746263686983/12500000000000 : ℝ)^6201 := by
    have hnat : (1138657759 : ℕ)^8249*12500000000000^6201 ≤ 1746263686983^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138657759 5000000000 1746263686983 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164427081/312500000 : ℝ)^8249 ≤ (42561695277493/100000000000000 : ℝ)^6201 := by
    have hnat : (164427081 : ℕ)^8249*100000000000000^6201 ≤ 42561695277493^6201*312500000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164427081 312500000 42561695277493 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5220399/9765625 : ℝ), (-1138657759/5000000000 : ℝ), (164427081/312500000 : ℝ)] ![(43468195204317/100000000000000 : ℝ), (1746263686983/12500000000000 : ℝ), (42561695277493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5220399/9765625 : ℝ)|^8249 ≤ (43468195204317/100000000000000 : ℝ)^6201
        have hw : |(5220399/9765625 : ℝ)|=(5220399/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138657759/5000000000 : ℝ)|^8249 ≤ (1746263686983/12500000000000 : ℝ)^6201
        have hw : |(-1138657759/5000000000 : ℝ)|=(1138657759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164427081/312500000 : ℝ)|^8249 ≤ (42561695277493/100000000000000 : ℝ)^6201
        have hw : |(164427081/312500000 : ℝ)|=(164427081/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672844307/5000000000 : ℝ)*x 0 + (1052333327/2000000000 : ℝ)*x 1 + (-569328853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672844307/5000000000 : ℝ)^8249 ≤ (10867048903841/25000000000000 : ℝ)^6201 := by
    have hnat : (2672844307 : ℕ)^8249*25000000000000^6201 ≤ 10867048903841^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672844307 5000000000 10867048903841 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052333327/2000000000 : ℝ)^8249 ≤ (21280847870099/50000000000000 : ℝ)^6201 := by
    have hnat : (1052333327 : ℕ)^8249*50000000000000^6201 ≤ 21280847870099^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052333327 2000000000 21280847870099 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569328853/2500000000 : ℝ)^8249 ≤ (3492527157713/25000000000000 : ℝ)^6201 := by
    have hnat : (569328853 : ℕ)^8249*25000000000000^6201 ≤ 3492527157713^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569328853 2500000000 3492527157713 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672844307/5000000000 : ℝ), (1052333327/2000000000 : ℝ), (-569328853/2500000000 : ℝ)] ![(10867048903841/25000000000000 : ℝ), (21280847870099/50000000000000 : ℝ), (3492527157713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672844307/5000000000 : ℝ)|^8249 ≤ (10867048903841/25000000000000 : ℝ)^6201
        have hw : |(2672844307/5000000000 : ℝ)|=(2672844307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052333327/2000000000 : ℝ)|^8249 ≤ (21280847870099/50000000000000 : ℝ)^6201
        have hw : |(1052333327/2000000000 : ℝ)|=(1052333327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569328853/2500000000 : ℝ)|^8249 ≤ (3492527157713/25000000000000 : ℝ)^6201
        have hw : |(-569328853/2500000000 : ℝ)|=(569328853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376792727/10000000000 : ℝ)*x 0 + (4246195261/10000000000 : ℝ)*x 1 + (2255735873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376792727/10000000000 : ℝ)^8249 ≤ (8328769084393/25000000000000 : ℝ)^6201 := by
    have hnat : (4376792727 : ℕ)^8249*25000000000000^6201 ≤ 8328769084393^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376792727 10000000000 8328769084393 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246195261/10000000000 : ℝ)^8249 ≤ (31999247439001/100000000000000 : ℝ)^6201 := by
    have hnat : (4246195261 : ℕ)^8249*100000000000000^6201 ≤ 31999247439001^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246195261 10000000000 31999247439001 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255735873/5000000000 : ℝ)^8249 ≤ (6937135241691/20000000000000 : ℝ)^6201 := by
    have hnat : (2255735873 : ℕ)^8249*20000000000000^6201 ≤ 6937135241691^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255735873 5000000000 6937135241691 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376792727/10000000000 : ℝ), (4246195261/10000000000 : ℝ), (2255735873/5000000000 : ℝ)] ![(8328769084393/25000000000000 : ℝ), (31999247439001/100000000000000 : ℝ), (6937135241691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376792727/10000000000 : ℝ)|^8249 ≤ (8328769084393/25000000000000 : ℝ)^6201
        have hw : |(4376792727/10000000000 : ℝ)|=(4376792727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246195261/10000000000 : ℝ)|^8249 ≤ (31999247439001/100000000000000 : ℝ)^6201
        have hw : |(4246195261/10000000000 : ℝ)|=(4246195261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255735873/5000000000 : ℝ)|^8249 ≤ (6937135241691/20000000000000 : ℝ)^6201
        have hw : |(2255735873/5000000000 : ℝ)|=(2255735873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104232859/5000000000 : ℝ)*x 0 + (657752519/1250000000 : ℝ)*x 1 + (21081781/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104232859/5000000000 : ℝ)^8249 ≤ (2682217133579/20000000000000 : ℝ)^6201 := by
    have hnat : (1104232859 : ℕ)^8249*20000000000000^6201 ≤ 2682217133579^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104232859 5000000000 2682217133579 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657752519/1250000000 : ℝ)^8249 ≤ (665085934779/1562500000000 : ℝ)^6201 := by
    have hnat : (657752519 : ℕ)^8249*1562500000000^6201 ≤ 665085934779^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657752519 1250000000 665085934779 1562500000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21081781/39062500 : ℝ)^8249 ≤ (22011707246443/50000000000000 : ℝ)^6201 := by
    have hnat : (21081781 : ℕ)^8249*50000000000000^6201 ≤ 22011707246443^6201*39062500^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21081781 39062500 22011707246443 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104232859/5000000000 : ℝ), (657752519/1250000000 : ℝ), (21081781/39062500 : ℝ)] ![(2682217133579/20000000000000 : ℝ), (665085934779/1562500000000 : ℝ), (22011707246443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104232859/5000000000 : ℝ)|^8249 ≤ (2682217133579/20000000000000 : ℝ)^6201
        have hw : |(-1104232859/5000000000 : ℝ)|=(1104232859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657752519/1250000000 : ℝ)|^8249 ≤ (665085934779/1562500000000 : ℝ)^6201
        have hw : |(657752519/1250000000 : ℝ)|=(657752519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21081781/39062500 : ℝ)|^8249 ≤ (22011707246443/50000000000000 : ℝ)^6201
        have hw : |(21081781/39062500 : ℝ)|=(21081781/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655777679/5000000000 : ℝ)*x 0 + (-2142046219/10000000000 : ℝ)*x 1 + (5396935877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655777679/5000000000 : ℝ)^8249 ≤ (5387420682519/12500000000000 : ℝ)^6201 := by
    have hnat : (2655777679 : ℕ)^8249*12500000000000^6201 ≤ 5387420682519^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655777679 5000000000 5387420682519 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142046219/10000000000 : ℝ)^8249 ≤ (12877220677909/100000000000000 : ℝ)^6201 := by
    have hnat : (2142046219 : ℕ)^8249*100000000000000^6201 ≤ 12877220677909^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142046219 10000000000 12877220677909 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396935877/10000000000 : ℝ)^8249 ≤ (11005853463167/25000000000000 : ℝ)^6201 := by
    have hnat : (5396935877 : ℕ)^8249*25000000000000^6201 ≤ 11005853463167^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396935877 10000000000 11005853463167 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655777679/5000000000 : ℝ), (-2142046219/10000000000 : ℝ), (5396935877/10000000000 : ℝ)] ![(5387420682519/12500000000000 : ℝ), (12877220677909/100000000000000 : ℝ), (11005853463167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655777679/5000000000 : ℝ)|^8249 ≤ (5387420682519/12500000000000 : ℝ)^6201
        have hw : |(2655777679/5000000000 : ℝ)|=(2655777679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142046219/10000000000 : ℝ)|^8249 ≤ (12877220677909/100000000000000 : ℝ)^6201
        have hw : |(-2142046219/10000000000 : ℝ)|=(2142046219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396935877/10000000000 : ℝ)|^8249 ≤ (11005853463167/25000000000000 : ℝ)^6201
        have hw : |(5396935877/10000000000 : ℝ)|=(5396935877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311555341/10000000000 : ℝ)*x 0 + (1349233961/2500000000 : ℝ)*x 1 + (-1071023143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311555341/10000000000 : ℝ)^8249 ≤ (43099365276651/100000000000000 : ℝ)^6201 := by
    have hnat : (5311555341 : ℕ)^8249*100000000000000^6201 ≤ 43099365276651^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311555341 10000000000 43099365276651 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349233961/2500000000 : ℝ)^8249 ≤ (44023413494579/100000000000000 : ℝ)^6201 := by
    have hnat : (1349233961 : ℕ)^8249*100000000000000^6201 ≤ 44023413494579^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349233961 2500000000 44023413494579 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071023143/5000000000 : ℝ)^8249 ≤ (2575444242743/20000000000000 : ℝ)^6201 := by
    have hnat : (1071023143 : ℕ)^8249*20000000000000^6201 ≤ 2575444242743^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071023143 5000000000 2575444242743 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311555341/10000000000 : ℝ), (1349233961/2500000000 : ℝ), (-1071023143/5000000000 : ℝ)] ![(43099365276651/100000000000000 : ℝ), (44023413494579/100000000000000 : ℝ), (2575444242743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311555341/10000000000 : ℝ)|^8249 ≤ (43099365276651/100000000000000 : ℝ)^6201
        have hw : |(5311555341/10000000000 : ℝ)|=(5311555341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349233961/2500000000 : ℝ)|^8249 ≤ (44023413494579/100000000000000 : ℝ)^6201
        have hw : |(1349233961/2500000000 : ℝ)|=(1349233961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071023143/5000000000 : ℝ)|^8249 ≤ (2575444242743/20000000000000 : ℝ)^6201
        have hw : |(-1071023143/5000000000 : ℝ)|=(1071023143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s5_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094200967/2500000000 : ℝ)*x 0 + (180431217/400000000 : ℝ)*x 1 + (1061722317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094200967/2500000000 : ℝ)^8249 ≤ (16657594573937/50000000000000 : ℝ)^6201 := by
    have hnat : (1094200967 : ℕ)^8249*50000000000000^6201 ≤ 16657594573937^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094200967 2500000000 16657594573937 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180431217/400000000 : ℝ)^8249 ≤ (34678605869161/100000000000000 : ℝ)^6201 := by
    have hnat : (180431217 : ℕ)^8249*100000000000000^6201 ≤ 34678605869161^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180431217 400000000 34678605869161 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061722317/2500000000 : ℝ)^8249 ≤ (32006204966757/100000000000000 : ℝ)^6201 := by
    have hnat : (1061722317 : ℕ)^8249*100000000000000^6201 ≤ 32006204966757^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061722317 2500000000 32006204966757 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094200967/2500000000 : ℝ), (180431217/400000000 : ℝ), (1061722317/2500000000 : ℝ)] ![(16657594573937/50000000000000 : ℝ), (34678605869161/100000000000000 : ℝ), (32006204966757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094200967/2500000000 : ℝ)|^8249 ≤ (16657594573937/50000000000000 : ℝ)^6201
        have hw : |(1094200967/2500000000 : ℝ)|=(1094200967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180431217/400000000 : ℝ)|^8249 ≤ (34678605869161/100000000000000 : ℝ)^6201
        have hw : |(180431217/400000000 : ℝ)|=(180431217/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061722317/2500000000 : ℝ)|^8249 ≤ (32006204966757/100000000000000 : ℝ)^6201
        have hw : |(1061722317/2500000000 : ℝ)|=(1061722317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    (5591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/100 : ℝ) ^ (1031/256 : ℝ) ≤ (13783478141824653/100000000000000000000 : ℝ) := by
    have hpowers : (11/100 : ℝ)^1031 ≤ (13783478141824653/100000000000000000000 : ℝ)^256 := by
      have hnat : (11 : ℕ)^1031*100000000000000000000^256 ≤ 13783478141824653^256*100^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 100 13783478141824653 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/100 : ℝ)) (X := (13783478141824653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2849/20000 : ℝ) ^ (1031/256 : ℝ) ≤ (39039816890550369/100000000000000000000 : ℝ) := by
    have hpowers : (2849/20000 : ℝ)^1031 ≤ (39039816890550369/100000000000000000000 : ℝ)^256 := by
      have hnat : (2849 : ℕ)^1031*100000000000000000000^256 ≤ 39039816890550369^256*20000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 20000 39039816890550369 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/20000 : ℝ)) (X := (39039816890550369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013783478141824653/50000000000000000000 : ℝ) ≤ (10000684423834687/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50013783478141824653/50000000000000000000 : ℝ)^256 ≤ (10000684423834687/10000000000000000 : ℝ)^1031 := by
      have hnat : (50013783478141824653 : ℕ)^256*10000000000000000^1031 ≤ 10000684423834687^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013783478141824653 50000000000000000000 10000684423834687 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684423834687/10000000000000000 : ℝ)) (X := (50013783478141824653/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026411647516187511/50000000000000000000 : ℝ) ≤ (5000655677963397/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50026411647516187511/50000000000000000000 : ℝ)^256 ≤ (5000655677963397/5000000000000000 : ℝ)^1031 := by
      have hnat : (50026411647516187511 : ℕ)^256*5000000000000000^1031 ≤ 5000655677963397^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026411647516187511 50000000000000000000 5000655677963397 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000655677963397/5000000000000000 : ℝ)) (X := (50026411647516187511/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039039816890550369/50000000000000000000 : ℝ) ≤ (10001938288018901/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50039039816890550369/50000000000000000000 : ℝ)^256 ≤ (10001938288018901/10000000000000000 : ℝ)^1031 := by
      have hnat : (50039039816890550369 : ℕ)^256*10000000000000000^1031 ≤ 10001938288018901^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039039816890550369 50000000000000000000 10001938288018901 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001938288018901/10000000000000000 : ℝ)) (X := (50039039816890550369/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13783478141824653/100000000000000000000 : ℝ) ≤ ((589789608169403733/590000000000000000 : ℝ)+2*(626932092107/324500000000000 : ℝ)*(11/100 : ℝ))^(1031/256 : ℝ) := by
    rw [show (589789608169403733/590000000000000000 : ℝ)+2*(626932092107/324500000000000 : ℝ)*(11/100 : ℝ)=(10000684423834687/10000000000000000 : ℝ) by norm_num, show 1+2*(13783478141824653/100000000000000000000 : ℝ)=(50013783478141824653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39039816890550369/100000000000000000000 : ℝ)+(13783478141824653/100000000000000000000 : ℝ) ≤ ((589789608169403733/590000000000000000 : ℝ)+(626932092107/324500000000000 : ℝ)*((2849/20000 : ℝ)+(11/100 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (589789608169403733/590000000000000000 : ℝ)+(626932092107/324500000000000 : ℝ)*((2849/20000 : ℝ)+(11/100 : ℝ))=(5000655677963397/5000000000000000 : ℝ) by norm_num, show 1+(39039816890550369/100000000000000000000 : ℝ)+(13783478141824653/100000000000000000000 : ℝ)=(50026411647516187511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39039816890550369/100000000000000000000 : ℝ) ≤ ((589789608169403733/590000000000000000 : ℝ)+2*(626932092107/324500000000000 : ℝ)*(2849/20000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (589789608169403733/590000000000000000 : ℝ)+2*(626932092107/324500000000000 : ℝ)*(2849/20000 : ℝ)=(10001938288018901/10000000000000000 : ℝ) by norm_num, show 1+2*(39039816890550369/100000000000000000000 : ℝ)=(50039039816890550369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (589789608169403733/590000000000000000 : ℝ)*(X 1 0+X 2 0)+(626932092107/324500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (11/100 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (589789608169403733/590000000000000000 : ℝ)) (alpha := (626932092107/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (589789608169403733/590000000000000000 : ℝ)*(X 0 1+X 2 1)+(626932092107/324500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (11/100 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (589789608169403733/590000000000000000 : ℝ)) (alpha := (626932092107/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (589789608169403733/590000000000000000 : ℝ)*(X 0 2+X 1 2)+(626932092107/324500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (11/100 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (589789608169403733/590000000000000000 : ℝ)) (alpha := (626932092107/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-138028757/625000000 : ℝ)*X 0 0+(5397290667/10000000000 : ℝ)*X 0 1+(5261666643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5220399/9765625 : ℝ)*X 1 0+(-1138657759/5000000000 : ℝ)*X 1 1+(164427081/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672844307/5000000000 : ℝ)*X 2 0+(1052333327/2000000000 : ℝ)*X 2 1+(-569328853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376792727/10000000000 : ℝ)*X 0 0+(4246195261/10000000000 : ℝ)*X 0 1+(2255735873/5000000000 : ℝ)*X 0 2+(4376792727/10000000000 : ℝ)*X 1 0+(4246195261/10000000000 : ℝ)*X 1 1+(2255735873/5000000000 : ℝ)*X 1 2+(4376792727/10000000000 : ℝ)*X 2 0+(4246195261/10000000000 : ℝ)*X 2 1+(2255735873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104232859/5000000000 : ℝ)*X 0 0+(657752519/1250000000 : ℝ)*X 0 1+(21081781/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655777679/5000000000 : ℝ)*X 1 0+(-2142046219/10000000000 : ℝ)*X 1 1+(5396935877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311555341/10000000000 : ℝ)*X 2 0+(1349233961/2500000000 : ℝ)*X 2 1+(-1071023143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094200967/2500000000 : ℝ)*X 0 0+(180431217/400000000 : ℝ)*X 0 1+(1061722317/2500000000 : ℝ)*X 0 2+(1094200967/2500000000 : ℝ)*X 1 0+(180431217/400000000 : ℝ)*X 1 1+(1061722317/2500000000 : ℝ)*X 1 2+(1094200967/2500000000 : ℝ)*X 2 0+(180431217/400000000 : ℝ)*X 2 1+(1061722317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207402839723886093141306219/29500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1482110129/100000000000000 : ℝ)*(base19) + (146324609/10000000000000 : ℝ)*(base23) + (7620611/20000000000000 : ℝ)*(lower2) + (86471053/100000000000000 : ℝ)*(upper3) + (102019663/50000000000000 : ℝ)*(upper5) + (5571546664380981/100000000000000 : ℝ)*(major0) + (5571546664380981/100000000000000 : ℝ)*(major1) + (5571546664380981/100000000000000 : ℝ)*(major2) + (7373360481155099/100000000000000 : ℝ)*(sp0) + (7373401743246053/100000000000000 : ℝ)*(sp1) + (1843350440527523/25000000000000 : ℝ)*(sp2) + (1884835824992583/50000000000000 : ℝ)*(sp3) + (42744201083/100000000000000 : ℝ)*(sp4) + (3643813423/20000000000000 : ℝ)*(sp7) + (1884844934526141/50000000000000 : ℝ)*(f.failure) + (3686701612678091/50000000000000 : ℝ)*(f.sum) + (71345087812467/16225000000000000000000000000 : ℝ)*base65 + (6175045746839037197/649000000000000000000000000000000 : ℝ)*base68 + (844398620161962803/649000000000000000000000000000000 : ℝ)*base69 + (4797135142659037197/649000000000000000000000000000000 : ℝ)*base72 + (5893994855473/4056250000000000000000000000 : ℝ)*base73 + (11400072080042962803/649000000000000000000000000000000 : ℝ)*base75 + (1383201714699037197/649000000000000000000000000000000 : ℝ)*base78 + (1745487553218037197/649000000000000000000000000000000 : ℝ)*base80 + (20838854859233/16225000000000000000000000000 : ℝ)*base82 + (25343211/2500000000000000000000 : ℝ)*base89 + (25343211/2500000000000000000000 : ℝ)*base91 + (25343211/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1794400943936825006775672303/162250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106192869/6250000000000 : ℝ)*(base19) + (1930076519/100000000000000 : ℝ)*(base23) + (122666239/100000000000000 : ℝ)*(upper3) + (134322871/100000000000000 : ℝ)*(lower4) + (11983347/6250000000000 : ℝ)*(upper5) + (5600734623155827/100000000000000 : ℝ)*(major0) + (5600734623155827/100000000000000 : ℝ)*(major1) + (5600734623155827/100000000000000 : ℝ)*(major2) + (45516830931/100000000000000 : ℝ)*(sp1) + (22900398577/50000000000000 : ℝ)*(sp2) + (741203053316503/10000000000000 : ℝ)*(sp4) + (1482396663449639/20000000000000 : ℝ)*(sp5) + (3705991401145679/50000000000000 : ℝ)*(sp6) + (3789438344497219/100000000000000 : ℝ)*(sp7) + (3789438344497219/100000000000000 : ℝ)*(f.failure) + (741203053316503/10000000000000 : ℝ)*(f.sum) + (119484922423711/16225000000000000000000000000 : ℝ)*base66 + (2265417460285695899/649000000000000000000000000000000 : ℝ)*base68 + (4244959058198695899/649000000000000000000000000000000 : ℝ)*base70 + (5831246406712695899/649000000000000000000000000000000 : ℝ)*base72 + (40893043409711/16225000000000000000000000000 : ℝ)*base74 + (4010300833661695899/649000000000000000000000000000000 : ℝ)*base76 + (434053848655304101/649000000000000000000000000000000 : ℝ)*base77 + (11821753200203695899/649000000000000000000000000000000 : ℝ)*base80 + (54588334606111/16225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4372651/5000000000000000000000 : ℝ)*base90 + (4372651/5000000000000000000000 : ℝ)*base92 + (4372651/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1056_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1056_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1056_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1056_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1056_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

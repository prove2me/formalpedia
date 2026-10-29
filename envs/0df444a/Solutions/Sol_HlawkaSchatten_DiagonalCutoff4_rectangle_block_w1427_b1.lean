-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1427_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:58.502199+00:00
-- url     : https://prove2.me/submissions/cd0f9700-3a54-4469-bc81-c0ae523e8b7b

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
theorem support_rectangle_w1427_s3_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15773467/80000000 : ℝ)*x 0 + (216699383/400000000 : ℝ)*x 1 + (1047680941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15773467/80000000 : ℝ)^4387 ≤ (6013012724541/50000000000000 : ℝ)^3363 := by
    have hnat : (15773467 : ℕ)^4387*50000000000000^3363 ≤ 6013012724541^3363*80000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15773467 80000000 6013012724541 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216699383/400000000 : ℝ)^4387 ≤ (11237811380309/25000000000000 : ℝ)^3363 := by
    have hnat : (216699383 : ℕ)^4387*25000000000000^3363 ≤ 11237811380309^3363*400000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216699383 400000000 11237811380309 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047680941/2000000000 : ℝ)^4387 ≤ (268892056313/625000000000 : ℝ)^3363 := by
    have hnat : (1047680941 : ℕ)^4387*625000000000^3363 ≤ 268892056313^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047680941 2000000000 268892056313 625000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15773467/80000000 : ℝ), (216699383/400000000 : ℝ), (1047680941/2000000000 : ℝ)] ![(6013012724541/50000000000000 : ℝ), (11237811380309/25000000000000 : ℝ), (268892056313/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15773467/80000000 : ℝ)|^4387 ≤ (6013012724541/50000000000000 : ℝ)^3363
        have hw : |(-15773467/80000000 : ℝ)|=(15773467/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216699383/400000000 : ℝ)|^4387 ≤ (11237811380309/25000000000000 : ℝ)^3363
        have hw : |(216699383/400000000 : ℝ)|=(216699383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047680941/2000000000 : ℝ)|^4387 ≤ (268892056313/625000000000 : ℝ)^3363
        have hw : |(1047680941/2000000000 : ℝ)|=(1047680941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534973467/1000000000 : ℝ)*x 0 + (-2063035189/10000000000 : ℝ)*x 1 + (1309601173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534973467/1000000000 : ℝ)^4387 ≤ (11054831458563/25000000000000 : ℝ)^3363 := by
    have hnat : (534973467 : ℕ)^4387*25000000000000^3363 ≤ 11054831458563^3363*1000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534973467 1000000000 11054831458563 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063035189/10000000000 : ℝ)^4387 ≤ (6378972635459/50000000000000 : ℝ)^3363 := by
    have hnat : (2063035189 : ℕ)^4387*50000000000000^3363 ≤ 6378972635459^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063035189 10000000000 6378972635459 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309601173/2500000000 : ℝ)^4387 ≤ (21511364435401/50000000000000 : ℝ)^3363 := by
    have hnat : (1309601173 : ℕ)^4387*50000000000000^3363 ≤ 21511364435401^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309601173 2500000000 21511364435401 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534973467/1000000000 : ℝ), (-2063035189/10000000000 : ℝ), (1309601173/2500000000 : ℝ)] ![(11054831458563/25000000000000 : ℝ), (6378972635459/50000000000000 : ℝ), (21511364435401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534973467/1000000000 : ℝ)|^4387 ≤ (11054831458563/25000000000000 : ℝ)^3363
        have hw : |(534973467/1000000000 : ℝ)|=(534973467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063035189/10000000000 : ℝ)|^4387 ≤ (6378972635459/50000000000000 : ℝ)^3363
        have hw : |(-2063035189/10000000000 : ℝ)|=(2063035189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309601173/2500000000 : ℝ)|^4387 ≤ (21511364435401/50000000000000 : ℝ)^3363
        have hw : |(1309601173/2500000000 : ℝ)|=(1309601173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674867351/5000000000 : ℝ)*x 0 + (1047680931/2000000000 : ℝ)*x 1 + (-2063035197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674867351/5000000000 : ℝ)^4387 ≤ (44219326179293/100000000000000 : ℝ)^3363 := by
    have hnat : (2674867351 : ℕ)^4387*100000000000000^3363 ≤ 44219326179293^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674867351 5000000000 44219326179293 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047680931/2000000000 : ℝ)^4387 ≤ (8604545694879/20000000000000 : ℝ)^3363 := by
    have hnat : (1047680931 : ℕ)^4387*20000000000000^3363 ≤ 8604545694879^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047680931 2000000000 8604545694879 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063035197/10000000000 : ℝ)^4387 ≤ (2551589067091/20000000000000 : ℝ)^3363 := by
    have hnat : (2063035197 : ℕ)^4387*20000000000000^3363 ≤ 2551589067091^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063035197 10000000000 2551589067091 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674867351/5000000000 : ℝ), (1047680931/2000000000 : ℝ), (-2063035197/10000000000 : ℝ)] ![(44219326179293/100000000000000 : ℝ), (8604545694879/20000000000000 : ℝ), (2551589067091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674867351/5000000000 : ℝ)|^4387 ≤ (44219326179293/100000000000000 : ℝ)^3363
        have hw : |(2674867351/5000000000 : ℝ)|=(2674867351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047680931/2000000000 : ℝ)|^4387 ≤ (8604545694879/20000000000000 : ℝ)^3363
        have hw : |(1047680931/2000000000 : ℝ)|=(1047680931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063035197/10000000000 : ℝ)|^4387 ≤ (2551589067091/20000000000000 : ℝ)^3363
        have hw : |(-2063035197/10000000000 : ℝ)|=(2063035197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269013771/625000000 : ℝ)*x 0 + (1028643581/2500000000 : ℝ)*x 1 + (562712481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269013771/625000000 : ℝ)^4387 ≤ (8324516613561/25000000000000 : ℝ)^3363 := by
    have hnat : (269013771 : ℕ)^4387*25000000000000^3363 ≤ 8324516613561^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269013771 625000000 8324516613561 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028643581/2500000000 : ℝ)^4387 ≤ (6279436669239/20000000000000 : ℝ)^3363 := by
    have hnat : (1028643581 : ℕ)^4387*20000000000000^3363 ≤ 6279436669239^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028643581 2500000000 6279436669239 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562712481/1250000000 : ℝ)^4387 ≤ (35304750173983/100000000000000 : ℝ)^3363 := by
    have hnat : (562712481 : ℕ)^4387*100000000000000^3363 ≤ 35304750173983^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562712481 1250000000 35304750173983 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269013771/625000000 : ℝ), (1028643581/2500000000 : ℝ), (562712481/1250000000 : ℝ)] ![(8324516613561/25000000000000 : ℝ), (6279436669239/20000000000000 : ℝ), (35304750173983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269013771/625000000 : ℝ)|^4387 ≤ (8324516613561/25000000000000 : ℝ)^3363
        have hw : |(269013771/625000000 : ℝ)|=(269013771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028643581/2500000000 : ℝ)|^4387 ≤ (6279436669239/20000000000000 : ℝ)^3363
        have hw : |(1028643581/2500000000 : ℝ)|=(1028643581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562712481/1250000000 : ℝ)|^4387 ≤ (35304750173983/100000000000000 : ℝ)^3363
        have hw : |(562712481/1250000000 : ℝ)|=(562712481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971698441/10000000000 : ℝ)*x 0 + (5239120567/10000000000 : ℝ)*x 1 + (5416764899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971698441/10000000000 : ℝ)^4387 ≤ (1503268165357/12500000000000 : ℝ)^3363 := by
    have hnat : (1971698441 : ℕ)^4387*12500000000000^3363 ≤ 1503268165357^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971698441 10000000000 1503268165357 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239120567/10000000000 : ℝ)^4387 ≤ (43030398703759/100000000000000 : ℝ)^3363 := by
    have hnat : (5239120567 : ℕ)^4387*100000000000000^3363 ≤ 43030398703759^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239120567 10000000000 43030398703759 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416764899/10000000000 : ℝ)^4387 ≤ (44943455959037/100000000000000 : ℝ)^3363 := by
    have hnat : (5416764899 : ℕ)^4387*100000000000000^3363 ≤ 44943455959037^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416764899 10000000000 44943455959037 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971698441/10000000000 : ℝ), (5239120567/10000000000 : ℝ), (5416764899/10000000000 : ℝ)] ![(1503268165357/12500000000000 : ℝ), (43030398703759/100000000000000 : ℝ), (44943455959037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971698441/10000000000 : ℝ)|^4387 ≤ (1503268165357/12500000000000 : ℝ)^3363
        have hw : |(-1971698441/10000000000 : ℝ)|=(1971698441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239120567/10000000000 : ℝ)|^4387 ≤ (43030398703759/100000000000000 : ℝ)^3363
        have hw : |(5239120567/10000000000 : ℝ)|=(5239120567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416764899/10000000000 : ℝ)|^4387 ≤ (44943455959037/100000000000000 : ℝ)^3363
        have hw : |(5416764899/10000000000 : ℝ)|=(5416764899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662898563/1250000000 : ℝ)*x 0 + (-188467509/1000000000 : ℝ)*x 1 + (2708382433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662898563/1250000000 : ℝ)^4387 ≤ (21859053300433/50000000000000 : ℝ)^3363 := by
    have hnat : (662898563 : ℕ)^4387*50000000000000^3363 ≤ 21859053300433^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662898563 1250000000 21859053300433 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188467509/1000000000 : ℝ)^4387 ≤ (2834609446511/25000000000000 : ℝ)^3363 := by
    have hnat : (188467509 : ℕ)^4387*25000000000000^3363 ≤ 2834609446511^3363*1000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188467509 1000000000 2834609446511 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708382433/5000000000 : ℝ)^4387 ≤ (44943455601861/100000000000000 : ℝ)^3363 := by
    have hnat : (2708382433 : ℕ)^4387*100000000000000^3363 ≤ 44943455601861^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708382433 5000000000 44943455601861 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662898563/1250000000 : ℝ), (-188467509/1000000000 : ℝ), (2708382433/5000000000 : ℝ)] ![(21859053300433/50000000000000 : ℝ), (2834609446511/25000000000000 : ℝ), (44943455601861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662898563/1250000000 : ℝ)|^4387 ≤ (21859053300433/50000000000000 : ℝ)^3363
        have hw : |(662898563/1250000000 : ℝ)|=(662898563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188467509/1000000000 : ℝ)|^4387 ≤ (2834609446511/25000000000000 : ℝ)^3363
        have hw : |(-188467509/1000000000 : ℝ)|=(188467509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708382433/5000000000 : ℝ)|^4387 ≤ (44943455601861/100000000000000 : ℝ)^3363
        have hw : |(2708382433/5000000000 : ℝ)|=(2708382433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662898523/1250000000 : ℝ)*x 0 + (1083353043/2000000000 : ℝ)*x 1 + (-1884675047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662898523/1250000000 : ℝ)^4387 ≤ (349744825277/800000000000 : ℝ)^3363 := by
    have hnat : (662898523 : ℕ)^4387*800000000000^3363 ≤ 349744825277^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662898523 1250000000 349744825277 800000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083353043/2000000000 : ℝ)^4387 ≤ (44943459379259/100000000000000 : ℝ)^3363 := by
    have hnat : (1083353043 : ℕ)^4387*100000000000000^3363 ≤ 44943459379259^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083353043 2000000000 44943459379259 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884675047/10000000000 : ℝ)^4387 ≤ (11338437448581/100000000000000 : ℝ)^3363 := by
    have hnat : (1884675047 : ℕ)^4387*100000000000000^3363 ≤ 11338437448581^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884675047 10000000000 11338437448581 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662898523/1250000000 : ℝ), (1083353043/2000000000 : ℝ), (-1884675047/10000000000 : ℝ)] ![(349744825277/800000000000 : ℝ), (44943459379259/100000000000000 : ℝ), (11338437448581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662898523/1250000000 : ℝ)|^4387 ≤ (349744825277/800000000000 : ℝ)^3363
        have hw : |(662898523/1250000000 : ℝ)|=(662898523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083353043/2000000000 : ℝ)|^4387 ≤ (44943459379259/100000000000000 : ℝ)^3363
        have hw : |(1083353043/2000000000 : ℝ)|=(1083353043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884675047/10000000000 : ℝ)|^4387 ≤ (11338437448581/100000000000000 : ℝ)^3363
        have hw : |(-1884675047/10000000000 : ℝ)|=(1884675047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s3_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215212667/500000000 : ℝ)*x 0 + (2250076503/5000000000 : ℝ)*x 1 + (4116130471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215212667/500000000 : ℝ)^4387 ≤ (33298399521833/100000000000000 : ℝ)^3363 := by
    have hnat : (215212667 : ℕ)^4387*100000000000000^3363 ≤ 33298399521833^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215212667 500000000 33298399521833 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250076503/5000000000 : ℝ)^4387 ≤ (35288926016057/100000000000000 : ℝ)^3363 := by
    have hnat : (2250076503 : ℕ)^4387*100000000000000^3363 ≤ 35288926016057^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250076503 5000000000 35288926016057 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4116130471/10000000000 : ℝ)^4387 ≤ (15706337221501/50000000000000 : ℝ)^3363 := by
    have hnat : (4116130471 : ℕ)^4387*50000000000000^3363 ≤ 15706337221501^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116130471 10000000000 15706337221501 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215212667/500000000 : ℝ), (2250076503/5000000000 : ℝ), (4116130471/10000000000 : ℝ)] ![(33298399521833/100000000000000 : ℝ), (35288926016057/100000000000000 : ℝ), (15706337221501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215212667/500000000 : ℝ)|^4387 ≤ (33298399521833/100000000000000 : ℝ)^3363
        have hw : |(215212667/500000000 : ℝ)|=(215212667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250076503/5000000000 : ℝ)|^4387 ≤ (35288926016057/100000000000000 : ℝ)^3363
        have hw : |(2250076503/5000000000 : ℝ)|=(2250076503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4116130471/10000000000 : ℝ)|^4387 ≤ (15706337221501/50000000000000 : ℝ)^3363
        have hw : |(4116130471/10000000000 : ℝ)|=(4116130471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2231/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3737/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7903/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7903/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7903/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7903/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7903/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7903/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10357/100000 : ℝ) ^ (2193/512 : ℝ) ≤ (3027032570952407/50000000000000000000 : ℝ) := by
    have hpowers : (10357/100000 : ℝ)^2193 ≤ (3027032570952407/50000000000000000000 : ℝ)^512 := by
      have hnat : (10357 : ℕ)^2193*50000000000000000000^512 ≤ 3027032570952407^512*100000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10357 100000 3027032570952407 50000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10357/100000 : ℝ)) (X := (3027032570952407/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7903/50000 : ℝ) ^ (2193/512 : ℝ) ≤ (7403239280296457/20000000000000000000 : ℝ) := by
    have hpowers : (7903/50000 : ℝ)^2193 ≤ (7403239280296457/20000000000000000000 : ℝ)^512 := by
      have hnat : (7903 : ℕ)^2193*20000000000000000000^512 ≤ 7403239280296457^512*50000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7903 50000 7403239280296457 20000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7903/50000 : ℝ)) (X := (7403239280296457/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003027032570952407/25000000000000000000 : ℝ) ≤ (2500070668890069/2500000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (25003027032570952407/25000000000000000000 : ℝ)^512 ≤ (2500070668890069/2500000000000000 : ℝ)^2193 := by
      have hnat : (25003027032570952407 : ℕ)^512*2500000000000000^2193 ≤ 2500070668890069^2193*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003027032570952407 25000000000000000000 2500070668890069 2500000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070668890069/2500000000000000 : ℝ)) (X := (25003027032570952407/25000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043070261543387099/100000000000000000000 : ℝ) ≤ (2000201079203311/2000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (100043070261543387099/100000000000000000000 : ℝ)^512 ≤ (2000201079203311/2000000000000000 : ℝ)^2193 := by
      have hnat : (100043070261543387099 : ℕ)^512*2000000000000000^2193 ≤ 2000201079203311^2193*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043070261543387099 100000000000000000000 2000201079203311 2000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000201079203311/2000000000000000 : ℝ)) (X := (100043070261543387099/100000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007403239280296457/10000000000000000000 : ℝ) ≤ (5000864058236417/5000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (10007403239280296457/10000000000000000000 : ℝ)^512 ≤ (5000864058236417/5000000000000000 : ℝ)^2193 := by
      have hnat : (10007403239280296457 : ℕ)^512*5000000000000000^2193 ≤ 5000864058236417^2193*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007403239280296457 10000000000000000000 5000864058236417 5000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000864058236417/5000000000000000 : ℝ)) (X := (10007403239280296457/10000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3027032570952407/50000000000000000000 : ℝ) ≤ ((27238284933798290359/27245000000000000000 : ℝ)+2*(722720456279/544900000000000 : ℝ)*(10357/100000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (27238284933798290359/27245000000000000000 : ℝ)+2*(722720456279/544900000000000 : ℝ)*(10357/100000 : ℝ)=(2500070668890069/2500000000000000 : ℝ) by norm_num, show 1+2*(3027032570952407/50000000000000000000 : ℝ)=(25003027032570952407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7403239280296457/20000000000000000000 : ℝ)+(3027032570952407/50000000000000000000 : ℝ) ≤ ((27238284933798290359/27245000000000000000 : ℝ)+(722720456279/544900000000000 : ℝ)*((7903/50000 : ℝ)+(10357/100000 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (27238284933798290359/27245000000000000000 : ℝ)+(722720456279/544900000000000 : ℝ)*((7903/50000 : ℝ)+(10357/100000 : ℝ))=(2000201079203311/2000000000000000 : ℝ) by norm_num, show 1+(7403239280296457/20000000000000000000 : ℝ)+(3027032570952407/50000000000000000000 : ℝ)=(100043070261543387099/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7403239280296457/20000000000000000000 : ℝ) ≤ ((27238284933798290359/27245000000000000000 : ℝ)+2*(722720456279/544900000000000 : ℝ)*(7903/50000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (27238284933798290359/27245000000000000000 : ℝ)+2*(722720456279/544900000000000 : ℝ)*(7903/50000 : ℝ)=(5000864058236417/5000000000000000 : ℝ) by norm_num, show 1+2*(7403239280296457/20000000000000000000 : ℝ)=(10007403239280296457/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27238284933798290359/27245000000000000000 : ℝ)*(X 1 0+X 2 0)+(722720456279/544900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (10357/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (27238284933798290359/27245000000000000000 : ℝ)) (alpha := (722720456279/544900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27238284933798290359/27245000000000000000 : ℝ)*(X 0 1+X 2 1)+(722720456279/544900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (10357/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (27238284933798290359/27245000000000000000 : ℝ)) (alpha := (722720456279/544900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27238284933798290359/27245000000000000000 : ℝ)*(X 0 2+X 1 2)+(722720456279/544900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (10357/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (27238284933798290359/27245000000000000000 : ℝ)) (alpha := (722720456279/544900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-15773467/80000000 : ℝ)*X 0 0+(216699383/400000000 : ℝ)*X 0 1+(1047680941/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534973467/1000000000 : ℝ)*X 1 0+(-2063035189/10000000000 : ℝ)*X 1 1+(1309601173/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674867351/5000000000 : ℝ)*X 2 0+(1047680931/2000000000 : ℝ)*X 2 1+(-2063035197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269013771/625000000 : ℝ)*X 0 0+(1028643581/2500000000 : ℝ)*X 0 1+(562712481/1250000000 : ℝ)*X 0 2+(269013771/625000000 : ℝ)*X 1 0+(1028643581/2500000000 : ℝ)*X 1 1+(562712481/1250000000 : ℝ)*X 1 2+(269013771/625000000 : ℝ)*X 2 0+(1028643581/2500000000 : ℝ)*X 2 1+(562712481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1971698441/10000000000 : ℝ)*X 0 0+(5239120567/10000000000 : ℝ)*X 0 1+(5416764899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662898563/1250000000 : ℝ)*X 1 0+(-188467509/1000000000 : ℝ)*X 1 1+(2708382433/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662898523/1250000000 : ℝ)*X 2 0+(1083353043/2000000000 : ℝ)*X 2 1+(-1884675047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215212667/500000000 : ℝ)*X 0 0+(2250076503/5000000000 : ℝ)*X 0 1+(4116130471/10000000000 : ℝ)*X 0 2+(215212667/500000000 : ℝ)*X 1 0+(2250076503/5000000000 : ℝ)*X 1 1+(4116130471/10000000000 : ℝ)*X 1 2+(215212667/500000000 : ℝ)*X 2 0+(2250076503/5000000000 : ℝ)*X 2 1+(4116130471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13460540800780790064182287209/1362250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89378827/5000000000000 : ℝ)*(base19) + (71580333/4000000000000 : ℝ)*(base23) + (8271807/3125000000000 : ℝ)*(upper3) + (16835869/100000000000000 : ℝ)*(upper4) + (47915623/20000000000000 : ℝ)*(upper5) + (4083667891475717/100000000000000 : ℝ)*(major0) + (4083667891475717/100000000000000 : ℝ)*(major1) + (2041833945737859/50000000000000 : ℝ)*(major2) + (1396033265321599/25000000000000 : ℝ)*(sp0) + (698020468516107/12500000000000 : ℝ)*(sp1) + (349010234137317/6250000000000 : ℝ)*(sp2) + (1291577685011887/50000000000000 : ℝ)*(sp3) + (32474419/100000000000 : ℝ)*(sp4) + (7273925977/50000000000000 : ℝ)*(sp7) + (161448119867233/6250000000000 : ℝ)*(f.failure) + (5584165535705397/100000000000000 : ℝ)*(f.sum) + (40255180411679/10898000000000000000000000000 : ℝ)*base66 + (1144192995570187597/2724500000000000000000000000000000 : ℝ)*base68 + (440311733698576381/1362250000000000000000000000000000 : ℝ)*base69 + (1034413259401812403/2724500000000000000000000000000000 : ℝ)*base71 + (9522461792979/2179600000000000000000000000 : ℝ)*base74 + (531542171108423619/1362250000000000000000000000000000 : ℝ)*base76 + (48147765926300137597/2724500000000000000000000000000000 : ℝ)*base78 + (45451425519154137597/2724500000000000000000000000000000 : ℝ)*base80 + (109104278584947/27245000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10018811/625000000000000000000 : ℝ)*base89 + (10018811/625000000000000000000 : ℝ)*base91 + (3768811/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4449994634059441110418092981/340562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282594663/25000000000000 : ℝ)*(base19) + (209857717/20000000000000 : ℝ)*(base23) + (36767409/25000000000000 : ℝ)*(upper3) + (2334767/2000000000000 : ℝ)*(lower4) + (14688371/10000000000000 : ℝ)*(upper5) + (1029154173650747/25000000000000 : ℝ)*(major0) + (1029154173650747/25000000000000 : ℝ)*(major1) + (1029154173650747/25000000000000 : ℝ)*(major2) + (19759627021/100000000000000 : ℝ)*(sp1) + (24140706379/100000000000000 : ℝ)*(sp2) + (70365261260999/1250000000000 : ℝ)*(sp4) + (5629200010874247/100000000000000 : ℝ)*(sp5) + (1407298927721239/25000000000000 : ℝ)*(sp6) + (651003013193163/25000000000000 : ℝ)*(sp7) + (651003013193163/25000000000000 : ℝ)*(f.failure) + (70365261260999/1250000000000 : ℝ)*(f.sum) + (2097944783387/6811250000000000000000000000 : ℝ)*base66 + (3595208661547101827/681125000000000000000000000000000 : ℝ)*base68 + (4761172978655398173/681125000000000000000000000000000 : ℝ)*base69 + (25566230576148173/681125000000000000000000000000000 : ℝ)*base71 + (74087368454033/27245000000000000000000000000 : ℝ)*base74 + (12117145645037148173/681125000000000000000000000000000 : ℝ)*base75 + (2139763794723351827/681125000000000000000000000000000 : ℝ)*base78 + (3215983344064773173/681125000000000000000000000000000 : ℝ)*base79 + (6019053959113/27245000000000000000000000000 : ℝ)*base82 + (20388121/2500000000000000000000 : ℝ)*base89 + (20388121/2500000000000000000000 : ℝ)*base91 + (20388121/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1427_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1427_s4_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-493148867/2500000000 : ℝ)*x 0 + (21638879/40000000 : ℝ)*x 1 + (2622784397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493148867/2500000000 : ℝ)^4387 ≤ (6016641544489/50000000000000 : ℝ)^3363 := by
    have hnat : (493148867 : ℕ)^4387*50000000000000^3363 ≤ 6016641544489^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493148867 2500000000 6016641544489 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21638879/40000000 : ℝ)^4387 ≤ (22433608988043/50000000000000 : ℝ)^3363 := by
    have hnat : (21638879 : ℕ)^4387*50000000000000^3363 ≤ 22433608988043^3363*40000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21638879 40000000 22433608988043 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622784397/5000000000 : ℝ)^4387 ≤ (10774874730127/25000000000000 : ℝ)^3363 := by
    have hnat : (2622784397 : ℕ)^4387*25000000000000^3363 ≤ 10774874730127^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622784397 5000000000 10774874730127 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493148867/2500000000 : ℝ), (21638879/40000000 : ℝ), (2622784397/5000000000 : ℝ)] ![(6016641544489/50000000000000 : ℝ), (22433608988043/50000000000000 : ℝ), (10774874730127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493148867/2500000000 : ℝ)|^4387 ≤ (6016641544489/50000000000000 : ℝ)^3363
        have hw : |(-493148867/2500000000 : ℝ)|=(493148867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21638879/40000000 : ℝ)|^4387 ≤ (22433608988043/50000000000000 : ℝ)^3363
        have hw : |(21638879/40000000 : ℝ)|=(21638879/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622784397/5000000000 : ℝ)|^4387 ≤ (10774874730127/25000000000000 : ℝ)^3363
        have hw : |(2622784397/5000000000 : ℝ)|=(2622784397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347730739/10000000000 : ℝ)*x 0 + (-411238719/2000000000 : ℝ)*x 1 + (5245568773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347730739/10000000000 : ℝ)^4387 ≤ (22098859811083/50000000000000 : ℝ)^3363 := by
    have hnat : (5347730739 : ℕ)^4387*50000000000000^3363 ≤ 22098859811083^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347730739 10000000000 22098859811083 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411238719/2000000000 : ℝ)^4387 ≤ (6351390831009/50000000000000 : ℝ)^3363 := by
    have hnat : (411238719 : ℕ)^4387*50000000000000^3363 ≤ 6351390831009^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411238719 2000000000 6351390831009 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245568773/10000000000 : ℝ)^4387 ≤ (43099498695427/100000000000000 : ℝ)^3363 := by
    have hnat : (5245568773 : ℕ)^4387*100000000000000^3363 ≤ 43099498695427^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245568773 10000000000 43099498695427 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347730739/10000000000 : ℝ), (-411238719/2000000000 : ℝ), (5245568773/10000000000 : ℝ)] ![(22098859811083/50000000000000 : ℝ), (6351390831009/50000000000000 : ℝ), (43099498695427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347730739/10000000000 : ℝ)|^4387 ≤ (22098859811083/50000000000000 : ℝ)^3363
        have hw : |(5347730739/10000000000 : ℝ)|=(5347730739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411238719/2000000000 : ℝ)|^4387 ≤ (6351390831009/50000000000000 : ℝ)^3363
        have hw : |(-411238719/2000000000 : ℝ)|=(411238719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245568773/10000000000 : ℝ)|^4387 ≤ (43099498695427/100000000000000 : ℝ)^3363
        have hw : |(5245568773/10000000000 : ℝ)|=(5245568773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673865369/5000000000 : ℝ)*x 0 + (20490503/39062500 : ℝ)*x 1 + (-514048401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673865369/5000000000 : ℝ)^4387 ≤ (8839543922277/20000000000000 : ℝ)^3363 := by
    have hnat : (2673865369 : ℕ)^4387*20000000000000^3363 ≤ 8839543922277^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673865369 5000000000 8839543922277 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20490503/39062500 : ℝ)^4387 ≤ (10774874660459/25000000000000 : ℝ)^3363 := by
    have hnat : (20490503 : ℕ)^4387*25000000000000^3363 ≤ 10774874660459^3363*39062500^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20490503 39062500 10774874660459 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514048401/2500000000 : ℝ)^4387 ≤ (3175695433637/25000000000000 : ℝ)^3363 := by
    have hnat : (514048401 : ℕ)^4387*25000000000000^3363 ≤ 3175695433637^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514048401 2500000000 3175695433637 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673865369/5000000000 : ℝ), (20490503/39062500 : ℝ), (-514048401/2500000000 : ℝ)] ![(8839543922277/20000000000000 : ℝ), (10774874660459/25000000000000 : ℝ), (3175695433637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673865369/5000000000 : ℝ)|^4387 ≤ (8839543922277/20000000000000 : ℝ)^3363
        have hw : |(2673865369/5000000000 : ℝ)|=(2673865369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20490503/39062500 : ℝ)|^4387 ≤ (10774874660459/25000000000000 : ℝ)^3363
        have hw : |(20490503/39062500 : ℝ)|=(20490503/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514048401/2500000000 : ℝ)|^4387 ≤ (3175695433637/25000000000000 : ℝ)^3363
        have hw : |(-514048401/2500000000 : ℝ)|=(514048401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304778241/10000000000 : ℝ)*x 0 + (4130643187/10000000000 : ℝ)*x 1 + (560687057/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304778241/10000000000 : ℝ)^4387 ≤ (3330369678763/10000000000000 : ℝ)^3363 := by
    have hnat : (4304778241 : ℕ)^4387*10000000000000^3363 ≤ 3330369678763^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304778241 10000000000 3330369678763 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130643187/10000000000 : ℝ)^4387 ≤ (31557231106579/100000000000000 : ℝ)^3363 := by
    have hnat : (4130643187 : ℕ)^4387*100000000000000^3363 ≤ 31557231106579^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130643187 10000000000 31557231106579 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560687057/1250000000 : ℝ)^4387 ≤ (35139072091157/100000000000000 : ℝ)^3363 := by
    have hnat : (560687057 : ℕ)^4387*100000000000000^3363 ≤ 35139072091157^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560687057 1250000000 35139072091157 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304778241/10000000000 : ℝ), (4130643187/10000000000 : ℝ), (560687057/1250000000 : ℝ)] ![(3330369678763/10000000000000 : ℝ), (31557231106579/100000000000000 : ℝ), (35139072091157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304778241/10000000000 : ℝ)|^4387 ≤ (3330369678763/10000000000000 : ℝ)^3363
        have hw : |(4304778241/10000000000 : ℝ)|=(4304778241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130643187/10000000000 : ℝ)|^4387 ≤ (31557231106579/100000000000000 : ℝ)^3363
        have hw : |(4130643187/10000000000 : ℝ)|=(4130643187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560687057/1250000000 : ℝ)|^4387 ≤ (35139072091157/100000000000000 : ℝ)^3363
        have hw : |(560687057/1250000000 : ℝ)|=(560687057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1972607853/10000000000 : ℝ)*x 0 + (5246170077/10000000000 : ℝ)*x 1 + (676139369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1972607853/10000000000 : ℝ)^4387 ≤ (12033381645029/100000000000000 : ℝ)^3363 := by
    have hnat : (1972607853 : ℕ)^4387*100000000000000^3363 ≤ 12033381645029^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972607853 10000000000 12033381645029 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246170077/10000000000 : ℝ)^4387 ≤ (5388242960353/12500000000000 : ℝ)^3363 := by
    have hnat : (5246170077 : ℕ)^4387*12500000000000^3363 ≤ 5388242960353^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246170077 10000000000 5388242960353 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676139369/1250000000 : ℝ)^4387 ≤ (22430337328527/50000000000000 : ℝ)^3363 := by
    have hnat : (676139369 : ℕ)^4387*50000000000000^3363 ≤ 22430337328527^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676139369 1250000000 22430337328527 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1972607853/10000000000 : ℝ), (5246170077/10000000000 : ℝ), (676139369/1250000000 : ℝ)] ![(12033381645029/100000000000000 : ℝ), (5388242960353/12500000000000 : ℝ), (22430337328527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1972607853/10000000000 : ℝ)|^4387 ≤ (12033381645029/100000000000000 : ℝ)^3363
        have hw : |(-1972607853/10000000000 : ℝ)|=(1972607853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246170077/10000000000 : ℝ)|^4387 ≤ (5388242960353/12500000000000 : ℝ)^3363
        have hw : |(5246170077/10000000000 : ℝ)|=(5246170077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676139369/1250000000 : ℝ)|^4387 ≤ (22430337328527/50000000000000 : ℝ)^3363
        have hw : |(676139369/1250000000 : ℝ)|=(676139369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331566537/625000000 : ℝ)*x 0 + (-1892647369/10000000000 : ℝ)*x 1 + (2704557391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331566537/625000000 : ℝ)^4387 ≤ (10934570726543/25000000000000 : ℝ)^3363 := by
    have hnat : (331566537 : ℕ)^4387*25000000000000^3363 ≤ 10934570726543^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331566537 625000000 10934570726543 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1892647369/10000000000 : ℝ)^4387 ≤ (5700522134789/50000000000000 : ℝ)^3363 := by
    have hnat : (1892647369 : ℕ)^4387*50000000000000^3363 ≤ 5700522134789^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892647369 10000000000 5700522134789 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704557391/5000000000 : ℝ)^4387 ≤ (44860672817853/100000000000000 : ℝ)^3363 := by
    have hnat : (2704557391 : ℕ)^4387*100000000000000^3363 ≤ 44860672817853^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704557391 5000000000 44860672817853 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331566537/625000000 : ℝ), (-1892647369/10000000000 : ℝ), (2704557391/5000000000 : ℝ)] ![(10934570726543/25000000000000 : ℝ), (5700522134789/50000000000000 : ℝ), (44860672817853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331566537/625000000 : ℝ)|^4387 ≤ (10934570726543/25000000000000 : ℝ)^3363
        have hw : |(331566537/625000000 : ℝ)|=(331566537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1892647369/10000000000 : ℝ)|^4387 ≤ (5700522134789/50000000000000 : ℝ)^3363
        have hw : |(-1892647369/10000000000 : ℝ)|=(1892647369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704557391/5000000000 : ℝ)|^4387 ≤ (44860672817853/100000000000000 : ℝ)^3363
        have hw : |(2704557391/5000000000 : ℝ)|=(2704557391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061013/2000000 : ℝ)*x 0 + (5409114351/10000000000 : ℝ)*x 1 + (-1892647403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061013/2000000 : ℝ)^4387 ≤ (21869143647113/50000000000000 : ℝ)^3363 := by
    have hnat : (1061013 : ℕ)^4387*50000000000000^3363 ≤ 21869143647113^3363*2000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061013 2000000 21869143647113 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409114351/10000000000 : ℝ)^4387 ≤ (5607583519367/12500000000000 : ℝ)^3363 := by
    have hnat : (5409114351 : ℕ)^4387*12500000000000^3363 ≤ 5607583519367^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409114351 10000000000 5607583519367 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892647403/10000000000 : ℝ)^4387 ≤ (712565283547/6250000000000 : ℝ)^3363 := by
    have hnat : (1892647403 : ℕ)^4387*6250000000000^3363 ≤ 712565283547^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892647403 10000000000 712565283547 6250000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061013/2000000 : ℝ), (5409114351/10000000000 : ℝ), (-1892647403/10000000000 : ℝ)] ![(21869143647113/50000000000000 : ℝ), (5607583519367/12500000000000 : ℝ), (712565283547/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061013/2000000 : ℝ)|^4387 ≤ (21869143647113/50000000000000 : ℝ)^3363
        have hw : |(1061013/2000000 : ℝ)|=(1061013/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409114351/10000000000 : ℝ)|^4387 ≤ (5607583519367/12500000000000 : ℝ)^3363
        have hw : |(5409114351/10000000000 : ℝ)|=(5409114351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892647403/10000000000 : ℝ)|^4387 ≤ (712565283547/6250000000000 : ℝ)^3363
        have hw : |(-1892647403/10000000000 : ℝ)|=(1892647403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s4_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (860960821/2000000000 : ℝ)*x 0 + (4484195583/10000000000 : ℝ)*x 1 + (826390161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860960821/2000000000 : ℝ)^4387 ≤ (33303957810473/100000000000000 : ℝ)^3363 := by
    have hnat : (860960821 : ℕ)^4387*100000000000000^3363 ≤ 33303957810473^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860960821 2000000000 33303957810473 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484195583/10000000000 : ℝ)^4387 ≤ (35125778685411/100000000000000 : ℝ)^3363 := by
    have hnat : (4484195583 : ℕ)^4387*100000000000000^3363 ≤ 35125778685411^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484195583 10000000000 35125778685411 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826390161/2000000000 : ℝ)^4387 ≤ (31570263488397/100000000000000 : ℝ)^3363 := by
    have hnat : (826390161 : ℕ)^4387*100000000000000^3363 ≤ 31570263488397^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826390161 2000000000 31570263488397 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860960821/2000000000 : ℝ), (4484195583/10000000000 : ℝ), (826390161/2000000000 : ℝ)] ![(33303957810473/100000000000000 : ℝ), (35125778685411/100000000000000 : ℝ), (31570263488397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860960821/2000000000 : ℝ)|^4387 ≤ (33303957810473/100000000000000 : ℝ)^3363
        have hw : |(860960821/2000000000 : ℝ)|=(860960821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484195583/10000000000 : ℝ)|^4387 ≤ (35125778685411/100000000000000 : ℝ)^3363
        have hw : |(4484195583/10000000000 : ℝ)|=(4484195583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826390161/2000000000 : ℝ)|^4387 ≤ (31570263488397/100000000000000 : ℝ)^3363
        have hw : |(826390161/2000000000 : ℝ)|=(826390161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2957/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3737/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3737/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3737/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3737/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3737/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3737/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2231/20000 : ℝ) ^ (2193/512 : ℝ) ≤ (2079977868710617/25000000000000000000 : ℝ) := by
    have hpowers : (2231/20000 : ℝ)^2193 ≤ (2079977868710617/25000000000000000000 : ℝ)^512 := by
      have hnat : (2231 : ℕ)^2193*25000000000000000000^512 ≤ 2079977868710617^512*20000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2231 20000 2079977868710617 25000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2231/20000 : ℝ)) (X := (2079977868710617/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3737/25000 : ℝ) ^ (2193/512 : ℝ) ≤ (7286378321326613/25000000000000000000 : ℝ) := by
    have hpowers : (3737/25000 : ℝ)^2193 ≤ (7286378321326613/25000000000000000000 : ℝ)^512 := by
      have hnat : (3737 : ℕ)^2193*25000000000000000000^512 ≤ 7286378321326613^512*25000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3737 25000 7286378321326613 25000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3737/25000 : ℝ)) (X := (7286378321326613/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502079977868710617/12500000000000000000 : ℝ) ≤ (1000038846539307/1000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (12502079977868710617/12500000000000000000 : ℝ)^512 ≤ (1000038846539307/1000000000000000 : ℝ)^2193 := by
      have hnat : (12502079977868710617 : ℕ)^512*1000000000000000^2193 ≤ 1000038846539307^2193*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502079977868710617 12500000000000000000 1000038846539307 1000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000038846539307/1000000000000000 : ℝ)) (X := (12502079977868710617/12500000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500936635619003723/2500000000000000000 : ℝ) ≤ (1000087458019441/1000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (2500936635619003723/2500000000000000000 : ℝ)^512 ≤ (1000087458019441/1000000000000000 : ℝ)^2193 := by
      have hnat : (2500936635619003723 : ℕ)^512*1000000000000000^2193 ≤ 1000087458019441^2193*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500936635619003723 2500000000000000000 1000087458019441 1000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000087458019441/1000000000000000 : ℝ)) (X := (2500936635619003723/2500000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507286378321326613/12500000000000000000 : ℝ) ≤ (40005442779983/40000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (12507286378321326613/12500000000000000000 : ℝ)^512 ≤ (40005442779983/40000000000000 : ℝ)^2193 := by
      have hnat : (12507286378321326613 : ℕ)^512*40000000000000^2193 ≤ 40005442779983^2193*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507286378321326613 12500000000000000000 40005442779983 40000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40005442779983/40000000000000 : ℝ)) (X := (12507286378321326613/12500000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2079977868710617/25000000000000000000 : ℝ) ≤ ((3792062822801801911/3793000000000000000 : ℝ)+2*(24305740067/18965000000000 : ℝ)*(2231/20000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (3792062822801801911/3793000000000000000 : ℝ)+2*(24305740067/18965000000000 : ℝ)*(2231/20000 : ℝ)=(1000038846539307/1000000000000000 : ℝ) by norm_num, show 1+2*(2079977868710617/25000000000000000000 : ℝ)=(12502079977868710617/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7286378321326613/25000000000000000000 : ℝ)+(2079977868710617/25000000000000000000 : ℝ) ≤ ((3792062822801801911/3793000000000000000 : ℝ)+(24305740067/18965000000000 : ℝ)*((3737/25000 : ℝ)+(2231/20000 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (3792062822801801911/3793000000000000000 : ℝ)+(24305740067/18965000000000 : ℝ)*((3737/25000 : ℝ)+(2231/20000 : ℝ))=(1000087458019441/1000000000000000 : ℝ) by norm_num, show 1+(7286378321326613/25000000000000000000 : ℝ)+(2079977868710617/25000000000000000000 : ℝ)=(2500936635619003723/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7286378321326613/25000000000000000000 : ℝ) ≤ ((3792062822801801911/3793000000000000000 : ℝ)+2*(24305740067/18965000000000 : ℝ)*(3737/25000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (3792062822801801911/3793000000000000000 : ℝ)+2*(24305740067/18965000000000 : ℝ)*(3737/25000 : ℝ)=(40005442779983/40000000000000 : ℝ) by norm_num, show 1+2*(7286378321326613/25000000000000000000 : ℝ)=(12507286378321326613/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3792062822801801911/3793000000000000000 : ℝ)*(X 1 0+X 2 0)+(24305740067/18965000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (3792062822801801911/3793000000000000000 : ℝ)) (alpha := (24305740067/18965000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3792062822801801911/3793000000000000000 : ℝ)*(X 0 1+X 2 1)+(24305740067/18965000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (3792062822801801911/3793000000000000000 : ℝ)) (alpha := (24305740067/18965000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3792062822801801911/3793000000000000000 : ℝ)*(X 0 2+X 1 2)+(24305740067/18965000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (3737/25000 : ℝ)) (c := (3792062822801801911/3793000000000000000 : ℝ)) (alpha := (24305740067/18965000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-493148867/2500000000 : ℝ)*X 0 0+(21638879/40000000 : ℝ)*X 0 1+(2622784397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347730739/10000000000 : ℝ)*X 1 0+(-411238719/2000000000 : ℝ)*X 1 1+(5245568773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673865369/5000000000 : ℝ)*X 2 0+(20490503/39062500 : ℝ)*X 2 1+(-514048401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304778241/10000000000 : ℝ)*X 0 0+(4130643187/10000000000 : ℝ)*X 0 1+(560687057/1250000000 : ℝ)*X 0 2+(4304778241/10000000000 : ℝ)*X 1 0+(4130643187/10000000000 : ℝ)*X 1 1+(560687057/1250000000 : ℝ)*X 1 2+(4304778241/10000000000 : ℝ)*X 2 0+(4130643187/10000000000 : ℝ)*X 2 1+(560687057/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1972607853/10000000000 : ℝ)*X 0 0+(5246170077/10000000000 : ℝ)*X 0 1+(676139369/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331566537/625000000 : ℝ)*X 1 0+(-1892647369/10000000000 : ℝ)*X 1 1+(2704557391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061013/2000000 : ℝ)*X 2 0+(5409114351/10000000000 : ℝ)*X 2 1+(-1892647403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860960821/2000000000 : ℝ)*X 0 0+(4484195583/10000000000 : ℝ)*X 0 1+(826390161/2000000000 : ℝ)*X 0 2+(860960821/2000000000 : ℝ)*X 1 0+(4484195583/10000000000 : ℝ)*X 1 1+(826390161/2000000000 : ℝ)*X 1 2+(860960821/2000000000 : ℝ)*X 2 0+(4484195583/10000000000 : ℝ)*X 2 1+(826390161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9150659522130039742175061/948250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1791890809/100000000000000 : ℝ)*(base19) + (840381457/50000000000000 : ℝ)*(base23) + (58819003/100000000000000 : ℝ)*(lower2) + (12269083/5000000000000 : ℝ)*(upper3) + (77040747/50000000000000 : ℝ)*(upper5) + (4455064782856599/100000000000000 : ℝ)*(major0) + (4455064782856599/100000000000000 : ℝ)*(major1) + (22275323914283/500000000000 : ℝ)*(major2) + (6091991751994247/100000000000000 : ℝ)*(sp0) + (6092026265893293/100000000000000 : ℝ)*(sp1) + (6092026377021187/100000000000000 : ℝ)*(sp2) + (2818082733387901/100000000000000 : ℝ)*(sp3) + (18152894927/50000000000000 : ℝ)*(sp4) + (18452872867/100000000000000 : ℝ)*(sp7) + (88065662070649/3125000000000 : ℝ)*(f.failure) + (3046014028892051/50000000000000 : ℝ)*(f.sum) + (6482448715977/948250000000000000000000000 : ℝ)*base66 + (2921618297046360689/379300000000000000000000000000000 : ℝ)*base67 + (5302734311137313/1896500000000000000000000000000 : ℝ)*base69 + (3447060359290739311/379300000000000000000000000000000 : ℝ)*base72 + (18994559739557/3793000000000000000000000000 : ℝ)*base73 + (24383583221707813/1896500000000000000000000000000 : ℝ)*base75 + (2817395270588839311/379300000000000000000000000000000 : ℝ)*base78 + (3821687065418560689/379300000000000000000000000000000 : ℝ)*base79 + (2429594397033/3793000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3581083/312500000000000000000 : ℝ)*base89 + (3581083/312500000000000000000 : ℝ)*base91 + (456083/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28347390863149157503918827/47412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (692927553/50000000000000 : ℝ)*(base19) + (293895101/12500000000000 : ℝ)*(base23) + (64718239/25000000000000 : ℝ)*(upper2) + (3792157/25000000000000 : ℝ)*(upper3) + (68884697/20000000000000 : ℝ)*(upper5) + (2243996149907181/50000000000000 : ℝ)*(major0) + (2243996149907181/50000000000000 : ℝ)*(major1) + (2243996149907181/50000000000000 : ℝ)*(major2) + (987359031/3125000000000 : ℝ)*(sp1) + (16130272187/50000000000000 : ℝ)*(sp2) + (3068527361673311/50000000000000 : ℝ)*(sp4) + (6137021742002523/100000000000000 : ℝ)*(sp5) + (6137020111641441/100000000000000 : ℝ)*(sp6) + (354866232044059/12500000000000 : ℝ)*(sp7) + (354866232044059/12500000000000 : ℝ)*(f.failure) + (3068527361673311/50000000000000 : ℝ)*(f.sum) + (5105908358387/1896500000000000000000000000 : ℝ)*base65 + (236571959498322891/189650000000000000000000000000000 : ℝ)*base67 + (1962525207900222891/189650000000000000000000000000000 : ℝ)*base69 + (2003497922156222891/189650000000000000000000000000000 : ℝ)*base71 + (21833487746541/3793000000000000000000000000 : ℝ)*base74 + (1013867525260522891/189650000000000000000000000000000 : ℝ)*base75 + (3055118113444022891/189650000000000000000000000000000 : ℝ)*base77 + (2793371479616527109/189650000000000000000000000000000 : ℝ)*base80 + (33396506628397/3793000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (5291447/1250000000000000000000 : ℝ)*base90 + (5291447/1250000000000000000000 : ℝ)*base92 + (5291447/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1427_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3737/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1427_s5_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-986367161/5000000000 : ℝ)*x 0 + (270425371/500000000 : ℝ)*x 1 + (262334469/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986367161/5000000000 : ℝ)^4387 ≤ (12034388057533/100000000000000 : ℝ)^3363 := by
    have hnat : (986367161 : ℕ)^4387*100000000000000^3363 ≤ 12034388057533^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986367161 5000000000 12034388057533 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270425371/500000000 : ℝ)^4387 ≤ (5606762747889/12500000000000 : ℝ)^3363 := by
    have hnat : (270425371 : ℕ)^4387*12500000000000^3363 ≤ 5606762747889^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270425371 500000000 5606762747889 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262334469/500000000 : ℝ)^4387 ≤ (21555754967863/50000000000000 : ℝ)^3363 := by
    have hnat : (262334469 : ℕ)^4387*50000000000000^3363 ≤ 21555754967863^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262334469 500000000 21555754967863 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986367161/5000000000 : ℝ), (270425371/500000000 : ℝ), (262334469/500000000 : ℝ)] ![(12034388057533/100000000000000 : ℝ), (5606762747889/12500000000000 : ℝ), (21555754967863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986367161/5000000000 : ℝ)|^4387 ≤ (12034388057533/100000000000000 : ℝ)^3363
        have hw : |(-986367161/5000000000 : ℝ)|=(986367161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270425371/500000000 : ℝ)|^4387 ≤ (5606762747889/12500000000000 : ℝ)^3363
        have hw : |(270425371/500000000 : ℝ)|=(270425371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262334469/500000000 : ℝ)|^4387 ≤ (21555754967863/50000000000000 : ℝ)^3363
        have hw : |(262334469/500000000 : ℝ)|=(262334469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167106751/312500000 : ℝ)*x 0 + (-513780093/2500000000 : ℝ)*x 1 + (5246692179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167106751/312500000 : ℝ)^4387 ≤ (44194326702247/100000000000000 : ℝ)^3363 := by
    have hnat : (167106751 : ℕ)^4387*100000000000000^3363 ≤ 44194326702247^3363*312500000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167106751 312500000 44194326702247 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513780093/2500000000 : ℝ)^4387 ≤ (126941333559/1000000000000 : ℝ)^3363 := by
    have hnat : (513780093 : ℕ)^4387*1000000000000^3363 ≤ 126941333559^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513780093 2500000000 126941333559 1000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246692179/10000000000 : ℝ)^4387 ≤ (43111539937821/100000000000000 : ℝ)^3363 := by
    have hnat : (5246692179 : ℕ)^4387*100000000000000^3363 ≤ 43111539937821^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246692179 10000000000 43111539937821 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167106751/312500000 : ℝ), (-513780093/2500000000 : ℝ), (5246692179/10000000000 : ℝ)] ![(44194326702247/100000000000000 : ℝ), (126941333559/1000000000000 : ℝ), (43111539937821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167106751/312500000 : ℝ)|^4387 ≤ (44194326702247/100000000000000 : ℝ)^3363
        have hw : |(167106751/312500000 : ℝ)|=(167106751/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513780093/2500000000 : ℝ)|^4387 ≤ (126941333559/1000000000000 : ℝ)^3363
        have hw : |(-513780093/2500000000 : ℝ)|=(513780093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246692179/10000000000 : ℝ)|^4387 ≤ (43111539937821/100000000000000 : ℝ)^3363
        have hw : |(5246692179/10000000000 : ℝ)|=(5246692179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347415601/10000000000 : ℝ)*x 0 + (2623345373/5000000000 : ℝ)*x 1 + (-2055122853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347415601/10000000000 : ℝ)^4387 ≤ (44194322055591/100000000000000 : ℝ)^3363 := by
    have hnat : (5347415601 : ℕ)^4387*100000000000000^3363 ≤ 44194322055591^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347415601 10000000000 44194322055591 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623345373/5000000000 : ℝ)^4387 ≤ (43111524577691/100000000000000 : ℝ)^3363 := by
    have hnat : (2623345373 : ℕ)^4387*100000000000000^3363 ≤ 43111524577691^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623345373 5000000000 43111524577691 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055122853/10000000000 : ℝ)^4387 ≤ (12694153346849/100000000000000 : ℝ)^3363 := by
    have hnat : (2055122853 : ℕ)^4387*100000000000000^3363 ≤ 12694153346849^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055122853 10000000000 12694153346849 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347415601/10000000000 : ℝ), (2623345373/5000000000 : ℝ), (-2055122853/10000000000 : ℝ)] ![(44194322055591/100000000000000 : ℝ), (43111524577691/100000000000000 : ℝ), (12694153346849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347415601/10000000000 : ℝ)|^4387 ≤ (44194322055591/100000000000000 : ℝ)^3363
        have hw : |(5347415601/10000000000 : ℝ)|=(5347415601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623345373/5000000000 : ℝ)|^4387 ≤ (43111524577691/100000000000000 : ℝ)^3363
        have hw : |(2623345373/5000000000 : ℝ)|=(2623345373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055122853/10000000000 : ℝ)|^4387 ≤ (12694153346849/100000000000000 : ℝ)^3363
        have hw : |(-2055122853/10000000000 : ℝ)|=(2055122853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304860189/10000000000 : ℝ)*x 0 + (4133159197/10000000000 : ℝ)*x 1 + (2241480713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304860189/10000000000 : ℝ)^4387 ≤ (33304523819117/100000000000000 : ℝ)^3363 := by
    have hnat : (4304860189 : ℕ)^4387*100000000000000^3363 ≤ 33304523819117^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304860189 10000000000 33304523819117 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133159197/10000000000 : ℝ)^4387 ≤ (31582308050293/100000000000000 : ℝ)^3363 := by
    have hnat : (4133159197 : ℕ)^4387*100000000000000^3363 ≤ 31582308050293^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133159197 10000000000 31582308050293 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241480713/5000000000 : ℝ)^4387 ≤ (35113168124827/100000000000000 : ℝ)^3363 := by
    have hnat : (2241480713 : ℕ)^4387*100000000000000^3363 ≤ 35113168124827^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241480713 5000000000 35113168124827 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304860189/10000000000 : ℝ), (4133159197/10000000000 : ℝ), (2241480713/5000000000 : ℝ)] ![(33304523819117/100000000000000 : ℝ), (31582308050293/100000000000000 : ℝ), (35113168124827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304860189/10000000000 : ℝ)|^4387 ≤ (33304523819117/100000000000000 : ℝ)^3363
        have hw : |(4304860189/10000000000 : ℝ)|=(4304860189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133159197/10000000000 : ℝ)|^4387 ≤ (31582308050293/100000000000000 : ℝ)^3363
        have hw : |(4133159197/10000000000 : ℝ)|=(4133159197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241480713/5000000000 : ℝ)|^4387 ≤ (35113168124827/100000000000000 : ℝ)^3363
        have hw : |(2241480713/5000000000 : ℝ)|=(2241480713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98637263/500000000 : ℝ)*x 0 + (5247275807/10000000000 : ℝ)*x 1 + (675989791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98637263/500000000 : ℝ)^4387 ≤ (2406895020131/20000000000000 : ℝ)^3363 := by
    have hnat : (98637263 : ℕ)^4387*20000000000000^3363 ≤ 2406895020131^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98637263 500000000 2406895020131 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247275807/10000000000 : ℝ)^4387 ≤ (10779448968077/25000000000000 : ℝ)^3363 := by
    have hnat : (5247275807 : ℕ)^4387*25000000000000^3363 ≤ 10779448968077^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247275807 10000000000 10779448968077 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675989791/1250000000 : ℝ)^4387 ≤ (44847729019681/100000000000000 : ℝ)^3363 := by
    have hnat : (675989791 : ℕ)^4387*100000000000000^3363 ≤ 44847729019681^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675989791 1250000000 44847729019681 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98637263/500000000 : ℝ), (5247275807/10000000000 : ℝ), (675989791/1250000000 : ℝ)] ![(2406895020131/20000000000000 : ℝ), (10779448968077/25000000000000 : ℝ), (44847729019681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98637263/500000000 : ℝ)|^4387 ≤ (2406895020131/20000000000000 : ℝ)^3363
        have hw : |(-98637263/500000000 : ℝ)|=(98637263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247275807/10000000000 : ℝ)|^4387 ≤ (10779448968077/25000000000000 : ℝ)^3363
        have hw : |(5247275807/10000000000 : ℝ)|=(5247275807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675989791/1250000000 : ℝ)|^4387 ≤ (44847729019681/100000000000000 : ℝ)^3363
        have hw : |(675989791/1250000000 : ℝ)|=(675989791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663169671/1250000000 : ℝ)*x 0 + (-1893893767/10000000000 : ℝ)*x 1 + (2703959149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663169671/1250000000 : ℝ)^4387 ≤ (437414317487/1000000000000 : ℝ)^3363 := by
    have hnat : (663169671 : ℕ)^4387*1000000000000^3363 ≤ 437414317487^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663169671 1250000000 437414317487 1000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893893767/10000000000 : ℝ)^4387 ≤ (11410839529641/100000000000000 : ℝ)^3363 := by
    have hnat : (1893893767 : ℕ)^4387*100000000000000^3363 ≤ 11410839529641^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893893767 10000000000 11410839529641 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703959149/5000000000 : ℝ)^4387 ≤ (22423864347569/50000000000000 : ℝ)^3363 := by
    have hnat : (2703959149 : ℕ)^4387*50000000000000^3363 ≤ 22423864347569^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703959149 5000000000 22423864347569 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663169671/1250000000 : ℝ), (-1893893767/10000000000 : ℝ), (2703959149/5000000000 : ℝ)] ![(437414317487/1000000000000 : ℝ), (11410839529641/100000000000000 : ℝ), (22423864347569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663169671/1250000000 : ℝ)|^4387 ≤ (437414317487/1000000000000 : ℝ)^3363
        have hw : |(663169671/1250000000 : ℝ)|=(663169671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1893893767/10000000000 : ℝ)|^4387 ≤ (11410839529641/100000000000000 : ℝ)^3363
        have hw : |(-1893893767/10000000000 : ℝ)|=(1893893767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703959149/5000000000 : ℝ)|^4387 ≤ (22423864347569/50000000000000 : ℝ)^3363
        have hw : |(2703959149/5000000000 : ℝ)|=(2703959149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305357657/10000000000 : ℝ)*x 0 + (1351979539/2500000000 : ℝ)*x 1 + (-29592087/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305357657/10000000000 : ℝ)^4387 ≤ (43741434856957/100000000000000 : ℝ)^3363 := by
    have hnat : (5305357657 : ℕ)^4387*100000000000000^3363 ≤ 43741434856957^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305357657 10000000000 43741434856957 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351979539/2500000000 : ℝ)^4387 ≤ (44847727158967/100000000000000 : ℝ)^3363 := by
    have hnat : (1351979539 : ℕ)^4387*100000000000000^3363 ≤ 44847727158967^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351979539 2500000000 44847727158967 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29592087/156250000 : ℝ)^4387 ≤ (2852709491393/25000000000000 : ℝ)^3363 := by
    have hnat : (29592087 : ℕ)^4387*25000000000000^3363 ≤ 2852709491393^3363*156250000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29592087 156250000 2852709491393 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305357657/10000000000 : ℝ), (1351979539/2500000000 : ℝ), (-29592087/156250000 : ℝ)] ![(43741434856957/100000000000000 : ℝ), (44847727158967/100000000000000 : ℝ), (2852709491393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305357657/10000000000 : ℝ)|^4387 ≤ (43741434856957/100000000000000 : ℝ)^3363
        have hw : |(5305357657/10000000000 : ℝ)|=(5305357657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351979539/2500000000 : ℝ)|^4387 ≤ (44847727158967/100000000000000 : ℝ)^3363
        have hw : |(1351979539/2500000000 : ℝ)|=(1351979539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29592087/156250000 : ℝ)|^4387 ≤ (2852709491393/25000000000000 : ℝ)^3363
        have hw : |(-29592087/156250000 : ℝ)|=(29592087/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s5_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304885919/10000000000 : ℝ)*x 0 + (4481697533/10000000000 : ℝ)*x 1 + (4134428579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304885919/10000000000 : ℝ)^4387 ≤ (33304783491119/100000000000000 : ℝ)^3363 := by
    have hnat : (4304885919 : ℕ)^4387*100000000000000^3363 ≤ 33304783491119^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304885919 10000000000 33304783491119 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481697533/10000000000 : ℝ)^4387 ≤ (7020050963739/20000000000000 : ℝ)^3363 := by
    have hnat : (4481697533 : ℕ)^4387*20000000000000^3363 ≤ 7020050963739^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481697533 10000000000 7020050963739 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4134428579/10000000000 : ℝ)^4387 ≤ (3159496168053/10000000000000 : ℝ)^3363 := by
    have hnat : (4134428579 : ℕ)^4387*10000000000000^3363 ≤ 3159496168053^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134428579 10000000000 3159496168053 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304885919/10000000000 : ℝ), (4481697533/10000000000 : ℝ), (4134428579/10000000000 : ℝ)] ![(33304783491119/100000000000000 : ℝ), (7020050963739/20000000000000 : ℝ), (3159496168053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304885919/10000000000 : ℝ)|^4387 ≤ (33304783491119/100000000000000 : ℝ)^3363
        have hw : |(4304885919/10000000000 : ℝ)|=(4304885919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481697533/10000000000 : ℝ)|^4387 ≤ (7020050963739/20000000000000 : ℝ)^3363
        have hw : |(4481697533/10000000000 : ℝ)|=(4481697533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4134428579/10000000000 : ℝ)|^4387 ≤ (3159496168053/10000000000000 : ℝ)^3363
        have hw : |(4134428579/10000000000 : ℝ)|=(4134428579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/25000 : ℝ) ^ (2193/512 : ℝ) ≤ (8819807362510173/100000000000000000000 : ℝ) := by
    have hpowers : (2827/25000 : ℝ)^2193 ≤ (8819807362510173/100000000000000000000 : ℝ)^512 := by
      have hnat : (2827 : ℕ)^2193*100000000000000000000^512 ≤ 8819807362510173^512*25000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 25000 8819807362510173 100000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/25000 : ℝ)) (X := (8819807362510173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2957/20000 : ℝ) ^ (2193/512 : ℝ) ≤ (13904203832478201/50000000000000000000 : ℝ) := by
    have hpowers : (2957/20000 : ℝ)^2193 ≤ (13904203832478201/50000000000000000000 : ℝ)^512 := by
      have hnat : (2957 : ℕ)^2193*50000000000000000000^512 ≤ 13904203832478201^512*20000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 20000 13904203832478201 50000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/20000 : ℝ)) (X := (13904203832478201/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008819807362510173/50000000000000000000 : ℝ) ≤ (10000411804478617/10000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (50008819807362510173/50000000000000000000 : ℝ)^512 ≤ (10000411804478617/10000000000000000 : ℝ)^2193 := by
      have hnat : (50008819807362510173 : ℕ)^512*10000000000000000^2193 ≤ 10000411804478617^2193*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008819807362510173 50000000000000000000 10000411804478617 10000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411804478617/10000000000000000 : ℝ)) (X := (50008819807362510173/50000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001465128601098663/4000000000000000000 : ℝ) ≤ (10000855039396567/10000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (4001465128601098663/4000000000000000000 : ℝ)^512 ≤ (10000855039396567/10000000000000000 : ℝ)^2193 := by
      have hnat : (4001465128601098663 : ℕ)^512*10000000000000000^2193 ≤ 10000855039396567^2193*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001465128601098663 4000000000000000000 10000855039396567 10000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000855039396567/10000000000000000 : ℝ)) (X := (4001465128601098663/4000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013904203832478201/25000000000000000000 : ℝ) ≤ (10001298274314517/10000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (25013904203832478201/25000000000000000000 : ℝ)^512 ≤ (10001298274314517/10000000000000000 : ℝ)^2193 := by
      have hnat : (25013904203832478201 : ℕ)^512*10000000000000000^2193 ≤ 10001298274314517^2193*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013904203832478201 25000000000000000000 10001298274314517 10000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001298274314517/10000000000000000 : ℝ)) (X := (25013904203832478201/25000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8819807362510173/100000000000000000000 : ℝ) ≤ ((11587135881089264703/11590000000000000000 : ℝ)+2*(2954899453/2318000000000 : ℝ)*(2827/25000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (11587135881089264703/11590000000000000000 : ℝ)+2*(2954899453/2318000000000 : ℝ)*(2827/25000 : ℝ)=(10000411804478617/10000000000000000 : ℝ) by norm_num, show 1+2*(8819807362510173/100000000000000000000 : ℝ)=(50008819807362510173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13904203832478201/50000000000000000000 : ℝ)+(8819807362510173/100000000000000000000 : ℝ) ≤ ((11587135881089264703/11590000000000000000 : ℝ)+(2954899453/2318000000000 : ℝ)*((2957/20000 : ℝ)+(2827/25000 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (11587135881089264703/11590000000000000000 : ℝ)+(2954899453/2318000000000 : ℝ)*((2957/20000 : ℝ)+(2827/25000 : ℝ))=(10000855039396567/10000000000000000 : ℝ) by norm_num, show 1+(13904203832478201/50000000000000000000 : ℝ)+(8819807362510173/100000000000000000000 : ℝ)=(4001465128601098663/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13904203832478201/50000000000000000000 : ℝ) ≤ ((11587135881089264703/11590000000000000000 : ℝ)+2*(2954899453/2318000000000 : ℝ)*(2957/20000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (11587135881089264703/11590000000000000000 : ℝ)+2*(2954899453/2318000000000 : ℝ)*(2957/20000 : ℝ)=(10001298274314517/10000000000000000 : ℝ) by norm_num, show 1+2*(13904203832478201/50000000000000000000 : ℝ)=(25013904203832478201/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11587135881089264703/11590000000000000000 : ℝ)*(X 1 0+X 2 0)+(2954899453/2318000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (11587135881089264703/11590000000000000000 : ℝ)) (alpha := (2954899453/2318000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11587135881089264703/11590000000000000000 : ℝ)*(X 0 1+X 2 1)+(2954899453/2318000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (11587135881089264703/11590000000000000000 : ℝ)) (alpha := (2954899453/2318000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11587135881089264703/11590000000000000000 : ℝ)*(X 0 2+X 1 2)+(2954899453/2318000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (11587135881089264703/11590000000000000000 : ℝ)) (alpha := (2954899453/2318000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-986367161/5000000000 : ℝ)*X 0 0+(270425371/500000000 : ℝ)*X 0 1+(262334469/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167106751/312500000 : ℝ)*X 1 0+(-513780093/2500000000 : ℝ)*X 1 1+(5246692179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347415601/10000000000 : ℝ)*X 2 0+(2623345373/5000000000 : ℝ)*X 2 1+(-2055122853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4304860189/10000000000 : ℝ)*X 0 0+(4133159197/10000000000 : ℝ)*X 0 1+(2241480713/5000000000 : ℝ)*X 0 2+(4304860189/10000000000 : ℝ)*X 1 0+(4133159197/10000000000 : ℝ)*X 1 1+(2241480713/5000000000 : ℝ)*X 1 2+(4304860189/10000000000 : ℝ)*X 2 0+(4133159197/10000000000 : ℝ)*X 2 1+(2241480713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98637263/500000000 : ℝ)*X 0 0+(5247275807/10000000000 : ℝ)*X 0 1+(675989791/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663169671/1250000000 : ℝ)*X 1 0+(-1893893767/10000000000 : ℝ)*X 1 1+(2703959149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305357657/10000000000 : ℝ)*X 2 0+(1351979539/2500000000 : ℝ)*X 2 1+(-29592087/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304885919/10000000000 : ℝ)*X 0 0+(4481697533/10000000000 : ℝ)*X 0 1+(4134428579/10000000000 : ℝ)*X 0 2+(4304885919/10000000000 : ℝ)*X 1 0+(4481697533/10000000000 : ℝ)*X 1 1+(4134428579/10000000000 : ℝ)*X 1 2+(4304885919/10000000000 : ℝ)*X 2 0+(4481697533/10000000000 : ℝ)*X 2 1+(4134428579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206235574435341754615868553/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483246019/100000000000000 : ℝ)*(base19) + (192548401/100000000000000 : ℝ)*(base23) + (101009359/25000000000000 : ℝ)*(upper2) + (251780011/50000000000000 : ℝ)*(upper3) + (4519396736978651/100000000000000 : ℝ)*(major0) + (4519396736978651/100000000000000 : ℝ)*(major1) + (1129849184244663/25000000000000 : ℝ)*(major2) + (1235981527266643/20000000000000 : ℝ)*(sp0) + (617999745468171/10000000000000 : ℝ)*(sp1) + (1235985609847449/20000000000000 : ℝ)*(sp2) + (1429388048799711/50000000000000 : ℝ)*(sp3) + (45150797257/50000000000000 : ℝ)*(sp4) + (17424035521/25000000000000 : ℝ)*(sp6) + (18987641997/100000000000000 : ℝ)*(sp7) + (142939754262071/5000000000000 : ℝ)*(f.failure) + (617999793792773/10000000000000 : ℝ)*(f.sum) + (3312574173233/579500000000000000000000000 : ℝ)*base65 + (14315713307531855653/1159000000000000000000000000000000 : ℝ)*base67 + (4964280877002530089/289750000000000000000000000000000 : ℝ)*base69 + (1056324375539855653/1159000000000000000000000000000000 : ℝ)*base71 + (156548831631/115900000000000000000000000 : ℝ)*base73 + (3914013389782030089/289750000000000000000000000000000 : ℝ)*base75 + (1897562112907855653/1159000000000000000000000000000000 : ℝ)*base77 + (22224750863882855653/1159000000000000000000000000000000 : ℝ)*base79 + (1002695052411/144875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3564157/500000000000000000000 : ℝ)*base89 + (3564157/500000000000000000000 : ℝ)*base91 + (1435843/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (533959698224469220459863651/72437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (714102697/50000000000000 : ℝ)*(base19) + (545314527/25000000000000 : ℝ)*(base23) + (25886873/20000000000000 : ℝ)*(upper3) + (152304547/100000000000000 : ℝ)*(lower4) + (118358239/100000000000000 : ℝ)*(upper5) + (569038406748287/12500000000000 : ℝ)*(major0) + (569038406748287/12500000000000 : ℝ)*(major1) + (569038406748287/12500000000000 : ℝ)*(major2) + (31492057183/100000000000000 : ℝ)*(sp1) + (9499548607/20000000000000 : ℝ)*(sp2) + (1556250315109501/25000000000000 : ℝ)*(sp4) + (6224968340175427/100000000000000 : ℝ)*(sp5) + (6224951581436861/100000000000000 : ℝ)*(sp6) + (719903250456011/25000000000000 : ℝ)*(sp7) + (719903250456011/25000000000000 : ℝ)*(f.failure) + (1556250315109501/25000000000000 : ℝ)*(f.sum) + (44654969229/289750000000000000000000000 : ℝ)*base65 + (1983773491574813761/144875000000000000000000000000000 : ℝ)*base67 + (2459914145678313761/144875000000000000000000000000000 : ℝ)*base69 + (1555198797833313761/144875000000000000000000000000000 : ℝ)*base71 + (2399474176973/1159000000000000000000000000 : ℝ)*base74 + (1050164830194688761/144875000000000000000000000000000 : ℝ)*base75 + (956208804648313761/144875000000000000000000000000000 : ℝ)*base77 + (2537567857014563761/144875000000000000000000000000000 : ℝ)*base79 + (375082920773/1159000000000000000000000000 : ℝ)*base81 + (26085863/2500000000000000000000 : ℝ)*base90 + (26085863/2500000000000000000000 : ℝ)*base92 + (26085863/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1427_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1427_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1427_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1427_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1427_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1427_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

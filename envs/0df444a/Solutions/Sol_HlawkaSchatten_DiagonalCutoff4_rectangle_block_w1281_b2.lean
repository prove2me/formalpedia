-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:35.135957+00:00
-- url     : https://prove2.me/submissions/bf6d6a05-5c5c-401b-8c37-4f75c8165299

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
theorem support_rectangle_w1281_s6_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-262232131/1250000000 : ℝ)*x 0 + (1353974419/2500000000 : ℝ)*x 1 + (5242493951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262232131/1250000000 : ℝ)^4241 ≤ (6380593378809/50000000000000 : ℝ)^3217 := by
    have hnat : (262232131 : ℕ)^4241*50000000000000^3217 ≤ 6380593378809^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262232131 1250000000 6380593378809 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353974419/2500000000 : ℝ)^4241 ≤ (44554888619357/100000000000000 : ℝ)^3217 := by
    have hnat : (1353974419 : ℕ)^4241*100000000000000^3217 ≤ 44554888619357^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353974419 2500000000 44554888619357 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242493951/10000000000 : ℝ)^4241 ≤ (42683924610227/100000000000000 : ℝ)^3217 := by
    have hnat : (5242493951 : ℕ)^4241*100000000000000^3217 ≤ 42683924610227^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242493951 10000000000 42683924610227 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262232131/1250000000 : ℝ), (1353974419/2500000000 : ℝ), (5242493951/10000000000 : ℝ)] ![(6380593378809/50000000000000 : ℝ), (44554888619357/100000000000000 : ℝ), (42683924610227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262232131/1250000000 : ℝ)|^4241 ≤ (6380593378809/50000000000000 : ℝ)^3217
        have hw : |(-262232131/1250000000 : ℝ)|=(262232131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353974419/2500000000 : ℝ)|^4241 ≤ (44554888619357/100000000000000 : ℝ)^3217
        have hw : |(1353974419/2500000000 : ℝ)|=(1353974419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242493951/10000000000 : ℝ)|^4241 ≤ (42683924610227/100000000000000 : ℝ)^3217
        have hw : |(5242493951/10000000000 : ℝ)|=(5242493951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349968113/10000000000 : ℝ)*x 0 + (-1093130289/5000000000 : ℝ)*x 1 + (5242493949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349968113/10000000000 : ℝ)^4241 ≤ (10960312748237/25000000000000 : ℝ)^3217 := by
    have hnat : (5349968113 : ℕ)^4241*25000000000000^3217 ≤ 10960312748237^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349968113 10000000000 10960312748237 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093130289/5000000000 : ℝ)^4241 ≤ (13474824400651/100000000000000 : ℝ)^3217 := by
    have hnat : (1093130289 : ℕ)^4241*100000000000000^3217 ≤ 13474824400651^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093130289 5000000000 13474824400651 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242493949/10000000000 : ℝ)^4241 ≤ (1067098114719/2500000000000 : ℝ)^3217 := by
    have hnat : (5242493949 : ℕ)^4241*2500000000000^3217 ≤ 1067098114719^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242493949 10000000000 1067098114719 2500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349968113/10000000000 : ℝ), (-1093130289/5000000000 : ℝ), (5242493949/10000000000 : ℝ)] ![(10960312748237/25000000000000 : ℝ), (13474824400651/100000000000000 : ℝ), (1067098114719/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349968113/10000000000 : ℝ)|^4241 ≤ (10960312748237/25000000000000 : ℝ)^3217
        have hw : |(5349968113/10000000000 : ℝ)|=(5349968113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093130289/5000000000 : ℝ)|^4241 ≤ (13474824400651/100000000000000 : ℝ)^3217
        have hw : |(-1093130289/5000000000 : ℝ)|=(1093130289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242493949/10000000000 : ℝ)|^4241 ≤ (1067098114719/2500000000000 : ℝ)^3217
        have hw : |(5242493949/10000000000 : ℝ)|=(5242493949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069993623/2000000000 : ℝ)*x 0 + (1310623487/2500000000 : ℝ)*x 1 + (-1093130289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069993623/2000000000 : ℝ)^4241 ≤ (21920625507277/50000000000000 : ℝ)^3217 := by
    have hnat : (1069993623 : ℕ)^4241*50000000000000^3217 ≤ 21920625507277^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069993623 2000000000 21920625507277 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310623487/2500000000 : ℝ)^4241 ≤ (21341962289013/50000000000000 : ℝ)^3217 := by
    have hnat : (1310623487 : ℕ)^4241*50000000000000^3217 ≤ 21341962289013^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310623487 2500000000 21341962289013 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093130289/5000000000 : ℝ)^4241 ≤ (13474824400651/100000000000000 : ℝ)^3217 := by
    have hnat : (1093130289 : ℕ)^4241*100000000000000^3217 ≤ 13474824400651^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093130289 5000000000 13474824400651 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069993623/2000000000 : ℝ), (1310623487/2500000000 : ℝ), (-1093130289/5000000000 : ℝ)] ![(21920625507277/50000000000000 : ℝ), (21341962289013/50000000000000 : ℝ), (13474824400651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069993623/2000000000 : ℝ)|^4241 ≤ (21920625507277/50000000000000 : ℝ)^3217
        have hw : |(1069993623/2000000000 : ℝ)|=(1069993623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310623487/2500000000 : ℝ)|^4241 ≤ (21341962289013/50000000000000 : ℝ)^3217
        have hw : |(1310623487/2500000000 : ℝ)|=(1310623487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093130289/5000000000 : ℝ)|^4241 ≤ (13474824400651/100000000000000 : ℝ)^3217
        have hw : |(-1093130289/5000000000 : ℝ)|=(1093130289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342820637/10000000000 : ℝ)*x 0 + (1042214763/2500000000 : ℝ)*x 1 + (113093687/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342820637/10000000000 : ℝ)^4241 ≤ (16651042783091/50000000000000 : ℝ)^3217 := by
    have hnat : (4342820637 : ℕ)^4241*50000000000000^3217 ≤ 16651042783091^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342820637 10000000000 16651042783091 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042214763/2500000000 : ℝ)^4241 ≤ (3944348593217/12500000000000 : ℝ)^3217 := by
    have hnat : (1042214763 : ℕ)^4241*12500000000000^3217 ≤ 3944348593217^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042214763 2500000000 3944348593217 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113093687/250000000 : ℝ)^4241 ≤ (7028625133343/20000000000000 : ℝ)^3217 := by
    have hnat : (113093687 : ℕ)^4241*20000000000000^3217 ≤ 7028625133343^3217*250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113093687 250000000 7028625133343 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342820637/10000000000 : ℝ), (1042214763/2500000000 : ℝ), (113093687/250000000 : ℝ)] ![(16651042783091/50000000000000 : ℝ), (3944348593217/12500000000000 : ℝ), (7028625133343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342820637/10000000000 : ℝ)|^4241 ≤ (16651042783091/50000000000000 : ℝ)^3217
        have hw : |(4342820637/10000000000 : ℝ)|=(4342820637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042214763/2500000000 : ℝ)|^4241 ≤ (3944348593217/12500000000000 : ℝ)^3217
        have hw : |(1042214763/2500000000 : ℝ)|=(1042214763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113093687/250000000 : ℝ)|^4241 ≤ (7028625133343/20000000000000 : ℝ)^3217
        have hw : |(113093687/250000000 : ℝ)|=(113093687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048934967/5000000000 : ℝ)*x 0 + (524311217/1000000000 : ℝ)*x 1 + (5415276277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048934967/5000000000 : ℝ)^4241 ≤ (12761290093449/100000000000000 : ℝ)^3217 := by
    have hnat : (1048934967 : ℕ)^4241*100000000000000^3217 ≤ 12761290093449^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048934967 5000000000 12761290093449 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524311217/1000000000 : ℝ)^4241 ≤ (21345280211443/50000000000000 : ℝ)^3217 := by
    have hnat : (524311217 : ℕ)^4241*50000000000000^3217 ≤ 21345280211443^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524311217 1000000000 21345280211443 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415276277/10000000000 : ℝ)^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217 := by
    have hnat : (5415276277 : ℕ)^4241*5000000000000^3217 ≤ 2227407473763^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415276277 10000000000 2227407473763 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048934967/5000000000 : ℝ), (524311217/1000000000 : ℝ), (5415276277/10000000000 : ℝ)] ![(12761290093449/100000000000000 : ℝ), (21345280211443/50000000000000 : ℝ), (2227407473763/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048934967/5000000000 : ℝ)|^4241 ≤ (12761290093449/100000000000000 : ℝ)^3217
        have hw : |(-1048934967/5000000000 : ℝ)|=(1048934967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524311217/1000000000 : ℝ)|^4241 ≤ (21345280211443/50000000000000 : ℝ)^3217
        have hw : |(524311217/1000000000 : ℝ)|=(524311217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415276277/10000000000 : ℝ)|^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217
        have hw : |(5415276277/10000000000 : ℝ)|=(5415276277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305634659/10000000000 : ℝ)*x 0 + (-2013478251/10000000000 : ℝ)*x 1 + (5415276277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305634659/10000000000 : ℝ)^4241 ≤ (1355092015217/3125000000000 : ℝ)^3217 := by
    have hnat : (5305634659 : ℕ)^4241*3125000000000^3217 ≤ 1355092015217^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305634659 10000000000 1355092015217 3125000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013478251/10000000000 : ℝ)^4241 ≤ (6044453015381/50000000000000 : ℝ)^3217 := by
    have hnat : (2013478251 : ℕ)^4241*50000000000000^3217 ≤ 6044453015381^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013478251 10000000000 6044453015381 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415276277/10000000000 : ℝ)^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217 := by
    have hnat : (5415276277 : ℕ)^4241*5000000000000^3217 ≤ 2227407473763^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415276277 10000000000 2227407473763 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305634659/10000000000 : ℝ), (-2013478251/10000000000 : ℝ), (5415276277/10000000000 : ℝ)] ![(1355092015217/3125000000000 : ℝ), (6044453015381/50000000000000 : ℝ), (2227407473763/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305634659/10000000000 : ℝ)|^4241 ≤ (1355092015217/3125000000000 : ℝ)^3217
        have hw : |(5305634659/10000000000 : ℝ)|=(5305634659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2013478251/10000000000 : ℝ)|^4241 ≤ (6044453015381/50000000000000 : ℝ)^3217
        have hw : |(-2013478251/10000000000 : ℝ)|=(2013478251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415276277/10000000000 : ℝ)|^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217
        have hw : |(5415276277/10000000000 : ℝ)|=(5415276277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305634659/10000000000 : ℝ)*x 0 + (5415276277/10000000000 : ℝ)*x 1 + (-2013478251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305634659/10000000000 : ℝ)^4241 ≤ (1355092015217/3125000000000 : ℝ)^3217 := by
    have hnat : (5305634659 : ℕ)^4241*3125000000000^3217 ≤ 1355092015217^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305634659 10000000000 1355092015217 3125000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415276277/10000000000 : ℝ)^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217 := by
    have hnat : (5415276277 : ℕ)^4241*5000000000000^3217 ≤ 2227407473763^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415276277 10000000000 2227407473763 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013478251/10000000000 : ℝ)^4241 ≤ (6044453015381/50000000000000 : ℝ)^3217 := by
    have hnat : (2013478251 : ℕ)^4241*50000000000000^3217 ≤ 6044453015381^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013478251 10000000000 6044453015381 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305634659/10000000000 : ℝ), (5415276277/10000000000 : ℝ), (-2013478251/10000000000 : ℝ)] ![(1355092015217/3125000000000 : ℝ), (2227407473763/5000000000000 : ℝ), (6044453015381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305634659/10000000000 : ℝ)|^4241 ≤ (1355092015217/3125000000000 : ℝ)^3217
        have hw : |(5305634659/10000000000 : ℝ)|=(5305634659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415276277/10000000000 : ℝ)|^4241 ≤ (2227407473763/5000000000000 : ℝ)^3217
        have hw : |(5415276277/10000000000 : ℝ)|=(5415276277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2013478251/10000000000 : ℝ)|^4241 ≤ (6044453015381/50000000000000 : ℝ)^3217
        have hw : |(-2013478251/10000000000 : ℝ)|=(2013478251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s6_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342847003/10000000000 : ℝ)*x 0 + (2261241113/5000000000 : ℝ)*x 1 + (4170130811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342847003/10000000000 : ℝ)^4241 ≤ (2081397006599/6250000000000 : ℝ)^3217 := by
    have hnat : (4342847003 : ℕ)^4241*6250000000000^3217 ≤ 2081397006599^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342847003 10000000000 2081397006599 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261241113/5000000000 : ℝ)^4241 ≤ (35130168273813/100000000000000 : ℝ)^3217 := by
    have hnat : (2261241113 : ℕ)^4241*100000000000000^3217 ≤ 35130168273813^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261241113 5000000000 35130168273813 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170130811/10000000000 : ℝ)^4241 ≤ (15783739804723/50000000000000 : ℝ)^3217 := by
    have hnat : (4170130811 : ℕ)^4241*50000000000000^3217 ≤ 15783739804723^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170130811 10000000000 15783739804723 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342847003/10000000000 : ℝ), (2261241113/5000000000 : ℝ), (4170130811/10000000000 : ℝ)] ![(2081397006599/6250000000000 : ℝ), (35130168273813/100000000000000 : ℝ), (15783739804723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342847003/10000000000 : ℝ)|^4241 ≤ (2081397006599/6250000000000 : ℝ)^3217
        have hw : |(4342847003/10000000000 : ℝ)|=(4342847003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261241113/5000000000 : ℝ)|^4241 ≤ (35130168273813/100000000000000 : ℝ)^3217
        have hw : |(2261241113/5000000000 : ℝ)|=(2261241113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170130811/10000000000 : ℝ)|^4241 ≤ (15783739804723/50000000000000 : ℝ)^3217
        have hw : |(4170130811/10000000000 : ℝ)|=(4170130811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14667/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2197/20000 : ℝ) ^ (265/64 : ℝ) ≤ (5336822491962903/50000000000000000000 : ℝ) := by
    have hpowers : (2197/20000 : ℝ)^265 ≤ (5336822491962903/50000000000000000000 : ℝ)^64 := by
      have hnat : (2197 : ℕ)^265*50000000000000000000^64 ≤ 5336822491962903^64*20000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2197 20000 5336822491962903 50000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2197/20000 : ℝ)) (X := (5336822491962903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (367/2500 : ℝ) ^ (265/64 : ℝ) ≤ (35458884897101327/100000000000000000000 : ℝ) := by
    have hpowers : (367/2500 : ℝ)^265 ≤ (35458884897101327/100000000000000000000 : ℝ)^64 := by
      have hnat : (367 : ℕ)^265*100000000000000000000^64 ≤ 35458884897101327^64*2500^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 2500 35458884897101327 100000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/2500 : ℝ)) (X := (35458884897101327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005336822491962903/25000000000000000000 : ℝ) ≤ (2000103103091623/2000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (25005336822491962903/25000000000000000000 : ℝ)^64 ≤ (2000103103091623/2000000000000000 : ℝ)^265 := by
      have hnat : (25005336822491962903 : ℕ)^64*2000000000000000^265 ≤ 2000103103091623^265*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005336822491962903 25000000000000000000 2000103103091623 2000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000103103091623/2000000000000000 : ℝ)) (X := (25005336822491962903/25000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046132529881027133/100000000000000000000 : ℝ) ≤ (10001113949244997/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (100046132529881027133/100000000000000000000 : ℝ)^64 ≤ (10001113949244997/10000000000000000 : ℝ)^265 := by
      have hnat : (100046132529881027133 : ℕ)^64*10000000000000000^265 ≤ 10001113949244997^265*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046132529881027133 100000000000000000000 10001113949244997 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001113949244997/10000000000000000 : ℝ)) (X := (100046132529881027133/100000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035458884897101327/50000000000000000000 : ℝ) ≤ (10001712383031879/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (50035458884897101327/50000000000000000000 : ℝ)^64 ≤ (10001712383031879/10000000000000000 : ℝ)^265 := by
      have hnat : (50035458884897101327 : ℕ)^64*10000000000000000^265 ≤ 10001712383031879^265*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035458884897101327 50000000000000000000 10001712383031879 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712383031879/10000000000000000 : ℝ)) (X := (50035458884897101327/50000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5336822491962903/50000000000000000000 : ℝ) ≤ ((7387751447863987477/7390000000000000000 : ℝ)+2*(299216893441/184750000000000 : ℝ)*(2197/20000 : ℝ))^(265/64 : ℝ) := by
    rw [show (7387751447863987477/7390000000000000000 : ℝ)+2*(299216893441/184750000000000 : ℝ)*(2197/20000 : ℝ)=(2000103103091623/2000000000000000 : ℝ) by norm_num, show 1+2*(5336822491962903/50000000000000000000 : ℝ)=(25005336822491962903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35458884897101327/100000000000000000000 : ℝ)+(5336822491962903/50000000000000000000 : ℝ) ≤ ((7387751447863987477/7390000000000000000 : ℝ)+(299216893441/184750000000000 : ℝ)*((367/2500 : ℝ)+(2197/20000 : ℝ)))^(265/64 : ℝ) := by
    rw [show (7387751447863987477/7390000000000000000 : ℝ)+(299216893441/184750000000000 : ℝ)*((367/2500 : ℝ)+(2197/20000 : ℝ))=(10001113949244997/10000000000000000 : ℝ) by norm_num, show 1+(35458884897101327/100000000000000000000 : ℝ)+(5336822491962903/50000000000000000000 : ℝ)=(100046132529881027133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35458884897101327/100000000000000000000 : ℝ) ≤ ((7387751447863987477/7390000000000000000 : ℝ)+2*(299216893441/184750000000000 : ℝ)*(367/2500 : ℝ))^(265/64 : ℝ) := by
    rw [show (7387751447863987477/7390000000000000000 : ℝ)+2*(299216893441/184750000000000 : ℝ)*(367/2500 : ℝ)=(10001712383031879/10000000000000000 : ℝ) by norm_num, show 1+2*(35458884897101327/100000000000000000000 : ℝ)=(50035458884897101327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7387751447863987477/7390000000000000000 : ℝ)*(X 1 0+X 2 0)+(299216893441/184750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (7387751447863987477/7390000000000000000 : ℝ)) (alpha := (299216893441/184750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7387751447863987477/7390000000000000000 : ℝ)*(X 0 1+X 2 1)+(299216893441/184750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (7387751447863987477/7390000000000000000 : ℝ)) (alpha := (299216893441/184750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7387751447863987477/7390000000000000000 : ℝ)*(X 0 2+X 1 2)+(299216893441/184750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (7387751447863987477/7390000000000000000 : ℝ)) (alpha := (299216893441/184750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262232131/1250000000 : ℝ)*X 0 0+(1353974419/2500000000 : ℝ)*X 0 1+(5242493951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349968113/10000000000 : ℝ)*X 1 0+(-1093130289/5000000000 : ℝ)*X 1 1+(5242493949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069993623/2000000000 : ℝ)*X 2 0+(1310623487/2500000000 : ℝ)*X 2 1+(-1093130289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342820637/10000000000 : ℝ)*X 0 0+(1042214763/2500000000 : ℝ)*X 0 1+(113093687/250000000 : ℝ)*X 0 2+(4342820637/10000000000 : ℝ)*X 1 0+(1042214763/2500000000 : ℝ)*X 1 1+(113093687/250000000 : ℝ)*X 1 2+(4342820637/10000000000 : ℝ)*X 2 0+(1042214763/2500000000 : ℝ)*X 2 1+(113093687/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1048934967/5000000000 : ℝ)*X 0 0+(524311217/1000000000 : ℝ)*X 0 1+(5415276277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305634659/10000000000 : ℝ)*X 1 0+(-2013478251/10000000000 : ℝ)*X 1 1+(5415276277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305634659/10000000000 : ℝ)*X 2 0+(5415276277/10000000000 : ℝ)*X 2 1+(-2013478251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342847003/10000000000 : ℝ)*X 0 0+(2261241113/5000000000 : ℝ)*X 0 1+(4170130811/10000000000 : ℝ)*X 0 2+(4342847003/10000000000 : ℝ)*X 1 0+(2261241113/5000000000 : ℝ)*X 1 1+(4170130811/10000000000 : ℝ)*X 1 2+(4342847003/10000000000 : ℝ)*X 2 0+(2261241113/5000000000 : ℝ)*X 2 1+(4170130811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143725086676384265276485833/18475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374703509/25000000000000 : ℝ)*(base19) + (69761417/5000000000000 : ℝ)*(base23) + (56571409/100000000000000 : ℝ)*(lower2) + (19686887/10000000000000 : ℝ)*(upper3) + (29793337/25000000000000 : ℝ)*(upper5) + (429238353417657/10000000000000 : ℝ)*(major0) + (429238353417657/10000000000000 : ℝ)*(major1) + (429238353417657/10000000000000 : ℝ)*(major2) + (5766920003273821/100000000000000 : ℝ)*(sp0) + (1153389662606183/20000000000000 : ℝ)*(sp1) + (1441737104154153/25000000000000 : ℝ)*(sp2) + (352225146003677/12500000000000 : ℝ)*(sp3) + (29808571131/100000000000000 : ℝ)*(sp4) + (7914582109/50000000000000 : ℝ)*(sp7) + (1408908498596817/50000000000000 : ℝ)*(f.failure) + (720868726480619/12500000000000 : ℝ)*(f.sum) + (1853822726929/461875000000000000000000000 : ℝ)*base66 + (262024226740761389/73900000000000000000000000000000 : ℝ)*base67 + (18890169497761389/73900000000000000000000000000000 : ℝ)*base69 + (836288278261389/73900000000000000000000000000000 : ℝ)*base71 + (7005715555049/1847500000000000000000000000 : ℝ)*base73 + (1055195982727461389/73900000000000000000000000000000 : ℝ)*base75 + (1275898538686761389/73900000000000000000000000000000 : ℝ)*base77 + (1529604410608238611/73900000000000000000000000000000 : ℝ)*base80 + (5975884920371/1847500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10917849/5000000000000000000000 : ℝ)*base90 + (10917849/5000000000000000000000 : ℝ)*base92 + (10917849/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (571182682062211813660571361/73900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137768639/10000000000000 : ℝ)*(base19) + (1497534587/100000000000000 : ℝ)*(base23) + (156844123/100000000000000 : ℝ)*(upper3) + (1087669/2000000000000 : ℝ)*(lower4) + (158444049/100000000000000 : ℝ)*(upper5) + (864648621783969/20000000000000 : ℝ)*(major0) + (864648621783969/20000000000000 : ℝ)*(major1) + (864648621783969/20000000000000 : ℝ)*(major2) + (6869727779/25000000000000 : ℝ)*(sp1) + (14777454927/50000000000000 : ℝ)*(sp2) + (2904205303444337/50000000000000 : ℝ)*(sp4) + (5808381750291169/100000000000000 : ℝ)*(sp5) + (5808379554444233/100000000000000 : ℝ)*(sp6) + (2838075353313353/100000000000000 : ℝ)*(sp7) + (2838075353313353/100000000000000 : ℝ)*(f.failure) + (2904205303444337/50000000000000 : ℝ)*(f.sum) + (4033868003273/3695000000000000000000000000 : ℝ)*base65 + (858152007796116213/147800000000000000000000000000000 : ℝ)*base67 + (829082759516716213/147800000000000000000000000000000 : ℝ)*base69 + (522102816192116213/147800000000000000000000000000000 : ℝ)*base71 + (6069407410513/3695000000000000000000000000 : ℝ)*base73 + (1679814584295483787/147800000000000000000000000000000 : ℝ)*base76 + (442659388303716213/147800000000000000000000000000000 : ℝ)*base77 + (1459405429737283787/147800000000000000000000000000000 : ℝ)*base80 + (1447135232501/1847500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (46234641/10000000000000000000000 : ℝ)*base90 + (46234641/10000000000000000000000 : ℝ)*base92 + (46234641/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1281_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1281_s7_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-131116951/625000000 : ℝ)*x 0 + (270789119/500000000 : ℝ)*x 1 + (5242599861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131116951/625000000 : ℝ)^4241 ≤ (3190325093529/25000000000000 : ℝ)^3217 := by
    have hnat : (131116951 : ℕ)^4241*25000000000000^3217 ≤ 3190325093529^3217*625000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131116951 625000000 3190325093529 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270789119/500000000 : ℝ)^4241 ≤ (44553638202291/100000000000000 : ℝ)^3217 := by
    have hnat : (270789119 : ℕ)^4241*100000000000000^3217 ≤ 44553638202291^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270789119 500000000 44553638202291 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242599861/10000000000 : ℝ)^4241 ≤ (1707402456191/4000000000000 : ℝ)^3217 := by
    have hnat : (5242599861 : ℕ)^4241*4000000000000^3217 ≤ 1707402456191^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242599861 10000000000 1707402456191 4000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131116951/625000000 : ℝ), (270789119/500000000 : ℝ), (5242599861/10000000000 : ℝ)] ![(3190325093529/25000000000000 : ℝ), (44553638202291/100000000000000 : ℝ), (1707402456191/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131116951/625000000 : ℝ)|^4241 ≤ (3190325093529/25000000000000 : ℝ)^3217
        have hw : |(-131116951/625000000 : ℝ)|=(131116951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270789119/500000000 : ℝ)|^4241 ≤ (44553638202291/100000000000000 : ℝ)^3217
        have hw : |(270789119/500000000 : ℝ)|=(270789119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242599861/10000000000 : ℝ)|^4241 ≤ (1707402456191/4000000000000 : ℝ)^3217
        have hw : |(5242599861/10000000000 : ℝ)|=(5242599861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349938751/10000000000 : ℝ)*x 0 + (-2186159749/10000000000 : ℝ)*x 1 + (1310649957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349938751/10000000000 : ℝ)^4241 ≤ (43840933792193/100000000000000 : ℝ)^3217 := by
    have hnat : (5349938751 : ℕ)^4241*100000000000000^3217 ≤ 43840933792193^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349938751 10000000000 43840933792193 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186159749/10000000000 : ℝ)^4241 ≤ (6737002571341/50000000000000 : ℝ)^3217 := by
    have hnat : (2186159749 : ℕ)^4241*50000000000000^3217 ≤ 6737002571341^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186159749 10000000000 6737002571341 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310649957/2500000000 : ℝ)^4241 ≤ (8537012210113/20000000000000 : ℝ)^3217 := by
    have hnat : (1310649957 : ℕ)^4241*20000000000000^3217 ≤ 8537012210113^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310649957 2500000000 8537012210113 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349938751/10000000000 : ℝ), (-2186159749/10000000000 : ℝ), (1310649957/2500000000 : ℝ)] ![(43840933792193/100000000000000 : ℝ), (6737002571341/50000000000000 : ℝ), (8537012210113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349938751/10000000000 : ℝ)|^4241 ≤ (43840933792193/100000000000000 : ℝ)^3217
        have hw : |(5349938751/10000000000 : ℝ)|=(5349938751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186159749/10000000000 : ℝ)|^4241 ≤ (6737002571341/50000000000000 : ℝ)^3217
        have hw : |(-2186159749/10000000000 : ℝ)|=(2186159749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310649957/2500000000 : ℝ)|^4241 ≤ (8537012210113/20000000000000 : ℝ)^3217
        have hw : |(1310649957/2500000000 : ℝ)|=(1310649957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349938727/10000000000 : ℝ)*x 0 + (1048519969/2000000000 : ℝ)*x 1 + (-1093079879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349938727/10000000000 : ℝ)^4241 ≤ (43840933532919/100000000000000 : ℝ)^3217 := by
    have hnat : (5349938727 : ℕ)^4241*100000000000000^3217 ≤ 43840933532919^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349938727 10000000000 43840933532919 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048519969/2000000000 : ℝ)^4241 ≤ (42685061233037/100000000000000 : ℝ)^3217 := by
    have hnat : (1048519969 : ℕ)^4241*100000000000000^3217 ≤ 42685061233037^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048519969 2000000000 42685061233037 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093079879/5000000000 : ℝ)^4241 ≤ (13474005215809/100000000000000 : ℝ)^3217 := by
    have hnat : (1093079879 : ℕ)^4241*100000000000000^3217 ≤ 13474005215809^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093079879 5000000000 13474005215809 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349938727/10000000000 : ℝ), (1048519969/2000000000 : ℝ), (-1093079879/5000000000 : ℝ)] ![(43840933532919/100000000000000 : ℝ), (42685061233037/100000000000000 : ℝ), (13474005215809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349938727/10000000000 : ℝ)|^4241 ≤ (43840933532919/100000000000000 : ℝ)^3217
        have hw : |(5349938727/10000000000 : ℝ)|=(5349938727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048519969/2000000000 : ℝ)|^4241 ≤ (42685061233037/100000000000000 : ℝ)^3217
        have hw : |(1048519969/2000000000 : ℝ)|=(1048519969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093079879/5000000000 : ℝ)|^4241 ≤ (13474005215809/100000000000000 : ℝ)^3217
        have hw : |(-1093079879/5000000000 : ℝ)|=(1093079879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542853559/1250000000 : ℝ)*x 0 + (4169084383/10000000000 : ℝ)*x 1 + (4523520197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542853559/1250000000 : ℝ)^4241 ≤ (1665108238589/5000000000000 : ℝ)^3217 := by
    have hnat : (542853559 : ℕ)^4241*5000000000000^3217 ≤ 1665108238589^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542853559 1250000000 1665108238589 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169084383/10000000000 : ℝ)^4241 ≤ (31557037230539/100000000000000 : ℝ)^3217 := by
    have hnat : (4169084383 : ℕ)^4241*100000000000000^3217 ≤ 31557037230539^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169084383 10000000000 31557037230539 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523520197/10000000000 : ℝ)^4241 ≤ (35140797989673/100000000000000 : ℝ)^3217 := by
    have hnat : (4523520197 : ℕ)^4241*100000000000000^3217 ≤ 35140797989673^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523520197 10000000000 35140797989673 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542853559/1250000000 : ℝ), (4169084383/10000000000 : ℝ), (4523520197/10000000000 : ℝ)] ![(1665108238589/5000000000000 : ℝ), (31557037230539/100000000000000 : ℝ), (35140797989673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542853559/1250000000 : ℝ)|^4241 ≤ (1665108238589/5000000000000 : ℝ)^3217
        have hw : |(542853559/1250000000 : ℝ)|=(542853559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169084383/10000000000 : ℝ)|^4241 ≤ (31557037230539/100000000000000 : ℝ)^3217
        have hw : |(4169084383/10000000000 : ℝ)|=(4169084383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523520197/10000000000 : ℝ)|^4241 ≤ (35140797989673/100000000000000 : ℝ)^3217
        have hw : |(4523520197/10000000000 : ℝ)|=(4523520197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097884021/10000000000 : ℝ)*x 0 + (40962629/78125000 : ℝ)*x 1 + (1083032517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097884021/10000000000 : ℝ)^4241 ≤ (12761403060609/100000000000000 : ℝ)^3217 := by
    have hnat : (2097884021 : ℕ)^4241*100000000000000^3217 ≤ 12761403060609^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097884021 10000000000 12761403060609 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40962629/78125000 : ℝ)^4241 ≤ (42691680429149/100000000000000 : ℝ)^3217 := by
    have hnat : (40962629 : ℕ)^4241*100000000000000^3217 ≤ 42691680429149^3217*78125000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40962629 78125000 42691680429149 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083032517/2000000000 : ℝ)^4241 ≤ (8909383299799/20000000000000 : ℝ)^3217 := by
    have hnat : (1083032517 : ℕ)^4241*20000000000000^3217 ≤ 8909383299799^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083032517 2000000000 8909383299799 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097884021/10000000000 : ℝ), (40962629/78125000 : ℝ), (1083032517/2000000000 : ℝ)] ![(12761403060609/100000000000000 : ℝ), (42691680429149/100000000000000 : ℝ), (8909383299799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097884021/10000000000 : ℝ)|^4241 ≤ (12761403060609/100000000000000 : ℝ)^3217
        have hw : |(-2097884021/10000000000 : ℝ)|=(2097884021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40962629/78125000 : ℝ)|^4241 ≤ (42691680429149/100000000000000 : ℝ)^3217
        have hw : |(40962629/78125000 : ℝ)|=(40962629/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083032517/2000000000 : ℝ)|^4241 ≤ (8909383299799/20000000000000 : ℝ)^3217
        have hw : |(1083032517/2000000000 : ℝ)|=(1083032517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305661821/10000000000 : ℝ)*x 0 + (-1006798523/5000000000 : ℝ)*x 1 + (5415162587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305661821/10000000000 : ℝ)^4241 ≤ (43363237145169/100000000000000 : ℝ)^3217 := by
    have hnat : (5305661821 : ℕ)^4241*100000000000000^3217 ≤ 43363237145169^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305661821 10000000000 43363237145169 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006798523/5000000000 : ℝ)^4241 ≤ (12089846315767/100000000000000 : ℝ)^3217 := by
    have hnat : (1006798523 : ℕ)^4241*100000000000000^3217 ≤ 12089846315767^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006798523 5000000000 12089846315767 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415162587/10000000000 : ℝ)^4241 ≤ (11136729130171/25000000000000 : ℝ)^3217 := by
    have hnat : (5415162587 : ℕ)^4241*25000000000000^3217 ≤ 11136729130171^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415162587 10000000000 11136729130171 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305661821/10000000000 : ℝ), (-1006798523/5000000000 : ℝ), (5415162587/10000000000 : ℝ)] ![(43363237145169/100000000000000 : ℝ), (12089846315767/100000000000000 : ℝ), (11136729130171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305661821/10000000000 : ℝ)|^4241 ≤ (43363237145169/100000000000000 : ℝ)^3217
        have hw : |(5305661821/10000000000 : ℝ)|=(5305661821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006798523/5000000000 : ℝ)|^4241 ≤ (12089846315767/100000000000000 : ℝ)^3217
        have hw : |(-1006798523/5000000000 : ℝ)|=(1006798523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415162587/10000000000 : ℝ)|^4241 ≤ (11136729130171/25000000000000 : ℝ)^3217
        have hw : |(5415162587/10000000000 : ℝ)|=(5415162587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061132361/2000000000 : ℝ)*x 0 + (5415162593/10000000000 : ℝ)*x 1 + (-100679853/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061132361/2000000000 : ℝ)^4241 ≤ (5420404621597/12500000000000 : ℝ)^3217 := by
    have hnat : (1061132361 : ℕ)^4241*12500000000000^3217 ≤ 5420404621597^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061132361 2000000000 5420404621597 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415162593/10000000000 : ℝ)^4241 ≤ (44546916585753/100000000000000 : ℝ)^3217 := by
    have hnat : (5415162593 : ℕ)^4241*100000000000000^3217 ≤ 44546916585753^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415162593 10000000000 44546916585753 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100679853/500000000 : ℝ)^4241 ≤ (12089846426581/100000000000000 : ℝ)^3217 := by
    have hnat : (100679853 : ℕ)^4241*100000000000000^3217 ≤ 12089846426581^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100679853 500000000 12089846426581 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061132361/2000000000 : ℝ), (5415162593/10000000000 : ℝ), (-100679853/500000000 : ℝ)] ![(5420404621597/12500000000000 : ℝ), (44546916585753/100000000000000 : ℝ), (12089846426581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061132361/2000000000 : ℝ)|^4241 ≤ (5420404621597/12500000000000 : ℝ)^3217
        have hw : |(1061132361/2000000000 : ℝ)|=(1061132361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415162593/10000000000 : ℝ)|^4241 ≤ (44546916585753/100000000000000 : ℝ)^3217
        have hw : |(5415162593/10000000000 : ℝ)|=(5415162593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100679853/500000000 : ℝ)|^4241 ≤ (12089846426581/100000000000000 : ℝ)^3217
        have hw : |(-100679853/500000000 : ℝ)|=(100679853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s7_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542856847/1250000000 : ℝ)*x 0 + (4522258093/10000000000 : ℝ)*x 1 + (130323529/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542856847/1250000000 : ℝ)^4241 ≤ (33302430684563/100000000000000 : ℝ)^3217 := by
    have hnat : (542856847 : ℕ)^4241*100000000000000^3217 ≤ 33302430684563^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542856847 1250000000 33302430684563 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522258093/10000000000 : ℝ)^4241 ≤ (8781968265261/25000000000000 : ℝ)^3217 := by
    have hnat : (4522258093 : ℕ)^4241*25000000000000^3217 ≤ 8781968265261^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522258093 10000000000 8781968265261 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130323529/312500000 : ℝ)^4241 ≤ (6313939247599/20000000000000 : ℝ)^3217 := by
    have hnat : (130323529 : ℕ)^4241*20000000000000^3217 ≤ 6313939247599^3217*312500000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130323529 312500000 6313939247599 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542856847/1250000000 : ℝ), (4522258093/10000000000 : ℝ), (130323529/312500000 : ℝ)] ![(33302430684563/100000000000000 : ℝ), (8781968265261/25000000000000 : ℝ), (6313939247599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542856847/1250000000 : ℝ)|^4241 ≤ (33302430684563/100000000000000 : ℝ)^3217
        have hw : |(542856847/1250000000 : ℝ)|=(542856847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522258093/10000000000 : ℝ)|^4241 ≤ (8781968265261/25000000000000 : ℝ)^3217
        have hw : |(4522258093/10000000000 : ℝ)|=(4522258093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130323529/312500000 : ℝ)|^4241 ≤ (6313939247599/20000000000000 : ℝ)^3217
        have hw : |(130323529/312500000 : ℝ)|=(130323529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10999/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1833/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10997/100000 : ℝ) ^ (265/64 : ℝ) ≤ (670125440109341/6250000000000000000 : ℝ) := by
    have hpowers : (10997/100000 : ℝ)^265 ≤ (670125440109341/6250000000000000000 : ℝ)^64 := by
      have hnat : (10997 : ℕ)^265*6250000000000000000^64 ≤ 670125440109341^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10997 100000 670125440109341 6250000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10997/100000 : ℝ)) (X := (670125440109341/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14667/100000 : ℝ) ^ (265/64 : ℝ) ≤ (35329046154561183/100000000000000000000 : ℝ) := by
    have hpowers : (14667/100000 : ℝ)^265 ≤ (35329046154561183/100000000000000000000 : ℝ)^64 := by
      have hnat : (14667 : ℕ)^265*100000000000000000000^64 ≤ 35329046154561183^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14667 100000 35329046154561183 100000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14667/100000 : ℝ)) (X := (35329046154561183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125670125440109341/3125000000000000000 : ℝ) ≤ (10000517851057737/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (3125670125440109341/3125000000000000000 : ℝ)^64 ≤ (10000517851057737/10000000000000000 : ℝ)^265 := by
      have hnat : (3125670125440109341 : ℕ)^64*10000000000000000^265 ≤ 10000517851057737^265*3125000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125670125440109341 3125000000000000000 10000517851057737 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000517851057737/10000000000000000 : ℝ)) (X := (3125670125440109341/3125000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046051053196310639/100000000000000000000 : ℝ) ≤ (10001111982193843/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (100046051053196310639/100000000000000000000 : ℝ)^64 ≤ (10001111982193843/10000000000000000 : ℝ)^265 := by
      have hnat : (100046051053196310639 : ℕ)^64*10000000000000000^265 ≤ 10001111982193843^265*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046051053196310639 100000000000000000000 10001111982193843 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111982193843/10000000000000000 : ℝ)) (X := (100046051053196310639/100000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035329046154561183/50000000000000000000 : ℝ) ≤ (10001706113329949/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (50035329046154561183/50000000000000000000 : ℝ)^64 ≤ (10001706113329949/10000000000000000 : ℝ)^265 := by
      have hnat : (50035329046154561183 : ℕ)^64*10000000000000000^265 ≤ 10001706113329949^265*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035329046154561183 50000000000000000000 10001706113329949 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001706113329949/10000000000000000 : ℝ)) (X := (50035329046154561183/50000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(670125440109341/6250000000000000000 : ℝ) ≤ ((18344416596587189713/18350000000000000000 : ℝ)+2*(297065568053/183500000000000 : ℝ)*(10997/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (18344416596587189713/18350000000000000000 : ℝ)+2*(297065568053/183500000000000 : ℝ)*(10997/100000 : ℝ)=(10000517851057737/10000000000000000 : ℝ) by norm_num, show 1+2*(670125440109341/6250000000000000000 : ℝ)=(3125670125440109341/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35329046154561183/100000000000000000000 : ℝ)+(670125440109341/6250000000000000000 : ℝ) ≤ ((18344416596587189713/18350000000000000000 : ℝ)+(297065568053/183500000000000 : ℝ)*((14667/100000 : ℝ)+(10997/100000 : ℝ)))^(265/64 : ℝ) := by
    rw [show (18344416596587189713/18350000000000000000 : ℝ)+(297065568053/183500000000000 : ℝ)*((14667/100000 : ℝ)+(10997/100000 : ℝ))=(10001111982193843/10000000000000000 : ℝ) by norm_num, show 1+(35329046154561183/100000000000000000000 : ℝ)+(670125440109341/6250000000000000000 : ℝ)=(100046051053196310639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35329046154561183/100000000000000000000 : ℝ) ≤ ((18344416596587189713/18350000000000000000 : ℝ)+2*(297065568053/183500000000000 : ℝ)*(14667/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (18344416596587189713/18350000000000000000 : ℝ)+2*(297065568053/183500000000000 : ℝ)*(14667/100000 : ℝ)=(10001706113329949/10000000000000000 : ℝ) by norm_num, show 1+2*(35329046154561183/100000000000000000000 : ℝ)=(50035329046154561183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18344416596587189713/18350000000000000000 : ℝ)*(X 1 0+X 2 0)+(297065568053/183500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (18344416596587189713/18350000000000000000 : ℝ)) (alpha := (297065568053/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18344416596587189713/18350000000000000000 : ℝ)*(X 0 1+X 2 1)+(297065568053/183500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (18344416596587189713/18350000000000000000 : ℝ)) (alpha := (297065568053/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18344416596587189713/18350000000000000000 : ℝ)*(X 0 2+X 1 2)+(297065568053/183500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (18344416596587189713/18350000000000000000 : ℝ)) (alpha := (297065568053/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-131116951/625000000 : ℝ)*X 0 0+(270789119/500000000 : ℝ)*X 0 1+(5242599861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349938751/10000000000 : ℝ)*X 1 0+(-2186159749/10000000000 : ℝ)*X 1 1+(1310649957/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349938727/10000000000 : ℝ)*X 2 0+(1048519969/2000000000 : ℝ)*X 2 1+(-1093079879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542853559/1250000000 : ℝ)*X 0 0+(4169084383/10000000000 : ℝ)*X 0 1+(4523520197/10000000000 : ℝ)*X 0 2+(542853559/1250000000 : ℝ)*X 1 0+(4169084383/10000000000 : ℝ)*X 1 1+(4523520197/10000000000 : ℝ)*X 1 2+(542853559/1250000000 : ℝ)*X 2 0+(4169084383/10000000000 : ℝ)*X 2 1+(4523520197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2097884021/10000000000 : ℝ)*X 0 0+(40962629/78125000 : ℝ)*X 0 1+(1083032517/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305661821/10000000000 : ℝ)*X 1 0+(-1006798523/5000000000 : ℝ)*X 1 1+(5415162587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061132361/2000000000 : ℝ)*X 2 0+(5415162593/10000000000 : ℝ)*X 2 1+(-100679853/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542856847/1250000000 : ℝ)*X 0 0+(4522258093/10000000000 : ℝ)*X 0 1+(130323529/312500000 : ℝ)*X 0 2+(542856847/1250000000 : ℝ)*X 1 0+(4522258093/10000000000 : ℝ)*X 1 1+(130323529/312500000 : ℝ)*X 1 2+(542856847/1250000000 : ℝ)*X 2 0+(4522258093/10000000000 : ℝ)*X 2 1+(130323529/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4552696035172936949034966777/458750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2049171403/100000000000000 : ℝ)*(base19) + (971123337/50000000000000 : ℝ)*(base23) + (21672833/50000000000000 : ℝ)*(lower2) + (242476659/100000000000000 : ℝ)*(upper3) + (4161783/2500000000000 : ℝ)*(upper5) + (2148941799544243/50000000000000 : ℝ)*(major0) + (2148941799544243/50000000000000 : ℝ)*(major1) + (2148941799544243/50000000000000 : ℝ)*(major2) + (288714895482849/5000000000000 : ℝ)*(sp0) + (2887168599273857/50000000000000 : ℝ)*(sp1) + (1443584326368111/25000000000000 : ℝ)*(sp2) + (70535142974477/2500000000000 : ℝ)*(sp3) + (41338062137/100000000000000 : ℝ)*(sp4) + (21900674329/100000000000000 : ℝ)*(sp7) + (88169613114169/3125000000000 : ℝ)*(f.failure) + (5774339247719117/100000000000000 : ℝ)*(f.sum) + (15522592163967/9175000000000000000000000000 : ℝ)*base66 + (74489564101627741/917500000000000000000000000000000 : ℝ)*base68 + (3365256734781627741/917500000000000000000000000000000 : ℝ)*base70 + (766807017400872259/917500000000000000000000000000000 : ℝ)*base71 + (703388550167/9175000000000000000000000000 : ℝ)*base74 + (3357293962745872259/917500000000000000000000000000000 : ℝ)*base75 + (275356986744127741/917500000000000000000000000000000 : ℝ)*base78 + (16257127607631627741/917500000000000000000000000000000 : ℝ)*base80 + (25412367579121/4587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4220593/312500000000000000000 : ℝ)*base90 + (4220593/312500000000000000000 : ℝ)*base92 + (4220593/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (448102564564697384510629149/229375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74766153/20000000000000 : ℝ)*(base19) + (191722153/50000000000000 : ℝ)*(base23) + (133715947/100000000000000 : ℝ)*(lower1) + (7262453/20000000000000 : ℝ)*(upper3) + (3763769/25000000000000 : ℝ)*(lower4) + (10570967/25000000000000 : ℝ)*(upper5) + (2164359886762591/50000000000000 : ℝ)*(major0) + (2164359886762591/50000000000000 : ℝ)*(major1) + (2164359886762591/50000000000000 : ℝ)*(major2) + (73314473/50000000000000 : ℝ)*(sp1) + (581576886773521/10000000000000 : ℝ)*(sp4) + (2907884173637749/50000000000000 : ℝ)*(sp5) + (726971060536363/12500000000000 : ℝ)*(sp6) + (177604413387237/6250000000000 : ℝ)*(sp7) + (177604413387237/6250000000000 : ℝ)*(f.failure) + (581576886773521/10000000000000 : ℝ)*(f.sum) + (4145670628949/2293750000000000000000000000 : ℝ)*base65 + (11575024936639273617/917500000000000000000000000000000 : ℝ)*base68 + (3495854503014273617/917500000000000000000000000000000 : ℝ)*base70 + (7753104112239273617/917500000000000000000000000000000 : ℝ)*base72 + (12047722899/2239990234375000000000000 : ℝ)*base74 + (1686463716015726383/917500000000000000000000000000000 : ℝ)*base75 + (899996971419273617/917500000000000000000000000000000 : ℝ)*base78 + (6395890248099273617/917500000000000000000000000000000 : ℝ)*base80 + (37056617171077/4587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3595411/625000000000000000000 : ℝ)*base89 + (3595411/625000000000000000000 : ℝ)*base91 + (3595411/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1281_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1281_s8_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097878303/10000000000 : ℝ)*x 0 + (1083151579/2000000000 : ℝ)*x 1 + (2621309653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097878303/10000000000 : ℝ)^4241 ≤ (2552271441303/20000000000000 : ℝ)^3217 := by
    have hnat : (2097878303 : ℕ)^4241*20000000000000^3217 ≤ 2552271441303^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097878303 10000000000 2552271441303 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083151579/2000000000 : ℝ)^4241 ≤ (11138343164193/25000000000000 : ℝ)^3217 := by
    have hnat : (1083151579 : ℕ)^4241*25000000000000^3217 ≤ 11138343164193^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083151579 2000000000 11138343164193 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621309653/5000000000 : ℝ)^4241 ≤ (5335658765029/12500000000000 : ℝ)^3217 := by
    have hnat : (2621309653 : ℕ)^4241*12500000000000^3217 ≤ 5335658765029^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621309653 5000000000 5335658765029 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097878303/10000000000 : ℝ), (1083151579/2000000000 : ℝ), (2621309653/5000000000 : ℝ)] ![(2552271441303/20000000000000 : ℝ), (11138343164193/25000000000000 : ℝ), (5335658765029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097878303/10000000000 : ℝ)|^4241 ≤ (2552271441303/20000000000000 : ℝ)^3217
        have hw : |(-2097878303/10000000000 : ℝ)|=(2097878303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083151579/2000000000 : ℝ)|^4241 ≤ (11138343164193/25000000000000 : ℝ)^3217
        have hw : |(1083151579/2000000000 : ℝ)|=(1083151579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621309653/5000000000 : ℝ)|^4241 ≤ (5335658765029/12500000000000 : ℝ)^3217
        have hw : |(2621309653/5000000000 : ℝ)|=(2621309653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349932181/10000000000 : ℝ)*x 0 + (-1093070233/5000000000 : ℝ)*x 1 + (5242621037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349932181/10000000000 : ℝ)^4241 ≤ (43840862815873/100000000000000 : ℝ)^3217 := by
    have hnat : (5349932181 : ℕ)^4241*100000000000000^3217 ≤ 43840862815873^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349932181 10000000000 43840862815873 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093070233/5000000000 : ℝ)^4241 ≤ (3368462116351/25000000000000 : ℝ)^3217 := by
    have hnat : (1093070233 : ℕ)^4241*25000000000000^3217 ≤ 3368462116351^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093070233 5000000000 3368462116351 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242621037/10000000000 : ℝ)^4241 ≤ (33347881797/78125000000 : ℝ)^3217 := by
    have hnat : (5242621037 : ℕ)^4241*78125000000^3217 ≤ 33347881797^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242621037 10000000000 33347881797 78125000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349932181/10000000000 : ℝ), (-1093070233/5000000000 : ℝ), (5242621037/10000000000 : ℝ)] ![(43840862815873/100000000000000 : ℝ), (3368462116351/25000000000000 : ℝ), (33347881797/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349932181/10000000000 : ℝ)|^4241 ≤ (43840862815873/100000000000000 : ℝ)^3217
        have hw : |(5349932181/10000000000 : ℝ)|=(5349932181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093070233/5000000000 : ℝ)|^4241 ≤ (3368462116351/25000000000000 : ℝ)^3217
        have hw : |(-1093070233/5000000000 : ℝ)|=(1093070233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242621037/10000000000 : ℝ)|^4241 ≤ (33347881797/78125000000 : ℝ)^3217
        have hw : |(5242621037/10000000000 : ℝ)|=(5242621037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349932527/10000000000 : ℝ)*x 0 + (209704773/400000000 : ℝ)*x 1 + (-2186142267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349932527/10000000000 : ℝ)^4241 ≤ (21920433276871/50000000000000 : ℝ)^3217 := by
    have hnat : (5349932527 : ℕ)^4241*50000000000000^3217 ≤ 21920433276871^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349932527 10000000000 21920433276871 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209704773/400000000 : ℝ)^4241 ≤ (10671317581043/25000000000000 : ℝ)^3217 := by
    have hnat : (209704773 : ℕ)^4241*25000000000000^3217 ≤ 10671317581043^3217*400000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209704773 400000000 10671317581043 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186142267/10000000000 : ℝ)^4241 ≤ (6736931549391/50000000000000 : ℝ)^3217 := by
    have hnat : (2186142267 : ℕ)^4241*50000000000000^3217 ≤ 6736931549391^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186142267 10000000000 6736931549391 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349932527/10000000000 : ℝ), (209704773/400000000 : ℝ), (-2186142267/10000000000 : ℝ)] ![(21920433276871/50000000000000 : ℝ), (10671317581043/25000000000000 : ℝ), (6736931549391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349932527/10000000000 : ℝ)|^4241 ≤ (21920433276871/50000000000000 : ℝ)^3217
        have hw : |(5349932527/10000000000 : ℝ)|=(5349932527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209704773/400000000 : ℝ)|^4241 ≤ (10671317581043/25000000000000 : ℝ)^3217
        have hw : |(209704773/400000000 : ℝ)|=(209704773/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186142267/10000000000 : ℝ)|^4241 ≤ (6736931549391/50000000000000 : ℝ)^3217
        have hw : |(-2186142267/10000000000 : ℝ)|=(2186142267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342830963/10000000000 : ℝ)*x 0 + (1042282423/2500000000 : ℝ)*x 1 + (452347359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342830963/10000000000 : ℝ)^4241 ≤ (8325547488453/25000000000000 : ℝ)^3217 := by
    have hnat : (4342830963 : ℕ)^4241*25000000000000^3217 ≤ 8325547488453^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342830963 10000000000 8325547488453 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042282423/2500000000 : ℝ)^4241 ≤ (7889372338743/25000000000000 : ℝ)^3217 := by
    have hnat : (1042282423 : ℕ)^4241*25000000000000^3217 ≤ 7889372338743^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042282423 2500000000 7889372338743 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452347359/1000000000 : ℝ)^4241 ≤ (17570160338627/50000000000000 : ℝ)^3217 := by
    have hnat : (452347359 : ℕ)^4241*50000000000000^3217 ≤ 17570160338627^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452347359 1000000000 17570160338627 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342830963/10000000000 : ℝ), (1042282423/2500000000 : ℝ), (452347359/1000000000 : ℝ)] ![(8325547488453/25000000000000 : ℝ), (7889372338743/25000000000000 : ℝ), (17570160338627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342830963/10000000000 : ℝ)|^4241 ≤ (8325547488453/25000000000000 : ℝ)^3217
        have hw : |(4342830963/10000000000 : ℝ)|=(4342830963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042282423/2500000000 : ℝ)|^4241 ≤ (7889372338743/25000000000000 : ℝ)^3217
        have hw : |(1042282423/2500000000 : ℝ)|=(1042282423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452347359/1000000000 : ℝ)|^4241 ≤ (17570160338627/50000000000000 : ℝ)^3217
        have hw : |(452347359/1000000000 : ℝ)|=(452347359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-83915467/400000000 : ℝ)*x 0 + (1048647783/2000000000 : ℝ)*x 1 + (338446153/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83915467/400000000 : ℝ)^4241 ≤ (12761424343723/100000000000000 : ℝ)^3217 := by
    have hnat : (83915467 : ℕ)^4241*100000000000000^3217 ≤ 12761424343723^3217*400000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83915467 400000000 12761424343723 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048647783/2000000000 : ℝ)^4241 ≤ (1334122528241/3125000000000 : ℝ)^3217 := by
    have hnat : (1048647783 : ℕ)^4241*3125000000000^3217 ≤ 1334122528241^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048647783 2000000000 1334122528241 3125000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338446153/625000000 : ℝ)^4241 ≤ (44546654737151/100000000000000 : ℝ)^3217 := by
    have hnat : (338446153 : ℕ)^4241*100000000000000^3217 ≤ 44546654737151^3217*625000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338446153 625000000 44546654737151 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83915467/400000000 : ℝ), (1048647783/2000000000 : ℝ), (338446153/625000000 : ℝ)] ![(12761424343723/100000000000000 : ℝ), (1334122528241/3125000000000 : ℝ), (44546654737151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83915467/400000000 : ℝ)|^4241 ≤ (12761424343723/100000000000000 : ℝ)^3217
        have hw : |(-83915467/400000000 : ℝ)|=(83915467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048647783/2000000000 : ℝ)|^4241 ≤ (1334122528241/3125000000000 : ℝ)^3217
        have hw : |(1048647783/2000000000 : ℝ)|=(1048647783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338446153/625000000 : ℝ)|^4241 ≤ (44546654737151/100000000000000 : ℝ)^3217
        have hw : |(338446153/625000000 : ℝ)|=(338446153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652836377/5000000000 : ℝ)*x 0 + (2707568223/5000000000 : ℝ)*x 1 + (-100680899/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652836377/5000000000 : ℝ)^4241 ≤ (43363354943417/100000000000000 : ℝ)^3217 := by
    have hnat : (2652836377 : ℕ)^4241*100000000000000^3217 ≤ 43363354943417^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652836377 5000000000 43363354943417 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707568223/5000000000 : ℝ)^4241 ≤ (22273316512901/50000000000000 : ℝ)^3217 := by
    have hnat : (2707568223 : ℕ)^4241*50000000000000^3217 ≤ 22273316512901^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707568223 5000000000 22273316512901 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100680899/500000000 : ℝ)^4241 ≤ (6045006007093/50000000000000 : ℝ)^3217 := by
    have hnat : (100680899 : ℕ)^4241*50000000000000^3217 ≤ 6045006007093^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100680899 500000000 6045006007093 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652836377/5000000000 : ℝ), (2707568223/5000000000 : ℝ), (-100680899/500000000 : ℝ)] ![(43363354943417/100000000000000 : ℝ), (22273316512901/50000000000000 : ℝ), (6045006007093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652836377/5000000000 : ℝ)|^4241 ≤ (43363354943417/100000000000000 : ℝ)^3217
        have hw : |(2652836377/5000000000 : ℝ)|=(2652836377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707568223/5000000000 : ℝ)|^4241 ≤ (22273316512901/50000000000000 : ℝ)^3217
        have hw : |(2707568223/5000000000 : ℝ)|=(2707568223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100680899/500000000 : ℝ)|^4241 ≤ (6045006007093/50000000000000 : ℝ)^3217
        have hw : |(-100680899/500000000 : ℝ)|=(100680899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342857039/10000000000 : ℝ)*x 0 + (1130553693/2500000000 : ℝ)*x 1 + (4170395089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342857039/10000000000 : ℝ)^4241 ≤ (33302453561739/100000000000000 : ℝ)^3217 := by
    have hnat : (4342857039 : ℕ)^4241*100000000000000^3217 ≤ 33302453561739^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342857039 10000000000 33302453561739 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130553693/2500000000 : ℝ)^4241 ≤ (1756371472031/5000000000000 : ℝ)^3217 := by
    have hnat : (1130553693 : ℕ)^4241*5000000000000^3217 ≤ 1756371472031^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130553693 2500000000 1756371472031 5000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170395089/10000000000 : ℝ)^4241 ≤ (15785058495103/50000000000000 : ℝ)^3217 := by
    have hnat : (4170395089 : ℕ)^4241*50000000000000^3217 ≤ 15785058495103^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170395089 10000000000 15785058495103 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342857039/10000000000 : ℝ), (1130553693/2500000000 : ℝ), (4170395089/10000000000 : ℝ)] ![(33302453561739/100000000000000 : ℝ), (1756371472031/5000000000000 : ℝ), (15785058495103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342857039/10000000000 : ℝ)|^4241 ≤ (33302453561739/100000000000000 : ℝ)^3217
        have hw : |(4342857039/10000000000 : ℝ)|=(4342857039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130553693/2500000000 : ℝ)|^4241 ≤ (1756371472031/5000000000000 : ℝ)^3217
        have hw : |(1130553693/2500000000 : ℝ)|=(1130553693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170395089/10000000000 : ℝ)|^4241 ≤ (15785058495103/50000000000000 : ℝ)^3217
        have hw : |(4170395089/10000000000 : ℝ)|=(4170395089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_s8_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5573553/2500000000 : ℝ)*x 0 + (118191299/200000000 : ℝ)*x 1 + (1181879/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5573553/2500000000 : ℝ)^4241 ≤ (7980642683/25000000000000 : ℝ)^3217 := by
    have hnat : (5573553 : ℕ)^4241*25000000000000^3217 ≤ 7980642683^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573553 2500000000 7980642683 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118191299/200000000 : ℝ)^4241 ≤ (49984986235373/100000000000000 : ℝ)^3217 := by
    have hnat : (118191299 : ℕ)^4241*100000000000000^3217 ≤ 49984986235373^3217*200000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118191299 200000000 49984986235373 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181879/2000000 : ℝ)^4241 ≤ (24991545593153/50000000000000 : ℝ)^3217 := by
    have hnat : (1181879 : ℕ)^4241*50000000000000^3217 ≤ 24991545593153^3217*2000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181879 2000000 24991545593153 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5573553/2500000000 : ℝ), (118191299/200000000 : ℝ), (1181879/2000000 : ℝ)] ![(7980642683/25000000000000 : ℝ), (49984986235373/100000000000000 : ℝ), (24991545593153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5573553/2500000000 : ℝ)|^4241 ≤ (7980642683/25000000000000 : ℝ)^3217
        have hw : |(-5573553/2500000000 : ℝ)|=(5573553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118191299/200000000 : ℝ)|^4241 ≤ (49984986235373/100000000000000 : ℝ)^3217
        have hw : |(118191299/200000000 : ℝ)|=(118191299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1181879/2000000 : ℝ)|^4241 ≤ (24991545593153/50000000000000 : ℝ)^3217
        have hw : |(1181879/2000000 : ℝ)|=(1181879/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1833/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10999/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10999/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10999/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10999/100000 : ℝ) ^ (265/64 : ℝ) ≤ (429203340620739/4000000000000000000 : ℝ) := by
    have hpowers : (10999/100000 : ℝ)^265 ≤ (429203340620739/4000000000000000000 : ℝ)^64 := by
      have hnat : (10999 : ℕ)^265*4000000000000000000^64 ≤ 429203340620739^64*100000^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10999 100000 429203340620739 4000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10999/100000 : ℝ)) (X := (429203340620739/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1833/12500 : ℝ) ^ (265/64 : ℝ) ≤ (8824783662127219/25000000000000000000 : ℝ) := by
    have hpowers : (1833/12500 : ℝ)^265 ≤ (8824783662127219/25000000000000000000 : ℝ)^64 := by
      have hnat : (1833 : ℕ)^265*25000000000000000000^64 ≤ 8824783662127219^64*12500^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1833 12500 8824783662127219 25000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1833/12500 : ℝ)) (X := (8824783662127219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000429203340620739/2000000000000000000 : ℝ) ≤ (2000103648220639/2000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (2000429203340620739/2000000000000000000 : ℝ)^64 ≤ (2000103648220639/2000000000000000 : ℝ)^265 := by
      have hnat : (2000429203340620739 : ℕ)^64*2000000000000000^265 ≤ 2000103648220639^265*2000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000429203340620739 2000000000000000000 2000103648220639 2000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000103648220639/2000000000000000 : ℝ)) (X := (2000429203340620739/2000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046029218164027351/100000000000000000000 : ℝ) ≤ (10001111455041291/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (100046029218164027351/100000000000000000000 : ℝ)^64 ≤ (10001111455041291/10000000000000000 : ℝ)^265 := by
      have hnat : (100046029218164027351 : ℕ)^64*10000000000000000^265 ≤ 10001111455041291^265*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046029218164027351 100000000000000000000 10001111455041291 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111455041291/10000000000000000 : ℝ)) (X := (100046029218164027351/100000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508824783662127219/12500000000000000000 : ℝ) ≤ (10001704668979387/10000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (12508824783662127219/12500000000000000000 : ℝ)^64 ≤ (10001704668979387/10000000000000000 : ℝ)^265 := by
      have hnat : (12508824783662127219 : ℕ)^64*10000000000000000^265 ≤ 10001704668979387^265*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508824783662127219 12500000000000000000 10001704668979387 10000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001704668979387/10000000000000000 : ℝ)) (X := (12508824783662127219/12500000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(429203340620739/4000000000000000000 : ℝ) ≤ ((36638849833432973867/36650000000000000000 : ℝ)+2*(37075871131/22906250000000 : ℝ)*(10999/100000 : ℝ))^(265/64 : ℝ) := by
    rw [show (36638849833432973867/36650000000000000000 : ℝ)+2*(37075871131/22906250000000 : ℝ)*(10999/100000 : ℝ)=(2000103648220639/2000000000000000 : ℝ) by norm_num, show 1+2*(429203340620739/4000000000000000000 : ℝ)=(2000429203340620739/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8824783662127219/25000000000000000000 : ℝ)+(429203340620739/4000000000000000000 : ℝ) ≤ ((36638849833432973867/36650000000000000000 : ℝ)+(37075871131/22906250000000 : ℝ)*((1833/12500 : ℝ)+(10999/100000 : ℝ)))^(265/64 : ℝ) := by
    rw [show (36638849833432973867/36650000000000000000 : ℝ)+(37075871131/22906250000000 : ℝ)*((1833/12500 : ℝ)+(10999/100000 : ℝ))=(10001111455041291/10000000000000000 : ℝ) by norm_num, show 1+(8824783662127219/25000000000000000000 : ℝ)+(429203340620739/4000000000000000000 : ℝ)=(100046029218164027351/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8824783662127219/25000000000000000000 : ℝ) ≤ ((36638849833432973867/36650000000000000000 : ℝ)+2*(37075871131/22906250000000 : ℝ)*(1833/12500 : ℝ))^(265/64 : ℝ) := by
    rw [show (36638849833432973867/36650000000000000000 : ℝ)+2*(37075871131/22906250000000 : ℝ)*(1833/12500 : ℝ)=(10001704668979387/10000000000000000 : ℝ) by norm_num, show 1+2*(8824783662127219/25000000000000000000 : ℝ)=(12508824783662127219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36638849833432973867/36650000000000000000 : ℝ)*(X 1 0+X 2 0)+(37075871131/22906250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (36638849833432973867/36650000000000000000 : ℝ)) (alpha := (37075871131/22906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36638849833432973867/36650000000000000000 : ℝ)*(X 0 1+X 2 1)+(37075871131/22906250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (36638849833432973867/36650000000000000000 : ℝ)) (alpha := (37075871131/22906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36638849833432973867/36650000000000000000 : ℝ)*(X 0 2+X 1 2)+(37075871131/22906250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (10999/100000 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (36638849833432973867/36650000000000000000 : ℝ)) (alpha := (37075871131/22906250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2097878303/10000000000 : ℝ)*X 0 0+(1083151579/2000000000 : ℝ)*X 0 1+(2621309653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349932181/10000000000 : ℝ)*X 1 0+(-1093070233/5000000000 : ℝ)*X 1 1+(5242621037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349932527/10000000000 : ℝ)*X 2 0+(209704773/400000000 : ℝ)*X 2 1+(-2186142267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342830963/10000000000 : ℝ)*X 0 0+(1042282423/2500000000 : ℝ)*X 0 1+(452347359/1000000000 : ℝ)*X 0 2+(4342830963/10000000000 : ℝ)*X 1 0+(1042282423/2500000000 : ℝ)*X 1 1+(452347359/1000000000 : ℝ)*X 1 2+(4342830963/10000000000 : ℝ)*X 2 0+(1042282423/2500000000 : ℝ)*X 2 1+(452347359/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83915467/400000000 : ℝ)*X 0 0+(1048647783/2000000000 : ℝ)*X 0 1+(338446153/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652836377/5000000000 : ℝ)*X 2 0+(2707568223/5000000000 : ℝ)*X 2 1+(-100680899/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4342857039/10000000000 : ℝ)*X 0 0+(1130553693/2500000000 : ℝ)*X 0 1+(4170395089/10000000000 : ℝ)*X 0 2+(4342857039/10000000000 : ℝ)*X 1 0+(1130553693/2500000000 : ℝ)*X 1 1+(4170395089/10000000000 : ℝ)*X 1 2+(4342857039/10000000000 : ℝ)*X 2 0+(1130553693/2500000000 : ℝ)*X 2 1+(4170395089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-5573553/2500000000 : ℝ)*X 0 0+(118191299/200000000 : ℝ)*X 0 1+(1181879/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_s8_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8402280105114004750071/2290625000000000000000000000 : ℝ) := by norm_num
    linear_combination (469530723/50000000000000 : ℝ)*(lower2) + (932774009/100000000000000 : ℝ)*(lower4) + (583613347/100000000000000 : ℝ)*(lower5) + (537368292256467/12500000000000 : ℝ)*(major0) + (537368292256467/12500000000000 : ℝ)*(major1) + (537368292256467/12500000000000 : ℝ)*(major2) + (2887873536656163/50000000000000 : ℝ)*(sp0) + (5775767278927957/100000000000000 : ℝ)*(sp1) + (721965443443197/12500000000000 : ℝ)*(sp2) + (352764623969821/12500000000000 : ℝ)*(sp3) + (7030276487/100000000000000 : ℝ)*(sp4) + (43731382381/100000000000000 : ℝ)*(sp5) + (8283146377/100000000000000 : ℝ)*(sp6) + (1646917393/12500000000000 : ℝ)*(sp7) + (564425054980989/20000000000000 : ℝ)*(f.failure) + (5775767278927957/100000000000000 : ℝ)*(f.sum) + (1551532814483/572656250000000000000000000 : ℝ)*base65 + (6496211385878427111/458125000000000000000000000000000 : ℝ)*base68 + (2409273372684677111/458125000000000000000000000000000 : ℝ)*base70 + (22616838603460947889/458125000000000000000000000000000 : ℝ)*base71 + (42537657122097/9162500000000000000000000000 : ℝ)*base74 + (1787924265664697889/458125000000000000000000000000000 : ℝ)*base75 + (907794756162177111/458125000000000000000000000000000 : ℝ)*base78 + (172894762819697889/458125000000000000000000000000000 : ℝ)*base79 + (43265294096169/18325000000000000000000000000 : ℝ)*base82 + (2588133/2000000000000000000000 : ℝ)*base90 + (2588133/2000000000000000000000 : ℝ)*base92 + (2588133/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1281_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10999/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1281_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1281_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1281_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1281_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1281_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

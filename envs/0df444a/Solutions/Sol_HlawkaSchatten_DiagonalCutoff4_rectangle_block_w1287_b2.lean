-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:31.715013+00:00
-- url     : https://prove2.me/submissions/37fb4715-e7c9-481f-8eb7-4a0047efdd6f

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
theorem support_rectangle_w1287_s6_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418490107/2000000000 : ℝ)*x 0 + (5415581061/10000000000 : ℝ)*x 1 + (1310680479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418490107/2000000000 : ℝ)^4247 ≤ (509185699907/4000000000000 : ℝ)^3223 := by
    have hnat : (418490107 : ℕ)^4247*4000000000000^3223 ≤ 509185699907^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418490107 2000000000 509185699907 4000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415581061/10000000000 : ℝ)^4247 ≤ (22283824486307/50000000000000 : ℝ)^3223 := by
    have hnat : (5415581061 : ℕ)^4247*50000000000000^3223 ≤ 22283824486307^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415581061 10000000000 22283824486307 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310680479/2500000000 : ℝ)^4247 ≤ (4270270851849/10000000000000 : ℝ)^3223 := by
    have hnat : (1310680479 : ℕ)^4247*10000000000000^3223 ≤ 4270270851849^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310680479 2500000000 4270270851849 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418490107/2000000000 : ℝ), (5415581061/10000000000 : ℝ), (1310680479/2500000000 : ℝ)] ![(509185699907/4000000000000 : ℝ), (22283824486307/50000000000000 : ℝ), (4270270851849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418490107/2000000000 : ℝ)|^4247 ≤ (509185699907/4000000000000 : ℝ)^3223
        have hw : |(-418490107/2000000000 : ℝ)|=(418490107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415581061/10000000000 : ℝ)|^4247 ≤ (22283824486307/50000000000000 : ℝ)^3223
        have hw : |(5415581061/10000000000 : ℝ)|=(5415581061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310680479/2500000000 : ℝ)|^4247 ≤ (4270270851849/10000000000000 : ℝ)^3223
        have hw : |(1310680479/2500000000 : ℝ)|=(1310680479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674940041/5000000000 : ℝ)*x 0 + (-87222853/400000000 : ℝ)*x 1 + (2621360833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674940041/5000000000 : ℝ)^4247 ≤ (43856552807899/100000000000000 : ℝ)^3223 := by
    have hnat : (2674940041 : ℕ)^4247*100000000000000^3223 ≤ 43856552807899^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674940041 5000000000 43856552807899 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87222853/400000000 : ℝ)^4247 ≤ (3360185337707/25000000000000 : ℝ)^3223 := by
    have hnat : (87222853 : ℕ)^4247*25000000000000^3223 ≤ 3360185337707^3223*400000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87222853 400000000 3360185337707 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621360833/5000000000 : ℝ)^4247 ≤ (10675676458811/25000000000000 : ℝ)^3223 := by
    have hnat : (2621360833 : ℕ)^4247*25000000000000^3223 ≤ 10675676458811^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621360833 5000000000 10675676458811 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674940041/5000000000 : ℝ), (-87222853/400000000 : ℝ), (2621360833/5000000000 : ℝ)] ![(43856552807899/100000000000000 : ℝ), (3360185337707/25000000000000 : ℝ), (10675676458811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674940041/5000000000 : ℝ)|^4247 ≤ (43856552807899/100000000000000 : ℝ)^3223
        have hw : |(2674940041/5000000000 : ℝ)|=(2674940041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87222853/400000000 : ℝ)|^4247 ≤ (3360185337707/25000000000000 : ℝ)^3223
        have hw : |(-87222853/400000000 : ℝ)|=(87222853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621360833/5000000000 : ℝ)|^4247 ≤ (10675676458811/25000000000000 : ℝ)^3223
        have hw : |(2621360833/5000000000 : ℝ)|=(2621360833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337470081/2500000000 : ℝ)*x 0 + (5242721889/10000000000 : ℝ)*x 1 + (-545142677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337470081/2500000000 : ℝ)^4247 ≤ (43856555422033/100000000000000 : ℝ)^3223 := by
    have hnat : (1337470081 : ℕ)^4247*100000000000000^3223 ≤ 43856555422033^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337470081 2500000000 43856555422033 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242721889/10000000000 : ℝ)^4247 ≤ (427027082287/1000000000000 : ℝ)^3223 := by
    have hnat : (5242721889 : ℕ)^4247*1000000000000^3223 ≤ 427027082287^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242721889 10000000000 427027082287 1000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545142677/2500000000 : ℝ)^4247 ≤ (13440736339417/100000000000000 : ℝ)^3223 := by
    have hnat : (545142677 : ℕ)^4247*100000000000000^3223 ≤ 13440736339417^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545142677 2500000000 13440736339417 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337470081/2500000000 : ℝ), (5242721889/10000000000 : ℝ), (-545142677/2500000000 : ℝ)] ![(43856555422033/100000000000000 : ℝ), (427027082287/1000000000000 : ℝ), (13440736339417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337470081/2500000000 : ℝ)|^4247 ≤ (43856555422033/100000000000000 : ℝ)^3223
        have hw : |(1337470081/2500000000 : ℝ)|=(1337470081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242721889/10000000000 : ℝ)|^4247 ≤ (427027082287/1000000000000 : ℝ)^3223
        have hw : |(5242721889/10000000000 : ℝ)|=(5242721889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545142677/2500000000 : ℝ)|^4247 ≤ (13440736339417/100000000000000 : ℝ)^3223
        have hw : |(-545142677/2500000000 : ℝ)|=(545142677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868240713/2000000000 : ℝ)*x 0 + (2083689693/5000000000 : ℝ)*x 1 + (2260983273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868240713/2000000000 : ℝ)^4247 ≤ (4162775222907/12500000000000 : ℝ)^3223 := by
    have hnat : (868240713 : ℕ)^4247*12500000000000^3223 ≤ 4162775222907^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868240713 2000000000 4162775222907 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083689693/5000000000 : ℝ)^4247 ≤ (31556388009497/100000000000000 : ℝ)^3223 := by
    have hnat : (2083689693 : ℕ)^4247*100000000000000^3223 ≤ 31556388009497^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083689693 5000000000 31556388009497 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260983273/5000000000 : ℝ)^4247 ≤ (8785352548813/25000000000000 : ℝ)^3223 := by
    have hnat : (2260983273 : ℕ)^4247*25000000000000^3223 ≤ 8785352548813^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260983273 5000000000 8785352548813 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868240713/2000000000 : ℝ), (2083689693/5000000000 : ℝ), (2260983273/5000000000 : ℝ)] ![(4162775222907/12500000000000 : ℝ), (31556388009497/100000000000000 : ℝ), (8785352548813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868240713/2000000000 : ℝ)|^4247 ≤ (4162775222907/12500000000000 : ℝ)^3223
        have hw : |(868240713/2000000000 : ℝ)|=(868240713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083689693/5000000000 : ℝ)|^4247 ≤ (31556388009497/100000000000000 : ℝ)^3223
        have hw : |(2083689693/5000000000 : ℝ)|=(2083689693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260983273/5000000000 : ℝ)|^4247 ≤ (8785352548813/25000000000000 : ℝ)^3223
        have hw : |(2260983273/5000000000 : ℝ)|=(2260983273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092463403/10000000000 : ℝ)*x 0 + (5243338551/10000000000 : ℝ)*x 1 + (5414961213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092463403/10000000000 : ℝ)^4247 ≤ (6364872826831/50000000000000 : ℝ)^3223 := by
    have hnat : (2092463403 : ℕ)^4247*50000000000000^3223 ≤ 6364872826831^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092463403 10000000000 6364872826831 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243338551/10000000000 : ℝ)^4247 ≤ (42709326976849/100000000000000 : ℝ)^3223 := by
    have hnat : (5243338551 : ℕ)^4247*100000000000000^3223 ≤ 42709326976849^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243338551 10000000000 42709326976849 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414961213/10000000000 : ℝ)^4247 ≤ (44560927353069/100000000000000 : ℝ)^3223 := by
    have hnat : (5414961213 : ℕ)^4247*100000000000000^3223 ≤ 44560927353069^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414961213 10000000000 44560927353069 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092463403/10000000000 : ℝ), (5243338551/10000000000 : ℝ), (5414961213/10000000000 : ℝ)] ![(6364872826831/50000000000000 : ℝ), (42709326976849/100000000000000 : ℝ), (44560927353069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092463403/10000000000 : ℝ)|^4247 ≤ (6364872826831/50000000000000 : ℝ)^3223
        have hw : |(-2092463403/10000000000 : ℝ)|=(2092463403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243338551/10000000000 : ℝ)|^4247 ≤ (42709326976849/100000000000000 : ℝ)^3223
        have hw : |(5243338551/10000000000 : ℝ)|=(5243338551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414961213/10000000000 : ℝ)|^4247 ≤ (44560927353069/100000000000000 : ℝ)^3223
        have hw : |(5414961213/10000000000 : ℝ)|=(5414961213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652825869/5000000000 : ℝ)*x 0 + (-1004165771/5000000000 : ℝ)*x 1 + (84608773/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652825869/5000000000 : ℝ)^4247 ≤ (43379417819153/100000000000000 : ℝ)^3223 := by
    have hnat : (2652825869 : ℕ)^4247*100000000000000^3223 ≤ 43379417819153^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652825869 5000000000 43379417819153 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004165771/5000000000 : ℝ)^4247 ≤ (2411930400819/20000000000000 : ℝ)^3223 := by
    have hnat : (1004165771 : ℕ)^4247*20000000000000^3223 ≤ 2411930400819^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004165771 5000000000 2411930400819 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84608773/156250000 : ℝ)^4247 ≤ (44560930161609/100000000000000 : ℝ)^3223 := by
    have hnat : (84608773 : ℕ)^4247*100000000000000^3223 ≤ 44560930161609^3223*156250000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84608773 156250000 44560930161609 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652825869/5000000000 : ℝ), (-1004165771/5000000000 : ℝ), (84608773/156250000 : ℝ)] ![(43379417819153/100000000000000 : ℝ), (2411930400819/20000000000000 : ℝ), (44560930161609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652825869/5000000000 : ℝ)|^4247 ≤ (43379417819153/100000000000000 : ℝ)^3223
        have hw : |(2652825869/5000000000 : ℝ)|=(2652825869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004165771/5000000000 : ℝ)|^4247 ≤ (2411930400819/20000000000000 : ℝ)^3223
        have hw : |(-1004165771/5000000000 : ℝ)|=(1004165771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84608773/156250000 : ℝ)|^4247 ≤ (44560930161609/100000000000000 : ℝ)^3223
        have hw : |(84608773/156250000 : ℝ)|=(84608773/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265282593/500000000 : ℝ)*x 0 + (5414961493/10000000000 : ℝ)*x 1 + (-2008331347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265282593/500000000 : ℝ)^4247 ≤ (43379419133551/100000000000000 : ℝ)^3223 := by
    have hnat : (265282593 : ℕ)^4247*100000000000000^3223 ≤ 43379419133551^3223*500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265282593 500000000 43379419133551 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414961493/10000000000 : ℝ)^4247 ≤ (44560930389329/100000000000000 : ℝ)^3223 := by
    have hnat : (5414961493 : ℕ)^4247*100000000000000^3223 ≤ 44560930389329^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414961493 10000000000 44560930389329 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008331347/10000000000 : ℝ)^4247 ≤ (1205965046113/10000000000000 : ℝ)^3223 := by
    have hnat : (2008331347 : ℕ)^4247*10000000000000^3223 ≤ 1205965046113^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008331347 10000000000 1205965046113 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265282593/500000000 : ℝ), (5414961493/10000000000 : ℝ), (-2008331347/10000000000 : ℝ)] ![(43379419133551/100000000000000 : ℝ), (44560930389329/100000000000000 : ℝ), (1205965046113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265282593/500000000 : ℝ)|^4247 ≤ (43379419133551/100000000000000 : ℝ)^3223
        have hw : |(265282593/500000000 : ℝ)|=(265282593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414961493/10000000000 : ℝ)|^4247 ≤ (44560930389329/100000000000000 : ℝ)^3223
        have hw : |(5414961493/10000000000 : ℝ)|=(5414961493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008331347/10000000000 : ℝ)|^4247 ≤ (1205965046113/10000000000000 : ℝ)^3223
        have hw : |(-2008331347/10000000000 : ℝ)|=(2008331347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s6_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170615217/5000000000 : ℝ)*x 0 + (904140391/2000000000 : ℝ)*x 1 + (33349199/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170615217/5000000000 : ℝ)^4247 ≤ (16651236693791/50000000000000 : ℝ)^3223 := by
    have hnat : (2170615217 : ℕ)^4247*50000000000000^3223 ≤ 16651236693791^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170615217 5000000000 16651236693791 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904140391/2000000000 : ℝ)^4247 ≤ (35128460946101/100000000000000 : ℝ)^3223 := by
    have hnat : (904140391 : ℕ)^4247*100000000000000^3223 ≤ 35128460946101^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904140391 2000000000 35128460946101 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33349199/80000000 : ℝ)^4247 ≤ (31569065641581/100000000000000 : ℝ)^3223 := by
    have hnat : (33349199 : ℕ)^4247*100000000000000^3223 ≤ 31569065641581^3223*80000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33349199 80000000 31569065641581 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170615217/5000000000 : ℝ), (904140391/2000000000 : ℝ), (33349199/80000000 : ℝ)] ![(16651236693791/50000000000000 : ℝ), (35128460946101/100000000000000 : ℝ), (31569065641581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170615217/5000000000 : ℝ)|^4247 ≤ (16651236693791/50000000000000 : ℝ)^3223
        have hw : |(2170615217/5000000000 : ℝ)|=(2170615217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904140391/2000000000 : ℝ)|^4247 ≤ (35128460946101/100000000000000 : ℝ)^3223
        have hw : |(904140391/2000000000 : ℝ)|=(904140391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33349199/80000000 : ℝ)|^4247 ≤ (31569065641581/100000000000000 : ℝ)^3223
        have hw : |(33349199/80000000 : ℝ)|=(33349199/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11013/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14671/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11001/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (10600185087933451/100000000000000000000 : ℝ) := by
    have hpowers : (11001/100000 : ℝ)^2123 ≤ (10600185087933451/100000000000000000000 : ℝ)^512 := by
      have hnat : (11001 : ℕ)^2123*100000000000000000000^512 ≤ 10600185087933451^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11001 100000 10600185087933451 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11001/100000 : ℝ)) (X := (10600185087933451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14683/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (548315607134049/1562500000000000000 : ℝ) := by
    have hpowers : (14683/100000 : ℝ)^2123 ≤ (548315607134049/1562500000000000000 : ℝ)^512 := by
      have hnat : (14683 : ℕ)^2123*1562500000000000000^512 ≤ 548315607134049^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14683 100000 548315607134049 1562500000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14683/100000 : ℝ)) (X := (548315607134049/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010600185087933451/50000000000000000000 : ℝ) ≤ (5000255622150769/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50010600185087933451/50000000000000000000 : ℝ)^512 ≤ (5000255622150769/5000000000000000 : ℝ)^2123 := by
      have hnat : (50010600185087933451 : ℕ)^512*5000000000000000^2123 ≤ 5000255622150769^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010600185087933451 50000000000000000000 5000255622150769 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000255622150769/5000000000000000 : ℝ)) (X := (50010600185087933451/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045692383944512587/100000000000000000000 : ℝ) ≤ (10001101763819941/10000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (100045692383944512587/100000000000000000000 : ℝ)^512 ≤ (10001101763819941/10000000000000000 : ℝ)^2123 := by
      have hnat : (100045692383944512587 : ℕ)^512*10000000000000000^2123 ≤ 10001101763819941^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045692383944512587 100000000000000000000 10001101763819941 10000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001101763819941/10000000000000000 : ℝ)) (X := (100045692383944512587/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (781798315607134049/781250000000000000 : ℝ) ≤ (1250211535417293/1250000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (781798315607134049/781250000000000000 : ℝ)^512 ≤ (1250211535417293/1250000000000000 : ℝ)^2123 := by
      have hnat : (781798315607134049 : ℕ)^512*1250000000000000^2123 ≤ 1250211535417293^2123*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781798315607134049 781250000000000000 1250211535417293 1250000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250211535417293/1250000000000000 : ℝ)) (X := (781798315607134049/781250000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10600185087933451/100000000000000000000 : ℝ) ≤ ((3680888979107436011/3682000000000000000 : ℝ)+2*(590519518403/368200000000000 : ℝ)*(11001/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (3680888979107436011/3682000000000000000 : ℝ)+2*(590519518403/368200000000000 : ℝ)*(11001/100000 : ℝ)=(5000255622150769/5000000000000000 : ℝ) by norm_num, show 1+2*(10600185087933451/100000000000000000000 : ℝ)=(50010600185087933451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(548315607134049/1562500000000000000 : ℝ)+(10600185087933451/100000000000000000000 : ℝ) ≤ ((3680888979107436011/3682000000000000000 : ℝ)+(590519518403/368200000000000 : ℝ)*((14683/100000 : ℝ)+(11001/100000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (3680888979107436011/3682000000000000000 : ℝ)+(590519518403/368200000000000 : ℝ)*((14683/100000 : ℝ)+(11001/100000 : ℝ))=(10001101763819941/10000000000000000 : ℝ) by norm_num, show 1+(548315607134049/1562500000000000000 : ℝ)+(10600185087933451/100000000000000000000 : ℝ)=(100045692383944512587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(548315607134049/1562500000000000000 : ℝ) ≤ ((3680888979107436011/3682000000000000000 : ℝ)+2*(590519518403/368200000000000 : ℝ)*(14683/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (3680888979107436011/3682000000000000000 : ℝ)+2*(590519518403/368200000000000 : ℝ)*(14683/100000 : ℝ)=(1250211535417293/1250000000000000 : ℝ) by norm_num, show 1+2*(548315607134049/1562500000000000000 : ℝ)=(781798315607134049/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3680888979107436011/3682000000000000000 : ℝ)*(X 1 0+X 2 0)+(590519518403/368200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3680888979107436011/3682000000000000000 : ℝ)) (alpha := (590519518403/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3680888979107436011/3682000000000000000 : ℝ)*(X 0 1+X 2 1)+(590519518403/368200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3680888979107436011/3682000000000000000 : ℝ)) (alpha := (590519518403/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3680888979107436011/3682000000000000000 : ℝ)*(X 0 2+X 1 2)+(590519518403/368200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11001/100000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3680888979107436011/3682000000000000000 : ℝ)) (alpha := (590519518403/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418490107/2000000000 : ℝ)*X 0 0+(5415581061/10000000000 : ℝ)*X 0 1+(1310680479/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674940041/5000000000 : ℝ)*X 1 0+(-87222853/400000000 : ℝ)*X 1 1+(2621360833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337470081/2500000000 : ℝ)*X 2 0+(5242721889/10000000000 : ℝ)*X 2 1+(-545142677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868240713/2000000000 : ℝ)*X 0 0+(2083689693/5000000000 : ℝ)*X 0 1+(2260983273/5000000000 : ℝ)*X 0 2+(868240713/2000000000 : ℝ)*X 1 0+(2083689693/5000000000 : ℝ)*X 1 1+(2260983273/5000000000 : ℝ)*X 1 2+(868240713/2000000000 : ℝ)*X 2 0+(2083689693/5000000000 : ℝ)*X 2 1+(2260983273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092463403/10000000000 : ℝ)*X 0 0+(5243338551/10000000000 : ℝ)*X 0 1+(5414961213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652825869/5000000000 : ℝ)*X 1 0+(-1004165771/5000000000 : ℝ)*X 1 1+(84608773/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265282593/500000000 : ℝ)*X 2 0+(5414961493/10000000000 : ℝ)*X 2 1+(-2008331347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170615217/5000000000 : ℝ)*X 0 0+(904140391/2000000000 : ℝ)*X 0 1+(33349199/80000000 : ℝ)*X 0 2+(2170615217/5000000000 : ℝ)*X 1 0+(904140391/2000000000 : ℝ)*X 1 1+(33349199/80000000 : ℝ)*X 1 2+(2170615217/5000000000 : ℝ)*X 2 0+(904140391/2000000000 : ℝ)*X 2 1+(33349199/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27310561391686693105977063/6575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (694020651/100000000000000 : ℝ)*(base19) + (89060643/12500000000000 : ℝ)*(base23) + (191098833/100000000000000 : ℝ)*(upper4) + (60810983/100000000000000 : ℝ)*(upper5) + (1075661405232541/25000000000000 : ℝ)*(major0) + (1075661405232541/25000000000000 : ℝ)*(major1) + (1075661405232541/25000000000000 : ℝ)*(major2) + (5785072059904657/100000000000000 : ℝ)*(sp0) + (1446270534500841/25000000000000 : ℝ)*(sp1) + (2892547953289313/50000000000000 : ℝ)*(sp2) + (1410093435609141/50000000000000 : ℝ)*(sp3) + (24559159113/100000000000000 : ℝ)*(sp4) + (2757407951/20000000000000 : ℝ)*(sp5) + (3806560843/50000000000000 : ℝ)*(sp7) + (11016384704453/390625000000 : ℝ)*(f.failure) + (578509661906377/10000000000000 : ℝ)*(f.sum) + (4271655250027/4602500000000000000000000000 : ℝ)*base66 + (395626313762563951/92050000000000000000000000000000 : ℝ)*base67 + (916966881271513951/92050000000000000000000000000000 : ℝ)*base69 + (109662884434063951/92050000000000000000000000000000 : ℝ)*base71 + (10112273577143/4602500000000000000000000000 : ℝ)*base73 + (570292138350363951/92050000000000000000000000000000 : ℝ)*base75 + (745460078382763951/92050000000000000000000000000000 : ℝ)*base77 + (728941372845863951/92050000000000000000000000000000 : ℝ)*base79 + (2324064925603/1150625000000000000000000000 : ℝ)*base82 + (7001/4882812500000000000 : ℝ)*base90 + (7001/4882812500000000000 : ℝ)*base92 + (7001/4882812500000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (549282738548604896017696629/92050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124262031/12500000000000 : ℝ)*(base19) + (1324838387/100000000000000 : ℝ)*(base23) + (22872311/50000000000000 : ℝ)*(upper2) + (60138629/25000000000000 : ℝ)*(upper3) + (100389401/100000000000000 : ℝ)*(upper5) + (2166805889553413/50000000000000 : ℝ)*(major0) + (2166805889553413/50000000000000 : ℝ)*(major1) + (2166805889553413/50000000000000 : ℝ)*(major2) + (2125843083/10000000000000 : ℝ)*(sp1) + (3451895681/10000000000000 : ℝ)*(sp2) + (5826731923698403/100000000000000 : ℝ)*(sp4) + (233068386846853/4000000000000 : ℝ)*(sp5) + (5826696079903207/100000000000000 : ℝ)*(sp6) + (1420245717803929/50000000000000 : ℝ)*(sp7) + (1420245717803929/50000000000000 : ℝ)*(f.failure) + (5826731923698403/100000000000000 : ℝ)*(f.sum) + (587788826561/575312500000000000000000000 : ℝ)*base66 + (1634624003297754457/184100000000000000000000000000000 : ℝ)*base68 + (1095235807423645543/184100000000000000000000000000000 : ℝ)*base69 + (257057983157654457/184100000000000000000000000000000 : ℝ)*base72 + (9814009246011/9205000000000000000000000000 : ℝ)*base74 + (389302453645545543/184100000000000000000000000000000 : ℝ)*base75 + (384193862412654457/184100000000000000000000000000000 : ℝ)*base78 + (2252792790298554457/184100000000000000000000000000000 : ℝ)*base80 + (14374747314983/4602500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7674761/1250000000000000000000 : ℝ)*base90 + (7674761/1250000000000000000000 : ℝ)*base92 + (7674761/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s7_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092460957/10000000000 : ℝ)*x 0 + (1353868199/2500000000 : ℝ)*x 1 + (2621411759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092460957/10000000000 : ℝ)^4247 ≤ (12729726045351/100000000000000 : ℝ)^3223 := by
    have hnat : (2092460957 : ℕ)^4247*100000000000000^3223 ≤ 12729726045351^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092460957 10000000000 12729726045351 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353868199/2500000000 : ℝ)^4247 ≤ (2228323746573/5000000000000 : ℝ)^3223 := by
    have hnat : (1353868199 : ℕ)^4247*5000000000000^3223 ≤ 2228323746573^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353868199 2500000000 2228323746573 5000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621411759/5000000000 : ℝ)^4247 ≤ (42703799014671/100000000000000 : ℝ)^3223 := by
    have hnat : (2621411759 : ℕ)^4247*100000000000000^3223 ≤ 42703799014671^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621411759 5000000000 42703799014671 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092460957/10000000000 : ℝ), (1353868199/2500000000 : ℝ), (2621411759/5000000000 : ℝ)] ![(12729726045351/100000000000000 : ℝ), (2228323746573/5000000000000 : ℝ), (42703799014671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092460957/10000000000 : ℝ)|^4247 ≤ (12729726045351/100000000000000 : ℝ)^3223
        have hw : |(-2092460957/10000000000 : ℝ)|=(2092460957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353868199/2500000000 : ℝ)|^4247 ≤ (2228323746573/5000000000000 : ℝ)^3223
        have hw : |(1353868199/2500000000 : ℝ)|=(1353868199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621411759/5000000000 : ℝ)|^4247 ≤ (42703799014671/100000000000000 : ℝ)^3223
        have hw : |(2621411759/5000000000 : ℝ)|=(2621411759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349852931/10000000000 : ℝ)*x 0 + (-2180472097/10000000000 : ℝ)*x 1 + (2621412041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349852931/10000000000 : ℝ)^4247 ≤ (43856259517477/100000000000000 : ℝ)^3223 := by
    have hnat : (5349852931 : ℕ)^4247*100000000000000^3223 ≤ 43856259517477^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349852931 10000000000 43856259517477 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180472097/10000000000 : ℝ)^4247 ≤ (335998385119/2500000000000 : ℝ)^3223 := by
    have hnat : (2180472097 : ℕ)^4247*2500000000000^3223 ≤ 335998385119^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180472097 10000000000 335998385119 2500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621412041/5000000000 : ℝ)^4247 ≤ (42703805068113/100000000000000 : ℝ)^3223 := by
    have hnat : (2621412041 : ℕ)^4247*100000000000000^3223 ≤ 42703805068113^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621412041 5000000000 42703805068113 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349852931/10000000000 : ℝ), (-2180472097/10000000000 : ℝ), (2621412041/5000000000 : ℝ)] ![(43856259517477/100000000000000 : ℝ), (335998385119/2500000000000 : ℝ), (42703805068113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349852931/10000000000 : ℝ)|^4247 ≤ (43856259517477/100000000000000 : ℝ)^3223
        have hw : |(5349852931/10000000000 : ℝ)|=(5349852931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180472097/10000000000 : ℝ)|^4247 ≤ (335998385119/2500000000000 : ℝ)^3223
        have hw : |(-2180472097/10000000000 : ℝ)|=(2180472097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621412041/5000000000 : ℝ)|^4247 ≤ (42703805068113/100000000000000 : ℝ)^3223
        have hw : |(2621412041/5000000000 : ℝ)|=(2621412041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349853047/10000000000 : ℝ)*x 0 + (5242822451/10000000000 : ℝ)*x 1 + (-1090237049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349853047/10000000000 : ℝ)^4247 ≤ (43856260770531/100000000000000 : ℝ)^3223 := by
    have hnat : (5349853047 : ℕ)^4247*100000000000000^3223 ≤ 43856260770531^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349853047 10000000000 43856260770531 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242822451/10000000000 : ℝ)^4247 ≤ (8540757512501/20000000000000 : ℝ)^3223 := by
    have hnat : (5242822451 : ℕ)^4247*20000000000000^3223 ≤ 8540757512501^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242822451 10000000000 8540757512501 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090237049/5000000000 : ℝ)^4247 ≤ (6719975828547/50000000000000 : ℝ)^3223 := by
    have hnat : (1090237049 : ℕ)^4247*50000000000000^3223 ≤ 6719975828547^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090237049 5000000000 6719975828547 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349853047/10000000000 : ℝ), (5242822451/10000000000 : ℝ), (-1090237049/5000000000 : ℝ)] ![(43856260770531/100000000000000 : ℝ), (8540757512501/20000000000000 : ℝ), (6719975828547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349853047/10000000000 : ℝ)|^4247 ≤ (43856260770531/100000000000000 : ℝ)^3223
        have hw : |(5349853047/10000000000 : ℝ)|=(5349853047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242822451/10000000000 : ℝ)|^4247 ≤ (8540757512501/20000000000000 : ℝ)^3223
        have hw : |(5242822451/10000000000 : ℝ)|=(5242822451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090237049/5000000000 : ℝ)|^4247 ≤ (6719975828547/50000000000000 : ℝ)^3223
        have hw : |(-1090237049/5000000000 : ℝ)|=(1090237049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341209893/10000000000 : ℝ)*x 0 + (4167593907/10000000000 : ℝ)*x 1 + (4521751269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341209893/10000000000 : ℝ)^4247 ≤ (3330226574957/10000000000000 : ℝ)^3223 := by
    have hnat : (4341209893 : ℕ)^4247*10000000000000^3223 ≤ 3330226574957^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341209893 10000000000 3330226574957 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167593907/10000000000 : ℝ)^4247 ≤ (15779264265433/50000000000000 : ℝ)^3223 := by
    have hnat : (4167593907 : ℕ)^4247*50000000000000^3223 ≤ 15779264265433^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167593907 10000000000 15779264265433 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521751269/10000000000 : ℝ)^4247 ≤ (35139205705197/100000000000000 : ℝ)^3223 := by
    have hnat : (4521751269 : ℕ)^4247*100000000000000^3223 ≤ 35139205705197^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521751269 10000000000 35139205705197 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341209893/10000000000 : ℝ), (4167593907/10000000000 : ℝ), (4521751269/10000000000 : ℝ)] ![(3330226574957/10000000000000 : ℝ), (15779264265433/50000000000000 : ℝ), (35139205705197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341209893/10000000000 : ℝ)|^4247 ≤ (3330226574957/10000000000000 : ℝ)^3223
        have hw : |(4341209893/10000000000 : ℝ)|=(4341209893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167593907/10000000000 : ℝ)|^4247 ≤ (15779264265433/50000000000000 : ℝ)^3223
        have hw : |(4167593907/10000000000 : ℝ)|=(4167593907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521751269/10000000000 : ℝ)|^4247 ≤ (35139205705197/100000000000000 : ℝ)^3223
        have hw : |(4521751269/10000000000 : ℝ)|=(4521751269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092473773/10000000000 : ℝ)*x 0 + (2621719177/5000000000 : ℝ)*x 1 + (135371369/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092473773/10000000000 : ℝ)^4247 ≤ (3182457196161/25000000000000 : ℝ)^3223 := by
    have hnat : (2092473773 : ℕ)^4247*25000000000000^3223 ≤ 3182457196161^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092473773 10000000000 3182457196161 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621719177/5000000000 : ℝ)^4247 ≤ (21355199102149/50000000000000 : ℝ)^3223 := by
    have hnat : (2621719177 : ℕ)^4247*50000000000000^3223 ≤ 21355199102149^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621719177 5000000000 21355199102149 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135371369/250000000 : ℝ)^4247 ≤ (44559773003423/100000000000000 : ℝ)^3223 := by
    have hnat : (135371369 : ℕ)^4247*100000000000000^3223 ≤ 44559773003423^3223*250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135371369 250000000 44559773003423 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092473773/10000000000 : ℝ), (2621719177/5000000000 : ℝ), (135371369/250000000 : ℝ)] ![(3182457196161/25000000000000 : ℝ), (21355199102149/50000000000000 : ℝ), (44559773003423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092473773/10000000000 : ℝ)|^4247 ≤ (3182457196161/25000000000000 : ℝ)^3223
        have hw : |(-2092473773/10000000000 : ℝ)|=(2092473773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621719177/5000000000 : ℝ)|^4247 ≤ (21355199102149/50000000000000 : ℝ)^3223
        have hw : |(2621719177/5000000000 : ℝ)|=(2621719177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135371369/250000000 : ℝ)|^4247 ≤ (44559773003423/100000000000000 : ℝ)^3223
        have hw : |(135371369/250000000 : ℝ)|=(135371369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305678673/10000000000 : ℝ)*x 0 + (-1004220693/5000000000 : ℝ)*x 1 + (5414854557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305678673/10000000000 : ℝ)^4247 ≤ (43379708010371/100000000000000 : ℝ)^3223 := by
    have hnat : (5305678673 : ℕ)^4247*100000000000000^3223 ≤ 43379708010371^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305678673 10000000000 43379708010371 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004220693/5000000000 : ℝ)^4247 ≤ (2412104233501/20000000000000 : ℝ)^3223 := by
    have hnat : (1004220693 : ℕ)^4247*20000000000000^3223 ≤ 2412104233501^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004220693 5000000000 2412104233501 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414854557/10000000000 : ℝ)^4247 ≤ (11139942700537/25000000000000 : ℝ)^3223 := by
    have hnat : (5414854557 : ℕ)^4247*25000000000000^3223 ≤ 11139942700537^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414854557 10000000000 11139942700537 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305678673/10000000000 : ℝ), (-1004220693/5000000000 : ℝ), (5414854557/10000000000 : ℝ)] ![(43379708010371/100000000000000 : ℝ), (2412104233501/20000000000000 : ℝ), (11139942700537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305678673/10000000000 : ℝ)|^4247 ≤ (43379708010371/100000000000000 : ℝ)^3223
        have hw : |(5305678673/10000000000 : ℝ)|=(5305678673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004220693/5000000000 : ℝ)|^4247 ≤ (2412104233501/20000000000000 : ℝ)^3223
        have hw : |(-1004220693/5000000000 : ℝ)|=(1004220693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414854557/10000000000 : ℝ)|^4247 ≤ (11139942700537/25000000000000 : ℝ)^3223
        have hw : |(5414854557/10000000000 : ℝ)|=(5414854557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326419677/2500000000 : ℝ)*x 0 + (1353713659/2500000000 : ℝ)*x 1 + (-200844123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326419677/2500000000 : ℝ)^4247 ≤ (43379708387453/100000000000000 : ℝ)^3223 := by
    have hnat : (1326419677 : ℕ)^4247*100000000000000^3223 ≤ 43379708387453^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326419677 2500000000 43379708387453 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353713659/2500000000 : ℝ)^4247 ≤ (22279885829401/50000000000000 : ℝ)^3223 := by
    have hnat : (1353713659 : ℕ)^4247*50000000000000^3223 ≤ 22279885829401^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353713659 2500000000 22279885829401 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200844123/1000000000 : ℝ)^4247 ≤ (1507564991639/12500000000000 : ℝ)^3223 := by
    have hnat : (200844123 : ℕ)^4247*12500000000000^3223 ≤ 1507564991639^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200844123 1000000000 1507564991639 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326419677/2500000000 : ℝ), (1353713659/2500000000 : ℝ), (-200844123/1000000000 : ℝ)] ![(43379708387453/100000000000000 : ℝ), (22279885829401/50000000000000 : ℝ), (1507564991639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326419677/2500000000 : ℝ)|^4247 ≤ (43379708387453/100000000000000 : ℝ)^3223
        have hw : |(1326419677/2500000000 : ℝ)|=(1326419677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353713659/2500000000 : ℝ)|^4247 ≤ (22279885829401/50000000000000 : ℝ)^3223
        have hw : |(1353713659/2500000000 : ℝ)|=(1353713659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200844123/1000000000 : ℝ)|^4247 ≤ (1507564991639/12500000000000 : ℝ)^3223
        have hw : |(-200844123/1000000000 : ℝ)|=(200844123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s7_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341237597/10000000000 : ℝ)*x 0 + (4520489447/10000000000 : ℝ)*x 1 + (416886067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341237597/10000000000 : ℝ)^4247 ≤ (16651272897301/50000000000000 : ℝ)^3223 := by
    have hnat : (4341237597 : ℕ)^4247*50000000000000^3223 ≤ 16651272897301^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341237597 10000000000 16651272897301 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520489447/10000000000 : ℝ)^4247 ≤ (17563142502229/50000000000000 : ℝ)^3223 := by
    have hnat : (4520489447 : ℕ)^4247*50000000000000^3223 ≤ 17563142502229^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520489447 10000000000 17563142502229 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416886067/1000000000 : ℝ)^4247 ≤ (31571169187793/100000000000000 : ℝ)^3223 := by
    have hnat : (416886067 : ℕ)^4247*100000000000000^3223 ≤ 31571169187793^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416886067 1000000000 31571169187793 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341237597/10000000000 : ℝ), (4520489447/10000000000 : ℝ), (416886067/1000000000 : ℝ)] ![(16651272897301/50000000000000 : ℝ), (17563142502229/50000000000000 : ℝ), (31571169187793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341237597/10000000000 : ℝ)|^4247 ≤ (16651272897301/50000000000000 : ℝ)^3223
        have hw : |(4341237597/10000000000 : ℝ)|=(4341237597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520489447/10000000000 : ℝ)|^4247 ≤ (17563142502229/50000000000000 : ℝ)^3223
        have hw : |(4520489447/10000000000 : ℝ)|=(4520489447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416886067/1000000000 : ℝ)|^4247 ≤ (31571169187793/100000000000000 : ℝ)^3223
        have hw : |(416886067/1000000000 : ℝ)|=(416886067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2203/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14669/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11013/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11013/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11013/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11013/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (2129642469387569/20000000000000000000 : ℝ) := by
    have hpowers : (11013/100000 : ℝ)^2123 ≤ (2129642469387569/20000000000000000000 : ℝ)^512 := by
      have hnat : (11013 : ℕ)^2123*20000000000000000000^512 ≤ 2129642469387569^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11013 100000 2129642469387569 20000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11013/100000 : ℝ)) (X := (2129642469387569/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14671/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (17486715539686079/50000000000000000000 : ℝ) := by
    have hpowers : (14671/100000 : ℝ)^2123 ≤ (17486715539686079/50000000000000000000 : ℝ)^512 := by
      have hnat : (14671 : ℕ)^2123*50000000000000000000^512 ≤ 17486715539686079^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14671 100000 17486715539686079 50000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14671/100000 : ℝ)) (X := (17486715539686079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002129642469387569/10000000000000000000 : ℝ) ≤ (2500128390114303/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (10002129642469387569/10000000000000000000 : ℝ)^512 ≤ (2500128390114303/2500000000000000 : ℝ)^2123 := by
      have hnat : (10002129642469387569 : ℕ)^512*2500000000000000^2123 ≤ 2500128390114303^2123*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002129642469387569 10000000000000000000 2500128390114303 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500128390114303/2500000000000000 : ℝ)) (X := (10002129642469387569/10000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045621643426310003/100000000000000000000 : ℝ) ≤ (1250137507296841/1250000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (100045621643426310003/100000000000000000000 : ℝ)^512 ≤ (1250137507296841/1250000000000000 : ℝ)^2123 := by
      have hnat : (100045621643426310003 : ℕ)^512*1250000000000000^2123 ≤ 1250137507296841^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045621643426310003 100000000000000000000 1250137507296841 1250000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250137507296841/1250000000000000 : ℝ)) (X := (100045621643426310003/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017486715539686079/25000000000000000000 : ℝ) ≤ (2500421639073061/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (25017486715539686079/25000000000000000000 : ℝ)^512 ≤ (2500421639073061/2500000000000000 : ℝ)^2123 := by
      have hnat : (25017486715539686079 : ℕ)^512*2500000000000000^2123 ≤ 2500421639073061^2123*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017486715539686079 25000000000000000000 2500421639073061 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500421639073061/2500000000000000 : ℝ)) (X := (25017486715539686079/25000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2129642469387569/20000000000000000000 : ℝ) ≤ ((228556002506382963/228625000000000000 : ℝ)+2*(146624479379/91450000000000 : ℝ)*(11013/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (228556002506382963/228625000000000000 : ℝ)+2*(146624479379/91450000000000 : ℝ)*(11013/100000 : ℝ)=(2500128390114303/2500000000000000 : ℝ) by norm_num, show 1+2*(2129642469387569/20000000000000000000 : ℝ)=(10002129642469387569/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17486715539686079/50000000000000000000 : ℝ)+(2129642469387569/20000000000000000000 : ℝ) ≤ ((228556002506382963/228625000000000000 : ℝ)+(146624479379/91450000000000 : ℝ)*((14671/100000 : ℝ)+(11013/100000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (228556002506382963/228625000000000000 : ℝ)+(146624479379/91450000000000 : ℝ)*((14671/100000 : ℝ)+(11013/100000 : ℝ))=(1250137507296841/1250000000000000 : ℝ) by norm_num, show 1+(17486715539686079/50000000000000000000 : ℝ)+(2129642469387569/20000000000000000000 : ℝ)=(100045621643426310003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17486715539686079/50000000000000000000 : ℝ) ≤ ((228556002506382963/228625000000000000 : ℝ)+2*(146624479379/91450000000000 : ℝ)*(14671/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (228556002506382963/228625000000000000 : ℝ)+2*(146624479379/91450000000000 : ℝ)*(14671/100000 : ℝ)=(2500421639073061/2500000000000000 : ℝ) by norm_num, show 1+2*(17486715539686079/50000000000000000000 : ℝ)=(25017486715539686079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (228556002506382963/228625000000000000 : ℝ)*(X 1 0+X 2 0)+(146624479379/91450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (228556002506382963/228625000000000000 : ℝ)) (alpha := (146624479379/91450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (228556002506382963/228625000000000000 : ℝ)*(X 0 1+X 2 1)+(146624479379/91450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (228556002506382963/228625000000000000 : ℝ)) (alpha := (146624479379/91450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (228556002506382963/228625000000000000 : ℝ)*(X 0 2+X 1 2)+(146624479379/91450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (11013/100000 : ℝ)) (hi := (14671/100000 : ℝ)) (c := (228556002506382963/228625000000000000 : ℝ)) (alpha := (146624479379/91450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2092460957/10000000000 : ℝ)*X 0 0+(1353868199/2500000000 : ℝ)*X 0 1+(2621411759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349852931/10000000000 : ℝ)*X 1 0+(-2180472097/10000000000 : ℝ)*X 1 1+(2621412041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349853047/10000000000 : ℝ)*X 2 0+(5242822451/10000000000 : ℝ)*X 2 1+(-1090237049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341209893/10000000000 : ℝ)*X 0 0+(4167593907/10000000000 : ℝ)*X 0 1+(4521751269/10000000000 : ℝ)*X 0 2+(4341209893/10000000000 : ℝ)*X 1 0+(4167593907/10000000000 : ℝ)*X 1 1+(4521751269/10000000000 : ℝ)*X 1 2+(4341209893/10000000000 : ℝ)*X 2 0+(4167593907/10000000000 : ℝ)*X 2 1+(4521751269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2092473773/10000000000 : ℝ)*X 0 0+(2621719177/5000000000 : ℝ)*X 0 1+(135371369/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305678673/10000000000 : ℝ)*X 1 0+(-1004220693/5000000000 : ℝ)*X 1 1+(5414854557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326419677/2500000000 : ℝ)*X 2 0+(1353713659/2500000000 : ℝ)*X 2 1+(-200844123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341237597/10000000000 : ℝ)*X 0 0+(4520489447/10000000000 : ℝ)*X 0 1+(416886067/1000000000 : ℝ)*X 0 2+(4341237597/10000000000 : ℝ)*X 1 0+(4520489447/10000000000 : ℝ)*X 1 1+(416886067/1000000000 : ℝ)*X 1 2+(4341237597/10000000000 : ℝ)*X 2 0+(4520489447/10000000000 : ℝ)*X 2 1+(416886067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99460596475461557536532709/11431250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245796723/100000000000000 : ℝ)*(base15) + (39808333/12500000000000 : ℝ)*(upper2) + (28513283/100000000000000 : ℝ)*(upper4) + (201730661/100000000000000 : ℝ)*(lower5) + (4307877690556869/100000000000000 : ℝ)*(major0) + (4307877690556869/100000000000000 : ℝ)*(major1) + (4307877690556869/100000000000000 : ℝ)*(major2) + (144802992933947/2500000000000 : ℝ)*(sp0) + (2896065485006677/50000000000000 : ℝ)*(sp1) + (5792076242036099/100000000000000 : ℝ)*(sp2) + (2823614620996303/100000000000000 : ℝ)*(sp3) + (5749226099/50000000000000 : ℝ)*(sp4) + (27486886989/50000000000000 : ℝ)*(sp6) + (4627140957/50000000000000 : ℝ)*(sp7) + (2823623875278217/100000000000000 : ℝ)*(f.failure) + (2896065607905039/50000000000000 : ℝ)*(f.sum) + (167688540858367/9145000000000000000000000000 : ℝ)*base65 + (143915737399637153/22862500000000000000000000000000 : ℝ)*base68 + (94587159910062847/22862500000000000000000000000000 : ℝ)*base69 + (109010617238612847/22862500000000000000000000000000 : ℝ)*base71 + (26403302153757/9145000000000000000000000000 : ℝ)*base73 + (114682600951587153/22862500000000000000000000000000 : ℝ)*base76 + (287517279151275347/22862500000000000000000000000000 : ℝ)*base77 + (125539719482050347/22862500000000000000000000000000 : ℝ)*base79 + (4484564288177/9145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16620153/2500000000000000000000 : ℝ)*base90 + (16620153/2500000000000000000000 : ℝ)*base92 + (16620153/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50076074117248127177129379/5715625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185198579/12500000000000 : ℝ)*(base19) + (852910039/50000000000000 : ℝ)*(base23) + (384337469/100000000000000 : ℝ)*(lower1) + (44141981/25000000000000 : ℝ)*(upper3) + (6592961/12500000000000 : ℝ)*(lower4) + (42778381/50000000000000 : ℝ)*(upper5) + (1084702546021893/25000000000000 : ℝ)*(major0) + (1084702546021893/25000000000000 : ℝ)*(major1) + (1084702546021893/25000000000000 : ℝ)*(major2) + (10369888249/100000000000000 : ℝ)*(sp2) + (5833721315278063/100000000000000 : ℝ)*(sp4) + (583371983368943/10000000000000 : ℝ)*(sp5) + (1166741847913947/20000000000000 : ℝ)*(sp6) + (1421949380427543/50000000000000 : ℝ)*(sp7) + (1421949380427543/50000000000000 : ℝ)*(f.failure) + (5833721315278063/100000000000000 : ℝ)*(f.sum) + (19723740205341/9145000000000000000000000000 : ℝ)*base65 + (106129287616723541/5715625000000000000000000000000 : ℝ)*base68 + (40115486434611041/5715625000000000000000000000000 : ℝ)*base70 + (76140913448738959/5715625000000000000000000000000 : ℝ)*base71 + (10688777642207/4572500000000000000000000000 : ℝ)*base74 + (51541607404204791/5715625000000000000000000000000 : ℝ)*base76 + (31592497256094583/2857812500000000000000000000000 : ℝ)*base78 + (7751631074680417/2857812500000000000000000000000 : ℝ)*base79 + (2197902366973/1143125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14732313/1250000000000000000000 : ℝ)*base89 + (14732313/1250000000000000000000 : ℝ)*base91 + (14732313/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1287_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11013/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s8_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674924773/5000000000 : ℝ)*x 0 + (5242839207/10000000000 : ℝ)*x 1 + (-2180456611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674924773/5000000000 : ℝ)^4247 ≤ (43856222952077/100000000000000 : ℝ)^3223 := by
    have hnat : (2674924773 : ℕ)^4247*100000000000000^3223 ≤ 43856222952077^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674924773 5000000000 43856222952077 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242839207/10000000000 : ℝ)^4247 ≤ (42703967405603/100000000000000 : ℝ)^3223 := by
    have hnat : (5242839207 : ℕ)^4247*100000000000000^3223 ≤ 42703967405603^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242839207 10000000000 42703967405603 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180456611/10000000000 : ℝ)^4247 ≤ (13439809625983/100000000000000 : ℝ)^3223 := by
    have hnat : (2180456611 : ℕ)^4247*100000000000000^3223 ≤ 13439809625983^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180456611 10000000000 13439809625983 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674924773/5000000000 : ℝ), (5242839207/10000000000 : ℝ), (-2180456611/10000000000 : ℝ)] ![(43856222952077/100000000000000 : ℝ), (42703967405603/100000000000000 : ℝ), (13439809625983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674924773/5000000000 : ℝ)|^4247 ≤ (43856222952077/100000000000000 : ℝ)^3223
        have hw : |(2674924773/5000000000 : ℝ)|=(2674924773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242839207/10000000000 : ℝ)|^4247 ≤ (42703967405603/100000000000000 : ℝ)^3223
        have hw : |(5242839207/10000000000 : ℝ)|=(5242839207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2180456611/10000000000 : ℝ)|^4247 ≤ (13439809625983/100000000000000 : ℝ)^3223
        have hw : |(-2180456611/10000000000 : ℝ)|=(2180456611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s8_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092475607/10000000000 : ℝ)*x 0 + (2621727457/5000000000 : ℝ)*x 1 + (5414837011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092475607/10000000000 : ℝ)^4247 ≤ (12729843486897/100000000000000 : ℝ)^3223 := by
    have hnat : (2092475607 : ℕ)^4247*100000000000000^3223 ≤ 12729843486897^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092475607 10000000000 12729843486897 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621727457/5000000000 : ℝ)^4247 ≤ (42710575950349/100000000000000 : ℝ)^3223 := by
    have hnat : (2621727457 : ℕ)^4247*100000000000000^3223 ≤ 42710575950349^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621727457 5000000000 42710575950349 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414837011/10000000000 : ℝ)^4247 ≤ (44559580538417/100000000000000 : ℝ)^3223 := by
    have hnat : (5414837011 : ℕ)^4247*100000000000000^3223 ≤ 44559580538417^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414837011 10000000000 44559580538417 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092475607/10000000000 : ℝ), (2621727457/5000000000 : ℝ), (5414837011/10000000000 : ℝ)] ![(12729843486897/100000000000000 : ℝ), (42710575950349/100000000000000 : ℝ), (44559580538417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092475607/10000000000 : ℝ)|^4247 ≤ (12729843486897/100000000000000 : ℝ)^3223
        have hw : |(-2092475607/10000000000 : ℝ)|=(2092475607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621727457/5000000000 : ℝ)|^4247 ≤ (42710575950349/100000000000000 : ℝ)^3223
        have hw : |(2621727457/5000000000 : ℝ)|=(2621727457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414837011/10000000000 : ℝ)|^4247 ≤ (44559580538417/100000000000000 : ℝ)^3223
        have hw : |(5414837011/10000000000 : ℝ)|=(5414837011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s8_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326420759/2500000000 : ℝ)*x 0 + (-401691899/2000000000 : ℝ)*x 1 + (338427313/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326420759/2500000000 : ℝ)^4247 ≤ (43379755016329/100000000000000 : ℝ)^3223 := by
    have hnat : (1326420759 : ℕ)^4247*100000000000000^3223 ≤ 43379755016329^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326420759 2500000000 43379755016329 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401691899/2000000000 : ℝ)^4247 ≤ (1206066446017/10000000000000 : ℝ)^3223 := by
    have hnat : (401691899 : ℕ)^4247*10000000000000^3223 ≤ 1206066446017^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401691899 2000000000 1206066446017 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338427313/625000000 : ℝ)^4247 ≤ (22279790252943/50000000000000 : ℝ)^3223 := by
    have hnat : (338427313 : ℕ)^4247*50000000000000^3223 ≤ 22279790252943^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338427313 625000000 22279790252943 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326420759/2500000000 : ℝ), (-401691899/2000000000 : ℝ), (338427313/625000000 : ℝ)] ![(43379755016329/100000000000000 : ℝ), (1206066446017/10000000000000 : ℝ), (22279790252943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326420759/2500000000 : ℝ)|^4247 ≤ (43379755016329/100000000000000 : ℝ)^3223
        have hw : |(1326420759/2500000000 : ℝ)|=(1326420759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401691899/2000000000 : ℝ)|^4247 ≤ (1206066446017/10000000000000 : ℝ)^3223
        have hw : |(-401691899/2000000000 : ℝ)|=(401691899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338427313/625000000 : ℝ)|^4247 ≤ (22279790252943/50000000000000 : ℝ)^3223
        have hw : |(338427313/625000000 : ℝ)|=(338427313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s8_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326420759/2500000000 : ℝ)*x 0 + (5414837009/10000000000 : ℝ)*x 1 + (-2008459493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326420759/2500000000 : ℝ)^4247 ≤ (43379755016329/100000000000000 : ℝ)^3223 := by
    have hnat : (1326420759 : ℕ)^4247*100000000000000^3223 ≤ 43379755016329^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326420759 2500000000 43379755016329 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414837009/10000000000 : ℝ)^4247 ≤ (4455958051673/10000000000000 : ℝ)^3223 := by
    have hnat : (5414837009 : ℕ)^4247*10000000000000^3223 ≤ 4455958051673^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414837009 10000000000 4455958051673 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008459493/10000000000 : ℝ)^4247 ≤ (1507583055543/12500000000000 : ℝ)^3223 := by
    have hnat : (2008459493 : ℕ)^4247*12500000000000^3223 ≤ 1507583055543^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008459493 10000000000 1507583055543 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326420759/2500000000 : ℝ), (5414837009/10000000000 : ℝ), (-2008459493/10000000000 : ℝ)] ![(43379755016329/100000000000000 : ℝ), (4455958051673/10000000000000 : ℝ), (1507583055543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326420759/2500000000 : ℝ)|^4247 ≤ (43379755016329/100000000000000 : ℝ)^3223
        have hw : |(1326420759/2500000000 : ℝ)|=(1326420759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414837009/10000000000 : ℝ)|^4247 ≤ (4455958051673/10000000000000 : ℝ)^3223
        have hw : |(5414837009/10000000000 : ℝ)|=(5414837009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008459493/10000000000 : ℝ)|^4247 ≤ (1507583055543/12500000000000 : ℝ)^3223
        have hw : |(-2008459493/10000000000 : ℝ)|=(2008459493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s8_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341238997/10000000000 : ℝ)*x 0 + (4520453827/10000000000 : ℝ)*x 1 + (20844479/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341238997/10000000000 : ℝ)^4247 ≤ (16651279973237/50000000000000 : ℝ)^3223 := by
    have hnat : (4341238997 : ℕ)^4247*50000000000000^3223 ≤ 16651279973237^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341238997 10000000000 16651279973237 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520453827/10000000000 : ℝ)^4247 ≤ (35125920282351/100000000000000 : ℝ)^3223 := by
    have hnat : (4520453827 : ℕ)^4247*100000000000000^3223 ≤ 35125920282351^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520453827 10000000000 35125920282351 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20844479/50000000 : ℝ)^4247 ≤ (15785759878583/50000000000000 : ℝ)^3223 := by
    have hnat : (20844479 : ℕ)^4247*50000000000000^3223 ≤ 15785759878583^3223*50000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20844479 50000000 15785759878583 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341238997/10000000000 : ℝ), (4520453827/10000000000 : ℝ), (20844479/50000000 : ℝ)] ![(16651279973237/50000000000000 : ℝ), (35125920282351/100000000000000 : ℝ), (15785759878583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341238997/10000000000 : ℝ)|^4247 ≤ (16651279973237/50000000000000 : ℝ)^3223
        have hw : |(4341238997/10000000000 : ℝ)|=(4341238997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520453827/10000000000 : ℝ)|^4247 ≤ (35125920282351/100000000000000 : ℝ)^3223
        have hw : |(4520453827/10000000000 : ℝ)|=(4520453827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20844479/50000000 : ℝ)|^4247 ≤ (15785759878583/50000000000000 : ℝ)^3223
        have hw : |(20844479/50000000 : ℝ)|=(20844479/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2203/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3667/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2203/20000 : ℝ) ^ (2123/512 : ℝ) ≤ (10656232915801949/100000000000000000000 : ℝ) := by
    have hpowers : (2203/20000 : ℝ)^2123 ≤ (10656232915801949/100000000000000000000 : ℝ)^512 := by
      have hnat : (2203 : ℕ)^2123*100000000000000000000^512 ≤ 10656232915801949^512*20000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2203 20000 10656232915801949 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2203/20000 : ℝ)) (X := (10656232915801949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14669/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (17476833071766807/50000000000000000000 : ℝ) := by
    have hpowers : (14669/100000 : ℝ)^2123 ≤ (17476833071766807/50000000000000000000 : ℝ)^512 := by
      have hnat : (14669 : ℕ)^2123*50000000000000000000^512 ≤ 17476833071766807^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14669 100000 17476833071766807 50000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14669/100000 : ℝ)) (X := (17476833071766807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010656232915801949/50000000000000000000 : ℝ) ≤ (5000256973627923/5000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50010656232915801949/50000000000000000000 : ℝ)^512 ≤ (5000256973627923/5000000000000000 : ℝ)^2123 := by
      have hnat : (50010656232915801949 : ℕ)^512*5000000000000000^2123 ≤ 5000256973627923^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010656232915801949 50000000000000000000 5000256973627923 5000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000256973627923/5000000000000000 : ℝ)) (X := (50010656232915801949/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045609899059335563/100000000000000000000 : ℝ) ≤ (2000219955047199/2000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (100045609899059335563/100000000000000000000 : ℝ)^512 ≤ (2000219955047199/2000000000000000 : ℝ)^2123 := by
      have hnat : (100045609899059335563 : ℕ)^512*2000000000000000^2123 ≤ 2000219955047199^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045609899059335563 100000000000000000000 2000219955047199 2000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000219955047199/2000000000000000 : ℝ)) (X := (100045609899059335563/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017476833071766807/25000000000000000000 : ℝ) ≤ (625105350201009/625000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (25017476833071766807/25000000000000000000 : ℝ)^512 ≤ (625105350201009/625000000000000 : ℝ)^2123 := by
      have hnat : (25017476833071766807 : ℕ)^512*625000000000000^2123 ≤ 625105350201009^2123*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017476833071766807 25000000000000000000 625105350201009 625000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625105350201009/625000000000000 : ℝ)) (X := (25017476833071766807/25000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10656232915801949/100000000000000000000 : ℝ) ≤ ((6088162028811696469/6090000000000000000 : ℝ)+2*(195275993383/121800000000000 : ℝ)*(2203/20000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (6088162028811696469/6090000000000000000 : ℝ)+2*(195275993383/121800000000000 : ℝ)*(2203/20000 : ℝ)=(5000256973627923/5000000000000000 : ℝ) by norm_num, show 1+2*(10656232915801949/100000000000000000000 : ℝ)=(50010656232915801949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17476833071766807/50000000000000000000 : ℝ)+(10656232915801949/100000000000000000000 : ℝ) ≤ ((6088162028811696469/6090000000000000000 : ℝ)+(195275993383/121800000000000 : ℝ)*((14669/100000 : ℝ)+(2203/20000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (6088162028811696469/6090000000000000000 : ℝ)+(195275993383/121800000000000 : ℝ)*((14669/100000 : ℝ)+(2203/20000 : ℝ))=(2000219955047199/2000000000000000 : ℝ) by norm_num, show 1+(17476833071766807/50000000000000000000 : ℝ)+(10656232915801949/100000000000000000000 : ℝ)=(100045609899059335563/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17476833071766807/50000000000000000000 : ℝ) ≤ ((6088162028811696469/6090000000000000000 : ℝ)+2*(195275993383/121800000000000 : ℝ)*(14669/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (6088162028811696469/6090000000000000000 : ℝ)+2*(195275993383/121800000000000 : ℝ)*(14669/100000 : ℝ)=(625105350201009/625000000000000 : ℝ) by norm_num, show 1+2*(17476833071766807/50000000000000000000 : ℝ)=(25017476833071766807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6088162028811696469/6090000000000000000 : ℝ)*(X 1 0+X 2 0)+(195275993383/121800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (6088162028811696469/6090000000000000000 : ℝ)) (alpha := (195275993383/121800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6088162028811696469/6090000000000000000 : ℝ)*(X 0 1+X 2 1)+(195275993383/121800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (6088162028811696469/6090000000000000000 : ℝ)) (alpha := (195275993383/121800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6088162028811696469/6090000000000000000 : ℝ)*(X 0 2+X 1 2)+(195275993383/121800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (6088162028811696469/6090000000000000000 : ℝ)) (alpha := (195275993383/121800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674924773/5000000000 : ℝ)*X 2 0+(5242839207/10000000000 : ℝ)*X 2 1+(-2180456611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2092475607/10000000000 : ℝ)*X 0 0+(2621727457/5000000000 : ℝ)*X 0 1+(5414837011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1326420759/2500000000 : ℝ)*X 1 0+(-401691899/2000000000 : ℝ)*X 1 1+(338427313/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1326420759/2500000000 : ℝ)*X 2 0+(5414837009/10000000000 : ℝ)*X 2 1+(-2008459493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4341238997/10000000000 : ℝ)*X 0 0+(4520453827/10000000000 : ℝ)*X 0 1+(20844479/50000000 : ℝ)*X 0 2+(4341238997/10000000000 : ℝ)*X 1 0+(4520453827/10000000000 : ℝ)*X 1 1+(20844479/50000000 : ℝ)*X 1 2+(4341238997/10000000000 : ℝ)*X 2 0+(4520453827/10000000000 : ℝ)*X 2 1+(20844479/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (524984591174812902321/203000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234123383/50000000000000 : ℝ)*(base19) + (101336807/20000000000000 : ℝ)*(base23) + (20031569/12500000000000 : ℝ)*(lower1) + (6586969/12500000000000 : ℝ)*(upper3) + (17247121/100000000000000 : ℝ)*(lower4) + (53502213/100000000000000 : ℝ)*(upper5) + (108492269715363/2500000000000 : ℝ)*(major0) + (108492269715363/2500000000000 : ℝ)*(major1) + (108492269715363/2500000000000 : ℝ)*(major2) + (142482463/20000000000000 : ℝ)*(sp0) + (5834905532731407/100000000000000 : ℝ)*(sp1) + (5834905064484641/100000000000000 : ℝ)*(sp2) + (5834904313635057/100000000000000 : ℝ)*(sp3) + (1422237979146631/50000000000000 : ℝ)*(sp4) + (1422237979146631/50000000000000 : ℝ)*(f.failure) + (5834905532731407/100000000000000 : ℝ)*(f.sum) + (469293923123/203000000000000000000000000 : ℝ)*base66 + (25307601707532251/5075000000000000000000000000000 : ℝ)*base68 + (8522823287092749/5075000000000000000000000000000 : ℝ)*base69 + (12464148406117749/5075000000000000000000000000000 : ℝ)*base71 + (43987702113/40600000000000000000000000 : ℝ)*base74 + (79630223308267749/5075000000000000000000000000000 : ℝ)*base75 + (36007694071332251/5075000000000000000000000000000 : ℝ)*base78 + (39105383411532251/5075000000000000000000000000000 : ℝ)*base80 + (10893641653/20300000000000000000000000 : ℝ)*base82 + (696279/1250000000000000000000 : ℝ)*base90 + (696279/1250000000000000000000 : ℝ)*base92 + (696279/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1287_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1287_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1287_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1287_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:04.050838+00:00
-- url     : https://prove2.me/submissions/f1afd4a2-ca13-41a7-be5b-95478ed4dc36

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
theorem support_rectangle_w1306_s6_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075476691/10000000000 : ℝ)*x 0 + (2707297401/5000000000 : ℝ)*x 1 + (5243407841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075476691/10000000000 : ℝ)^2133 ≤ (12630673951897/100000000000000 : ℝ)^1621 := by
    have hnat : (2075476691 : ℕ)^2133*100000000000000^1621 ≤ 12630673951897^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075476691 10000000000 12630673951897 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707297401/5000000000 : ℝ)^2133 ≤ (22303940622407/50000000000000 : ℝ)^1621 := by
    have hnat : (2707297401 : ℕ)^2133*50000000000000^1621 ≤ 22303940622407^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707297401 5000000000 22303940622407 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243407841/10000000000 : ℝ)^2133 ≤ (855228895763/2000000000000 : ℝ)^1621 := by
    have hnat : (5243407841 : ℕ)^2133*2000000000000^1621 ≤ 855228895763^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243407841 10000000000 855228895763 2000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075476691/10000000000 : ℝ), (2707297401/5000000000 : ℝ), (5243407841/10000000000 : ℝ)] ![(12630673951897/100000000000000 : ℝ), (22303940622407/50000000000000 : ℝ), (855228895763/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075476691/10000000000 : ℝ)|^2133 ≤ (12630673951897/100000000000000 : ℝ)^1621
        have hw : |(-2075476691/10000000000 : ℝ)|=(2075476691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707297401/5000000000 : ℝ)|^2133 ≤ (22303940622407/50000000000000 : ℝ)^1621
        have hw : |(2707297401/5000000000 : ℝ)|=(2707297401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243407841/10000000000 : ℝ)|^2133 ≤ (855228895763/2000000000000 : ℝ)^1621
        have hw : |(5243407841/10000000000 : ℝ)|=(5243407841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349595811/10000000000 : ℝ)*x 0 + (-13517051/62500000 : ℝ)*x 1 + (131085187/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349595811/10000000000 : ℝ)^2133 ≤ (43904592457877/100000000000000 : ℝ)^1621 := by
    have hnat : (5349595811 : ℕ)^2133*100000000000000^1621 ≤ 43904592457877^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349595811 10000000000 43904592457877 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13517051/62500000 : ℝ)^2133 ≤ (1666745825347/12500000000000 : ℝ)^1621 := by
    have hnat : (13517051 : ℕ)^2133*12500000000000^1621 ≤ 1666745825347^1621*62500000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13517051 62500000 1666745825347 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131085187/250000000 : ℝ)^2133 ≤ (21380720457101/50000000000000 : ℝ)^1621 := by
    have hnat : (131085187 : ℕ)^2133*50000000000000^1621 ≤ 21380720457101^1621*250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131085187 250000000 21380720457101 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349595811/10000000000 : ℝ), (-13517051/62500000 : ℝ), (131085187/250000000 : ℝ)] ![(43904592457877/100000000000000 : ℝ), (1666745825347/12500000000000 : ℝ), (21380720457101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349595811/10000000000 : ℝ)|^2133 ≤ (43904592457877/100000000000000 : ℝ)^1621
        have hw : |(5349595811/10000000000 : ℝ)|=(5349595811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13517051/62500000 : ℝ)|^2133 ≤ (1666745825347/12500000000000 : ℝ)^1621
        have hw : |(-13517051/62500000 : ℝ)|=(13517051/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131085187/250000000 : ℝ)|^2133 ≤ (21380720457101/50000000000000 : ℝ)^1621
        have hw : |(131085187/250000000 : ℝ)|=(131085187/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267479751/500000000 : ℝ)*x 0 + (1310851941/2500000000 : ℝ)*x 1 + (-1081364419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267479751/500000000 : ℝ)^2133 ≤ (43904583915607/100000000000000 : ℝ)^1621 := by
    have hnat : (267479751 : ℕ)^2133*100000000000000^1621 ≤ 43904583915607^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267479751 500000000 43904583915607 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310851941/2500000000 : ℝ)^2133 ≤ (42761443961851/100000000000000 : ℝ)^1621 := by
    have hnat : (1310851941 : ℕ)^2133*100000000000000^1621 ≤ 42761443961851^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310851941 2500000000 42761443961851 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081364419/5000000000 : ℝ)^2133 ≤ (2666794420637/20000000000000 : ℝ)^1621 := by
    have hnat : (1081364419 : ℕ)^2133*20000000000000^1621 ≤ 2666794420637^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081364419 5000000000 2666794420637 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267479751/500000000 : ℝ), (1310851941/2500000000 : ℝ), (-1081364419/5000000000 : ℝ)] ![(43904583915607/100000000000000 : ℝ), (42761443961851/100000000000000 : ℝ), (2666794420637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267479751/500000000 : ℝ)|^2133 ≤ (43904583915607/100000000000000 : ℝ)^1621
        have hw : |(267479751/500000000 : ℝ)|=(267479751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310851941/2500000000 : ℝ)|^2133 ≤ (42761443961851/100000000000000 : ℝ)^1621
        have hw : |(1310851941/2500000000 : ℝ)|=(1310851941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1081364419/5000000000 : ℝ)|^2133 ≤ (2666794420637/20000000000000 : ℝ)^1621
        have hw : |(-1081364419/5000000000 : ℝ)|=(1081364419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4336117281/10000000000 : ℝ)*x 0 + (1040671773/2500000000 : ℝ)*x 1 + (2258200279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336117281/10000000000 : ℝ)^2133 ≤ (1665128603417/5000000000000 : ℝ)^1621 := by
    have hnat : (4336117281 : ℕ)^2133*5000000000000^1621 ≤ 1665128603417^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336117281 10000000000 1665128603417 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040671773/2500000000 : ℝ)^2133 ≤ (15780519486673/50000000000000 : ℝ)^1621 := by
    have hnat : (1040671773 : ℕ)^2133*50000000000000^1621 ≤ 15780519486673^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040671773 2500000000 15780519486673 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258200279/5000000000 : ℝ)^2133 ≤ (17568194468309/50000000000000 : ℝ)^1621 := by
    have hnat : (2258200279 : ℕ)^2133*50000000000000^1621 ≤ 17568194468309^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258200279 5000000000 17568194468309 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336117281/10000000000 : ℝ), (1040671773/2500000000 : ℝ), (2258200279/5000000000 : ℝ)] ![(1665128603417/5000000000000 : ℝ), (15780519486673/50000000000000 : ℝ), (17568194468309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336117281/10000000000 : ℝ)|^2133 ≤ (1665128603417/5000000000000 : ℝ)^1621
        have hw : |(4336117281/10000000000 : ℝ)|=(4336117281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040671773/2500000000 : ℝ)|^2133 ≤ (15780519486673/50000000000000 : ℝ)^1621
        have hw : |(1040671773/2500000000 : ℝ)|=(1040671773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258200279/5000000000 : ℝ)|^2133 ≤ (17568194468309/50000000000000 : ℝ)^1621
        have hw : |(2258200279/5000000000 : ℝ)|=(2258200279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-518872427/2500000000 : ℝ)*x 0 + (5244018987/10000000000 : ℝ)*x 1 + (5413980189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518872427/2500000000 : ℝ)^2133 ≤ (6315389095161/50000000000000 : ℝ)^1621 := by
    have hnat : (518872427 : ℕ)^2133*50000000000000^1621 ≤ 6315389095161^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518872427 2500000000 6315389095161 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244018987/10000000000 : ℝ)^2133 ≤ (42768003212891/100000000000000 : ℝ)^1621 := by
    have hnat : (5244018987 : ℕ)^2133*100000000000000^1621 ≤ 42768003212891^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244018987 10000000000 42768003212891 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413980189/10000000000 : ℝ)^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621 := by
    have hnat : (5413980189 : ℕ)^2133*50000000000000^1621 ≤ 22300609294099^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413980189 10000000000 22300609294099 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-518872427/2500000000 : ℝ), (5244018987/10000000000 : ℝ), (5413980189/10000000000 : ℝ)] ![(6315389095161/50000000000000 : ℝ), (42768003212891/100000000000000 : ℝ), (22300609294099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-518872427/2500000000 : ℝ)|^2133 ≤ (6315389095161/50000000000000 : ℝ)^1621
        have hw : |(-518872427/2500000000 : ℝ)|=(518872427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244018987/10000000000 : ℝ)|^2133 ≤ (42768003212891/100000000000000 : ℝ)^1621
        have hw : |(5244018987/10000000000 : ℝ)|=(5244018987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413980189/10000000000 : ℝ)|^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621
        have hw : |(5413980189/10000000000 : ℝ)|=(5413980189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305690259/10000000000 : ℝ)*x 0 + (-249019511/1250000000 : ℝ)*x 1 + (5413980189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305690259/10000000000 : ℝ)^2133 ≤ (43431057628583/100000000000000 : ℝ)^1621 := by
    have hnat : (5305690259 : ℕ)^2133*100000000000000^1621 ≤ 43431057628583^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305690259 10000000000 43431057628583 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249019511/1250000000 : ℝ)^2133 ≤ (2393544753893/20000000000000 : ℝ)^1621 := by
    have hnat : (249019511 : ℕ)^2133*20000000000000^1621 ≤ 2393544753893^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249019511 1250000000 2393544753893 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413980189/10000000000 : ℝ)^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621 := by
    have hnat : (5413980189 : ℕ)^2133*50000000000000^1621 ≤ 22300609294099^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413980189 10000000000 22300609294099 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305690259/10000000000 : ℝ), (-249019511/1250000000 : ℝ), (5413980189/10000000000 : ℝ)] ![(43431057628583/100000000000000 : ℝ), (2393544753893/20000000000000 : ℝ), (22300609294099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305690259/10000000000 : ℝ)|^2133 ≤ (43431057628583/100000000000000 : ℝ)^1621
        have hw : |(5305690259/10000000000 : ℝ)|=(5305690259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249019511/1250000000 : ℝ)|^2133 ≤ (2393544753893/20000000000000 : ℝ)^1621
        have hw : |(-249019511/1250000000 : ℝ)|=(249019511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413980189/10000000000 : ℝ)|^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621
        have hw : |(5413980189/10000000000 : ℝ)|=(5413980189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305690259/10000000000 : ℝ)*x 0 + (5413980189/10000000000 : ℝ)*x 1 + (-249019511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305690259/10000000000 : ℝ)^2133 ≤ (43431057628583/100000000000000 : ℝ)^1621 := by
    have hnat : (5305690259 : ℕ)^2133*100000000000000^1621 ≤ 43431057628583^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305690259 10000000000 43431057628583 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413980189/10000000000 : ℝ)^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621 := by
    have hnat : (5413980189 : ℕ)^2133*50000000000000^1621 ≤ 22300609294099^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413980189 10000000000 22300609294099 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249019511/1250000000 : ℝ)^2133 ≤ (2393544753893/20000000000000 : ℝ)^1621 := by
    have hnat : (249019511 : ℕ)^2133*20000000000000^1621 ≤ 2393544753893^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249019511 1250000000 2393544753893 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305690259/10000000000 : ℝ), (5413980189/10000000000 : ℝ), (-249019511/1250000000 : ℝ)] ![(43431057628583/100000000000000 : ℝ), (22300609294099/50000000000000 : ℝ), (2393544753893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305690259/10000000000 : ℝ)|^2133 ≤ (43431057628583/100000000000000 : ℝ)^1621
        have hw : |(5305690259/10000000000 : ℝ)|=(5305690259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413980189/10000000000 : ℝ)|^2133 ≤ (22300609294099/50000000000000 : ℝ)^1621
        have hw : |(5413980189/10000000000 : ℝ)|=(5413980189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249019511/1250000000 : ℝ)|^2133 ≤ (2393544753893/20000000000000 : ℝ)^1621
        have hw : |(-249019511/1250000000 : ℝ)|=(249019511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s6_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2168071889/5000000000 : ℝ)*x 0 + (2257568453/5000000000 : ℝ)*x 1 + (4163956759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168071889/5000000000 : ℝ)^2133 ≤ (666056797011/2000000000000 : ℝ)^1621 := by
    have hnat : (2168071889 : ℕ)^2133*2000000000000^1621 ≤ 666056797011^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168071889 5000000000 666056797011 2000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257568453/5000000000 : ℝ)^2133 ≤ (35123453508367/100000000000000 : ℝ)^1621 := by
    have hnat : (2257568453 : ℕ)^2133*100000000000000^1621 ≤ 35123453508367^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257568453 5000000000 35123453508367 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163956759/10000000000 : ℝ)^2133 ≤ (31573706625097/100000000000000 : ℝ)^1621 := by
    have hnat : (4163956759 : ℕ)^2133*100000000000000^1621 ≤ 31573706625097^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163956759 10000000000 31573706625097 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168071889/5000000000 : ℝ), (2257568453/5000000000 : ℝ), (4163956759/10000000000 : ℝ)] ![(666056797011/2000000000000 : ℝ), (35123453508367/100000000000000 : ℝ), (31573706625097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168071889/5000000000 : ℝ)|^2133 ≤ (666056797011/2000000000000 : ℝ)^1621
        have hw : |(2168071889/5000000000 : ℝ)|=(2168071889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257568453/5000000000 : ℝ)|^2133 ≤ (35123453508367/100000000000000 : ℝ)^1621
        have hw : |(2257568453/5000000000 : ℝ)|=(2257568453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163956759/10000000000 : ℝ)|^2133 ≤ (31573706625097/100000000000000 : ℝ)^1621
        have hw : |(4163956759/10000000000 : ℝ)|=(4163956759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3671/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11051/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (10368840860489337/100000000000000000000 : ℝ) := by
    have hpowers : (11051/100000 : ℝ)^4265 ≤ (10368840860489337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11051 : ℕ)^4265*100000000000000000000^1024 ≤ 10368840860489337^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11051 100000 10368840860489337 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11051/100000 : ℝ)) (X := (10368840860489337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2939/20000 : ℝ) ^ (4265/1024 : ℝ) ≤ (16990212704948149/50000000000000000000 : ℝ) := by
    have hpowers : (2939/20000 : ℝ)^4265 ≤ (16990212704948149/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2939 : ℕ)^4265*50000000000000000000^1024 ≤ 16990212704948149^1024*20000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2939 20000 16990212704948149 50000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2939/20000 : ℝ)) (X := (16990212704948149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010368840860489337/50000000000000000000 : ℝ) ≤ (10000497859626639/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50010368840860489337/50000000000000000000 : ℝ)^1024 ≤ (10000497859626639/10000000000000000 : ℝ)^4265 := by
      have hnat : (50010368840860489337 : ℕ)^1024*10000000000000000^4265 ≤ 10000497859626639^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010368840860489337 50000000000000000000 10000497859626639 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000497859626639/10000000000000000 : ℝ)) (X := (50010368840860489337/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008869853254077127/20000000000000000000 : ℝ) ≤ (5000532309474327/5000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (20008869853254077127/20000000000000000000 : ℝ)^1024 ≤ (5000532309474327/5000000000000000 : ℝ)^4265 := by
      have hnat : (20008869853254077127 : ℕ)^1024*5000000000000000^4265 ≤ 5000532309474327^4265*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008869853254077127 20000000000000000000 5000532309474327 5000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000532309474327/5000000000000000 : ℝ)) (X := (20008869853254077127/20000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016990212704948149/25000000000000000000 : ℝ) ≤ (10001631378270669/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (25016990212704948149/25000000000000000000 : ℝ)^1024 ≤ (10001631378270669/10000000000000000 : ℝ)^4265 := by
      have hnat : (25016990212704948149 : ℕ)^1024*10000000000000000^4265 ≤ 10001631378270669^4265*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016990212704948149 25000000000000000000 10001631378270669 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001631378270669/10000000000000000 : ℝ)) (X := (25016990212704948149/25000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10368840860489337/100000000000000000000 : ℝ) ≤ ((18214643842972148493/18220000000000000000 : ℝ)+2*(113351864403/72880000000000 : ℝ)*(11051/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (18214643842972148493/18220000000000000000 : ℝ)+2*(113351864403/72880000000000 : ℝ)*(11051/100000 : ℝ)=(10000497859626639/10000000000000000 : ℝ) by norm_num, show 1+2*(10368840860489337/100000000000000000000 : ℝ)=(50010368840860489337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16990212704948149/50000000000000000000 : ℝ)+(10368840860489337/100000000000000000000 : ℝ) ≤ ((18214643842972148493/18220000000000000000 : ℝ)+(113351864403/72880000000000 : ℝ)*((2939/20000 : ℝ)+(11051/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (18214643842972148493/18220000000000000000 : ℝ)+(113351864403/72880000000000 : ℝ)*((2939/20000 : ℝ)+(11051/100000 : ℝ))=(5000532309474327/5000000000000000 : ℝ) by norm_num, show 1+(16990212704948149/50000000000000000000 : ℝ)+(10368840860489337/100000000000000000000 : ℝ)=(20008869853254077127/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16990212704948149/50000000000000000000 : ℝ) ≤ ((18214643842972148493/18220000000000000000 : ℝ)+2*(113351864403/72880000000000 : ℝ)*(2939/20000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (18214643842972148493/18220000000000000000 : ℝ)+2*(113351864403/72880000000000 : ℝ)*(2939/20000 : ℝ)=(10001631378270669/10000000000000000 : ℝ) by norm_num, show 1+2*(16990212704948149/50000000000000000000 : ℝ)=(25016990212704948149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18214643842972148493/18220000000000000000 : ℝ)*(X 1 0+X 2 0)+(113351864403/72880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (18214643842972148493/18220000000000000000 : ℝ)) (alpha := (113351864403/72880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18214643842972148493/18220000000000000000 : ℝ)*(X 0 1+X 2 1)+(113351864403/72880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (18214643842972148493/18220000000000000000 : ℝ)) (alpha := (113351864403/72880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18214643842972148493/18220000000000000000 : ℝ)*(X 0 2+X 1 2)+(113351864403/72880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (18214643842972148493/18220000000000000000 : ℝ)) (alpha := (113351864403/72880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075476691/10000000000 : ℝ)*X 0 0+(2707297401/5000000000 : ℝ)*X 0 1+(5243407841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349595811/10000000000 : ℝ)*X 1 0+(-13517051/62500000 : ℝ)*X 1 1+(131085187/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267479751/500000000 : ℝ)*X 2 0+(1310851941/2500000000 : ℝ)*X 2 1+(-1081364419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336117281/10000000000 : ℝ)*X 0 0+(1040671773/2500000000 : ℝ)*X 0 1+(2258200279/5000000000 : ℝ)*X 0 2+(4336117281/10000000000 : ℝ)*X 1 0+(1040671773/2500000000 : ℝ)*X 1 1+(2258200279/5000000000 : ℝ)*X 1 2+(4336117281/10000000000 : ℝ)*X 2 0+(1040671773/2500000000 : ℝ)*X 2 1+(2258200279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-518872427/2500000000 : ℝ)*X 0 0+(5244018987/10000000000 : ℝ)*X 0 1+(5413980189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305690259/10000000000 : ℝ)*X 1 0+(-249019511/1250000000 : ℝ)*X 1 1+(5413980189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305690259/10000000000 : ℝ)*X 2 0+(5413980189/10000000000 : ℝ)*X 2 1+(-249019511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2168071889/5000000000 : ℝ)*X 0 0+(2257568453/5000000000 : ℝ)*X 0 1+(4163956759/10000000000 : ℝ)*X 0 2+(2168071889/5000000000 : ℝ)*X 1 0+(2257568453/5000000000 : ℝ)*X 1 1+(4163956759/10000000000 : ℝ)*X 1 2+(2168071889/5000000000 : ℝ)*X 2 0+(2257568453/5000000000 : ℝ)*X 2 1+(4163956759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27228015609227274161637/3644000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1203027063/100000000000000 : ℝ)*(base19) + (486412359/100000000000000 : ℝ)*(base23) + (164588849/100000000000000 : ℝ)*(lower4) + (10810611/12500000000000 : ℝ)*(lower5) + (4334401322370451/100000000000000 : ℝ)*(major0) + (4334401322370451/100000000000000 : ℝ)*(major1) + (4334401322370451/100000000000000 : ℝ)*(major2) + (5841601756740381/100000000000000 : ℝ)*(sp0) + (1460405434544179/25000000000000 : ℝ)*(sp1) + (1168320579017333/20000000000000 : ℝ)*(sp2) + (1413582538502497/50000000000000 : ℝ)*(sp3) + (10592231699/50000000000000 : ℝ)*(sp4) + (4889926189/25000000000000 : ℝ)*(sp6) + (7188732511/50000000000000 : ℝ)*(sp7) + (22087339488047/781250000000 : ℝ)*(f.failure) + (5841622941203779/100000000000000 : ℝ)*(f.sum) + (9812408841253/3644000000000000000000000000 : ℝ)*base65 + (8192088399230369657/1822000000000000000000000000000000 : ℝ)*base68 + (780453355180369657/1822000000000000000000000000000000 : ℝ)*base70 + (14408195483066369657/1822000000000000000000000000000000 : ℝ)*base72 + (10379539736327/3644000000000000000000000000 : ℝ)*base74 + (27402450285405630343/1822000000000000000000000000000000 : ℝ)*base75 + (4383468991117630343/1822000000000000000000000000000000 : ℝ)*base77 + (1934025411737630343/1822000000000000000000000000000000 : ℝ)*base79 + (758720492853/728800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (29529/78125000000000000000 : ℝ)*base89 + (29529/78125000000000000000 : ℝ)*base91 + (29529/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1033948359119428886558910213/227750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200917119/25000000000000 : ℝ)*(base19) + (218224243/25000000000000 : ℝ)*(base23) + (92314343/100000000000000 : ℝ)*(upper3) + (15714823/50000000000000 : ℝ)*(lower4) + (46665709/50000000000000 : ℝ)*(upper5) + (2182809112526347/50000000000000 : ℝ)*(major0) + (2182809112526347/50000000000000 : ℝ)*(major1) + (2182809112526347/50000000000000 : ℝ)*(major2) + (1619541677/10000000000000 : ℝ)*(sp1) + (8701530193/50000000000000 : ℝ)*(sp2) + (735461892851267/12500000000000 : ℝ)*(sp4) + (588367814372489/10000000000000 : ℝ)*(sp5) + (2941838433426389/50000000000000 : ℝ)*(sp6) + (1423770577983637/50000000000000 : ℝ)*(sp7) + (1423770577983637/50000000000000 : ℝ)*(f.failure) + (735461892851267/12500000000000 : ℝ)*(f.sum) + (1209021235193/1822000000000000000000000000 : ℝ)*base65 + (11693537098516904929/911000000000000000000000000000000 : ℝ)*base68 + (7360761149250904929/911000000000000000000000000000000 : ℝ)*base70 + (11802448675352904929/911000000000000000000000000000000 : ℝ)*base72 + (9081701326713/1822000000000000000000000000 : ℝ)*base73 + (16989346173816904929/911000000000000000000000000000000 : ℝ)*base76 + (8966114165814904929/911000000000000000000000000000000 : ℝ)*base78 + (637030362029095071/911000000000000000000000000000000 : ℝ)*base79 + (8164148718107/1822000000000000000000000000 : ℝ)*base82 + (4083909/5000000000000000000000 : ℝ)*base89 + (4083909/5000000000000000000000 : ℝ)*base91 + (4083909/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1306_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_s7_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075489269/10000000000 : ℝ)*x 0 + (5414501491/10000000000 : ℝ)*x 1 + (5243492717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075489269/10000000000 : ℝ)^2133 ≤ (789423417179/6250000000000 : ℝ)^1621 := by
    have hnat : (2075489269 : ℕ)^2133*6250000000000^1621 ≤ 789423417179^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075489269 10000000000 789423417179 6250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414501491/10000000000 : ℝ)^2133 ≤ (2230343484999/5000000000000 : ℝ)^1621 := by
    have hnat : (5414501491 : ℕ)^2133*5000000000000^1621 ≤ 2230343484999^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414501491 10000000000 2230343484999 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243492717/10000000000 : ℝ)^2133 ≤ (2672647225513/6250000000000 : ℝ)^1621 := by
    have hnat : (5243492717 : ℕ)^2133*6250000000000^1621 ≤ 2672647225513^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243492717 10000000000 2672647225513 6250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075489269/10000000000 : ℝ), (5414501491/10000000000 : ℝ), (5243492717/10000000000 : ℝ)] ![(789423417179/6250000000000 : ℝ), (2230343484999/5000000000000 : ℝ), (2672647225513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075489269/10000000000 : ℝ)|^2133 ≤ (789423417179/6250000000000 : ℝ)^1621
        have hw : |(-2075489269/10000000000 : ℝ)|=(2075489269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414501491/10000000000 : ℝ)|^2133 ≤ (2230343484999/5000000000000 : ℝ)^1621
        have hw : |(5414501491/10000000000 : ℝ)|=(5414501491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243492717/10000000000 : ℝ)|^2133 ≤ (2672647225513/6250000000000 : ℝ)^1621
        have hw : |(5243492717/10000000000 : ℝ)|=(5243492717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349571191/10000000000 : ℝ)*x 0 + (-216264743/1000000000 : ℝ)*x 1 + (5243493289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349571191/10000000000 : ℝ)^2133 ≤ (43904326578561/100000000000000 : ℝ)^1621 := by
    have hnat : (5349571191 : ℕ)^2133*100000000000000^1621 ≤ 43904326578561^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349571191 10000000000 43904326578561 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216264743/1000000000 : ℝ)^2133 ≤ (13333311668589/100000000000000 : ℝ)^1621 := by
    have hnat : (216264743 : ℕ)^2133*100000000000000^1621 ≤ 13333311668589^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216264743 1000000000 13333311668589 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243493289/10000000000 : ℝ)^2133 ≤ (21381180873231/50000000000000 : ℝ)^1621 := by
    have hnat : (5243493289 : ℕ)^2133*50000000000000^1621 ≤ 21381180873231^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243493289 10000000000 21381180873231 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349571191/10000000000 : ℝ), (-216264743/1000000000 : ℝ), (5243493289/10000000000 : ℝ)] ![(43904326578561/100000000000000 : ℝ), (13333311668589/100000000000000 : ℝ), (21381180873231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349571191/10000000000 : ℝ)|^2133 ≤ (43904326578561/100000000000000 : ℝ)^1621
        have hw : |(5349571191/10000000000 : ℝ)|=(5349571191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216264743/1000000000 : ℝ)|^2133 ≤ (13333311668589/100000000000000 : ℝ)^1621
        have hw : |(-216264743/1000000000 : ℝ)|=(216264743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243493289/10000000000 : ℝ)|^2133 ≤ (21381180873231/50000000000000 : ℝ)^1621
        have hw : |(5243493289/10000000000 : ℝ)|=(5243493289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53495707/100000000 : ℝ)*x 0 + (5243493939/10000000000 : ℝ)*x 1 + (-2162647223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53495707/100000000 : ℝ)^2133 ≤ (21952160638049/50000000000000 : ℝ)^1621 := by
    have hnat : (53495707 : ℕ)^2133*50000000000000^1621 ≤ 21952160638049^1621*100000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53495707 100000000 21952160638049 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243493939/10000000000 : ℝ)^2133 ≤ (171049474887/400000000000 : ℝ)^1621 := by
    have hnat : (5243493939 : ℕ)^2133*400000000000^1621 ≤ 171049474887^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243493939 10000000000 171049474887 400000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162647223/10000000000 : ℝ)^2133 ≤ (83333187433/625000000000 : ℝ)^1621 := by
    have hnat : (2162647223 : ℕ)^2133*625000000000^1621 ≤ 83333187433^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162647223 10000000000 83333187433 625000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53495707/100000000 : ℝ), (5243493939/10000000000 : ℝ), (-2162647223/10000000000 : ℝ)] ![(21952160638049/50000000000000 : ℝ), (171049474887/400000000000 : ℝ), (83333187433/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53495707/100000000 : ℝ)|^2133 ≤ (21952160638049/50000000000000 : ℝ)^1621
        have hw : |(53495707/100000000 : ℝ)|=(53495707/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243493939/10000000000 : ℝ)|^2133 ≤ (171049474887/400000000000 : ℝ)^1621
        have hw : |(5243493939/10000000000 : ℝ)|=(5243493939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2162647223/10000000000 : ℝ)|^2133 ≤ (83333187433/625000000000 : ℝ)^1621
        have hw : |(-2162647223/10000000000 : ℝ)|=(2162647223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (867225069/2000000000 : ℝ)*x 0 + (4162869697/10000000000 : ℝ)*x 1 + (903242927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867225069/2000000000 : ℝ)^2133 ≤ (33302653564143/100000000000000 : ℝ)^1621 := by
    have hnat : (867225069 : ℕ)^2133*100000000000000^1621 ≤ 33302653564143^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867225069 2000000000 33302653564143 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162869697/10000000000 : ℝ)^2133 ≤ (31562860774779/100000000000000 : ℝ)^1621 := by
    have hnat : (4162869697 : ℕ)^2133*100000000000000^1621 ≤ 31562860774779^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162869697 10000000000 31562860774779 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903242927/2000000000 : ℝ)^2133 ≤ (3513448565607/10000000000000 : ℝ)^1621 := by
    have hnat : (903242927 : ℕ)^2133*10000000000000^1621 ≤ 3513448565607^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903242927 2000000000 3513448565607 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867225069/2000000000 : ℝ), (4162869697/10000000000 : ℝ), (903242927/2000000000 : ℝ)] ![(33302653564143/100000000000000 : ℝ), (31562860774779/100000000000000 : ℝ), (3513448565607/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867225069/2000000000 : ℝ)|^2133 ≤ (33302653564143/100000000000000 : ℝ)^1621
        have hw : |(867225069/2000000000 : ℝ)|=(867225069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162869697/10000000000 : ℝ)|^2133 ≤ (31562860774779/100000000000000 : ℝ)^1621
        have hw : |(4162869697/10000000000 : ℝ)|=(4162869697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903242927/2000000000 : ℝ)|^2133 ≤ (3513448565607/10000000000000 : ℝ)^1621
        have hw : |(903242927/2000000000 : ℝ)|=(903242927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075501479/10000000000 : ℝ)*x 0 + (5244103151/10000000000 : ℝ)*x 1 + (5413888173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075501479/10000000000 : ℝ)^2133 ≤ (157885905639/1250000000000 : ℝ)^1621 := by
    have hnat : (2075501479 : ℕ)^2133*1250000000000^1621 ≤ 157885905639^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075501479 10000000000 157885905639 1250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244103151/10000000000 : ℝ)^2133 ≤ (21384453212787/50000000000000 : ℝ)^1621 := by
    have hnat : (5244103151 : ℕ)^2133*50000000000000^1621 ≤ 21384453212787^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244103151 10000000000 21384453212787 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413888173/10000000000 : ℝ)^2133 ≤ (11150055279409/25000000000000 : ℝ)^1621 := by
    have hnat : (5413888173 : ℕ)^2133*25000000000000^1621 ≤ 11150055279409^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413888173 10000000000 11150055279409 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075501479/10000000000 : ℝ), (5244103151/10000000000 : ℝ), (5413888173/10000000000 : ℝ)] ![(157885905639/1250000000000 : ℝ), (21384453212787/50000000000000 : ℝ), (11150055279409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075501479/10000000000 : ℝ)|^2133 ≤ (157885905639/1250000000000 : ℝ)^1621
        have hw : |(-2075501479/10000000000 : ℝ)|=(2075501479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244103151/10000000000 : ℝ)|^2133 ≤ (21384453212787/50000000000000 : ℝ)^1621
        have hw : |(5244103151/10000000000 : ℝ)|=(5244103151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413888173/10000000000 : ℝ)|^2133 ≤ (11150055279409/25000000000000 : ℝ)^1621
        have hw : |(5413888173/10000000000 : ℝ)|=(5413888173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530571207/1000000000 : ℝ)*x 0 + (-99612627/500000000 : ℝ)*x 1 + (5413888181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530571207/1000000000 : ℝ)^2133 ≤ (43431292560603/100000000000000 : ℝ)^1621 := by
    have hnat : (530571207 : ℕ)^2133*100000000000000^1621 ≤ 43431292560603^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530571207 1000000000 43431292560603 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99612627/500000000 : ℝ)^2133 ≤ (5984243109051/50000000000000 : ℝ)^1621 := by
    have hnat : (99612627 : ℕ)^2133*50000000000000^1621 ≤ 5984243109051^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99612627 500000000 5984243109051 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413888181/10000000000 : ℝ)^2133 ≤ (44600221204357/100000000000000 : ℝ)^1621 := by
    have hnat : (5413888181 : ℕ)^2133*100000000000000^1621 ≤ 44600221204357^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413888181 10000000000 44600221204357 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530571207/1000000000 : ℝ), (-99612627/500000000 : ℝ), (5413888181/10000000000 : ℝ)] ![(43431292560603/100000000000000 : ℝ), (5984243109051/50000000000000 : ℝ), (44600221204357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530571207/1000000000 : ℝ)|^2133 ≤ (43431292560603/100000000000000 : ℝ)^1621
        have hw : |(530571207/1000000000 : ℝ)|=(530571207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99612627/500000000 : ℝ)|^2133 ≤ (5984243109051/50000000000000 : ℝ)^1621
        have hw : |(-99612627/500000000 : ℝ)|=(99612627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413888181/10000000000 : ℝ)|^2133 ≤ (44600221204357/100000000000000 : ℝ)^1621
        have hw : |(5413888181/10000000000 : ℝ)|=(5413888181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652856043/5000000000 : ℝ)*x 0 + (2706944083/5000000000 : ℝ)*x 1 + (-99612627/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652856043/5000000000 : ℝ)^2133 ≤ (43431292732943/100000000000000 : ℝ)^1621 := by
    have hnat : (2652856043 : ℕ)^2133*100000000000000^1621 ≤ 43431292732943^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652856043 5000000000 43431292732943 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706944083/5000000000 : ℝ)^2133 ≤ (22300110520877/50000000000000 : ℝ)^1621 := by
    have hnat : (2706944083 : ℕ)^2133*50000000000000^1621 ≤ 22300110520877^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706944083 5000000000 22300110520877 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99612627/500000000 : ℝ)^2133 ≤ (5984243109051/50000000000000 : ℝ)^1621 := by
    have hnat : (99612627 : ℕ)^2133*50000000000000^1621 ≤ 5984243109051^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99612627 500000000 5984243109051 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652856043/5000000000 : ℝ), (2706944083/5000000000 : ℝ), (-99612627/500000000 : ℝ)] ![(43431292732943/100000000000000 : ℝ), (22300110520877/50000000000000 : ℝ), (5984243109051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652856043/5000000000 : ℝ)|^2133 ≤ (43431292732943/100000000000000 : ℝ)^1621
        have hw : |(2652856043/5000000000 : ℝ)|=(2652856043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706944083/5000000000 : ℝ)|^2133 ≤ (22300110520877/50000000000000 : ℝ)^1621
        have hw : |(2706944083/5000000000 : ℝ)|=(2706944083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99612627/500000000 : ℝ)|^2133 ≤ (5984243109051/50000000000000 : ℝ)^1621
        have hw : |(-99612627/500000000 : ℝ)|=(99612627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s7_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4336150047/10000000000 : ℝ)*x 0 + (4514954069/10000000000 : ℝ)*x 1 + (208206899/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336150047/10000000000 : ℝ)^2133 ≤ (1332116128239/4000000000000 : ℝ)^1621 := by
    have hnat : (4336150047 : ℕ)^2133*4000000000000^1621 ≤ 1332116128239^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336150047 10000000000 1332116128239 4000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514954069/10000000000 : ℝ)^2133 ≤ (35121581984207/100000000000000 : ℝ)^1621 := by
    have hnat : (4514954069 : ℕ)^2133*100000000000000^1621 ≤ 35121581984207^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514954069 10000000000 35121581984207 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208206899/500000000 : ℝ)^2133 ≤ (6315102958559/20000000000000 : ℝ)^1621 := by
    have hnat : (208206899 : ℕ)^2133*20000000000000^1621 ≤ 6315102958559^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208206899 500000000 6315102958559 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336150047/10000000000 : ℝ), (4514954069/10000000000 : ℝ), (208206899/500000000 : ℝ)] ![(1332116128239/4000000000000 : ℝ), (35121581984207/100000000000000 : ℝ), (6315102958559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336150047/10000000000 : ℝ)|^2133 ≤ (1332116128239/4000000000000 : ℝ)^1621
        have hw : |(4336150047/10000000000 : ℝ)|=(4336150047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514954069/10000000000 : ℝ)|^2133 ≤ (35121581984207/100000000000000 : ℝ)^1621
        have hw : |(4514954069/10000000000 : ℝ)|=(4514954069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208206899/500000000 : ℝ)|^2133 ≤ (6315102958559/20000000000000 : ℝ)^1621
        have hw : |(208206899/500000000 : ℝ)|=(208206899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11063/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11061/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (10407976243262517/100000000000000000000 : ℝ) := by
    have hpowers : (11061/100000 : ℝ)^4265 ≤ (10407976243262517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11061 : ℕ)^4265*100000000000000000000^1024 ≤ 10407976243262517^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11061 100000 10407976243262517 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11061/100000 : ℝ)) (X := (10407976243262517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3671/25000 : ℝ) ^ (4265/1024 : ℝ) ≤ (105858150483017/312500000000000000 : ℝ) := by
    have hpowers : (3671/25000 : ℝ)^4265 ≤ (105858150483017/312500000000000000 : ℝ)^1024 := by
      have hnat : (3671 : ℕ)^4265*312500000000000000^1024 ≤ 105858150483017^1024*25000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3671 25000 105858150483017 312500000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3671/25000 : ℝ)) (X := (105858150483017/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010407976243262517/50000000000000000000 : ℝ) ≤ (250012493464061/250000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50010407976243262517/50000000000000000000 : ℝ)^1024 ≤ (250012493464061/250000000000000 : ℝ)^4265 := by
      have hnat : (50010407976243262517 : ℕ)^1024*250000000000000^4265 ≤ 250012493464061^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010407976243262517 50000000000000000000 250012493464061 250000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250012493464061/250000000000000 : ℝ)) (X := (50010407976243262517/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044282584397827957/100000000000000000000 : ℝ) ≤ (625066438656079/625000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (100044282584397827957/100000000000000000000 : ℝ)^1024 ≤ (625066438656079/625000000000000 : ℝ)^4265 := by
      have hnat : (100044282584397827957 : ℕ)^1024*625000000000000^4265 ≤ 625066438656079^4265*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044282584397827957 100000000000000000000 625066438656079 625000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625066438656079/625000000000000 : ℝ)) (X := (100044282584397827957/100000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (156355858150483017/156250000000000000 : ℝ) ≤ (1250203287304011/1250000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (156355858150483017/156250000000000000 : ℝ)^1024 ≤ (1250203287304011/1250000000000000 : ℝ)^4265 := by
      have hnat : (156355858150483017 : ℕ)^1024*1250000000000000^4265 ≤ 1250203287304011^4265*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156355858150483017 156250000000000000 1250203287304011 1250000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250203287304011/1250000000000000 : ℝ)) (X := (156355858150483017/156250000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10407976243262517/100000000000000000000 : ℝ) ≤ ((4527418709261692949/4528750000000000000 : ℝ)+2*(70409991853/45287500000000 : ℝ)*(11061/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (4527418709261692949/4528750000000000000 : ℝ)+2*(70409991853/45287500000000 : ℝ)*(11061/100000 : ℝ)=(250012493464061/250000000000000 : ℝ) by norm_num, show 1+2*(10407976243262517/100000000000000000000 : ℝ)=(50010407976243262517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(105858150483017/312500000000000000 : ℝ)+(10407976243262517/100000000000000000000 : ℝ) ≤ ((4527418709261692949/4528750000000000000 : ℝ)+(70409991853/45287500000000 : ℝ)*((3671/25000 : ℝ)+(11061/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (4527418709261692949/4528750000000000000 : ℝ)+(70409991853/45287500000000 : ℝ)*((3671/25000 : ℝ)+(11061/100000 : ℝ))=(625066438656079/625000000000000 : ℝ) by norm_num, show 1+(105858150483017/312500000000000000 : ℝ)+(10407976243262517/100000000000000000000 : ℝ)=(100044282584397827957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(105858150483017/312500000000000000 : ℝ) ≤ ((4527418709261692949/4528750000000000000 : ℝ)+2*(70409991853/45287500000000 : ℝ)*(3671/25000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (4527418709261692949/4528750000000000000 : ℝ)+2*(70409991853/45287500000000 : ℝ)*(3671/25000 : ℝ)=(1250203287304011/1250000000000000 : ℝ) by norm_num, show 1+2*(105858150483017/312500000000000000 : ℝ)=(156355858150483017/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4527418709261692949/4528750000000000000 : ℝ)*(X 1 0+X 2 0)+(70409991853/45287500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (4527418709261692949/4528750000000000000 : ℝ)) (alpha := (70409991853/45287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4527418709261692949/4528750000000000000 : ℝ)*(X 0 1+X 2 1)+(70409991853/45287500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (4527418709261692949/4528750000000000000 : ℝ)) (alpha := (70409991853/45287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4527418709261692949/4528750000000000000 : ℝ)*(X 0 2+X 1 2)+(70409991853/45287500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (4527418709261692949/4528750000000000000 : ℝ)) (alpha := (70409991853/45287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075489269/10000000000 : ℝ)*X 0 0+(5414501491/10000000000 : ℝ)*X 0 1+(5243492717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349571191/10000000000 : ℝ)*X 1 0+(-216264743/1000000000 : ℝ)*X 1 1+(5243493289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53495707/100000000 : ℝ)*X 2 0+(5243493939/10000000000 : ℝ)*X 2 1+(-2162647223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867225069/2000000000 : ℝ)*X 0 0+(4162869697/10000000000 : ℝ)*X 0 1+(903242927/2000000000 : ℝ)*X 0 2+(867225069/2000000000 : ℝ)*X 1 0+(4162869697/10000000000 : ℝ)*X 1 1+(903242927/2000000000 : ℝ)*X 1 2+(867225069/2000000000 : ℝ)*X 2 0+(4162869697/10000000000 : ℝ)*X 2 1+(903242927/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2075501479/10000000000 : ℝ)*X 0 0+(5244103151/10000000000 : ℝ)*X 0 1+(5413888173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530571207/1000000000 : ℝ)*X 1 0+(-99612627/500000000 : ℝ)*X 1 1+(5413888181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652856043/5000000000 : ℝ)*X 2 0+(2706944083/5000000000 : ℝ)*X 2 1+(-99612627/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336150047/10000000000 : ℝ)*X 0 0+(4514954069/10000000000 : ℝ)*X 0 1+(208206899/500000000 : ℝ)*X 0 2+(4336150047/10000000000 : ℝ)*X 1 0+(4514954069/10000000000 : ℝ)*X 1 1+(208206899/500000000 : ℝ)*X 1 2+(4336150047/10000000000 : ℝ)*X 2 0+(4514954069/10000000000 : ℝ)*X 2 1+(208206899/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (339876979863670289575526649/113218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1651975391/100000000000000 : ℝ)*(base19) + (801981499/100000000000000 : ℝ)*(base23) + (41896543/25000000000000 : ℝ)*(lower2) + (192703441/50000000000000 : ℝ)*(upper3) + (305192487/100000000000000 : ℝ)*(upper5) + (2169470878891233/50000000000000 : ℝ)*(major0) + (2169470878891233/50000000000000 : ℝ)*(major1) + (2169470878891233/50000000000000 : ℝ)*(major2) + (5847699266709171/100000000000000 : ℝ)*(sp0) + (5847740740718681/100000000000000 : ℝ)*(sp1) + (1461935397678143/25000000000000 : ℝ)*(sp2) + (1415059023530603/50000000000000 : ℝ)*(sp3) + (43125984901/100000000000000 : ℝ)*(sp4) + (22975744659/100000000000000 : ℝ)*(sp7) + (1415070511402933/50000000000000 : ℝ)*(f.failure) + (730967799086759/12500000000000 : ℝ)*(f.sum) + (124535333172509/18115000000000000000000000000 : ℝ)*base65 + (85257988557978617/226437500000000000000000000000000 : ℝ)*base67 + (682986264694208883/226437500000000000000000000000000 : ℝ)*base70 + (1193829178400041117/226437500000000000000000000000000 : ℝ)*base71 + (4488283226339/18115000000000000000000000000 : ℝ)*base73 + (606982139442146383/226437500000000000000000000000000 : ℝ)*base76 + (3281646029964603617/226437500000000000000000000000000 : ℝ)*base77 + (2889074117319978617/226437500000000000000000000000000 : ℝ)*base79 + (45956462195237/9057500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (33476581/5000000000000000000000 : ℝ)*base89 + (33476581/5000000000000000000000 : ℝ)*base91 + (33476581/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931008076907776600925681793/226437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (690542497/100000000000000 : ℝ)*(base19) + (6120413/800000000000 : ℝ)*(base23) + (29910101/12500000000000 : ℝ)*(lower1) + (82121539/100000000000000 : ℝ)*(upper3) + (654081/2500000000000 : ℝ)*(lower4) + (89891563/100000000000000 : ℝ)*(upper5) + (4370138152329619/100000000000000 : ℝ)*(major0) + (4370138152329619/100000000000000 : ℝ)*(major1) + (4370138152329619/100000000000000 : ℝ)*(major2) + (449796689/50000000000000 : ℝ)*(sp2) + (47118294560391/800000000000 : ℝ)*(sp4) + (2944893064753189/50000000000000 : ℝ)*(sp5) + (184055786106371/3125000000000 : ℝ)*(sp6) + (114019573902353/4000000000000 : ℝ)*(sp7) + (114019573902353/4000000000000 : ℝ)*(f.failure) + (47118294560391/800000000000 : ℝ)*(f.sum) + (31169058621347/9057500000000000000000000000 : ℝ)*base66 + (11787020820776893569/452875000000000000000000000000000 : ℝ)*base68 + (973006559648768569/452875000000000000000000000000000 : ℝ)*base70 + (40472070418183768569/452875000000000000000000000000000 : ℝ)*base72 + (65774173250519/18115000000000000000000000000 : ℝ)*base74 + (30015480214752606431/452875000000000000000000000000000 : ℝ)*base75 + (2361660565088268569/452875000000000000000000000000000 : ℝ)*base78 + (4825607320662231431/452875000000000000000000000000000 : ℝ)*base79 + (54208808644217/9057500000000000000000000000 : ℝ)*base82 + (900479/400000000000000000000 : ℝ)*base90 + (900479/400000000000000000000 : ℝ)*base92 + (900479/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1306_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_box_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-476328217/2500000000 : ℝ)*x 0 + (2695717893/5000000000 : ℝ)*x 1 + (5391435983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476328217/2500000000 : ℝ)^2133 ≤ (5643005648567/50000000000000 : ℝ)^1621 := by
    have hnat : (476328217 : ℕ)^2133*50000000000000^1621 ≤ 5643005648567^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476328217 2500000000 5643005648567 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695717893/5000000000 : ℝ)^2133 ≤ (11089248319067/25000000000000 : ℝ)^1621 := by
    have hnat : (2695717893 : ℕ)^2133*25000000000000^1621 ≤ 11089248319067^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695717893 5000000000 11089248319067 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391435983/10000000000 : ℝ)^2133 ≤ (22178497704489/50000000000000 : ℝ)^1621 := by
    have hnat : (5391435983 : ℕ)^2133*50000000000000^1621 ≤ 22178497704489^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391435983 10000000000 22178497704489 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-476328217/2500000000 : ℝ), (2695717893/5000000000 : ℝ), (5391435983/10000000000 : ℝ)] ![(5643005648567/50000000000000 : ℝ), (11089248319067/25000000000000 : ℝ), (22178497704489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-476328217/2500000000 : ℝ)|^2133 ≤ (5643005648567/50000000000000 : ℝ)^1621
        have hw : |(-476328217/2500000000 : ℝ)|=(476328217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695717893/5000000000 : ℝ)|^2133 ≤ (11089248319067/25000000000000 : ℝ)^1621
        have hw : |(2695717893/5000000000 : ℝ)|=(2695717893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391435983/10000000000 : ℝ)|^2133 ≤ (22178497704489/50000000000000 : ℝ)^1621
        have hw : |(5391435983/10000000000 : ℝ)|=(5391435983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284613437/10000000000 : ℝ)*x 0 + (-1025737429/5000000000 : ℝ)*x 1 + (2695718253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284613437/10000000000 : ℝ)^2133 ≤ (1350130510511/3125000000000 : ℝ)^1621 := by
    have hnat : (5284613437 : ℕ)^2133*3125000000000^1621 ≤ 1350130510511^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284613437 10000000000 1350130510511 3125000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025737429/5000000000 : ℝ)^2133 ≤ (2487764515879/20000000000000 : ℝ)^1621 := by
    have hnat : (1025737429 : ℕ)^2133*20000000000000^1621 ≤ 2487764515879^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025737429 5000000000 2487764515879 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695718253/5000000000 : ℝ)^2133 ≤ (44357001070943/100000000000000 : ℝ)^1621 := by
    have hnat : (2695718253 : ℕ)^2133*100000000000000^1621 ≤ 44357001070943^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695718253 5000000000 44357001070943 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284613437/10000000000 : ℝ), (-1025737429/5000000000 : ℝ), (2695718253/5000000000 : ℝ)] ![(1350130510511/3125000000000 : ℝ), (2487764515879/20000000000000 : ℝ), (44357001070943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284613437/10000000000 : ℝ)|^2133 ≤ (1350130510511/3125000000000 : ℝ)^1621
        have hw : |(5284613437/10000000000 : ℝ)|=(5284613437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025737429/5000000000 : ℝ)|^2133 ≤ (2487764515879/20000000000000 : ℝ)^1621
        have hw : |(-1025737429/5000000000 : ℝ)|=(1025737429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695718253/5000000000 : ℝ)|^2133 ≤ (44357001070943/100000000000000 : ℝ)^1621
        have hw : |(2695718253/5000000000 : ℝ)|=(2695718253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321153503/2500000000 : ℝ)*x 0 + (5391435959/10000000000 : ℝ)*x 1 + (-256434353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321153503/2500000000 : ℝ)^2133 ≤ (21602091261021/50000000000000 : ℝ)^1621 := by
    have hnat : (1321153503 : ℕ)^2133*50000000000000^1621 ≤ 21602091261021^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321153503 2500000000 21602091261021 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391435959/10000000000 : ℝ)^2133 ≤ (8871399029831/20000000000000 : ℝ)^1621 := by
    have hnat : (5391435959 : ℕ)^2133*20000000000000^1621 ≤ 8871399029831^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391435959 10000000000 8871399029831 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256434353/1250000000 : ℝ)^2133 ≤ (12438822308127/100000000000000 : ℝ)^1621 := by
    have hnat : (256434353 : ℕ)^2133*100000000000000^1621 ≤ 12438822308127^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256434353 1250000000 12438822308127 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321153503/2500000000 : ℝ), (5391435959/10000000000 : ℝ), (-256434353/1250000000 : ℝ)] ![(21602091261021/50000000000000 : ℝ), (8871399029831/20000000000000 : ℝ), (12438822308127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321153503/2500000000 : ℝ)|^2133 ≤ (21602091261021/50000000000000 : ℝ)^1621
        have hw : |(1321153503/2500000000 : ℝ)|=(1321153503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391435959/10000000000 : ℝ)|^2133 ≤ (8871399029831/20000000000000 : ℝ)^1621
        have hw : |(5391435959/10000000000 : ℝ)|=(5391435959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256434353/1250000000 : ℝ)|^2133 ≤ (12438822308127/100000000000000 : ℝ)^1621
        have hw : |(-256434353/1250000000 : ℝ)|=(256434353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (897038281/2000000000 : ℝ)*x 0 + (1066390597/2500000000 : ℝ)*x 1 + (4265562417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897038281/2000000000 : ℝ)^2133 ≤ (6963450037341/20000000000000 : ℝ)^1621 := by
    have hnat : (897038281 : ℕ)^2133*20000000000000^1621 ≤ 6963450037341^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897038281 2000000000 6963450037341 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066390597/2500000000 : ℝ)^2133 ≤ (2036960921953/6250000000000 : ℝ)^1621 := by
    have hnat : (1066390597 : ℕ)^2133*6250000000000^1621 ≤ 2036960921953^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066390597 2500000000 2036960921953 6250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4265562417/10000000000 : ℝ)^2133 ≤ (32591375042811/100000000000000 : ℝ)^1621 := by
    have hnat : (4265562417 : ℕ)^2133*100000000000000^1621 ≤ 32591375042811^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265562417 10000000000 32591375042811 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897038281/2000000000 : ℝ), (1066390597/2500000000 : ℝ), (4265562417/10000000000 : ℝ)] ![(6963450037341/20000000000000 : ℝ), (2036960921953/6250000000000 : ℝ), (32591375042811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897038281/2000000000 : ℝ)|^2133 ≤ (6963450037341/20000000000000 : ℝ)^1621
        have hw : |(897038281/2000000000 : ℝ)|=(897038281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1066390597/2500000000 : ℝ)|^2133 ≤ (2036960921953/6250000000000 : ℝ)^1621
        have hw : |(1066390597/2500000000 : ℝ)|=(1066390597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4265562417/10000000000 : ℝ)|^2133 ≤ (32591375042811/100000000000000 : ℝ)^1621
        have hw : |(4265562417/10000000000 : ℝ)|=(4265562417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1124211833/5000000000 : ℝ)*x 0 + (329004001/625000000 : ℝ)*x 1 + (5264064519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124211833/5000000000 : ℝ)^2133 ≤ (7016750050129/50000000000000 : ℝ)^1621 := by
    have hnat : (1124211833 : ℕ)^2133*50000000000000^1621 ≤ 7016750050129^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124211833 5000000000 7016750050129 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329004001/625000000 : ℝ)^2133 ≤ (42983247241227/100000000000000 : ℝ)^1621 := by
    have hnat : (329004001 : ℕ)^2133*100000000000000^1621 ≤ 42983247241227^1621*625000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329004001 625000000 42983247241227 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264064519/10000000000 : ℝ)^2133 ≤ (42983252645707/100000000000000 : ℝ)^1621 := by
    have hnat : (5264064519 : ℕ)^2133*100000000000000^1621 ≤ 42983252645707^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264064519 10000000000 42983252645707 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1124211833/5000000000 : ℝ), (329004001/625000000 : ℝ), (5264064519/10000000000 : ℝ)] ![(7016750050129/50000000000000 : ℝ), (42983247241227/100000000000000 : ℝ), (42983252645707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1124211833/5000000000 : ℝ)|^2133 ≤ (7016750050129/50000000000000 : ℝ)^1621
        have hw : |(-1124211833/5000000000 : ℝ)|=(1124211833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329004001/625000000 : ℝ)|^2133 ≤ (42983247241227/100000000000000 : ℝ)^1621
        have hw : |(329004001/625000000 : ℝ)|=(329004001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264064519/10000000000 : ℝ)|^2133 ≤ (42983252645707/100000000000000 : ℝ)^1621
        have hw : |(5264064519/10000000000 : ℝ)|=(5264064519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2687107321/5000000000 : ℝ)*x 0 + (-525580849/2500000000 : ℝ)*x 1 + (658008047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687107321/5000000000 : ℝ)^2133 ≤ (22085326183859/50000000000000 : ℝ)^1621 := by
    have hnat : (2687107321 : ℕ)^2133*50000000000000^1621 ≤ 22085326183859^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687107321 5000000000 22085326183859 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525580849/2500000000 : ℝ)^2133 ≤ (401440515929/3125000000000 : ℝ)^1621 := by
    have hnat : (525580849 : ℕ)^2133*3125000000000^1621 ≤ 401440515929^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525580849 2500000000 401440515929 3125000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658008047/1250000000 : ℝ)^2133 ≤ (10745812777311/25000000000000 : ℝ)^1621 := by
    have hnat : (658008047 : ℕ)^2133*25000000000000^1621 ≤ 10745812777311^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658008047 1250000000 10745812777311 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687107321/5000000000 : ℝ), (-525580849/2500000000 : ℝ), (658008047/1250000000 : ℝ)] ![(22085326183859/50000000000000 : ℝ), (401440515929/3125000000000 : ℝ), (10745812777311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687107321/5000000000 : ℝ)|^2133 ≤ (22085326183859/50000000000000 : ℝ)^1621
        have hw : |(2687107321/5000000000 : ℝ)|=(2687107321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525580849/2500000000 : ℝ)|^2133 ≤ (401440515929/3125000000000 : ℝ)^1621
        have hw : |(-525580849/2500000000 : ℝ)|=(525580849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658008047/1250000000 : ℝ)|^2133 ≤ (10745812777311/25000000000000 : ℝ)^1621
        have hw : |(658008047/1250000000 : ℝ)|=(658008047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671776849/1250000000 : ℝ)*x 0 + (210562567/400000000 : ℝ)*x 1 + (-2102323463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671776849/1250000000 : ℝ)^2133 ≤ (2760665874373/6250000000000 : ℝ)^1621 := by
    have hnat : (671776849 : ℕ)^2133*6250000000000^1621 ≤ 2760665874373^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671776849 1250000000 2760665874373 6250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210562567/400000000 : ℝ)^2133 ≤ (42983248949601/100000000000000 : ℝ)^1621 := by
    have hnat : (210562567 : ℕ)^2133*100000000000000^1621 ≤ 42983248949601^1621*400000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210562567 400000000 42983248949601 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102323463/10000000000 : ℝ)^2133 ≤ (12846097048437/100000000000000 : ℝ)^1621 := by
    have hnat : (2102323463 : ℕ)^2133*100000000000000^1621 ≤ 12846097048437^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102323463 10000000000 12846097048437 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671776849/1250000000 : ℝ), (210562567/400000000 : ℝ), (-2102323463/10000000000 : ℝ)] ![(2760665874373/6250000000000 : ℝ), (42983248949601/100000000000000 : ℝ), (12846097048437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671776849/1250000000 : ℝ)|^2133 ≤ (2760665874373/6250000000000 : ℝ)^1621
        have hw : |(671776849/1250000000 : ℝ)|=(671776849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210562567/400000000 : ℝ)|^2133 ≤ (42983248949601/100000000000000 : ℝ)^1621
        have hw : |(210562567/400000000 : ℝ)|=(210562567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102323463/10000000000 : ℝ)|^2133 ≤ (12846097048437/100000000000000 : ℝ)^1621
        have hw : |(-2102323463/10000000000 : ℝ)|=(2102323463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1046546283/2500000000 : ℝ)*x 0 + (220750537/500000000 : ℝ)*x 1 + (4415010633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046546283/2500000000 : ℝ)^2133 ≤ (15897839879197/50000000000000 : ℝ)^1621 := by
    have hnat : (1046546283 : ℕ)^2133*50000000000000^1621 ≤ 15897839879197^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046546283 2500000000 15897839879197 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220750537/500000000 : ℝ)^2133 ≤ (34102160653753/100000000000000 : ℝ)^1621 := by
    have hnat : (220750537 : ℕ)^2133*100000000000000^1621 ≤ 34102160653753^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220750537 500000000 34102160653753 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415010633/10000000000 : ℝ)^2133 ≤ (34102159566221/100000000000000 : ℝ)^1621 := by
    have hnat : (4415010633 : ℕ)^2133*100000000000000^1621 ≤ 34102159566221^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415010633 10000000000 34102159566221 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046546283/2500000000 : ℝ), (220750537/500000000 : ℝ), (4415010633/10000000000 : ℝ)] ![(15897839879197/50000000000000 : ℝ), (34102160653753/100000000000000 : ℝ), (34102159566221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046546283/2500000000 : ℝ)|^2133 ≤ (15897839879197/50000000000000 : ℝ)^1621
        have hw : |(1046546283/2500000000 : ℝ)|=(1046546283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220750537/500000000 : ℝ)|^2133 ≤ (34102160653753/100000000000000 : ℝ)^1621
        have hw : |(220750537/500000000 : ℝ)|=(220750537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415010633/10000000000 : ℝ)|^2133 ≤ (34102159566221/100000000000000 : ℝ)^1621
        have hw : |(4415010633/10000000000 : ℝ)|=(4415010633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_8 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088235341/5000000000 : ℝ)*x 0 + (161767231/312500000 : ℝ)*x 1 + (2702734857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088235341/5000000000 : ℝ)^2133 ≤ (13445567241529/100000000000000 : ℝ)^1621 := by
    have hnat : (1088235341 : ℕ)^2133*100000000000000^1621 ≤ 13445567241529^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088235341 5000000000 13445567241529 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161767231/312500000 : ℝ)^2133 ≤ (8409089323809/20000000000000 : ℝ)^1621 := by
    have hnat : (161767231 : ℕ)^2133*20000000000000^1621 ≤ 8409089323809^1621*312500000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161767231 312500000 8409089323809 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702734857/5000000000 : ℝ)^2133 ≤ (22254493059407/50000000000000 : ℝ)^1621 := by
    have hnat : (2702734857 : ℕ)^2133*50000000000000^1621 ≤ 22254493059407^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702734857 5000000000 22254493059407 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088235341/5000000000 : ℝ), (161767231/312500000 : ℝ), (2702734857/5000000000 : ℝ)] ![(13445567241529/100000000000000 : ℝ), (8409089323809/20000000000000 : ℝ), (22254493059407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088235341/5000000000 : ℝ)|^2133 ≤ (13445567241529/100000000000000 : ℝ)^1621
        have hw : |(-1088235341/5000000000 : ℝ)|=(1088235341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161767231/312500000 : ℝ)|^2133 ≤ (8409089323809/20000000000000 : ℝ)^1621
        have hw : |(161767231/312500000 : ℝ)|=(161767231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702734857/5000000000 : ℝ)|^2133 ≤ (22254493059407/50000000000000 : ℝ)^1621
        have hw : |(2702734857/5000000000 : ℝ)|=(2702734857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_9 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637368139/5000000000 : ℝ)*x 0 + (-2045737571/10000000000 : ℝ)*x 1 + (5405469159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637368139/5000000000 : ℝ)^2133 ≤ (43097951975781/100000000000000 : ℝ)^1621 := by
    have hnat : (2637368139 : ℕ)^2133*100000000000000^1621 ≤ 43097951975781^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637368139 5000000000 43097951975781 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045737571/10000000000 : ℝ)^2133 ≤ (1549133487573/12500000000000 : ℝ)^1621 := by
    have hnat : (2045737571 : ℕ)^2133*12500000000000^1621 ≤ 1549133487573^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045737571 10000000000 1549133487573 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405469159/10000000000 : ℝ)^2133 ≤ (44508980105483/100000000000000 : ℝ)^1621 := by
    have hnat : (5405469159 : ℕ)^2133*100000000000000^1621 ≤ 44508980105483^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405469159 10000000000 44508980105483 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637368139/5000000000 : ℝ), (-2045737571/10000000000 : ℝ), (5405469159/10000000000 : ℝ)] ![(43097951975781/100000000000000 : ℝ), (1549133487573/12500000000000 : ℝ), (44508980105483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637368139/5000000000 : ℝ)|^2133 ≤ (43097951975781/100000000000000 : ℝ)^1621
        have hw : |(2637368139/5000000000 : ℝ)|=(2637368139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045737571/10000000000 : ℝ)|^2133 ≤ (1549133487573/12500000000000 : ℝ)^1621
        have hw : |(-2045737571/10000000000 : ℝ)|=(2045737571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405469159/10000000000 : ℝ)|^2133 ≤ (44508980105483/100000000000000 : ℝ)^1621
        have hw : |(5405469159/10000000000 : ℝ)|=(5405469159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_10 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1318683849/2500000000 : ℝ)*x 0 + (2702735189/5000000000 : ℝ)*x 1 + (-127858569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318683849/2500000000 : ℝ)^2133 ≤ (1723917699723/4000000000000 : ℝ)^1621 := by
    have hnat : (1318683849 : ℕ)^2133*4000000000000^1621 ≤ 1723917699723^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318683849 2500000000 1723917699723 4000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702735189/5000000000 : ℝ)^2133 ≤ (44508993313141/100000000000000 : ℝ)^1621 := by
    have hnat : (2702735189 : ℕ)^2133*100000000000000^1621 ≤ 44508993313141^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702735189 5000000000 44508993313141 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127858569/625000000 : ℝ)^2133 ≤ (6196532088961/50000000000000 : ℝ)^1621 := by
    have hnat : (127858569 : ℕ)^2133*50000000000000^1621 ≤ 6196532088961^1621*625000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127858569 625000000 6196532088961 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318683849/2500000000 : ℝ), (2702735189/5000000000 : ℝ), (-127858569/625000000 : ℝ)] ![(1723917699723/4000000000000 : ℝ), (44508993313141/100000000000000 : ℝ), (6196532088961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318683849/2500000000 : ℝ)|^2133 ≤ (1723917699723/4000000000000 : ℝ)^1621
        have hw : |(1318683849/2500000000 : ℝ)|=(1318683849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702735189/5000000000 : ℝ)|^2133 ≤ (44508993313141/100000000000000 : ℝ)^1621
        have hw : |(2702735189/5000000000 : ℝ)|=(2702735189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127858569/625000000 : ℝ)|^2133 ≤ (6196532088961/50000000000000 : ℝ)^1621
        have hw : |(-127858569/625000000 : ℝ)|=(127858569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_11 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4517574923/10000000000 : ℝ)*x 0 + (4249082663/10000000000 : ℝ)*x 1 + (4249083407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4517574923/10000000000 : ℝ)^2133 ≤ (8787102849883/25000000000000 : ℝ)^1621 := by
    have hnat : (4517574923 : ℕ)^2133*25000000000000^1621 ≤ 8787102849883^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517574923 10000000000 8787102849883 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249082663/10000000000 : ℝ)^2133 ≤ (32425790554129/100000000000000 : ℝ)^1621 := by
    have hnat : (4249082663 : ℕ)^2133*100000000000000^1621 ≤ 32425790554129^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249082663 10000000000 32425790554129 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249083407/10000000000 : ℝ)^2133 ≤ (6485159605017/20000000000000 : ℝ)^1621 := by
    have hnat : (4249083407 : ℕ)^2133*20000000000000^1621 ≤ 6485159605017^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249083407 10000000000 6485159605017 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4517574923/10000000000 : ℝ), (4249082663/10000000000 : ℝ), (4249083407/10000000000 : ℝ)] ![(8787102849883/25000000000000 : ℝ), (32425790554129/100000000000000 : ℝ), (6485159605017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4517574923/10000000000 : ℝ)|^2133 ≤ (8787102849883/25000000000000 : ℝ)^1621
        have hw : |(4517574923/10000000000 : ℝ)|=(4517574923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249082663/10000000000 : ℝ)|^2133 ≤ (32425790554129/100000000000000 : ℝ)^1621
        have hw : |(4249082663/10000000000 : ℝ)|=(4249082663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249083407/10000000000 : ℝ)|^2133 ≤ (6485159605017/20000000000000 : ℝ)^1621
        have hw : |(4249083407/10000000000 : ℝ)|=(4249083407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_12 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977675239/10000000000 : ℝ)*x 0 + (2738329667/5000000000 : ℝ)*x 1 + (5253027161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977675239/10000000000 : ℝ)^2133 ≤ (5926692911339/50000000000000 : ℝ)^1621 := by
    have hnat : (1977675239 : ℕ)^2133*50000000000000^1621 ≤ 5926692911339^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977675239 10000000000 5926692911339 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738329667/5000000000 : ℝ)^2133 ≤ (22640956518437/50000000000000 : ℝ)^1621 := by
    have hnat : (2738329667 : ℕ)^2133*50000000000000^1621 ≤ 22640956518437^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738329667 5000000000 22640956518437 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253027161/10000000000 : ℝ)^2133 ≤ (4286470112167/10000000000000 : ℝ)^1621 := by
    have hnat : (5253027161 : ℕ)^2133*10000000000000^1621 ≤ 4286470112167^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253027161 10000000000 4286470112167 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977675239/10000000000 : ℝ), (2738329667/5000000000 : ℝ), (5253027161/10000000000 : ℝ)] ![(5926692911339/50000000000000 : ℝ), (22640956518437/50000000000000 : ℝ), (4286470112167/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977675239/10000000000 : ℝ)|^2133 ≤ (5926692911339/50000000000000 : ℝ)^1621
        have hw : |(-1977675239/10000000000 : ℝ)|=(1977675239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738329667/5000000000 : ℝ)|^2133 ≤ (22640956518437/50000000000000 : ℝ)^1621
        have hw : |(2738329667/5000000000 : ℝ)|=(2738329667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253027161/10000000000 : ℝ)|^2133 ≤ (4286470112167/10000000000000 : ℝ)^1621
        have hw : |(5253027161/10000000000 : ℝ)|=(5253027161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_13 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1345494013/2500000000 : ℝ)*x 0 + (-42132483/200000000 : ℝ)*x 1 + (164157099/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345494013/2500000000 : ℝ)^2133 ≤ (44254611179/100000000000 : ℝ)^1621 := by
    have hnat : (1345494013 : ℕ)^2133*100000000000^1621 ≤ 44254611179^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345494013 2500000000 44254611179 100000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42132483/200000000 : ℝ)^2133 ≤ (644034380279/5000000000000 : ℝ)^1621 := by
    have hnat : (42132483 : ℕ)^2133*5000000000000^1621 ≤ 644034380279^1621*200000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42132483 200000000 644034380279 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164157099/312500000 : ℝ)^2133 ≤ (42864701196831/100000000000000 : ℝ)^1621 := by
    have hnat : (164157099 : ℕ)^2133*100000000000000^1621 ≤ 42864701196831^1621*312500000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164157099 312500000 42864701196831 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345494013/2500000000 : ℝ), (-42132483/200000000 : ℝ), (164157099/312500000 : ℝ)] ![(44254611179/100000000000 : ℝ), (644034380279/5000000000000 : ℝ), (42864701196831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345494013/2500000000 : ℝ)|^2133 ≤ (44254611179/100000000000 : ℝ)^1621
        have hw : |(1345494013/2500000000 : ℝ)|=(1345494013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42132483/200000000 : ℝ)|^2133 ≤ (644034380279/5000000000000 : ℝ)^1621
        have hw : |(-42132483/200000000 : ℝ)|=(42132483/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164157099/312500000 : ℝ)|^2133 ≤ (42864701196831/100000000000000 : ℝ)^1621
        have hw : |(164157099/312500000 : ℝ)|=(164157099/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_14 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1345494013/2500000000 : ℝ)*x 0 + (5253027167/10000000000 : ℝ)*x 1 + (-263328019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345494013/2500000000 : ℝ)^2133 ≤ (44254611179/100000000000 : ℝ)^1621 := by
    have hnat : (1345494013 : ℕ)^2133*100000000000^1621 ≤ 44254611179^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345494013 2500000000 44254611179 100000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253027167/10000000000 : ℝ)^2133 ≤ (21432350593047/50000000000000 : ℝ)^1621 := by
    have hnat : (5253027167 : ℕ)^2133*50000000000000^1621 ≤ 21432350593047^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253027167 10000000000 21432350593047 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263328019/1250000000 : ℝ)^2133 ≤ (1610085952709/12500000000000 : ℝ)^1621 := by
    have hnat : (263328019 : ℕ)^2133*12500000000000^1621 ≤ 1610085952709^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263328019 1250000000 1610085952709 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345494013/2500000000 : ℝ), (5253027167/10000000000 : ℝ), (-263328019/1250000000 : ℝ)] ![(44254611179/100000000000 : ℝ), (21432350593047/50000000000000 : ℝ), (1610085952709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345494013/2500000000 : ℝ)|^2133 ≤ (44254611179/100000000000 : ℝ)^1621
        have hw : |(1345494013/2500000000 : ℝ)|=(1345494013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253027167/10000000000 : ℝ)|^2133 ≤ (21432350593047/50000000000000 : ℝ)^1621
        have hw : |(5253027167/10000000000 : ℝ)|=(5253027167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263328019/1250000000 : ℝ)|^2133 ≤ (1610085952709/12500000000000 : ℝ)^1621
        have hw : |(-263328019/1250000000 : ℝ)|=(263328019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_box_15 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (831965681/2000000000 : ℝ)*x 0 + (1106987619/2500000000 : ℝ)*x 1 + (885590099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831965681/2000000000 : ℝ)^2133 ≤ (3941565238251/12500000000000 : ℝ)^1621 := by
    have hnat : (831965681 : ℕ)^2133*12500000000000^1621 ≤ 3941565238251^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831965681 2000000000 3941565238251 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106987619/2500000000 : ℝ)^2133 ≤ (34233738939943/100000000000000 : ℝ)^1621 := by
    have hnat : (1106987619 : ℕ)^2133*100000000000000^1621 ≤ 34233738939943^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106987619 2500000000 34233738939943 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885590099/2000000000 : ℝ)^2133 ≤ (6846747826647/20000000000000 : ℝ)^1621 := by
    have hnat : (885590099 : ℕ)^2133*20000000000000^1621 ≤ 6846747826647^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885590099 2000000000 6846747826647 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(831965681/2000000000 : ℝ), (1106987619/2500000000 : ℝ), (885590099/2000000000 : ℝ)] ![(3941565238251/12500000000000 : ℝ), (34233738939943/100000000000000 : ℝ), (6846747826647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(831965681/2000000000 : ℝ)|^2133 ≤ (3941565238251/12500000000000 : ℝ)^1621
        have hw : |(831965681/2000000000 : ℝ)|=(831965681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106987619/2500000000 : ℝ)|^2133 ≤ (34233738939943/100000000000000 : ℝ)^1621
        have hw : |(1106987619/2500000000 : ℝ)|=(1106987619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(885590099/2000000000 : ℝ)|^2133 ≤ (6846747826647/20000000000000 : ℝ)^1621
        have hw : |(885590099/2000000000 : ℝ)|=(885590099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62843/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7359/12500 : ℝ) ∧ (79741/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84211/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11063/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (10415816770063063/100000000000000000000 : ℝ) := by
    have hpowers : (11063/100000 : ℝ)^4265 ≤ (10415816770063063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11063 : ℕ)^4265*100000000000000000000^1024 ≤ 10415816770063063^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11063 100000 10415816770063063 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11063/100000 : ℝ)) (X := (10415816770063063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7341/50000 : ℝ) ^ (4265/1024 : ℝ) ≤ (6771079117745971/20000000000000000000 : ℝ) := by
    have hpowers : (7341/50000 : ℝ)^4265 ≤ (6771079117745971/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7341 : ℕ)^4265*20000000000000000000^1024 ≤ 6771079117745971^1024*50000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7341 50000 6771079117745971 20000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7341/50000 : ℝ)) (X := (6771079117745971/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010415816770063063/50000000000000000000 : ℝ) ≤ (2500125028748807/2500000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50010415816770063063/50000000000000000000 : ℝ)^1024 ≤ (2500125028748807/2500000000000000 : ℝ)^4265 := by
      have hnat : (50010415816770063063 : ℕ)^1024*2500000000000000^4265 ≤ 2500125028748807^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010415816770063063 50000000000000000000 2500125028748807 2500000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500125028748807/2500000000000000 : ℝ)) (X := (50010415816770063063/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022135606179396459/50000000000000000000 : ℝ) ≤ (312533210798547/312500000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50022135606179396459/50000000000000000000 : ℝ)^1024 ≤ (312533210798547/312500000000000 : ℝ)^4265 := by
      have hnat : (50022135606179396459 : ℕ)^1024*312500000000000^4265 ≤ 312533210798547^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022135606179396459 50000000000000000000 312533210798547 312500000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312533210798547/312500000000000 : ℝ)) (X := (50022135606179396459/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006771079117745971/10000000000000000000 : ℝ) ≤ (500081268805589/500000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (10006771079117745971/10000000000000000000 : ℝ)^1024 ≤ (500081268805589/500000000000000 : ℝ)^4265 := by
      have hnat : (10006771079117745971 : ℕ)^1024*500000000000000^4265 ≤ 500081268805589^4265*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006771079117745971 10000000000000000000 500081268805589 500000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500081268805589/500000000000000 : ℝ)) (X := (10006771079117745971/10000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10415816770063063/100000000000000000000 : ℝ) ≤ ((9044840288108828839/9047500000000000000 : ℝ)+2*(140657639569/90475000000000 : ℝ)*(11063/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (9044840288108828839/9047500000000000000 : ℝ)+2*(140657639569/90475000000000 : ℝ)*(11063/100000 : ℝ)=(2500125028748807/2500000000000000 : ℝ) by norm_num, show 1+2*(10415816770063063/100000000000000000000 : ℝ)=(50010415816770063063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6771079117745971/20000000000000000000 : ℝ)+(10415816770063063/100000000000000000000 : ℝ) ≤ ((9044840288108828839/9047500000000000000 : ℝ)+(140657639569/90475000000000 : ℝ)*((7341/50000 : ℝ)+(11063/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (9044840288108828839/9047500000000000000 : ℝ)+(140657639569/90475000000000 : ℝ)*((7341/50000 : ℝ)+(11063/100000 : ℝ))=(312533210798547/312500000000000 : ℝ) by norm_num, show 1+(6771079117745971/20000000000000000000 : ℝ)+(10415816770063063/100000000000000000000 : ℝ)=(50022135606179396459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6771079117745971/20000000000000000000 : ℝ) ≤ ((9044840288108828839/9047500000000000000 : ℝ)+2*(140657639569/90475000000000 : ℝ)*(7341/50000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (9044840288108828839/9047500000000000000 : ℝ)+2*(140657639569/90475000000000 : ℝ)*(7341/50000 : ℝ)=(500081268805589/500000000000000 : ℝ) by norm_num, show 1+2*(6771079117745971/20000000000000000000 : ℝ)=(10006771079117745971/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9044840288108828839/9047500000000000000 : ℝ)*(X 1 0+X 2 0)+(140657639569/90475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (9044840288108828839/9047500000000000000 : ℝ)) (alpha := (140657639569/90475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9044840288108828839/9047500000000000000 : ℝ)*(X 0 1+X 2 1)+(140657639569/90475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (9044840288108828839/9047500000000000000 : ℝ)) (alpha := (140657639569/90475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9044840288108828839/9047500000000000000 : ℝ)*(X 0 2+X 1 2)+(140657639569/90475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (11063/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (9044840288108828839/9047500000000000000 : ℝ)) (alpha := (140657639569/90475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-476328217/2500000000 : ℝ)*X 0 0+(2695717893/5000000000 : ℝ)*X 0 1+(5391435983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284613437/10000000000 : ℝ)*X 1 0+(-1025737429/5000000000 : ℝ)*X 1 1+(2695718253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321153503/2500000000 : ℝ)*X 2 0+(5391435959/10000000000 : ℝ)*X 2 1+(-256434353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((897038281/2000000000 : ℝ)*X 0 0+(1066390597/2500000000 : ℝ)*X 0 1+(4265562417/10000000000 : ℝ)*X 0 2+(897038281/2000000000 : ℝ)*X 1 0+(1066390597/2500000000 : ℝ)*X 1 1+(4265562417/10000000000 : ℝ)*X 1 2+(897038281/2000000000 : ℝ)*X 2 0+(1066390597/2500000000 : ℝ)*X 2 1+(4265562417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1124211833/5000000000 : ℝ)*X 0 0+(329004001/625000000 : ℝ)*X 0 1+(5264064519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687107321/5000000000 : ℝ)*X 1 0+(-525580849/2500000000 : ℝ)*X 1 1+(658008047/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671776849/1250000000 : ℝ)*X 2 0+(210562567/400000000 : ℝ)*X 2 1+(-2102323463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046546283/2500000000 : ℝ)*X 0 0+(220750537/500000000 : ℝ)*X 0 1+(4415010633/10000000000 : ℝ)*X 0 2+(1046546283/2500000000 : ℝ)*X 1 0+(220750537/500000000 : ℝ)*X 1 1+(4415010633/10000000000 : ℝ)*X 1 2+(1046546283/2500000000 : ℝ)*X 2 0+(220750537/500000000 : ℝ)*X 2 1+(4415010633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1088235341/5000000000 : ℝ)*X 0 0+(161767231/312500000 : ℝ)*X 0 1+(2702734857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637368139/5000000000 : ℝ)*X 1 0+(-2045737571/10000000000 : ℝ)*X 1 1+(5405469159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318683849/2500000000 : ℝ)*X 2 0+(2702735189/5000000000 : ℝ)*X 2 1+(-127858569/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4517574923/10000000000 : ℝ)*X 0 0+(4249082663/10000000000 : ℝ)*X 0 1+(4249083407/10000000000 : ℝ)*X 0 2+(4517574923/10000000000 : ℝ)*X 1 0+(4249082663/10000000000 : ℝ)*X 1 1+(4249083407/10000000000 : ℝ)*X 1 2+(4517574923/10000000000 : ℝ)*X 2 0+(4249082663/10000000000 : ℝ)*X 2 1+(4249083407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1977675239/10000000000 : ℝ)*X 0 0+(2738329667/5000000000 : ℝ)*X 0 1+(5253027161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345494013/2500000000 : ℝ)*X 1 0+(-42132483/200000000 : ℝ)*X 1 1+(164157099/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1345494013/2500000000 : ℝ)*X 2 0+(5253027167/10000000000 : ℝ)*X 2 1+(-263328019/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((831965681/2000000000 : ℝ)*X 0 0+(1106987619/2500000000 : ℝ)*X 0 1+(885590099/2000000000 : ℝ)*X 0 2+(831965681/2000000000 : ℝ)*X 1 0+(1106987619/2500000000 : ℝ)*X 1 1+(885590099/2000000000 : ℝ)*X 1 2+(831965681/2000000000 : ℝ)*X 2 0+(1106987619/2500000000 : ℝ)*X 2 1+(885590099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62843/100000 : ℝ) ≤ (-71068675498757354676371221962813/113093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4398723/50000000000000 : ℝ)*(lower0) + (17550011/100000000000000 : ℝ)*(upper1) + (13320573/100000000000000 : ℝ)*(lower3) + (720003117425087/25000000000000 : ℝ)*(major0) + (720003117425087/25000000000000 : ℝ)*(major1) + (720003117425087/25000000000000 : ℝ)*(major2) + (1332200069/100000000000000 : ℝ)*(sp1) + (7865251629/100000000000000 : ℝ)*(sp2) + (393940751/10000000000000 : ℝ)*(sp3) + (780486487997713/20000000000000 : ℝ)*(sp4) + (1951219162451079/50000000000000 : ℝ)*(sp5) + (3902431791850597/100000000000000 : ℝ)*(sp6) + (234816021937033/12500000000000 : ℝ)*(sp7) + (7217113661/100000000000000 : ℝ)*(sp12) + (1878532114903773/100000000000000 : ℝ)*(f.failure) + (1951219828551113/50000000000000 : ℝ)*(f.sum) + (96688665359207/18095000000000000000000000000 : ℝ)*base66 + (1176473176076141007/226187500000000000000000000000000 : ℝ)*base68 + (7073554597307141007/226187500000000000000000000000000 : ℝ)*base70 + (3381818249984078507/226187500000000000000000000000000 : ℝ)*base72 + (43801368874801/9047500000000000000000000000 : ℝ)*base74 + (7497943568573016007/226187500000000000000000000000000 : ℝ)*base76 + (1983964070151391007/226187500000000000000000000000000 : ℝ)*base78 + (1916434470186641007/226187500000000000000000000000000 : ℝ)*base80 + (1732098759927923/18095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (14936461/10000000000000000000000 : ℝ)*base89 + (14936461/10000000000000000000000 : ℝ)*base91 + (14936461/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7359/12500 : ℝ) ≤ (302650451281265172432782130429/514062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27417957/100000000000000 : ℝ)*(lower1) + (21890321/100000000000000 : ℝ)*(lower3) + (3351179/3125000000000 : ℝ)*(upper4) + (37834339/100000000000000 : ℝ)*(upper5) + (36843684478557/1250000000000 : ℝ)*(major0) + (36843684478557/1250000000000 : ℝ)*(major1) + (36843684478557/1250000000000 : ℝ)*(major2) + (1976408148876743/50000000000000 : ℝ)*(sp0) + (988200125288451/25000000000000 : ℝ)*(sp1) + (247050868706969/6250000000000 : ℝ)*(sp2) + (30039805054403/1562500000000 : ℝ)*(sp3) + (15796599681/100000000000000 : ℝ)*(sp5) + (2398441981/100000000000000 : ℝ)*(sp6) + (472346739/50000000000000 : ℝ)*(sp7) + (1922548468175269/100000000000000 : ℝ)*(f.failure) + (1976408148876743/50000000000000 : ℝ)*(f.sum) + (15936143973/4112500000000000000000000 : ℝ)*base66 + (13803152773121107/1028125000000000000000000000000 : ℝ)*base68 + (71670526415766393/1028125000000000000000000000000 : ℝ)*base69 + (8520972843827357/1028125000000000000000000000000 : ℝ)*base72 + (62770530267/16450000000000000000000000 : ℝ)*base74 + (61176098663522643/1028125000000000000000000000000 : ℝ)*base75 + (5611773328358607/1028125000000000000000000000000 : ℝ)*base78 + (1853201452083991/514062500000000000000000000000 : ℝ)*base80 + (48121504611261/329000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (108135467/10000000000000000000000 : ℝ)*base90 + (108135467/10000000000000000000000 : ℝ)*base92 + (108135467/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79741/100000 : ℝ) ≤ (25767113157561308765828296429011/32312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125772797/100000000000000 : ℝ)*(upper0) + (3433659/10000000000000 : ℝ)*(upper2) + (16319919/50000000000000 : ℝ)*(lower3) + (1630500656405681/50000000000000 : ℝ)*(major0) + (1630500656405681/50000000000000 : ℝ)*(major1) + (1630500656405681/50000000000000 : ℝ)*(major2) + (355267215691/100000000000000 : ℝ)*(sp2) + (1625300043/100000000000000 : ℝ)*(sp3) + (10080124443/100000000000000 : ℝ)*(sp4) + (2184184532814949/50000000000000 : ℝ)*(sp8) + (2184191779191989/50000000000000 : ℝ)*(sp9) + (136500884099009/3125000000000 : ℝ)*(sp10) + (1063518140359387/50000000000000 : ℝ)*(sp11) + (2206314819/50000000000000 : ℝ)*(sp12) + (4154370910193/195312500000 : ℝ)*(f.failure) + (2184191779191989/50000000000000 : ℝ)*(f.sum) + (71476036937883/18095000000000000000000000000 : ℝ)*base66 + (736198348674615641/452375000000000000000000000000000 : ℝ)*base68 + (4573565060295365641/452375000000000000000000000000000 : ℝ)*base70 + (503857131710259359/452375000000000000000000000000000 : ℝ)*base71 + (2237684832839/565468750000000000000000000 : ℝ)*base74 + (113813638929009359/452375000000000000000000000000000 : ℝ)*base75 + (3106380570822740641/452375000000000000000000000000000 : ℝ)*base78 + (997944033249990641/452375000000000000000000000000000 : ℝ)*base80 + (87773529435323/18095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5139/1220703125000000000 : ℝ)*base90 + (5139/1220703125000000000 : ℝ)*base92 + (5139/1220703125000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84211/100000 : ℝ) ≤ (-2176777773166023368100961341/2585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (805607/100000000000000 : ℝ)*(lower1) + (1957181/100000000000000 : ℝ)*(upper3) + (2424803/100000000000000 : ℝ)*(lower4) + (5686901/100000000000000 : ℝ)*(upper5) + (3297057947197343/100000000000000 : ℝ)*(major0) + (3297057947197343/100000000000000 : ℝ)*(major1) + (3297057947197343/100000000000000 : ℝ)*(major2) + (41602639/12500000000000 : ℝ)*(sp4) + (781059639/25000000000000 : ℝ)*(sp6) + (3466730177/100000000000000 : ℝ)*(sp7) + (2235814255513467/50000000000000 : ℝ)*(sp12) + (2235814421924023/50000000000000 : ℝ)*(sp13) + (447162571960949/10000000000000 : ℝ)*(sp14) + (2150552929698667/100000000000000 : ℝ)*(sp15) + (537639099107211/25000000000000 : ℝ)*(f.failure) + (2235814421924023/50000000000000 : ℝ)*(f.sum) + (11557233391139/2585000000000000000000000000 : ℝ)*base65 + (174058335340817889/129250000000000000000000000000000 : ℝ)*base68 + (2530353479335182111/129250000000000000000000000000000 : ℝ)*base69 + (1986932558432432111/129250000000000000000000000000000 : ℝ)*base71 + (79962064811/40390625000000000000000000 : ℝ)*base73 + (4726237094375317889/129250000000000000000000000000000 : ℝ)*base76 + (1694199475812432111/129250000000000000000000000000000 : ℝ)*base77 + (553218171214317889/129250000000000000000000000000000 : ℝ)*base80 + (21393594040597/1292500000000000000000000000 : ℝ)*base81 + (14499173/2500000000000000000000 : ℝ)*base90 + (14499173/2500000000000000000000 : ℝ)*base92 + (14499173/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1306_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7359/12500 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84211/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1306_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1306_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7359/12500 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84211/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1306_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1306_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1306_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7359/12500 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84211/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

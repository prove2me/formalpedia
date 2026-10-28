-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:35.614564+00:00
-- url     : https://prove2.me/submissions/5c3e33b0-396d-4d4e-86fa-392c5a849931

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
theorem support_rectangle_w1033_s6_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-444012491/2000000000 : ℝ)*x 0 + (1079119969/2000000000 : ℝ)*x 1 + (5263197267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444012491/2000000000 : ℝ)^4113 ≤ (13479879006889/100000000000000 : ℝ)^3089 := by
    have hnat : (444012491 : ℕ)^4113*100000000000000^3089 ≤ 13479879006889^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444012491 2000000000 13479879006889 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079119969/2000000000 : ℝ)^4113 ≤ (43975542804081/100000000000000 : ℝ)^3089 := by
    have hnat : (1079119969 : ℕ)^4113*100000000000000^3089 ≤ 43975542804081^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079119969 2000000000 43975542804081 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263197267/10000000000 : ℝ)^4113 ≤ (8508915634097/20000000000000 : ℝ)^3089 := by
    have hnat : (5263197267 : ℕ)^4113*20000000000000^3089 ≤ 8508915634097^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263197267 10000000000 8508915634097 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444012491/2000000000 : ℝ), (1079119969/2000000000 : ℝ), (5263197267/10000000000 : ℝ)] ![(13479879006889/100000000000000 : ℝ), (43975542804081/100000000000000 : ℝ), (8508915634097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444012491/2000000000 : ℝ)|^4113 ≤ (13479879006889/100000000000000 : ℝ)^3089
        have hw : |(-444012491/2000000000 : ℝ)|=(444012491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079119969/2000000000 : ℝ)|^4113 ≤ (43975542804081/100000000000000 : ℝ)^3089
        have hw : |(1079119969/2000000000 : ℝ)|=(1079119969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263197267/10000000000 : ℝ)|^4113 ≤ (8508915634097/20000000000000 : ℝ)^3089
        have hw : |(5263197267/10000000000 : ℝ)|=(5263197267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345211643/10000000000 : ℝ)*x 0 + (-114362937/500000000 : ℝ)*x 1 + (5263197407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345211643/10000000000 : ℝ)^4113 ≤ (21714787540179/50000000000000 : ℝ)^3089 := by
    have hnat : (5345211643 : ℕ)^4113*50000000000000^3089 ≤ 21714787540179^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345211643 10000000000 21714787540179 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114362937/500000000 : ℝ)^4113 ≤ (43830766339/312500000000 : ℝ)^3089 := by
    have hnat : (114362937 : ℕ)^4113*312500000000^3089 ≤ 43830766339^3089*500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114362937 500000000 43830766339 312500000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263197407/10000000000 : ℝ)^4113 ≤ (332379528729/781250000000 : ℝ)^3089 := by
    have hnat : (5263197407 : ℕ)^4113*781250000000^3089 ≤ 332379528729^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263197407 10000000000 332379528729 781250000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345211643/10000000000 : ℝ), (-114362937/500000000 : ℝ), (5263197407/10000000000 : ℝ)] ![(21714787540179/50000000000000 : ℝ), (43830766339/312500000000 : ℝ), (332379528729/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345211643/10000000000 : ℝ)|^4113 ≤ (21714787540179/50000000000000 : ℝ)^3089
        have hw : |(5345211643/10000000000 : ℝ)|=(5345211643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114362937/500000000 : ℝ)|^4113 ≤ (43830766339/312500000000 : ℝ)^3089
        have hw : |(-114362937/500000000 : ℝ)|=(114362937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263197407/10000000000 : ℝ)|^4113 ≤ (332379528729/781250000000 : ℝ)^3089
        have hw : |(5263197407/10000000000 : ℝ)|=(5263197407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106904233/200000000 : ℝ)*x 0 + (5263197273/10000000000 : ℝ)*x 1 + (-571814727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106904233/200000000 : ℝ)^4113 ≤ (21714787578043/50000000000000 : ℝ)^3089 := by
    have hnat : (106904233 : ℕ)^4113*50000000000000^3089 ≤ 21714787578043^3089*200000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106904233 200000000 21714787578043 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263197273/10000000000 : ℝ)^4113 ≤ (42544578235063/100000000000000 : ℝ)^3089 := by
    have hnat : (5263197273 : ℕ)^4113*100000000000000^3089 ≤ 42544578235063^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263197273 10000000000 42544578235063 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571814727/2500000000 : ℝ)^4113 ≤ (7012923300097/50000000000000 : ℝ)^3089 := by
    have hnat : (571814727 : ℕ)^4113*50000000000000^3089 ≤ 7012923300097^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571814727 2500000000 7012923300097 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106904233/200000000 : ℝ), (5263197273/10000000000 : ℝ), (-571814727/2500000000 : ℝ)] ![(21714787578043/50000000000000 : ℝ), (42544578235063/100000000000000 : ℝ), (7012923300097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106904233/200000000 : ℝ)|^4113 ≤ (21714787578043/50000000000000 : ℝ)^3089
        have hw : |(106904233/200000000 : ℝ)|=(106904233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263197273/10000000000 : ℝ)|^4113 ≤ (42544578235063/100000000000000 : ℝ)^3089
        have hw : |(5263197273/10000000000 : ℝ)|=(5263197273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571814727/2500000000 : ℝ)|^4113 ≤ (7012923300097/50000000000000 : ℝ)^3089
        have hw : |(-571814727/2500000000 : ℝ)|=(571814727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2190112717/5000000000 : ℝ)*x 0 + (2126633821/5000000000 : ℝ)*x 1 + (902211667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190112717/5000000000 : ℝ)^4113 ≤ (33316007115551/100000000000000 : ℝ)^3089 := by
    have hnat : (2190112717 : ℕ)^4113*100000000000000^3089 ≤ 33316007115551^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190112717 5000000000 33316007115551 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126633821/5000000000 : ℝ)^4113 ≤ (32036474081703/100000000000000 : ℝ)^3089 := by
    have hnat : (2126633821 : ℕ)^4113*100000000000000^3089 ≤ 32036474081703^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126633821 5000000000 32036474081703 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902211667/2000000000 : ℝ)^4113 ≤ (34647518784071/100000000000000 : ℝ)^3089 := by
    have hnat : (902211667 : ℕ)^4113*100000000000000^3089 ≤ 34647518784071^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902211667 2000000000 34647518784071 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2190112717/5000000000 : ℝ), (2126633821/5000000000 : ℝ), (902211667/2000000000 : ℝ)] ![(33316007115551/100000000000000 : ℝ), (32036474081703/100000000000000 : ℝ), (34647518784071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2190112717/5000000000 : ℝ)|^4113 ≤ (33316007115551/100000000000000 : ℝ)^3089
        have hw : |(2190112717/5000000000 : ℝ)|=(2190112717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126633821/5000000000 : ℝ)|^4113 ≤ (32036474081703/100000000000000 : ℝ)^3089
        have hw : |(2126633821/5000000000 : ℝ)|=(2126633821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902211667/2000000000 : ℝ)|^4113 ≤ (34647518784071/100000000000000 : ℝ)^3089
        have hw : |(902211667/2000000000 : ℝ)|=(902211667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69377143/312500000 : ℝ)*x 0 + (2631765949/5000000000 : ℝ)*x 1 + (168601981/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69377143/312500000 : ℝ)^4113 ≤ (6739964246549/50000000000000 : ℝ)^3089 := by
    have hnat : (69377143 : ℕ)^4113*50000000000000^3089 ≤ 6739964246549^3089*312500000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69377143 312500000 6739964246549 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631765949/5000000000 : ℝ)^4113 ≤ (42548179858769/100000000000000 : ℝ)^3089 := by
    have hnat : (2631765949 : ℕ)^4113*100000000000000^3089 ≤ 42548179858769^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631765949 5000000000 42548179858769 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168601981/312500000 : ℝ)^4113 ≤ (43971891632917/100000000000000 : ℝ)^3089 := by
    have hnat : (168601981 : ℕ)^4113*100000000000000^3089 ≤ 43971891632917^3089*312500000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168601981 312500000 43971891632917 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69377143/312500000 : ℝ), (2631765949/5000000000 : ℝ), (168601981/312500000 : ℝ)] ![(6739964246549/50000000000000 : ℝ), (42548179858769/100000000000000 : ℝ), (43971891632917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69377143/312500000 : ℝ)|^4113 ≤ (6739964246549/50000000000000 : ℝ)^3089
        have hw : |(-69377143/312500000 : ℝ)|=(69377143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631765949/5000000000 : ℝ)|^4113 ≤ (42548179858769/100000000000000 : ℝ)^3089
        have hw : |(2631765949/5000000000 : ℝ)|=(2631765949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168601981/312500000 : ℝ)|^4113 ≤ (43971891632917/100000000000000 : ℝ)^3089
        have hw : |(168601981/312500000 : ℝ)|=(168601981/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311951097/10000000000 : ℝ)*x 0 + (-2155192783/10000000000 : ℝ)*x 1 + (5395263351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311951097/10000000000 : ℝ)^4113 ≤ (21535061055709/50000000000000 : ℝ)^3089 := by
    have hnat : (5311951097 : ℕ)^4113*50000000000000^3089 ≤ 21535061055709^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311951097 10000000000 21535061055709 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155192783/10000000000 : ℝ)^4113 ≤ (12957986686677/100000000000000 : ℝ)^3089 := by
    have hnat : (2155192783 : ℕ)^4113*100000000000000^3089 ≤ 12957986686677^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155192783 10000000000 12957986686677 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395263351/10000000000 : ℝ)^4113 ≤ (5496486398499/12500000000000 : ℝ)^3089 := by
    have hnat : (5395263351 : ℕ)^4113*12500000000000^3089 ≤ 5496486398499^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395263351 10000000000 5496486398499 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311951097/10000000000 : ℝ), (-2155192783/10000000000 : ℝ), (5395263351/10000000000 : ℝ)] ![(21535061055709/50000000000000 : ℝ), (12957986686677/100000000000000 : ℝ), (5496486398499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311951097/10000000000 : ℝ)|^4113 ≤ (21535061055709/50000000000000 : ℝ)^3089
        have hw : |(5311951097/10000000000 : ℝ)|=(5311951097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155192783/10000000000 : ℝ)|^4113 ≤ (12957986686677/100000000000000 : ℝ)^3089
        have hw : |(-2155192783/10000000000 : ℝ)|=(2155192783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395263351/10000000000 : ℝ)|^4113 ≤ (5496486398499/12500000000000 : ℝ)^3089
        have hw : |(5395263351/10000000000 : ℝ)|=(5395263351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311950983/10000000000 : ℝ)*x 0 + (5395263599/10000000000 : ℝ)*x 1 + (-1077596301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311950983/10000000000 : ℝ)^4113 ≤ (21535060440337/50000000000000 : ℝ)^3089 := by
    have hnat : (5311950983 : ℕ)^4113*50000000000000^3089 ≤ 21535060440337^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311950983 10000000000 21535060440337 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395263599/10000000000 : ℝ)^4113 ≤ (2748243367453/6250000000000 : ℝ)^3089 := by
    have hnat : (5395263599 : ℕ)^4113*6250000000000^3089 ≤ 2748243367453^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395263599 10000000000 2748243367453 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077596301/5000000000 : ℝ)^4113 ≤ (12957985237669/100000000000000 : ℝ)^3089 := by
    have hnat : (1077596301 : ℕ)^4113*100000000000000^3089 ≤ 12957985237669^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077596301 5000000000 12957985237669 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311950983/10000000000 : ℝ), (5395263599/10000000000 : ℝ), (-1077596301/5000000000 : ℝ)] ![(21535060440337/50000000000000 : ℝ), (2748243367453/6250000000000 : ℝ), (12957985237669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311950983/10000000000 : ℝ)|^4113 ≤ (21535060440337/50000000000000 : ℝ)^3089
        have hw : |(5311950983/10000000000 : ℝ)|=(5311950983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395263599/10000000000 : ℝ)|^4113 ≤ (2748243367453/6250000000000 : ℝ)^3089
        have hw : |(5395263599/10000000000 : ℝ)|=(5395263599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077596301/5000000000 : ℝ)|^4113 ≤ (12957985237669/100000000000000 : ℝ)^3089
        have hw : |(-1077596301/5000000000 : ℝ)|=(1077596301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s6_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273764767/625000000 : ℝ)*x 0 + (1127601717/2500000000 : ℝ)*x 1 + (2126960483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273764767/625000000 : ℝ)^4113 ≤ (6663223375237/20000000000000 : ℝ)^3089 := by
    have hnat : (273764767 : ℕ)^4113*20000000000000^3089 ≤ 6663223375237^3089*625000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273764767 625000000 6663223375237 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127601717/2500000000 : ℝ)^4113 ≤ (17320428300809/50000000000000 : ℝ)^3089 := by
    have hnat : (1127601717 : ℕ)^4113*50000000000000^3089 ≤ 17320428300809^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127601717 2500000000 17320428300809 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126960483/5000000000 : ℝ)^4113 ≤ (8010756628227/25000000000000 : ℝ)^3089 := by
    have hnat : (2126960483 : ℕ)^4113*25000000000000^3089 ≤ 8010756628227^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126960483 5000000000 8010756628227 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273764767/625000000 : ℝ), (1127601717/2500000000 : ℝ), (2126960483/5000000000 : ℝ)] ![(6663223375237/20000000000000 : ℝ), (17320428300809/50000000000000 : ℝ), (8010756628227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273764767/625000000 : ℝ)|^4113 ≤ (6663223375237/20000000000000 : ℝ)^3089
        have hw : |(273764767/625000000 : ℝ)|=(273764767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127601717/2500000000 : ℝ)|^4113 ≤ (17320428300809/50000000000000 : ℝ)^3089
        have hw : |(1127601717/2500000000 : ℝ)|=(1127601717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126960483/5000000000 : ℝ)|^4113 ≤ (8010756628227/25000000000000 : ℝ)^3089
        have hw : |(2126960483/5000000000 : ℝ)|=(2126960483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1399/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (1393/12500 : ℝ) ^ (8225/2048 : ℝ) ≤ (14887066177497231/100000000000000000000 : ℝ) := by
    have hpowers : (1393/12500 : ℝ)^8225 ≤ (14887066177497231/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1393 : ℕ)^8225*100000000000000000000^2048 ≤ 14887066177497231^2048*12500^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1393 12500 14887066177497231 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1393/12500 : ℝ)) (X := (14887066177497231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7023/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (7542319547134453/20000000000000000000 : ℝ) := by
    have hpowers : (7023/50000 : ℝ)^8225 ≤ (7542319547134453/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7023 : ℕ)^8225*20000000000000000000^2048 ≤ 7542319547134453^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7023 50000 7542319547134453 20000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7023/50000 : ℝ)) (X := (7542319547134453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014887066177497231/50000000000000000000 : ℝ) ≤ (500037064198681/500000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50014887066177497231/50000000000000000000 : ℝ)^2048 ≤ (500037064198681/500000000000000 : ℝ)^8225 := by
      have hnat : (50014887066177497231 : ℕ)^2048*500000000000000^8225 ≤ 500037064198681^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014887066177497231 50000000000000000000 500037064198681 500000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500037064198681/500000000000000 : ℝ)) (X := (50014887066177497231/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506574832989146187/12500000000000000000 : ℝ) ≤ (10001309432147963/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (12506574832989146187/12500000000000000000 : ℝ)^2048 ≤ (10001309432147963/10000000000000000 : ℝ)^8225 := by
      have hnat : (12506574832989146187 : ℕ)^2048*10000000000000000^8225 ≤ 10001309432147963^8225*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506574832989146187 12500000000000000000 10001309432147963 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001309432147963/10000000000000000 : ℝ)) (X := (12506574832989146187/12500000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007542319547134453/10000000000000000000 : ℝ) ≤ (5000938790161153/5000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (10007542319547134453/10000000000000000000 : ℝ)^2048 ≤ (5000938790161153/5000000000000000 : ℝ)^8225 := by
      have hnat : (10007542319547134453 : ℕ)^2048*5000000000000000^8225 ≤ 5000938790161153^8225*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007542319547134453 10000000000000000000 5000938790161153 5000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000938790161153/5000000000000000 : ℝ)) (X := (10007542319547134453/10000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14887066177497231/100000000000000000000 : ℝ) ≤ ((3626186039947711057/3627500000000000000 : ℝ)+2*(568148174343/290200000000000 : ℝ)*(1393/12500 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (3626186039947711057/3627500000000000000 : ℝ)+2*(568148174343/290200000000000 : ℝ)*(1393/12500 : ℝ)=(500037064198681/500000000000000 : ℝ) by norm_num, show 1+2*(14887066177497231/100000000000000000000 : ℝ)=(50014887066177497231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7542319547134453/20000000000000000000 : ℝ)+(14887066177497231/100000000000000000000 : ℝ) ≤ ((3626186039947711057/3627500000000000000 : ℝ)+(568148174343/290200000000000 : ℝ)*((7023/50000 : ℝ)+(1393/12500 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (3626186039947711057/3627500000000000000 : ℝ)+(568148174343/290200000000000 : ℝ)*((7023/50000 : ℝ)+(1393/12500 : ℝ))=(10001309432147963/10000000000000000 : ℝ) by norm_num, show 1+(7542319547134453/20000000000000000000 : ℝ)+(14887066177497231/100000000000000000000 : ℝ)=(12506574832989146187/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7542319547134453/20000000000000000000 : ℝ) ≤ ((3626186039947711057/3627500000000000000 : ℝ)+2*(568148174343/290200000000000 : ℝ)*(7023/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (3626186039947711057/3627500000000000000 : ℝ)+2*(568148174343/290200000000000 : ℝ)*(7023/50000 : ℝ)=(5000938790161153/5000000000000000 : ℝ) by norm_num, show 1+2*(7542319547134453/20000000000000000000 : ℝ)=(10007542319547134453/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3626186039947711057/3627500000000000000 : ℝ)*(X 1 0+X 2 0)+(568148174343/290200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (3626186039947711057/3627500000000000000 : ℝ)) (alpha := (568148174343/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3626186039947711057/3627500000000000000 : ℝ)*(X 0 1+X 2 1)+(568148174343/290200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (3626186039947711057/3627500000000000000 : ℝ)) (alpha := (568148174343/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3626186039947711057/3627500000000000000 : ℝ)*(X 0 2+X 1 2)+(568148174343/290200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (3626186039947711057/3627500000000000000 : ℝ)) (alpha := (568148174343/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-444012491/2000000000 : ℝ)*X 0 0+(1079119969/2000000000 : ℝ)*X 0 1+(5263197267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345211643/10000000000 : ℝ)*X 1 0+(-114362937/500000000 : ℝ)*X 1 1+(5263197407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106904233/200000000 : ℝ)*X 2 0+(5263197273/10000000000 : ℝ)*X 2 1+(-571814727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2190112717/5000000000 : ℝ)*X 0 0+(2126633821/5000000000 : ℝ)*X 0 1+(902211667/2000000000 : ℝ)*X 0 2+(2190112717/5000000000 : ℝ)*X 1 0+(2126633821/5000000000 : ℝ)*X 1 1+(902211667/2000000000 : ℝ)*X 1 2+(2190112717/5000000000 : ℝ)*X 2 0+(2126633821/5000000000 : ℝ)*X 2 1+(902211667/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69377143/312500000 : ℝ)*X 0 0+(2631765949/5000000000 : ℝ)*X 0 1+(168601981/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311951097/10000000000 : ℝ)*X 1 0+(-2155192783/10000000000 : ℝ)*X 1 1+(5395263351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311950983/10000000000 : ℝ)*X 2 0+(5395263599/10000000000 : ℝ)*X 2 1+(-1077596301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273764767/625000000 : ℝ)*X 0 0+(1127601717/2500000000 : ℝ)*X 0 1+(2126960483/5000000000 : ℝ)*X 0 2+(273764767/625000000 : ℝ)*X 1 0+(1127601717/2500000000 : ℝ)*X 1 1+(2126960483/5000000000 : ℝ)*X 1 2+(273764767/625000000 : ℝ)*X 2 0+(1127601717/2500000000 : ℝ)*X 2 1+(2126960483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (690264463475245540628446593/181375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444613863/100000000000000 : ℝ)*(base8) + (34312519/25000000000000 : ℝ)*(base15) + (6751101/100000000000000 : ℝ)*(lower2) + (1633779/2500000000000 : ℝ)*(lower4) + (109041321/50000000000000 : ℝ)*(lower5) + (5715953149874517/100000000000000 : ℝ)*(major0) + (5715953149874517/100000000000000 : ℝ)*(major1) + (5715953149874517/100000000000000 : ℝ)*(major2) + (3776378732804289/50000000000000 : ℝ)*(sp0) + (1888194507193391/25000000000000 : ℝ)*(sp1) + (188819454150591/2500000000000 : ℝ)*(sp2) + (1939560410854073/50000000000000 : ℝ)*(sp3) + (20255801199/100000000000000 : ℝ)*(sp4) + (359257977/5000000000000 : ℝ)*(sp7) + (1939564003433843/50000000000000 : ℝ)*(f.failure) + (188819454150591/2500000000000 : ℝ)*(f.sum) + (1547316196031/14510000000000000000000000000 : ℝ)*base65 + (3384768890799071969/362750000000000000000000000000000 : ℝ)*base67 + (3091004030469071969/362750000000000000000000000000000 : ℝ)*base69 + (4518130661383928031/362750000000000000000000000000000 : ℝ)*base72 + (47773979747589/14510000000000000000000000000 : ℝ)*base74 + (5042894594090571969/362750000000000000000000000000000 : ℝ)*base75 + (2229019212379071969/362750000000000000000000000000000 : ℝ)*base77 + (2611821471502928031/362750000000000000000000000000000 : ℝ)*base80 + (32997639091969/14510000000000000000000000000 : ℝ)*base82 + (6634891/625000000000000000000 : ℝ)*base89 + (6634891/625000000000000000000 : ℝ)*base91 + (6634891/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579899632604498328425661423/90687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200063937/25000000000000 : ℝ)*(base19) + (381213713/50000000000000 : ℝ)*(base23) + (99304301/100000000000000 : ℝ)*(upper3) + (18163197/100000000000000 : ℝ)*(lower4) + (2872512866482929/50000000000000 : ℝ)*(major0) + (2872512866482929/50000000000000 : ℝ)*(major1) + (2872512866482929/50000000000000 : ℝ)*(major2) + (18026487189/100000000000000 : ℝ)*(sp1) + (6508543957/20000000000000 : ℝ)*(sp2) + (1718326099/50000000000000 : ℝ)*(sp3) + (1897798288925343/25000000000000 : ℝ)*(sp4) + (1518234865791687/20000000000000 : ℝ)*(sp5) + (94889498131927/1250000000000 : ℝ)*(sp6) + (779770932085743/20000000000000 : ℝ)*(sp7) + (3898858097080913/100000000000000 : ℝ)*(f.failure) + (1897798288925343/25000000000000 : ℝ)*(f.sum) + (36092192934947/7255000000000000000000000000 : ℝ)*base65 + (1478531976874133453/181375000000000000000000000000000 : ℝ)*base67 + (876053732817633453/181375000000000000000000000000000 : ℝ)*base69 + (2697010434468883453/181375000000000000000000000000000 : ℝ)*base71 + (11616214550229/3627500000000000000000000000 : ℝ)*base74 + (1894372645619633453/181375000000000000000000000000000 : ℝ)*base75 + (4859827539292883453/181375000000000000000000000000000 : ℝ)*base77 + (5875641635231758453/181375000000000000000000000000000 : ℝ)*base79 + (45075175921047/7255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4550519/1250000000000000000000 : ℝ)*base90 + (4550519/1250000000000000000000 : ℝ)*base92 + (4550519/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1033_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s7_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220110547/10000000000 : ℝ)*x 0 + (539505247/1000000000 : ℝ)*x 1 + (5263713027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220110547/10000000000 : ℝ)^4113 ≤ (13480267815613/100000000000000 : ℝ)^3089 := by
    have hnat : (2220110547 : ℕ)^4113*100000000000000^3089 ≤ 13480267815613^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220110547 10000000000 13480267815613 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539505247/1000000000 : ℝ)^4113 ≤ (4396960275639/10000000000000 : ℝ)^3089 := by
    have hnat : (539505247 : ℕ)^4113*10000000000000^3089 ≤ 4396960275639^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539505247 1000000000 4396960275639 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263713027/10000000000 : ℝ)^4113 ≤ (42550129411539/100000000000000 : ℝ)^3089 := by
    have hnat : (5263713027 : ℕ)^4113*100000000000000^3089 ≤ 42550129411539^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263713027 10000000000 42550129411539 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220110547/10000000000 : ℝ), (539505247/1000000000 : ℝ), (5263713027/10000000000 : ℝ)] ![(13480267815613/100000000000000 : ℝ), (4396960275639/10000000000000 : ℝ), (42550129411539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220110547/10000000000 : ℝ)|^4113 ≤ (13480267815613/100000000000000 : ℝ)^3089
        have hw : |(-2220110547/10000000000 : ℝ)|=(2220110547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539505247/1000000000 : ℝ)|^4113 ≤ (4396960275639/10000000000000 : ℝ)^3089
        have hw : |(539505247/1000000000 : ℝ)|=(539505247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263713027/10000000000 : ℝ)|^4113 ≤ (42550129411539/100000000000000 : ℝ)^3089
        have hw : |(5263713027/10000000000 : ℝ)|=(5263713027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336268959/2500000000 : ℝ)*x 0 + (-2286758979/10000000000 : ℝ)*x 1 + (5263713013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336268959/2500000000 : ℝ)^4113 ≤ (43428105877371/100000000000000 : ℝ)^3089 := by
    have hnat : (1336268959 : ℕ)^4113*100000000000000^3089 ≤ 43428105877371^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336268959 2500000000 43428105877371 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286758979/10000000000 : ℝ)^4113 ≤ (3505441210781/25000000000000 : ℝ)^3089 := by
    have hnat : (2286758979 : ℕ)^4113*25000000000000^3089 ≤ 3505441210781^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286758979 10000000000 3505441210781 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263713013/10000000000 : ℝ)^4113 ≤ (42550129260851/100000000000000 : ℝ)^3089 := by
    have hnat : (5263713013 : ℕ)^4113*100000000000000^3089 ≤ 42550129260851^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263713013 10000000000 42550129260851 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336268959/2500000000 : ℝ), (-2286758979/10000000000 : ℝ), (5263713013/10000000000 : ℝ)] ![(43428105877371/100000000000000 : ℝ), (3505441210781/25000000000000 : ℝ), (42550129260851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336268959/2500000000 : ℝ)|^4113 ≤ (43428105877371/100000000000000 : ℝ)^3089
        have hw : |(1336268959/2500000000 : ℝ)|=(1336268959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286758979/10000000000 : ℝ)|^4113 ≤ (3505441210781/25000000000000 : ℝ)^3089
        have hw : |(-2286758979/10000000000 : ℝ)|=(2286758979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263713013/10000000000 : ℝ)|^4113 ≤ (42550129260851/100000000000000 : ℝ)^3089
        have hw : |(5263713013/10000000000 : ℝ)|=(5263713013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345075839/10000000000 : ℝ)*x 0 + (210548521/400000000 : ℝ)*x 1 + (-28584487/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345075839/10000000000 : ℝ)^4113 ≤ (21714052954913/50000000000000 : ℝ)^3089 := by
    have hnat : (5345075839 : ℕ)^4113*50000000000000^3089 ≤ 21714052954913^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345075839 10000000000 21714052954913 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210548521/400000000 : ℝ)^4113 ≤ (10637532347503/25000000000000 : ℝ)^3089 := by
    have hnat : (210548521 : ℕ)^4113*25000000000000^3089 ≤ 10637532347503^3089*400000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210548521 400000000 10637532347503 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28584487/125000000 : ℝ)^4113 ≤ (14021764688001/100000000000000 : ℝ)^3089 := by
    have hnat : (28584487 : ℕ)^4113*100000000000000^3089 ≤ 14021764688001^3089*125000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28584487 125000000 14021764688001 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345075839/10000000000 : ℝ), (210548521/400000000 : ℝ), (-28584487/125000000 : ℝ)] ![(21714052954913/50000000000000 : ℝ), (10637532347503/25000000000000 : ℝ), (14021764688001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345075839/10000000000 : ℝ)|^4113 ≤ (21714052954913/50000000000000 : ℝ)^3089
        have hw : |(5345075839/10000000000 : ℝ)|=(5345075839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210548521/400000000 : ℝ)|^4113 ≤ (10637532347503/25000000000000 : ℝ)^3089
        have hw : |(210548521/400000000 : ℝ)|=(210548521/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28584487/125000000 : ℝ)|^4113 ≤ (14021764688001/100000000000000 : ℝ)^3089
        have hw : |(-28584487/125000000 : ℝ)|=(28584487/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54753169/125000000 : ℝ)*x 0 + (2127149021/5000000000 : ℝ)*x 1 + (4510019947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54753169/125000000 : ℝ)^4113 ≤ (6663258310713/20000000000000 : ℝ)^3089 := by
    have hnat : (54753169 : ℕ)^4113*20000000000000^3089 ≤ 6663258310713^3089*125000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54753169 125000000 6663258310713 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127149021/5000000000 : ℝ)^4113 ≤ (31295711427/97656250000 : ℝ)^3089 := by
    have hnat : (2127149021 : ℕ)^4113*97656250000^3089 ≤ 31295711427^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127149021 5000000000 31295711427 97656250000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510019947/10000000000 : ℝ)^4113 ≤ (6927379986323/20000000000000 : ℝ)^3089 := by
    have hnat : (4510019947 : ℕ)^4113*20000000000000^3089 ≤ 6927379986323^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510019947 10000000000 6927379986323 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54753169/125000000 : ℝ), (2127149021/5000000000 : ℝ), (4510019947/10000000000 : ℝ)] ![(6663258310713/20000000000000 : ℝ), (31295711427/97656250000 : ℝ), (6927379986323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54753169/125000000 : ℝ)|^4113 ≤ (6663258310713/20000000000000 : ℝ)^3089
        have hw : |(54753169/125000000 : ℝ)|=(54753169/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127149021/5000000000 : ℝ)|^4113 ≤ (31295711427/97656250000 : ℝ)^3089
        have hw : |(2127149021/5000000000 : ℝ)|=(2127149021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510019947/10000000000 : ℝ)|^4113 ≤ (6927379986323/20000000000000 : ℝ)^3089
        have hw : |(4510019947/10000000000 : ℝ)|=(4510019947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-277514481/1250000000 : ℝ)*x 0 + (5264042227/10000000000 : ℝ)*x 1 + (674340249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277514481/1250000000 : ℝ)^4113 ≤ (2696062134541/20000000000000 : ℝ)^3089 := by
    have hnat : (277514481 : ℕ)^4113*20000000000000^3089 ≤ 2696062134541^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277514481 1250000000 2696062134541 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264042227/10000000000 : ℝ)^4113 ≤ (2659604547473/6250000000000 : ℝ)^3089 := by
    have hnat : (5264042227 : ℕ)^4113*6250000000000^3089 ≤ 2659604547473^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264042227 10000000000 2659604547473 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674340249/1250000000 : ℝ)^4113 ≤ (21983008272793/50000000000000 : ℝ)^3089 := by
    have hnat : (674340249 : ℕ)^4113*50000000000000^3089 ≤ 21983008272793^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674340249 1250000000 21983008272793 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277514481/1250000000 : ℝ), (5264042227/10000000000 : ℝ), (674340249/1250000000 : ℝ)] ![(2696062134541/20000000000000 : ℝ), (2659604547473/6250000000000 : ℝ), (21983008272793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277514481/1250000000 : ℝ)|^4113 ≤ (2696062134541/20000000000000 : ℝ)^3089
        have hw : |(-277514481/1250000000 : ℝ)|=(277514481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264042227/10000000000 : ℝ)|^4113 ≤ (2659604547473/6250000000000 : ℝ)^3089
        have hw : |(5264042227/10000000000 : ℝ)|=(5264042227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674340249/1250000000 : ℝ)|^4113 ≤ (21983008272793/50000000000000 : ℝ)^3089
        have hw : |(674340249/1250000000 : ℝ)|=(674340249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312082171/10000000000 : ℝ)*x 0 + (-538937473/2500000000 : ℝ)*x 1 + (337170121/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312082171/10000000000 : ℝ)^4113 ≤ (2153576859599/5000000000000 : ℝ)^3089 := by
    have hnat : (5312082171 : ℕ)^4113*5000000000000^3089 ≤ 2153576859599^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312082171 10000000000 2153576859599 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538937473/2500000000 : ℝ)^4113 ≤ (1620305856539/12500000000000 : ℝ)^3089 := by
    have hnat : (538937473 : ℕ)^4113*12500000000000^3089 ≤ 1620305856539^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538937473 2500000000 1620305856539 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337170121/625000000 : ℝ)^4113 ≤ (2747875996119/6250000000000 : ℝ)^3089 := by
    have hnat : (337170121 : ℕ)^4113*6250000000000^3089 ≤ 2747875996119^3089*625000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337170121 625000000 2747875996119 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312082171/10000000000 : ℝ), (-538937473/2500000000 : ℝ), (337170121/625000000 : ℝ)] ![(2153576859599/5000000000000 : ℝ), (1620305856539/12500000000000 : ℝ), (2747875996119/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312082171/10000000000 : ℝ)|^4113 ≤ (2153576859599/5000000000000 : ℝ)^3089
        have hw : |(5312082171/10000000000 : ℝ)|=(5312082171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538937473/2500000000 : ℝ)|^4113 ≤ (1620305856539/12500000000000 : ℝ)^3089
        have hw : |(-538937473/2500000000 : ℝ)|=(538937473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337170121/625000000 : ℝ)|^4113 ≤ (2747875996119/6250000000000 : ℝ)^3089
        have hw : |(337170121/625000000 : ℝ)|=(337170121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062416389/2000000000 : ℝ)*x 0 + (42146267/78125000 : ℝ)*x 1 + (-2155749871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062416389/2000000000 : ℝ)^4113 ≤ (672992730501/1562500000000 : ℝ)^3089 := by
    have hnat : (1062416389 : ℕ)^4113*1562500000000^3089 ≤ 672992730501^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062416389 2000000000 672992730501 1562500000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42146267/78125000 : ℝ)^4113 ≤ (21983009271129/50000000000000 : ℝ)^3089 := by
    have hnat : (42146267 : ℕ)^4113*50000000000000^3089 ≤ 21983009271129^3089*78125000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42146267 78125000 21983009271129 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155749871/10000000000 : ℝ)^4113 ≤ (648122334209/5000000000000 : ℝ)^3089 := by
    have hnat : (2155749871 : ℕ)^4113*5000000000000^3089 ≤ 648122334209^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155749871 10000000000 648122334209 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062416389/2000000000 : ℝ), (42146267/78125000 : ℝ), (-2155749871/10000000000 : ℝ)] ![(672992730501/1562500000000 : ℝ), (21983009271129/50000000000000 : ℝ), (648122334209/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062416389/2000000000 : ℝ)|^4113 ≤ (672992730501/1562500000000 : ℝ)^3089
        have hw : |(1062416389/2000000000 : ℝ)|=(1062416389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42146267/78125000 : ℝ)|^4113 ≤ (21983009271129/50000000000000 : ℝ)^3089
        have hw : |(42146267/78125000 : ℝ)|=(42146267/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155749871/10000000000 : ℝ)|^4113 ≤ (648122334209/5000000000000 : ℝ)^3089
        have hw : |(-2155749871/10000000000 : ℝ)|=(2155749871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s7_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4380263379/10000000000 : ℝ)*x 0 + (4509379201/10000000000 : ℝ)*x 1 + (106373533/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380263379/10000000000 : ℝ)^4113 ≤ (6663278279939/20000000000000 : ℝ)^3089 := by
    have hnat : (4380263379 : ℕ)^4113*20000000000000^3089 ≤ 6663278279939^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380263379 10000000000 6663278279939 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509379201/10000000000 : ℝ)^4113 ≤ (8657586971057/25000000000000 : ℝ)^3089 := by
    have hnat : (4509379201 : ℕ)^4113*25000000000000^3089 ≤ 8657586971057^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509379201 10000000000 8657586971057 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106373533/250000000 : ℝ)^4113 ≤ (32053260692877/100000000000000 : ℝ)^3089 := by
    have hnat : (106373533 : ℕ)^4113*100000000000000^3089 ≤ 32053260692877^3089*250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106373533 250000000 32053260692877 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380263379/10000000000 : ℝ), (4509379201/10000000000 : ℝ), (106373533/250000000 : ℝ)] ![(6663278279939/20000000000000 : ℝ), (8657586971057/25000000000000 : ℝ), (32053260692877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380263379/10000000000 : ℝ)|^4113 ≤ (6663278279939/20000000000000 : ℝ)^3089
        have hw : |(4380263379/10000000000 : ℝ)|=(4380263379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509379201/10000000000 : ℝ)|^4113 ≤ (8657586971057/25000000000000 : ℝ)^3089
        have hw : |(4509379201/10000000000 : ℝ)|=(4509379201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106373533/250000000 : ℝ)|^4113 ≤ (32053260692877/100000000000000 : ℝ)^3089
        have hw : |(106373533/250000000 : ℝ)|=(106373533/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11203/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2797/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1399/12500 : ℝ) ^ (8225/2048 : ℝ) ≤ (15146266298622811/100000000000000000000 : ℝ) := by
    have hpowers : (1399/12500 : ℝ)^8225 ≤ (15146266298622811/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8225*100000000000000000000^2048 ≤ 15146266298622811^2048*12500^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 12500 15146266298622811 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/12500 : ℝ)) (X := (15146266298622811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/25000 : ℝ) ^ (8225/2048 : ℝ) ≤ (18587674589805581/50000000000000000000 : ℝ) := by
    have hpowers : (3499/25000 : ℝ)^8225 ≤ (18587674589805581/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3499 : ℕ)^8225*50000000000000000000^2048 ≤ 18587674589805581^2048*25000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 25000 18587674589805581 50000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/25000 : ℝ)) (X := (18587674589805581/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015146266298622811/50000000000000000000 : ℝ) ≤ (1250094273633929/1250000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50015146266298622811/50000000000000000000 : ℝ)^2048 ≤ (1250094273633929/1250000000000000 : ℝ)^8225 := by
      have hnat : (50015146266298622811 : ℕ)^2048*1250000000000000^8225 ≤ 1250094273633929^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015146266298622811 50000000000000000000 1250094273633929 1250000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094273633929/1250000000000000 : ℝ)) (X := (50015146266298622811/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052321615478233973/100000000000000000000 : ℝ) ≤ (2500325634110679/2500000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (100052321615478233973/100000000000000000000 : ℝ)^2048 ≤ (2500325634110679/2500000000000000 : ℝ)^8225 := by
      have hnat : (100052321615478233973 : ℕ)^2048*2500000000000000^8225 ≤ 2500325634110679^8225*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052321615478233973 100000000000000000000 2500325634110679 2500000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500325634110679/2500000000000000 : ℝ)) (X := (100052321615478233973/100000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018587674589805581/25000000000000000000 : ℝ) ≤ (5000925441907/5000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (25018587674589805581/25000000000000000000 : ℝ)^2048 ≤ (5000925441907/5000000000000 : ℝ)^8225 := by
      have hnat : (25018587674589805581 : ℕ)^2048*5000000000000^8225 ≤ 5000925441907^8225*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018587674589805581 25000000000000000000 5000925441907 5000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000925441907/5000000000000 : ℝ)) (X := (25018587674589805581/25000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15146266298622811/100000000000000000000 : ℝ) ≤ ((875932516831171071/876250000000000000 : ℝ)+2*(137086842821/70100000000000 : ℝ)*(1399/12500 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (875932516831171071/876250000000000000 : ℝ)+2*(137086842821/70100000000000 : ℝ)*(1399/12500 : ℝ)=(1250094273633929/1250000000000000 : ℝ) by norm_num, show 1+2*(15146266298622811/100000000000000000000 : ℝ)=(50015146266298622811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18587674589805581/50000000000000000000 : ℝ)+(15146266298622811/100000000000000000000 : ℝ) ≤ ((875932516831171071/876250000000000000 : ℝ)+(137086842821/70100000000000 : ℝ)*((3499/25000 : ℝ)+(1399/12500 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (875932516831171071/876250000000000000 : ℝ)+(137086842821/70100000000000 : ℝ)*((3499/25000 : ℝ)+(1399/12500 : ℝ))=(2500325634110679/2500000000000000 : ℝ) by norm_num, show 1+(18587674589805581/50000000000000000000 : ℝ)+(15146266298622811/100000000000000000000 : ℝ)=(100052321615478233973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18587674589805581/50000000000000000000 : ℝ) ≤ ((875932516831171071/876250000000000000 : ℝ)+2*(137086842821/70100000000000 : ℝ)*(3499/25000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (875932516831171071/876250000000000000 : ℝ)+2*(137086842821/70100000000000 : ℝ)*(3499/25000 : ℝ)=(5000925441907/5000000000000 : ℝ) by norm_num, show 1+2*(18587674589805581/50000000000000000000 : ℝ)=(25018587674589805581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (875932516831171071/876250000000000000 : ℝ)*(X 1 0+X 2 0)+(137086842821/70100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (875932516831171071/876250000000000000 : ℝ)) (alpha := (137086842821/70100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (875932516831171071/876250000000000000 : ℝ)*(X 0 1+X 2 1)+(137086842821/70100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (875932516831171071/876250000000000000 : ℝ)) (alpha := (137086842821/70100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (875932516831171071/876250000000000000 : ℝ)*(X 0 2+X 1 2)+(137086842821/70100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (875932516831171071/876250000000000000 : ℝ)) (alpha := (137086842821/70100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2220110547/10000000000 : ℝ)*X 0 0+(539505247/1000000000 : ℝ)*X 0 1+(5263713027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336268959/2500000000 : ℝ)*X 1 0+(-2286758979/10000000000 : ℝ)*X 1 1+(5263713013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345075839/10000000000 : ℝ)*X 2 0+(210548521/400000000 : ℝ)*X 2 1+(-28584487/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54753169/125000000 : ℝ)*X 0 0+(2127149021/5000000000 : ℝ)*X 0 1+(4510019947/10000000000 : ℝ)*X 0 2+(54753169/125000000 : ℝ)*X 1 0+(2127149021/5000000000 : ℝ)*X 1 1+(4510019947/10000000000 : ℝ)*X 1 2+(54753169/125000000 : ℝ)*X 2 0+(2127149021/5000000000 : ℝ)*X 2 1+(4510019947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-277514481/1250000000 : ℝ)*X 0 0+(5264042227/10000000000 : ℝ)*X 0 1+(674340249/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312082171/10000000000 : ℝ)*X 1 0+(-538937473/2500000000 : ℝ)*X 1 1+(337170121/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062416389/2000000000 : ℝ)*X 2 0+(42146267/78125000 : ℝ)*X 2 1+(-2155749871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4380263379/10000000000 : ℝ)*X 0 0+(4509379201/10000000000 : ℝ)*X 0 1+(106373533/250000000 : ℝ)*X 0 2+(4380263379/10000000000 : ℝ)*X 1 0+(4509379201/10000000000 : ℝ)*X 1 1+(106373533/250000000 : ℝ)*X 1 2+(4380263379/10000000000 : ℝ)*X 2 0+(4509379201/10000000000 : ℝ)*X 2 1+(106373533/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146937426055292265660393207/43812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325251341/50000000000000 : ℝ)*(base19) + (576389537/100000000000000 : ℝ)*(base23) + (20949103/50000000000000 : ℝ)*(lower2) + (81687629/100000000000000 : ℝ)*(upper3) + (54063691/100000000000000 : ℝ)*(upper5) + (5762204157488613/100000000000000 : ℝ)*(major0) + (5762204157488613/100000000000000 : ℝ)*(major1) + (5762204157488613/100000000000000 : ℝ)*(major2) + (3806937755401399/50000000000000 : ℝ)*(sp0) + (190347283215319/2500000000000 : ℝ)*(sp1) + (1522778280545181/20000000000000 : ℝ)*(sp2) + (3910506600071097/100000000000000 : ℝ)*(sp3) + (4117078161/25000000000000 : ℝ)*(sp4) + (9623998059/100000000000000 : ℝ)*(sp7) + (977629056017289/25000000000000 : ℝ)*(f.failure) + (3806945989557721/50000000000000 : ℝ)*(f.sum) + (5280990827929/1752500000000000000000000000 : ℝ)*base65 + (544927002506697977/87625000000000000000000000000000 : ℝ)*base68 + (452227985050697977/87625000000000000000000000000000 : ℝ)*base70 + (485873709254197977/87625000000000000000000000000000 : ℝ)*base72 + (3452676070673/876250000000000000000000000 : ℝ)*base74 + (1790325656261447977/87625000000000000000000000000000 : ℝ)*base76 + (19502083808572977/87625000000000000000000000000000 : ℝ)*base78 + (1786273870916322977/87625000000000000000000000000000 : ℝ)*base80 + (3472765521961/1752500000000000000000000000 : ℝ)*base82 + (1376793/312500000000000000000 : ℝ)*base89 + (1376793/312500000000000000000 : ℝ)*base91 + (1376793/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32603300499132080334789/3505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2036600887/100000000000000 : ℝ)*(base19) + (30518443/1562500000000 : ℝ)*(base23) + (95655273/100000000000000 : ℝ)*(upper2) + (267956227/100000000000000 : ℝ)*(upper3) + (28646207/25000000000000 : ℝ)*(upper5) + (1447814351420013/25000000000000 : ℝ)*(major0) + (1447814351420013/25000000000000 : ℝ)*(major1) + (1447814351420013/25000000000000 : ℝ)*(major2) + (23933573479/50000000000000 : ℝ)*(sp1) + (28930175209/50000000000000 : ℝ)*(sp2) + (7652281308630687/100000000000000 : ℝ)*(sp4) + (3826115702441421/50000000000000 : ℝ)*(sp5) + (7652221495099917/100000000000000 : ℝ)*(sp6) + (3930233192664737/100000000000000 : ℝ)*(sp7) + (3930233192664737/100000000000000 : ℝ)*(f.failure) + (7652281308630687/100000000000000 : ℝ)*(f.sum) + (12400763798457/3505000000000000000000000000 : ℝ)*base65 + (95583493318231077/21906250000000000000000000000000 : ℝ)*base68 + (115714418342456423/21906250000000000000000000000000 : ℝ)*base69 + (60413624662199827/21906250000000000000000000000000 : ℝ)*base72 + (19294276292763/3505000000000000000000000000 : ℝ)*base74 + (188214947671768923/21906250000000000000000000000000 : ℝ)*base75 + (167557437516018923/21906250000000000000000000000000 : ℝ)*base77 + (269747685786762327/21906250000000000000000000000000 : ℝ)*base80 + (17503384486927/3505000000000000000000000000 : ℝ)*base81 + (2924569/1250000000000000000000 : ℝ)*base89 + (2924569/1250000000000000000000 : ℝ)*base91 + (2924569/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1033_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s8_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220119383/10000000000 : ℝ)*x 0 + (134873313/250000000 : ℝ)*x 1 + (1315956831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220119383/10000000000 : ℝ)^4113 ≤ (13480339252203/100000000000000 : ℝ)^3089 := by
    have hnat : (2220119383 : ℕ)^4113*100000000000000^3089 ≤ 13480339252203^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220119383 10000000000 13480339252203 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134873313/250000000 : ℝ)^4113 ≤ (43968301100097/100000000000000 : ℝ)^3089 := by
    have hnat : (134873313 : ℕ)^4113*100000000000000^3089 ≤ 43968301100097^3089*250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134873313 250000000 43968301100097 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315956831/2500000000 : ℝ)^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089 := by
    have hnat : (1315956831 : ℕ)^4113*100000000000000^3089 ≤ 42551359640303^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315956831 2500000000 42551359640303 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220119383/10000000000 : ℝ), (134873313/250000000 : ℝ), (1315956831/2500000000 : ℝ)] ![(13480339252203/100000000000000 : ℝ), (43968301100097/100000000000000 : ℝ), (42551359640303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220119383/10000000000 : ℝ)|^4113 ≤ (13480339252203/100000000000000 : ℝ)^3089
        have hw : |(-2220119383/10000000000 : ℝ)|=(2220119383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134873313/250000000 : ℝ)|^4113 ≤ (43968301100097/100000000000000 : ℝ)^3089
        have hw : |(134873313/250000000 : ℝ)|=(134873313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315956831/2500000000 : ℝ)|^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089
        have hw : |(1315956831/2500000000 : ℝ)|=(1315956831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672523243/5000000000 : ℝ)*x 0 + (-17864431/78125000 : ℝ)*x 1 + (1315956831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672523243/5000000000 : ℝ)^4113 ≤ (8685557672287/20000000000000 : ℝ)^3089 := by
    have hnat : (2672523243 : ℕ)^4113*20000000000000^3089 ≤ 8685557672287^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672523243 5000000000 8685557672287 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17864431/78125000 : ℝ)^4113 ≤ (1752606497911/12500000000000 : ℝ)^3089 := by
    have hnat : (17864431 : ℕ)^4113*12500000000000^3089 ≤ 1752606497911^3089*78125000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17864431 78125000 1752606497911 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315956831/2500000000 : ℝ)^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089 := by
    have hnat : (1315956831 : ℕ)^4113*100000000000000^3089 ≤ 42551359640303^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315956831 2500000000 42551359640303 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672523243/5000000000 : ℝ), (-17864431/78125000 : ℝ), (1315956831/2500000000 : ℝ)] ![(8685557672287/20000000000000 : ℝ), (1752606497911/12500000000000 : ℝ), (42551359640303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672523243/5000000000 : ℝ)|^4113 ≤ (8685557672287/20000000000000 : ℝ)^3089
        have hw : |(2672523243/5000000000 : ℝ)|=(2672523243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17864431/78125000 : ℝ)|^4113 ≤ (1752606497911/12500000000000 : ℝ)^3089
        have hw : |(-17864431/78125000 : ℝ)|=(17864431/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315956831/2500000000 : ℝ)|^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089
        have hw : |(1315956831/2500000000 : ℝ)|=(1315956831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672523243/5000000000 : ℝ)*x 0 + (1315956831/2500000000 : ℝ)*x 1 + (-17864431/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672523243/5000000000 : ℝ)^4113 ≤ (8685557672287/20000000000000 : ℝ)^3089 := by
    have hnat : (2672523243 : ℕ)^4113*20000000000000^3089 ≤ 8685557672287^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672523243 5000000000 8685557672287 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315956831/2500000000 : ℝ)^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089 := by
    have hnat : (1315956831 : ℕ)^4113*100000000000000^3089 ≤ 42551359640303^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315956831 2500000000 42551359640303 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17864431/78125000 : ℝ)^4113 ≤ (1752606497911/12500000000000 : ℝ)^3089 := by
    have hnat : (17864431 : ℕ)^4113*12500000000000^3089 ≤ 1752606497911^3089*78125000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17864431 78125000 1752606497911 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672523243/5000000000 : ℝ), (1315956831/2500000000 : ℝ), (-17864431/78125000 : ℝ)] ![(8685557672287/20000000000000 : ℝ), (42551359640303/100000000000000 : ℝ), (1752606497911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672523243/5000000000 : ℝ)|^4113 ≤ (8685557672287/20000000000000 : ℝ)^3089
        have hw : |(2672523243/5000000000 : ℝ)|=(2672523243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315956831/2500000000 : ℝ)|^4113 ≤ (42551359640303/100000000000000 : ℝ)^3089
        have hw : |(1315956831/2500000000 : ℝ)|=(1315956831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17864431/78125000 : ℝ)|^4113 ≤ (1752606497911/12500000000000 : ℝ)^3089
        have hw : |(-17864431/78125000 : ℝ)|=(17864431/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4380259493/10000000000 : ℝ)*x 0 + (4254525343/10000000000 : ℝ)*x 1 + (4509791083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380259493/10000000000 : ℝ)^4113 ≤ (33316352044573/100000000000000 : ℝ)^3089 := by
    have hnat : (4380259493 : ℕ)^4113*100000000000000^3089 ≤ 33316352044573^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380259493 10000000000 33316352044573 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254525343/10000000000 : ℝ)^4113 ≤ (16024544166681/50000000000000 : ℝ)^3089 := by
    have hnat : (4254525343 : ℕ)^4113*50000000000000^3089 ≤ 16024544166681^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254525343 10000000000 16024544166681 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509791083/10000000000 : ℝ)^4113 ≤ (1082329987873/3125000000000 : ℝ)^3089 := by
    have hnat : (4509791083 : ℕ)^4113*3125000000000^3089 ≤ 1082329987873^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509791083 10000000000 1082329987873 3125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380259493/10000000000 : ℝ), (4254525343/10000000000 : ℝ), (4509791083/10000000000 : ℝ)] ![(33316352044573/100000000000000 : ℝ), (16024544166681/50000000000000 : ℝ), (1082329987873/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380259493/10000000000 : ℝ)|^4113 ≤ (33316352044573/100000000000000 : ℝ)^3089
        have hw : |(4380259493/10000000000 : ℝ)|=(4380259493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254525343/10000000000 : ℝ)|^4113 ≤ (16024544166681/50000000000000 : ℝ)^3089
        have hw : |(4254525343/10000000000 : ℝ)|=(4254525343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509791083/10000000000 : ℝ)|^4113 ≤ (1082329987873/3125000000000 : ℝ)^3089
        have hw : |(4509791083/10000000000 : ℝ)|=(4509791083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110062257/5000000000 : ℝ)*x 0 + (5264155361/10000000000 : ℝ)*x 1 + (5394603317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110062257/5000000000 : ℝ)^4113 ≤ (13480380734947/100000000000000 : ℝ)^3089 := by
    have hnat : (1110062257 : ℕ)^4113*100000000000000^3089 ≤ 13480380734947^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110062257 5000000000 13480380734947 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264155361/10000000000 : ℝ)^4113 ≤ (42554890495653/100000000000000 : ℝ)^3089 := by
    have hnat : (5264155361 : ℕ)^4113*100000000000000^3089 ≤ 42554890495653^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264155361 10000000000 42554890495653 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394603317/10000000000 : ℝ)^4113 ≤ (21982364375629/50000000000000 : ℝ)^3089 := by
    have hnat : (5394603317 : ℕ)^4113*50000000000000^3089 ≤ 21982364375629^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394603317 10000000000 21982364375629 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110062257/5000000000 : ℝ), (5264155361/10000000000 : ℝ), (5394603317/10000000000 : ℝ)] ![(13480380734947/100000000000000 : ℝ), (42554890495653/100000000000000 : ℝ), (21982364375629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110062257/5000000000 : ℝ)|^4113 ≤ (13480380734947/100000000000000 : ℝ)^3089
        have hw : |(-1110062257/5000000000 : ℝ)|=(1110062257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264155361/10000000000 : ℝ)|^4113 ≤ (42554890495653/100000000000000 : ℝ)^3089
        have hw : |(5264155361/10000000000 : ℝ)|=(5264155361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394603317/10000000000 : ℝ)|^4113 ≤ (21982364375629/50000000000000 : ℝ)^3089
        have hw : |(5394603317/10000000000 : ℝ)|=(5394603317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328027867/2500000000 : ℝ)*x 0 + (-538967791/2500000000 : ℝ)*x 1 + (5394603313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328027867/2500000000 : ℝ)^4113 ≤ (43071853485239/100000000000000 : ℝ)^3089 := by
    have hnat : (1328027867 : ℕ)^4113*100000000000000^3089 ≤ 43071853485239^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328027867 2500000000 43071853485239 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538967791/2500000000 : ℝ)^4113 ≤ (6481708897959/50000000000000 : ℝ)^3089 := by
    have hnat : (538967791 : ℕ)^4113*50000000000000^3089 ≤ 6481708897959^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538967791 2500000000 6481708897959 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394603313/10000000000 : ℝ)^4113 ≤ (10991182176963/25000000000000 : ℝ)^3089 := by
    have hnat : (5394603313 : ℕ)^4113*25000000000000^3089 ≤ 10991182176963^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394603313 10000000000 10991182176963 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328027867/2500000000 : ℝ), (-538967791/2500000000 : ℝ), (5394603313/10000000000 : ℝ)] ![(43071853485239/100000000000000 : ℝ), (6481708897959/50000000000000 : ℝ), (10991182176963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328027867/2500000000 : ℝ)|^4113 ≤ (43071853485239/100000000000000 : ℝ)^3089
        have hw : |(1328027867/2500000000 : ℝ)|=(1328027867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538967791/2500000000 : ℝ)|^4113 ≤ (6481708897959/50000000000000 : ℝ)^3089
        have hw : |(-538967791/2500000000 : ℝ)|=(538967791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394603313/10000000000 : ℝ)|^4113 ≤ (10991182176963/25000000000000 : ℝ)^3089
        have hw : |(5394603313/10000000000 : ℝ)|=(5394603313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656055733/5000000000 : ℝ)*x 0 + (2697301659/5000000000 : ℝ)*x 1 + (-53896779/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656055733/5000000000 : ℝ)^4113 ≤ (43071853463647/100000000000000 : ℝ)^3089 := by
    have hnat : (2656055733 : ℕ)^4113*100000000000000^3089 ≤ 43071853463647^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656055733 5000000000 43071853463647 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697301659/5000000000 : ℝ)^4113 ≤ (43964728762109/100000000000000 : ℝ)^3089 := by
    have hnat : (2697301659 : ℕ)^4113*100000000000000^3089 ≤ 43964728762109^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697301659 5000000000 43964728762109 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53896779/250000000 : ℝ)^4113 ≤ (3240854440973/25000000000000 : ℝ)^3089 := by
    have hnat : (53896779 : ℕ)^4113*25000000000000^3089 ≤ 3240854440973^3089*250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53896779 250000000 3240854440973 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656055733/5000000000 : ℝ), (2697301659/5000000000 : ℝ), (-53896779/250000000 : ℝ)] ![(43071853463647/100000000000000 : ℝ), (43964728762109/100000000000000 : ℝ), (3240854440973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656055733/5000000000 : ℝ)|^4113 ≤ (43071853463647/100000000000000 : ℝ)^3089
        have hw : |(2656055733/5000000000 : ℝ)|=(2656055733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697301659/5000000000 : ℝ)|^4113 ≤ (43964728762109/100000000000000 : ℝ)^3089
        have hw : |(2697301659/5000000000 : ℝ)|=(2697301659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53896779/250000000 : ℝ)|^4113 ≤ (3240854440973/25000000000000 : ℝ)^3089
        have hw : |(-53896779/250000000 : ℝ)|=(53896779/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s8_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4380269493/10000000000 : ℝ)*x 0 + (2254576219/5000000000 : ℝ)*x 1 + (851033263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380269493/10000000000 : ℝ)^4113 ≤ (16658226659357/50000000000000 : ℝ)^3089 := by
    have hnat : (4380269493 : ℕ)^4113*50000000000000^3089 ≤ 16658226659357^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380269493 10000000000 16658226659357 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254576219/5000000000 : ℝ)^4113 ≤ (34628029158013/100000000000000 : ℝ)^3089 := by
    have hnat : (2254576219 : ℕ)^4113*100000000000000^3089 ≤ 34628029158013^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254576219 5000000000 34628029158013 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851033263/2000000000 : ℝ)^4113 ≤ (6411103501737/20000000000000 : ℝ)^3089 := by
    have hnat : (851033263 : ℕ)^4113*20000000000000^3089 ≤ 6411103501737^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851033263 2000000000 6411103501737 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380269493/10000000000 : ℝ), (2254576219/5000000000 : ℝ), (851033263/2000000000 : ℝ)] ![(16658226659357/50000000000000 : ℝ), (34628029158013/100000000000000 : ℝ), (6411103501737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380269493/10000000000 : ℝ)|^4113 ≤ (16658226659357/50000000000000 : ℝ)^3089
        have hw : |(4380269493/10000000000 : ℝ)|=(4380269493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254576219/5000000000 : ℝ)|^4113 ≤ (34628029158013/100000000000000 : ℝ)^3089
        have hw : |(2254576219/5000000000 : ℝ)|=(2254576219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(851033263/2000000000 : ℝ)|^4113 ≤ (6411103501737/20000000000000 : ℝ)^3089
        have hw : |(851033263/2000000000 : ℝ)|=(851033263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6991/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (8225/2048 : ℝ) ≤ (950383785090489/6250000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^8225 ≤ (950383785090489/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11203 : ℕ)^8225*6250000000000000000^2048 ≤ 950383785090489^2048*100000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 950383785090489 6250000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (950383785090489/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2797/20000 : ℝ) ^ (8225/2048 : ℝ) ≤ (18529073594816789/50000000000000000000 : ℝ) := by
    have hpowers : (2797/20000 : ℝ)^8225 ≤ (18529073594816789/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2797 : ℕ)^8225*50000000000000000000^2048 ≤ 18529073594816789^2048*20000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2797 20000 18529073594816789 50000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2797/20000 : ℝ)) (X := (18529073594816789/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125950383785090489/3125000000000000000 : ℝ) ≤ (1250094646261729/1250000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (3125950383785090489/3125000000000000000 : ℝ)^2048 ≤ (1250094646261729/1250000000000000 : ℝ)^8225 := by
      have hnat : (3125950383785090489 : ℕ)^2048*1250000000000000^8225 ≤ 1250094646261729^8225*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125950383785090489 3125000000000000000 1250094646261729 1250000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094646261729/1250000000000000 : ℝ)) (X := (3125950383785090489/3125000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026132143875540701/50000000000000000000 : ℝ) ≤ (5000650554780033/5000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50026132143875540701/50000000000000000000 : ℝ)^2048 ≤ (5000650554780033/5000000000000000 : ℝ)^8225 := by
      have hnat : (50026132143875540701 : ℕ)^2048*5000000000000000^8225 ≤ 5000650554780033^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026132143875540701 50000000000000000000 5000650554780033 5000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000650554780033/5000000000000000 : ℝ)) (X := (50026132143875540701/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018529073594816789/25000000000000000000 : ℝ) ≤ (100018450490263/100000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (25018529073594816789/25000000000000000000 : ℝ)^2048 ≤ (100018450490263/100000000000000 : ℝ)^8225 := by
      have hnat : (25018529073594816789 : ℕ)^2048*100000000000000^8225 ≤ 100018450490263^8225*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018529073594816789 25000000000000000000 100018450490263 100000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100018450490263/100000000000000 : ℝ)) (X := (25018529073594816789/25000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(950383785090489/6250000000000000000 : ℝ) ≤ ((1390495946976030081/1391000000000000000 : ℝ)+2*(271969733117/139100000000000 : ℝ)*(11203/100000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1390495946976030081/1391000000000000000 : ℝ)+2*(271969733117/139100000000000 : ℝ)*(11203/100000 : ℝ)=(1250094646261729/1250000000000000 : ℝ) by norm_num, show 1+2*(950383785090489/6250000000000000000 : ℝ)=(3125950383785090489/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18529073594816789/50000000000000000000 : ℝ)+(950383785090489/6250000000000000000 : ℝ) ≤ ((1390495946976030081/1391000000000000000 : ℝ)+(271969733117/139100000000000 : ℝ)*((2797/20000 : ℝ)+(11203/100000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (1390495946976030081/1391000000000000000 : ℝ)+(271969733117/139100000000000 : ℝ)*((2797/20000 : ℝ)+(11203/100000 : ℝ))=(5000650554780033/5000000000000000 : ℝ) by norm_num, show 1+(18529073594816789/50000000000000000000 : ℝ)+(950383785090489/6250000000000000000 : ℝ)=(50026132143875540701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18529073594816789/50000000000000000000 : ℝ) ≤ ((1390495946976030081/1391000000000000000 : ℝ)+2*(271969733117/139100000000000 : ℝ)*(2797/20000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1390495946976030081/1391000000000000000 : ℝ)+2*(271969733117/139100000000000 : ℝ)*(2797/20000 : ℝ)=(100018450490263/100000000000000 : ℝ) by norm_num, show 1+2*(18529073594816789/50000000000000000000 : ℝ)=(25018529073594816789/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1390495946976030081/1391000000000000000 : ℝ)*(X 1 0+X 2 0)+(271969733117/139100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (1390495946976030081/1391000000000000000 : ℝ)) (alpha := (271969733117/139100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1390495946976030081/1391000000000000000 : ℝ)*(X 0 1+X 2 1)+(271969733117/139100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (1390495946976030081/1391000000000000000 : ℝ)) (alpha := (271969733117/139100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1390495946976030081/1391000000000000000 : ℝ)*(X 0 2+X 1 2)+(271969733117/139100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (1390495946976030081/1391000000000000000 : ℝ)) (alpha := (271969733117/139100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2220119383/10000000000 : ℝ)*X 0 0+(134873313/250000000 : ℝ)*X 0 1+(1315956831/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672523243/5000000000 : ℝ)*X 1 0+(-17864431/78125000 : ℝ)*X 1 1+(1315956831/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672523243/5000000000 : ℝ)*X 2 0+(1315956831/2500000000 : ℝ)*X 2 1+(-17864431/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4380259493/10000000000 : ℝ)*X 0 0+(4254525343/10000000000 : ℝ)*X 0 1+(4509791083/10000000000 : ℝ)*X 0 2+(4380259493/10000000000 : ℝ)*X 1 0+(4254525343/10000000000 : ℝ)*X 1 1+(4509791083/10000000000 : ℝ)*X 1 2+(4380259493/10000000000 : ℝ)*X 2 0+(4254525343/10000000000 : ℝ)*X 2 1+(4509791083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1110062257/5000000000 : ℝ)*X 0 0+(5264155361/10000000000 : ℝ)*X 0 1+(5394603317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328027867/2500000000 : ℝ)*X 1 0+(-538967791/2500000000 : ℝ)*X 1 1+(5394603313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656055733/5000000000 : ℝ)*X 2 0+(2697301659/5000000000 : ℝ)*X 2 1+(-53896779/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4380269493/10000000000 : ℝ)*X 0 0+(2254576219/5000000000 : ℝ)*X 0 1+(851033263/2000000000 : ℝ)*X 0 2+(4380269493/10000000000 : ℝ)*X 1 0+(2254576219/5000000000 : ℝ)*X 1 1+(851033263/2000000000 : ℝ)*X 1 2+(4380269493/10000000000 : ℝ)*X 2 0+(2254576219/5000000000 : ℝ)*X 2 1+(851033263/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (502046726173820508155349441/69550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (730708539/50000000000000 : ℝ)*(base19) + (680756807/50000000000000 : ℝ)*(base23) + (26699433/50000000000000 : ℝ)*(lower2) + (1465019/800000000000 : ℝ)*(upper3) + (5425733/5000000000000 : ℝ)*(upper5) + (5772534982758187/100000000000000 : ℝ)*(major0) + (5772534982758187/100000000000000 : ℝ)*(major1) + (5772534982758187/100000000000000 : ℝ)*(major2) + (76275035693373/1000000000000 : ℝ)*(sp0) + (1525508206269537/20000000000000 : ℝ)*(sp1) + (7627541131251149/100000000000000 : ℝ)*(sp2) + (489688202611861/12500000000000 : ℝ)*(sp3) + (4865428433/12500000000000 : ℝ)*(sp4) + (10805620013/50000000000000 : ℝ)*(sp7) + (1958763616067457/50000000000000 : ℝ)*(f.failure) + (7627542492764763/100000000000000 : ℝ)*(f.sum) + (8650333453851/6955000000000000000000000000 : ℝ)*base66 + (687397405561786853/139100000000000000000000000000000 : ℝ)*base68 + (28198273233613147/139100000000000000000000000000000 : ℝ)*base69 + (341208529869386853/139100000000000000000000000000000 : ℝ)*base72 + (18834287389981/6955000000000000000000000000 : ℝ)*base74 + (3998042559586853/139100000000000000000000000000000 : ℝ)*base76 + (228875195675786853/139100000000000000000000000000000 : ℝ)*base78 + (1999546554653013147/139100000000000000000000000000000 : ℝ)*base79 + (36864345721331/6955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9483209/625000000000000000000 : ℝ)*base89 + (9483209/625000000000000000000 : ℝ)*base91 + (9483209/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28036895067311212193451117/5350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76853/8000000000 : ℝ)*(base19) + (1056990511/100000000000000 : ℝ)*(base23) + (339190997/100000000000000 : ℝ)*(lower1) + (1252073/1250000000000 : ℝ)*(upper3) + (42613843/100000000000000 : ℝ)*(lower4) + (85199913/100000000000000 : ℝ)*(upper5) + (5801537209708253/100000000000000 : ℝ)*(major0) + (5801537209708253/100000000000000 : ℝ)*(major1) + (5801537209708253/100000000000000 : ℝ)*(major2) + (3063564487/100000000000000 : ℝ)*(sp2) + (958233083691827/12500000000000 : ℝ)*(sp4) + (1916465927218029/25000000000000 : ℝ)*(sp5) + (7665860548979617/100000000000000 : ℝ)*(sp6) + (787441915039431/20000000000000 : ℝ)*(sp7) + (787441915039431/20000000000000 : ℝ)*(f.failure) + (958233083691827/12500000000000 : ℝ)*(f.sum) + (313581750227/133750000000000000000000000 : ℝ)*base66 + (210605964254412961/10700000000000000000000000000000 : ℝ)*base67 + (92994080562712961/10700000000000000000000000000000 : ℝ)*base69 + (1586148439978512961/10700000000000000000000000000000 : ℝ)*base71 + (2813205733967/535000000000000000000000000 : ℝ)*base73 + (614778809122487039/10700000000000000000000000000000 : ℝ)*base76 + (268007897377312961/10700000000000000000000000000000 : ℝ)*base77 + (182059806858187039/10700000000000000000000000000000 : ℝ)*base80 + (982103258831/267500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (395153/250000000000000000000 : ℝ)*base90 + (395153/250000000000000000000 : ℝ)*base92 + (395153/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1033_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1033_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1033_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1033_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1033_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

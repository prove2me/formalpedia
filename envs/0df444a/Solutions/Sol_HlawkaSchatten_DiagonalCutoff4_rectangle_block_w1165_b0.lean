-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:50.952843+00:00
-- url     : https://prove2.me/submissions/392647a9-559d-42b7-b9d0-33d38397728d

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
theorem support_rectangle_w1165_s0_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37691053/200000000 : ℝ)*x 0 + (1209805907/2000000000 : ℝ)*x 1 + (956674843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37691053/200000000 : ℝ)^4179 ≤ (10963944803989/100000000000000 : ℝ)^3155 := by
    have hnat : (37691053 : ℕ)^4179*100000000000000^3155 ≤ 10963944803989^3155*200000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37691053 200000000 10963944803989 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209805907/2000000000 : ℝ)^4179 ≤ (51384094063331/100000000000000 : ℝ)^3155 := by
    have hnat : (1209805907 : ℕ)^4179*100000000000000^3155 ≤ 51384094063331^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209805907 2000000000 51384094063331 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956674843/2000000000 : ℝ)^4179 ≤ (37651961110361/100000000000000 : ℝ)^3155 := by
    have hnat : (956674843 : ℕ)^4179*100000000000000^3155 ≤ 37651961110361^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956674843 2000000000 37651961110361 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37691053/200000000 : ℝ), (1209805907/2000000000 : ℝ), (956674843/2000000000 : ℝ)] ![(10963944803989/100000000000000 : ℝ), (51384094063331/100000000000000 : ℝ), (37651961110361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37691053/200000000 : ℝ)|^4179 ≤ (10963944803989/100000000000000 : ℝ)^3155
        have hw : |(-37691053/200000000 : ℝ)|=(37691053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209805907/2000000000 : ℝ)|^4179 ≤ (51384094063331/100000000000000 : ℝ)^3155
        have hw : |(1209805907/2000000000 : ℝ)|=(1209805907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956674843/2000000000 : ℝ)|^4179 ≤ (37651961110361/100000000000000 : ℝ)^3155
        have hw : |(956674843/2000000000 : ℝ)|=(956674843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5515497973/10000000000 : ℝ)*x 0 + (-1305120093/5000000000 : ℝ)*x 1 + (2391687089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515497973/10000000000 : ℝ)^4179 ≤ (22734342172451/50000000000000 : ℝ)^3155 := by
    have hnat : (5515497973 : ℕ)^4179*50000000000000^3155 ≤ 22734342172451^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515497973 10000000000 22734342172451 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305120093/5000000000 : ℝ)^4179 ≤ (8439677455807/50000000000000 : ℝ)^3155 := by
    have hnat : (1305120093 : ℕ)^4179*50000000000000^3155 ≤ 8439677455807^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305120093 5000000000 8439677455807 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391687089/5000000000 : ℝ)^4179 ≤ (2353247545287/6250000000000 : ℝ)^3155 := by
    have hnat : (2391687089 : ℕ)^4179*6250000000000^3155 ≤ 2353247545287^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391687089 5000000000 2353247545287 6250000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515497973/10000000000 : ℝ), (-1305120093/5000000000 : ℝ), (2391687089/5000000000 : ℝ)] ![(22734342172451/50000000000000 : ℝ), (8439677455807/50000000000000 : ℝ), (2353247545287/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515497973/10000000000 : ℝ)|^4179 ≤ (22734342172451/50000000000000 : ℝ)^3155
        have hw : |(5515497973/10000000000 : ℝ)|=(5515497973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1305120093/5000000000 : ℝ)|^4179 ≤ (8439677455807/50000000000000 : ℝ)^3155
        have hw : |(-1305120093/5000000000 : ℝ)|=(1305120093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391687089/5000000000 : ℝ)|^4179 ≤ (2353247545287/6250000000000 : ℝ)^3155
        have hw : |(2391687089/5000000000 : ℝ)|=(2391687089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2757748959/5000000000 : ℝ)*x 0 + (4783374253/10000000000 : ℝ)*x 1 + (-522048033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757748959/5000000000 : ℝ)^4179 ≤ (11367170936083/25000000000000 : ℝ)^3155 := by
    have hnat : (2757748959 : ℕ)^4179*25000000000000^3155 ≤ 11367170936083^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757748959 5000000000 11367170936083 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4783374253/10000000000 : ℝ)^4179 ≤ (37651961506557/100000000000000 : ℝ)^3155 := by
    have hnat : (4783374253 : ℕ)^4179*100000000000000^3155 ≤ 37651961506557^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783374253 10000000000 37651961506557 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522048033/2000000000 : ℝ)^4179 ≤ (843967736587/5000000000000 : ℝ)^3155 := by
    have hnat : (522048033 : ℕ)^4179*5000000000000^3155 ≤ 843967736587^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522048033 2000000000 843967736587 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757748959/5000000000 : ℝ), (4783374253/10000000000 : ℝ), (-522048033/2000000000 : ℝ)] ![(11367170936083/25000000000000 : ℝ), (37651961506557/100000000000000 : ℝ), (843967736587/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757748959/5000000000 : ℝ)|^4179 ≤ (11367170936083/25000000000000 : ℝ)^3155
        have hw : |(2757748959/5000000000 : ℝ)|=(2757748959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4783374253/10000000000 : ℝ)|^4179 ≤ (37651961506557/100000000000000 : ℝ)^3155
        have hw : |(4783374253/10000000000 : ℝ)|=(4783374253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522048033/2000000000 : ℝ)|^4179 ≤ (843967736587/5000000000000 : ℝ)^3155
        have hw : |(-522048033/2000000000 : ℝ)|=(522048033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199137003/10000000000 : ℝ)*x 0 + (1560018453/5000000000 : ℝ)*x 1 + (282469487/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199137003/10000000000 : ℝ)^4179 ≤ (7921205865709/25000000000000 : ℝ)^3155 := by
    have hnat : (4199137003 : ℕ)^4179*25000000000000^3155 ≤ 7921205865709^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199137003 10000000000 7921205865709 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560018453/5000000000 : ℝ)^4179 ≤ (10689369793369/50000000000000 : ℝ)^3155 := by
    have hnat : (1560018453 : ℕ)^4179*50000000000000^3155 ≤ 10689369793369^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560018453 5000000000 10689369793369 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282469487/500000000 : ℝ)^4179 ≤ (46936436933163/100000000000000 : ℝ)^3155 := by
    have hnat : (282469487 : ℕ)^4179*100000000000000^3155 ≤ 46936436933163^3155*500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282469487 500000000 46936436933163 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199137003/10000000000 : ℝ), (1560018453/5000000000 : ℝ), (282469487/500000000 : ℝ)] ![(7921205865709/25000000000000 : ℝ), (10689369793369/50000000000000 : ℝ), (46936436933163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199137003/10000000000 : ℝ)|^4179 ≤ (7921205865709/25000000000000 : ℝ)^3155
        have hw : |(4199137003/10000000000 : ℝ)|=(4199137003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560018453/5000000000 : ℝ)|^4179 ≤ (10689369793369/50000000000000 : ℝ)^3155
        have hw : |(1560018453/5000000000 : ℝ)|=(1560018453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282469487/500000000 : ℝ)|^4179 ≤ (46936436933163/100000000000000 : ℝ)^3155
        have hw : |(282469487/500000000 : ℝ)|=(282469487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1889630851/10000000000 : ℝ)*x 0 + (1204003187/2500000000 : ℝ)*x 1 + (6015241831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1889630851/10000000000 : ℝ)^4179 ≤ (11003094754449/100000000000000 : ℝ)^3155 := by
    have hnat : (1889630851 : ℕ)^4179*100000000000000^3155 ≤ 11003094754449^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889630851 10000000000 11003094754449 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204003187/2500000000 : ℝ)^4179 ≤ (18996316686647/50000000000000 : ℝ)^3155 := by
    have hnat : (1204003187 : ℕ)^4179*50000000000000^3155 ≤ 18996316686647^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204003187 2500000000 18996316686647 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015241831/10000000000 : ℝ)^4179 ≤ (25502135931099/50000000000000 : ℝ)^3155 := by
    have hnat : (6015241831 : ℕ)^4179*50000000000000^3155 ≤ 25502135931099^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015241831 10000000000 25502135931099 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1889630851/10000000000 : ℝ), (1204003187/2500000000 : ℝ), (6015241831/10000000000 : ℝ)] ![(11003094754449/100000000000000 : ℝ), (18996316686647/50000000000000 : ℝ), (25502135931099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1889630851/10000000000 : ℝ)|^4179 ≤ (11003094754449/100000000000000 : ℝ)^3155
        have hw : |(-1889630851/10000000000 : ℝ)|=(1889630851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204003187/2500000000 : ℝ)|^4179 ≤ (18996316686647/50000000000000 : ℝ)^3155
        have hw : |(1204003187/2500000000 : ℝ)|=(1204003187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6015241831/10000000000 : ℝ)|^4179 ≤ (25502135931099/50000000000000 : ℝ)^3155
        have hw : |(6015241831/10000000000 : ℝ)|=(6015241831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103429603/200000000 : ℝ)*x 0 + (-137837279/1000000000 : ℝ)*x 1 + (1203048323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103429603/200000000 : ℝ)^4179 ≤ (20875385672639/50000000000000 : ℝ)^3155 := by
    have hnat : (103429603 : ℕ)^4179*50000000000000^3155 ≤ 20875385672639^3155*200000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103429603 200000000 20875385672639 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137837279/1000000000 : ℝ)^4179 ≤ (7244959195749/100000000000000 : ℝ)^3155 := by
    have hnat : (137837279 : ℕ)^4179*100000000000000^3155 ≤ 7244959195749^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137837279 1000000000 7244959195749 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203048323/2000000000 : ℝ)^4179 ≤ (51004269436257/100000000000000 : ℝ)^3155 := by
    have hnat : (1203048323 : ℕ)^4179*100000000000000^3155 ≤ 51004269436257^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203048323 2000000000 51004269436257 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103429603/200000000 : ℝ), (-137837279/1000000000 : ℝ), (1203048323/2000000000 : ℝ)] ![(20875385672639/50000000000000 : ℝ), (7244959195749/100000000000000 : ℝ), (51004269436257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103429603/200000000 : ℝ)|^4179 ≤ (20875385672639/50000000000000 : ℝ)^3155
        have hw : |(103429603/200000000 : ℝ)|=(103429603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137837279/1000000000 : ℝ)|^4179 ≤ (7244959195749/100000000000000 : ℝ)^3155
        have hw : |(-137837279/1000000000 : ℝ)|=(137837279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203048323/2000000000 : ℝ)|^4179 ≤ (51004269436257/100000000000000 : ℝ)^3155
        have hw : |(1203048323/2000000000 : ℝ)|=(1203048323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585740059/5000000000 : ℝ)*x 0 + (751905213/1250000000 : ℝ)*x 1 + (-1378372697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585740059/5000000000 : ℝ)^4179 ≤ (10437692750771/25000000000000 : ℝ)^3155 := by
    have hnat : (2585740059 : ℕ)^4179*25000000000000^3155 ≤ 10437692750771^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585740059 5000000000 10437692750771 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751905213/1250000000 : ℝ)^4179 ≤ (25502135217917/50000000000000 : ℝ)^3155 := by
    have hnat : (751905213 : ℕ)^4179*50000000000000^3155 ≤ 25502135217917^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751905213 1250000000 25502135217917 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378372697/10000000000 : ℝ)^4179 ≤ (7244958548271/100000000000000 : ℝ)^3155 := by
    have hnat : (1378372697 : ℕ)^4179*100000000000000^3155 ≤ 7244958548271^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378372697 10000000000 7244958548271 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585740059/5000000000 : ℝ), (751905213/1250000000 : ℝ), (-1378372697/10000000000 : ℝ)] ![(10437692750771/25000000000000 : ℝ), (25502135217917/50000000000000 : ℝ), (7244958548271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585740059/5000000000 : ℝ)|^4179 ≤ (10437692750771/25000000000000 : ℝ)^3155
        have hw : |(2585740059/5000000000 : ℝ)|=(2585740059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751905213/1250000000 : ℝ)|^4179 ≤ (25502135217917/50000000000000 : ℝ)^3155
        have hw : |(751905213/1250000000 : ℝ)|=(751905213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378372697/10000000000 : ℝ)|^4179 ≤ (7244958548271/100000000000000 : ℝ)^3155
        have hw : |(-1378372697/10000000000 : ℝ)|=(1378372697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s0_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (841857167/2000000000 : ℝ)*x 0 + (1396040747/2500000000 : ℝ)*x 1 + (3187560237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841857167/2000000000 : ℝ)^4179 ≤ (31786296469817/100000000000000 : ℝ)^3155 := by
    have hnat : (841857167 : ℕ)^4179*100000000000000^3155 ≤ 31786296469817^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841857167 2000000000 31786296469817 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396040747/2500000000 : ℝ)^4179 ≤ (46219978958001/100000000000000 : ℝ)^3155 := by
    have hnat : (1396040747 : ℕ)^4179*100000000000000^3155 ≤ 46219978958001^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396040747 2500000000 46219978958001 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187560237/10000000000 : ℝ)^4179 ≤ (2749215568927/12500000000000 : ℝ)^3155 := by
    have hnat : (3187560237 : ℕ)^4179*12500000000000^3155 ≤ 2749215568927^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187560237 10000000000 2749215568927 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841857167/2000000000 : ℝ), (1396040747/2500000000 : ℝ), (3187560237/10000000000 : ℝ)] ![(31786296469817/100000000000000 : ℝ), (46219978958001/100000000000000 : ℝ), (2749215568927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841857167/2000000000 : ℝ)|^4179 ≤ (31786296469817/100000000000000 : ℝ)^3155
        have hw : |(841857167/2000000000 : ℝ)|=(841857167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396040747/2500000000 : ℝ)|^4179 ≤ (46219978958001/100000000000000 : ℝ)^3155
        have hw : |(1396040747/2500000000 : ℝ)|=(1396040747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187560237/10000000000 : ℝ)|^4179 ≤ (2749215568927/12500000000000 : ℝ)^3155
        have hw : |(3187560237/10000000000 : ℝ)|=(3187560237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (127/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8357/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8357 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8357*1^2048 ≤ 0^2048*1^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8357/2048 : ℝ) ≤ (148613884584808137/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8357 ≤ (148613884584808137/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8357*6250000000000000000^2048 ≤ 148613884584808137^2048*5^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 148613884584808137 6250000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (148613884584808137/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8357 := by
      have hnat : (1 : ℕ)^2048*1^8357 ≤ 1^8357*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6398613884584808137/6250000000000000000 : ℝ) ≤ (5028878001511889/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (6398613884584808137/6250000000000000000 : ℝ)^2048 ≤ (5028878001511889/5000000000000000 : ℝ)^8357 := by
      have hnat : (6398613884584808137 : ℕ)^2048*5000000000000000^8357 ≤ 5028878001511889^8357*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6398613884584808137 6250000000000000000 5028878001511889 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028878001511889/5000000000000000 : ℝ)) (X := (6398613884584808137/6250000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3273613884584808137/3125000000000000000 : ℝ) ≤ (2528878001511889/2500000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (3273613884584808137/3125000000000000000 : ℝ)^2048 ≤ (2528878001511889/2500000000000000 : ℝ)^8357 := by
      have hnat : (3273613884584808137 : ℕ)^2048*2500000000000000^8357 ≤ 2528878001511889^8357*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3273613884584808137 3125000000000000000 2528878001511889 2500000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528878001511889/2500000000000000 : ℝ)) (X := (3273613884584808137/3125000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28878001511889/2000000000000000 : ℝ)*(0 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28878001511889/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(148613884584808137/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28878001511889/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28878001511889/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028878001511889/5000000000000000 : ℝ) by norm_num, show 1+(148613884584808137/6250000000000000000 : ℝ)+(0 : ℝ)=(6398613884584808137/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(148613884584808137/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28878001511889/2000000000000000 : ℝ)*(2/5 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28878001511889/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528878001511889/2500000000000000 : ℝ) by norm_num, show 1+2*(148613884584808137/6250000000000000000 : ℝ)=(3273613884584808137/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28878001511889/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28878001511889/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28878001511889/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28878001511889/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28878001511889/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28878001511889/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37691053/200000000 : ℝ)*X 0 0+(1209805907/2000000000 : ℝ)*X 0 1+(956674843/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5515497973/10000000000 : ℝ)*X 1 0+(-1305120093/5000000000 : ℝ)*X 1 1+(2391687089/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757748959/5000000000 : ℝ)*X 2 0+(4783374253/10000000000 : ℝ)*X 2 1+(-522048033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199137003/10000000000 : ℝ)*X 0 0+(1560018453/5000000000 : ℝ)*X 0 1+(282469487/500000000 : ℝ)*X 0 2+(4199137003/10000000000 : ℝ)*X 1 0+(1560018453/5000000000 : ℝ)*X 1 1+(282469487/500000000 : ℝ)*X 1 2+(4199137003/10000000000 : ℝ)*X 2 0+(1560018453/5000000000 : ℝ)*X 2 1+(282469487/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1889630851/10000000000 : ℝ)*X 0 0+(1204003187/2500000000 : ℝ)*X 0 1+(6015241831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((103429603/200000000 : ℝ)*X 1 0+(-137837279/1000000000 : ℝ)*X 1 1+(1203048323/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585740059/5000000000 : ℝ)*X 2 0+(751905213/1250000000 : ℝ)*X 2 1+(-1378372697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841857167/2000000000 : ℝ)*X 0 0+(1396040747/2500000000 : ℝ)*X 0 1+(3187560237/10000000000 : ℝ)*X 0 2+(841857167/2000000000 : ℝ)*X 1 0+(1396040747/2500000000 : ℝ)*X 1 1+(3187560237/10000000000 : ℝ)*X 1 2+(841857167/2000000000 : ℝ)*X 2 0+(1396040747/2500000000 : ℝ)*X 2 1+(3187560237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7998613316224215361239/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3316089/12500000000000 : ℝ)*(base1) + (824575237/100000000000000 : ℝ)*(base19) + (190051049/25000000000000 : ℝ)*(base23) + (28246079/50000000000000 : ℝ)*(base24) + (92971643/50000000000000 : ℝ)*(upper3) + (74091852852783/12500000000000 : ℝ)*(major0) + (74091852852783/12500000000000 : ℝ)*(major1) + (74091852852783/12500000000000 : ℝ)*(major2) + (790107324037301/100000000000000 : ℝ)*(sp0) + (197527082150237/25000000000000 : ℝ)*(sp1) + (79010833647983/10000000000000 : ℝ)*(sp2) + (395358910686657/100000000000000 : ℝ)*(sp3) + (371133519/20000000000000 : ℝ)*(sp4) + (181075599/12500000000000 : ℝ)*(sp7) + (395360385820161/100000000000000 : ℝ)*(f.failure) + (98763644147023/12500000000000 : ℝ)*(f.sum) + (24611500037087/12500000000000000000000000000 : ℝ)*base65 + (71572045412087/25000000000000000000000000000 : ℝ)*base67 + (132433865137087/25000000000000000000000000000 : ℝ)*base69 + (33650023862087/25000000000000000000000000000 : ℝ)*base71 + (28037923612087/12500000000000000000000000000 : ℝ)*base73 + (26385149462913/25000000000000000000000000000 : ℝ)*base76 + (53797135462087/25000000000000000000000000000 : ℝ)*base77 + (153706273037087/25000000000000000000000000000 : ℝ)*base79 + (30551954562087/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4746387/1250000000000000000000 : ℝ)*base90 + (4746387/1250000000000000000000 : ℝ)*base92 + (4746387/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (210572552557029949338567/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55197887/100000000000000 : ℝ)*(base1) + (4204927/400000000000 : ℝ)*(base19) + (261628531/25000000000000 : ℝ)*(base23) + (54497707/50000000000000 : ℝ)*(upper3) + (127343063/100000000000000 : ℝ)*(upper5) + (312781635769567/50000000000000 : ℝ)*(major0) + (312781635769567/50000000000000 : ℝ)*(major1) + (312781635769567/50000000000000 : ℝ)*(major2) + (1049953081/50000000000000 : ℝ)*(sp1) + (2106553251/100000000000000 : ℝ)*(sp2) + (104233643765917/12500000000000 : ℝ)*(sp4) + (52116621486971/6250000000000 : ℝ)*(sp5) + (416932970931037/50000000000000 : ℝ)*(sp6) + (208628626284613/50000000000000 : ℝ)*(sp7) + (417257307767113/100000000000000 : ℝ)*(f.failure) + (833869094929449/100000000000000 : ℝ)*(f.sum) + (113385523817937/50000000000000000000000000000 : ℝ)*base66 + (303280646717937/100000000000000000000000000000 : ℝ)*base68 + (266777862917937/100000000000000000000000000000 : ℝ)*base70 + (218154641282063/100000000000000000000000000000 : ℝ)*base71 + (139695770917937/50000000000000000000000000000 : ℝ)*base74 + (194984188917937/100000000000000000000000000000 : ℝ)*base76 + (329110971117937/100000000000000000000000000000 : ℝ)*base78 + (738110773817937/100000000000000000000000000000 : ℝ)*base80 + (6620686432063/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9068629/1250000000000000000000 : ℝ)*base89 + (9068629/1250000000000000000000 : ℝ)*base91 + (9068629/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (127/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s1_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13047209/62500000 : ℝ)*x 0 + (5695400009/10000000000 : ℝ)*x 1 + (2503525379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13047209/62500000 : ℝ)^4179 ≤ (1255498897033/10000000000000 : ℝ)^3155 := by
    have hnat : (13047209 : ℕ)^4179*10000000000000^3155 ≤ 1255498897033^3155*62500000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13047209 62500000 1255498897033 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5695400009/10000000000 : ℝ)^4179 ≤ (11860859516491/25000000000000 : ℝ)^3155 := by
    have hnat : (5695400009 : ℕ)^4179*25000000000000^3155 ≤ 11860859516491^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5695400009 10000000000 11860859516491 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503525379/5000000000 : ℝ)^4179 ≤ (40001572949001/100000000000000 : ℝ)^3155 := by
    have hnat : (2503525379 : ℕ)^4179*100000000000000^3155 ≤ 40001572949001^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503525379 5000000000 40001572949001 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13047209/62500000 : ℝ), (5695400009/10000000000 : ℝ), (2503525379/5000000000 : ℝ)] ![(1255498897033/10000000000000 : ℝ), (11860859516491/25000000000000 : ℝ), (40001572949001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13047209/62500000 : ℝ)|^4179 ≤ (1255498897033/10000000000000 : ℝ)^3155
        have hw : |(-13047209/62500000 : ℝ)|=(13047209/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5695400009/10000000000 : ℝ)|^4179 ≤ (11860859516491/25000000000000 : ℝ)^3155
        have hw : |(5695400009/10000000000 : ℝ)|=(5695400009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503525379/5000000000 : ℝ)|^4179 ≤ (40001572949001/100000000000000 : ℝ)^3155
        have hw : |(2503525379/5000000000 : ℝ)|=(2503525379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216714383/400000000 : ℝ)*x 0 + (-2458591873/10000000000 : ℝ)*x 1 + (25035249/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216714383/400000000 : ℝ)^4179 ≤ (22202801071891/50000000000000 : ℝ)^3155 := by
    have hnat : (216714383 : ℕ)^4179*50000000000000^3155 ≤ 22202801071891^3155*400000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216714383 400000000 22202801071891 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458591873/10000000000 : ℝ)^4179 ≤ (7796417511731/50000000000000 : ℝ)^3155 := by
    have hnat : (2458591873 : ℕ)^4179*50000000000000^3155 ≤ 7796417511731^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458591873 10000000000 7796417511731 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25035249/50000000 : ℝ)^4179 ≤ (40001562811437/100000000000000 : ℝ)^3155 := by
    have hnat : (25035249 : ℕ)^4179*100000000000000^3155 ≤ 40001562811437^3155*50000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25035249 50000000 40001562811437 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216714383/400000000 : ℝ), (-2458591873/10000000000 : ℝ), (25035249/50000000 : ℝ)] ![(22202801071891/50000000000000 : ℝ), (7796417511731/50000000000000 : ℝ), (40001562811437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216714383/400000000 : ℝ)|^4179 ≤ (22202801071891/50000000000000 : ℝ)^3155
        have hw : |(216714383/400000000 : ℝ)|=(216714383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2458591873/10000000000 : ℝ)|^4179 ≤ (7796417511731/50000000000000 : ℝ)^3155
        have hw : |(-2458591873/10000000000 : ℝ)|=(2458591873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25035249/50000000 : ℝ)|^4179 ≤ (40001562811437/100000000000000 : ℝ)^3155
        have hw : |(25035249/50000000 : ℝ)|=(25035249/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541786169/1000000000 : ℝ)*x 0 + (5007047861/10000000000 : ℝ)*x 1 + (-76830987/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541786169/1000000000 : ℝ)^4179 ≤ (44405625104921/100000000000000 : ℝ)^3155 := by
    have hnat : (541786169 : ℕ)^4179*100000000000000^3155 ≤ 44405625104921^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541786169 1000000000 44405625104921 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007047861/10000000000 : ℝ)^4179 ≤ (40001542292927/100000000000000 : ℝ)^3155 := by
    have hnat : (5007047861 : ℕ)^4179*100000000000000^3155 ≤ 40001542292927^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007047861 10000000000 40001542292927 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76830987/312500000 : ℝ)^4179 ≤ (15592832595681/100000000000000 : ℝ)^3155 := by
    have hnat : (76830987 : ℕ)^4179*100000000000000^3155 ≤ 15592832595681^3155*312500000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76830987 312500000 15592832595681 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541786169/1000000000 : ℝ), (5007047861/10000000000 : ℝ), (-76830987/312500000 : ℝ)] ![(44405625104921/100000000000000 : ℝ), (40001542292927/100000000000000 : ℝ), (15592832595681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541786169/1000000000 : ℝ)|^4179 ≤ (44405625104921/100000000000000 : ℝ)^3155
        have hw : |(541786169/1000000000 : ℝ)|=(541786169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007047861/10000000000 : ℝ)|^4179 ≤ (40001542292927/100000000000000 : ℝ)^3155
        have hw : |(5007047861/10000000000 : ℝ)|=(5007047861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76830987/312500000 : ℝ)|^4179 ≤ (15592832595681/100000000000000 : ℝ)^3155
        have hw : |(-76830987/312500000 : ℝ)|=(76830987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315486763/10000000000 : ℝ)*x 0 + (736269923/2000000000 : ℝ)*x 1 + (5056978673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315486763/10000000000 : ℝ)^4179 ≤ (32852886259931/100000000000000 : ℝ)^3155 := by
    have hnat : (4315486763 : ℕ)^4179*100000000000000^3155 ≤ 32852886259931^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315486763 10000000000 32852886259931 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736269923/2000000000 : ℝ)^4179 ≤ (6654087533417/25000000000000 : ℝ)^3155 := by
    have hnat : (736269923 : ℕ)^4179*25000000000000^3155 ≤ 6654087533417^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736269923 2000000000 6654087533417 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056978673/10000000000 : ℝ)^4179 ≤ (5066345448197/12500000000000 : ℝ)^3155 := by
    have hnat : (5056978673 : ℕ)^4179*12500000000000^3155 ≤ 5066345448197^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056978673 10000000000 5066345448197 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315486763/10000000000 : ℝ), (736269923/2000000000 : ℝ), (5056978673/10000000000 : ℝ)] ![(32852886259931/100000000000000 : ℝ), (6654087533417/25000000000000 : ℝ), (5066345448197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315486763/10000000000 : ℝ)|^4179 ≤ (32852886259931/100000000000000 : ℝ)^3155
        have hw : |(4315486763/10000000000 : ℝ)|=(4315486763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736269923/2000000000 : ℝ)|^4179 ≤ (6654087533417/25000000000000 : ℝ)^3155
        have hw : |(736269923/2000000000 : ℝ)|=(736269923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5056978673/10000000000 : ℝ)|^4179 ≤ (5066345448197/12500000000000 : ℝ)^3155
        have hw : |(5056978673/10000000000 : ℝ)|=(5056978673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-522083061/2500000000 : ℝ)*x 0 + (2508183599/5000000000 : ℝ)*x 1 + (113717949/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522083061/2500000000 : ℝ)^4179 ≤ (6280596730993/50000000000000 : ℝ)^3155 := by
    have hnat : (522083061 : ℕ)^4179*50000000000000^3155 ≤ 6280596730993^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522083061 2500000000 6280596730993 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508183599/5000000000 : ℝ)^4179 ≤ (40100189346977/100000000000000 : ℝ)^3155 := by
    have hnat : (2508183599 : ℕ)^4179*100000000000000^3155 ≤ 40100189346977^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508183599 5000000000 40100189346977 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113717949/200000000 : ℝ)^4179 ≤ (2366930858667/5000000000000 : ℝ)^3155 := by
    have hnat : (113717949 : ℕ)^4179*5000000000000^3155 ≤ 2366930858667^3155*200000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113717949 200000000 2366930858667 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522083061/2500000000 : ℝ), (2508183599/5000000000 : ℝ), (113717949/200000000 : ℝ)] ![(6280596730993/50000000000000 : ℝ), (40100189346977/100000000000000 : ℝ), (2366930858667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522083061/2500000000 : ℝ)|^4179 ≤ (6280596730993/50000000000000 : ℝ)^3155
        have hw : |(-522083061/2500000000 : ℝ)|=(522083061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508183599/5000000000 : ℝ)|^4179 ≤ (40100189346977/100000000000000 : ℝ)^3155
        have hw : |(2508183599/5000000000 : ℝ)|=(2508183599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113717949/200000000 : ℝ)|^4179 ≤ (2366930858667/5000000000000 : ℝ)^3155
        have hw : |(113717949/200000000 : ℝ)|=(113717949/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5241176987/10000000000 : ℝ)*x 0 + (-444935213/2500000000 : ℝ)*x 1 + (1421475153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241176987/10000000000 : ℝ)^4179 ≤ (8499540875897/20000000000000 : ℝ)^3155 := by
    have hnat : (5241176987 : ℕ)^4179*20000000000000^3155 ≤ 8499540875897^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241176987 10000000000 8499540875897 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444935213/2500000000 : ℝ)^4179 ≤ (10163643561821/100000000000000 : ℝ)^3155 := by
    have hnat : (444935213 : ℕ)^4179*100000000000000^3155 ≤ 10163643561821^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444935213 2500000000 10163643561821 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1421475153/2500000000 : ℝ)^4179 ≤ (47338652043301/100000000000000 : ℝ)^3155 := by
    have hnat : (1421475153 : ℕ)^4179*100000000000000^3155 ≤ 47338652043301^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421475153 2500000000 47338652043301 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241176987/10000000000 : ℝ), (-444935213/2500000000 : ℝ), (1421475153/2500000000 : ℝ)] ![(8499540875897/20000000000000 : ℝ), (10163643561821/100000000000000 : ℝ), (47338652043301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241176987/10000000000 : ℝ)|^4179 ≤ (8499540875897/20000000000000 : ℝ)^3155
        have hw : |(5241176987/10000000000 : ℝ)|=(5241176987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444935213/2500000000 : ℝ)|^4179 ≤ (10163643561821/100000000000000 : ℝ)^3155
        have hw : |(-444935213/2500000000 : ℝ)|=(444935213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1421475153/2500000000 : ℝ)|^4179 ≤ (47338652043301/100000000000000 : ℝ)^3155
        have hw : |(1421475153/2500000000 : ℝ)|=(1421475153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524117613/1000000000 : ℝ)*x 0 + (710737749/1250000000 : ℝ)*x 1 + (-222467507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524117613/1000000000 : ℝ)^4179 ≤ (5312211896899/12500000000000 : ℝ)^3155 := by
    have hnat : (524117613 : ℕ)^4179*12500000000000^3155 ≤ 5312211896899^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524117613 1000000000 5312211896899 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710737749/1250000000 : ℝ)^4179 ≤ (47338667261691/100000000000000 : ℝ)^3155 := by
    have hnat : (710737749 : ℕ)^4179*100000000000000^3155 ≤ 47338667261691^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710737749 1250000000 47338667261691 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222467507/1250000000 : ℝ)^4179 ≤ (10163637540681/100000000000000 : ℝ)^3155 := by
    have hnat : (222467507 : ℕ)^4179*100000000000000^3155 ≤ 10163637540681^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222467507 1250000000 10163637540681 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524117613/1000000000 : ℝ), (710737749/1250000000 : ℝ), (-222467507/1250000000 : ℝ)] ![(5312211896899/12500000000000 : ℝ), (47338667261691/100000000000000 : ℝ), (10163637540681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524117613/1000000000 : ℝ)|^4179 ≤ (5312211896899/12500000000000 : ℝ)^3155
        have hw : |(524117613/1000000000 : ℝ)|=(524117613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710737749/1250000000 : ℝ)|^4179 ≤ (47338667261691/100000000000000 : ℝ)^3155
        have hw : |(710737749/1250000000 : ℝ)|=(710737749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222467507/1250000000 : ℝ)|^4179 ≤ (10163637540681/100000000000000 : ℝ)^3155
        have hw : |(-222467507/1250000000 : ℝ)|=(222467507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s1_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863406283/2000000000 : ℝ)*x 0 + (1259590673/2500000000 : ℝ)*x 1 + (3700331497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863406283/2000000000 : ℝ)^4179 ≤ (32868462858353/100000000000000 : ℝ)^3155 := by
    have hnat : (863406283 : ℕ)^4179*100000000000000^3155 ≤ 32868462858353^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863406283 2000000000 32868462858353 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259590673/2500000000 : ℝ)^4179 ≤ (40333251871653/100000000000000 : ℝ)^3155 := by
    have hnat : (1259590673 : ℕ)^4179*100000000000000^3155 ≤ 40333251871653^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259590673 2500000000 40333251871653 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3700331497/10000000000 : ℝ)^4179 ≤ (13399142627151/50000000000000 : ℝ)^3155 := by
    have hnat : (3700331497 : ℕ)^4179*50000000000000^3155 ≤ 13399142627151^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700331497 10000000000 13399142627151 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863406283/2000000000 : ℝ), (1259590673/2500000000 : ℝ), (3700331497/10000000000 : ℝ)] ![(32868462858353/100000000000000 : ℝ), (40333251871653/100000000000000 : ℝ), (13399142627151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863406283/2000000000 : ℝ)|^4179 ≤ (32868462858353/100000000000000 : ℝ)^3155
        have hw : |(863406283/2000000000 : ℝ)|=(863406283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1259590673/2500000000 : ℝ)|^4179 ≤ (40333251871653/100000000000000 : ℝ)^3155
        have hw : |(1259590673/2500000000 : ℝ)|=(1259590673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3700331497/10000000000 : ℝ)|^4179 ≤ (13399142627151/50000000000000 : ℝ)^3155
        have hw : |(3700331497/10000000000 : ℝ)|=(3700331497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (127/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5777/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10167/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (127/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (127/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (127/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (127/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (127/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (127/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (127/25000 : ℝ) ^ (8357/2048 : ℝ) ≤ (4351355169/10000000000000000000 : ℝ) := by
    have hpowers : (127/25000 : ℝ)^8357 ≤ (4351355169/10000000000000000000 : ℝ)^2048 := by
      have hnat : (127 : ℕ)^8357*10000000000000000000^2048 ≤ 4351355169^2048*25000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127 25000 4351355169 10000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (127/25000 : ℝ)) (X := (4351355169/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27727/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (533001237038426269/100000000000000000000 : ℝ) := by
    have hpowers : (27727/100000 : ℝ)^8357 ≤ (533001237038426269/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27727 : ℕ)^8357*100000000000000000000^2048 ≤ 533001237038426269^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27727 100000 533001237038426269 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27727/100000 : ℝ)) (X := (533001237038426269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000004351355169/5000000000000000000 : ℝ) ≤ (5000000001066361/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (5000000004351355169/5000000000000000000 : ℝ)^2048 ≤ (5000000001066361/5000000000000000 : ℝ)^8357 := by
      have hnat : (5000000004351355169 : ℕ)^2048*5000000000000000^8357 ≤ 5000000001066361^8357*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000004351355169 5000000000000000000 5000000001066361 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000001066361/5000000000000000 : ℝ)) (X := (5000000004351355169/5000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100533001280551977959/100000000000000000000 : ℝ) ≤ (1001303574574467/1000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (100533001280551977959/100000000000000000000 : ℝ)^2048 ≤ (1001303574574467/1000000000000000 : ℝ)^8357 := by
      have hnat : (100533001280551977959 : ℕ)^2048*1000000000000000^8357 ≤ 1001303574574467^8357*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100533001280551977959 100000000000000000000 1001303574574467 1000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001303574574467/1000000000000000 : ℝ)) (X := (100533001280551977959/100000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50533001237038426269/50000000000000000000 : ℝ) ≤ (5013035744678309/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50533001237038426269/50000000000000000000 : ℝ)^2048 ≤ (5013035744678309/5000000000000000 : ℝ)^8357 := by
      have hnat : (50533001237038426269 : ℕ)^2048*5000000000000000^8357 ≤ 5013035744678309^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50533001237038426269 50000000000000000000 5013035744678309 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013035744678309/5000000000000000 : ℝ)) (X := (50533001237038426269/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4351355169/10000000000000000000 : ℝ) ≤ ((5443535114850816419/5443800000000000000 : ℝ)+2*(3258935902987/680475000000000 : ℝ)*(127/25000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (5443535114850816419/5443800000000000000 : ℝ)+2*(3258935902987/680475000000000 : ℝ)*(127/25000 : ℝ)=(5000000001066361/5000000000000000 : ℝ) by norm_num, show 1+2*(4351355169/10000000000000000000 : ℝ)=(5000000004351355169/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(533001237038426269/100000000000000000000 : ℝ)+(4351355169/10000000000000000000 : ℝ) ≤ ((5443535114850816419/5443800000000000000 : ℝ)+(3258935902987/680475000000000 : ℝ)*((27727/100000 : ℝ)+(127/25000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (5443535114850816419/5443800000000000000 : ℝ)+(3258935902987/680475000000000 : ℝ)*((27727/100000 : ℝ)+(127/25000 : ℝ))=(1001303574574467/1000000000000000 : ℝ) by norm_num, show 1+(533001237038426269/100000000000000000000 : ℝ)+(4351355169/10000000000000000000 : ℝ)=(100533001280551977959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(533001237038426269/100000000000000000000 : ℝ) ≤ ((5443535114850816419/5443800000000000000 : ℝ)+2*(3258935902987/680475000000000 : ℝ)*(27727/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (5443535114850816419/5443800000000000000 : ℝ)+2*(3258935902987/680475000000000 : ℝ)*(27727/100000 : ℝ)=(5013035744678309/5000000000000000 : ℝ) by norm_num, show 1+2*(533001237038426269/100000000000000000000 : ℝ)=(50533001237038426269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5443535114850816419/5443800000000000000 : ℝ)*(X 1 0+X 2 0)+(3258935902987/680475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (127/25000 : ℝ)) (hi := (27727/100000 : ℝ)) (c := (5443535114850816419/5443800000000000000 : ℝ)) (alpha := (3258935902987/680475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5443535114850816419/5443800000000000000 : ℝ)*(X 0 1+X 2 1)+(3258935902987/680475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (127/25000 : ℝ)) (hi := (27727/100000 : ℝ)) (c := (5443535114850816419/5443800000000000000 : ℝ)) (alpha := (3258935902987/680475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5443535114850816419/5443800000000000000 : ℝ)*(X 0 2+X 1 2)+(3258935902987/680475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (127/25000 : ℝ)) (hi := (27727/100000 : ℝ)) (c := (5443535114850816419/5443800000000000000 : ℝ)) (alpha := (3258935902987/680475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13047209/62500000 : ℝ)*X 0 0+(5695400009/10000000000 : ℝ)*X 0 1+(2503525379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((216714383/400000000 : ℝ)*X 1 0+(-2458591873/10000000000 : ℝ)*X 1 1+(25035249/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541786169/1000000000 : ℝ)*X 2 0+(5007047861/10000000000 : ℝ)*X 2 1+(-76830987/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315486763/10000000000 : ℝ)*X 0 0+(736269923/2000000000 : ℝ)*X 0 1+(5056978673/10000000000 : ℝ)*X 0 2+(4315486763/10000000000 : ℝ)*X 1 0+(736269923/2000000000 : ℝ)*X 1 1+(5056978673/10000000000 : ℝ)*X 1 2+(4315486763/10000000000 : ℝ)*X 2 0+(736269923/2000000000 : ℝ)*X 2 1+(5056978673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-522083061/2500000000 : ℝ)*X 0 0+(2508183599/5000000000 : ℝ)*X 0 1+(113717949/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241176987/10000000000 : ℝ)*X 1 0+(-444935213/2500000000 : ℝ)*X 1 1+(1421475153/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524117613/1000000000 : ℝ)*X 2 0+(710737749/1250000000 : ℝ)*X 2 1+(-222467507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863406283/2000000000 : ℝ)*X 0 0+(1259590673/2500000000 : ℝ)*X 0 1+(3700331497/10000000000 : ℝ)*X 0 2+(863406283/2000000000 : ℝ)*X 1 0+(1259590673/2500000000 : ℝ)*X 1 1+(3700331497/10000000000 : ℝ)*X 1 2+(863406283/2000000000 : ℝ)*X 2 0+(1259590673/2500000000 : ℝ)*X 2 1+(3700331497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (719618571335475929654395229/90730000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83490071/10000000000000 : ℝ)*(base1) + (1390693281/100000000000000 : ℝ)*(base19) + (8155151/400000000000 : ℝ)*(base23) + (34655461/25000000000000 : ℝ)*(upper3) + (347991/4000000000000 : ℝ)*(upper5) + (1089847524053009/100000000000000 : ℝ)*(major0) + (1089847524053009/100000000000000 : ℝ)*(major1) + (1089847524053009/100000000000000 : ℝ)*(major2) + (58110134015019/4000000000000 : ℝ)*(sp0) + (1452751103163333/100000000000000 : ℝ)*(sp1) + (290550587624523/20000000000000 : ℝ)*(sp2) + (726938971913961/100000000000000 : ℝ)*(sp3) + (2461435601/100000000000000 : ℝ)*(sp4) + (310381719/12500000000000 : ℝ)*(sp5) + (726939806814671/100000000000000 : ℝ)*(f.failure) + (290550995382073/20000000000000 : ℝ)*(f.sum) + (398083030205627/136095000000000000000000000000 : ℝ)*base65 + (162591288394821229/544380000000000000000000000000000 : ℝ)*base68 + (586152116521521229/544380000000000000000000000000000 : ℝ)*base70 + (1022035851100658771/544380000000000000000000000000000 : ℝ)*base71 + (48931060326329/68047500000000000000000000000 : ℝ)*base74 + (2003897891215358771/544380000000000000000000000000000 : ℝ)*base75 + (2447358431709278771/544380000000000000000000000000000 : ℝ)*base77 + (7743286349085218771/544380000000000000000000000000000 : ℝ)*base79 + (353731062647803/136095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (8674557/1250000000000000000000 : ℝ)*base90 + (8674557/1250000000000000000000 : ℝ)*base92 + (8674557/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (193986509840228108712929/45365000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2576108317/100000000000000 : ℝ)*(base19) + (3216453453/100000000000000 : ℝ)*(base23) + (44428441/12500000000000 : ℝ)*(upper2) + (626064913/100000000000000 : ℝ)*(upper3) + (329059117/100000000000000 : ℝ)*(upper5) + (560236696170251/50000000000000 : ℝ)*(major0) + (560236696170251/50000000000000 : ℝ)*(major1) + (560236696170251/50000000000000 : ℝ)*(major2) + (7052827359/50000000000000 : ℝ)*(sp1) + (20228619631/100000000000000 : ℝ)*(sp2) + (1866973822233/125000000000 : ℝ)*(sp4) + (746781188011683/50000000000000 : ℝ)*(sp5) + (373388903178329/25000000000000 : ℝ)*(sp6) + (747367584357027/100000000000000 : ℝ)*(sp7) + (747367584357027/100000000000000 : ℝ)*(f.failure) + (1866973822233/125000000000 : ℝ)*(f.sum) + (356788952685421/136095000000000000000000000000 : ℝ)*base65 + (532530169297912831/272190000000000000000000000000000 : ℝ)*base68 + (1572719157230437169/272190000000000000000000000000000 : ℝ)*base69 + (590795817492382831/272190000000000000000000000000000 : ℝ)*base72 + (168570228971857/68047500000000000000000000000 : ℝ)*base74 + (1446405896908042831/272190000000000000000000000000000 : ℝ)*base76 + (847597578419797169/272190000000000000000000000000000 : ℝ)*base77 + (855644937829117169/272190000000000000000000000000000 : ℝ)*base79 + (396598561953091/136095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1869991/1250000000000000000000 : ℝ)*base89 + (1869991/1250000000000000000000 : ℝ)*base91 + (1869991/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (127/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5777/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10167/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s2_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139558401/10000000000 : ℝ)*x 0 + (1101298649/2000000000 : ℝ)*x 1 + (516286591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139558401/10000000000 : ℝ)^4179 ≤ (6485468474021/50000000000000 : ℝ)^3155 := by
    have hnat : (2139558401 : ℕ)^4179*50000000000000^3155 ≤ 6485468474021^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139558401 10000000000 6485468474021 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101298649/2000000000 : ℝ)^4179 ≤ (45370383750683/100000000000000 : ℝ)^3155 := by
    have hnat : (1101298649 : ℕ)^4179*100000000000000^3155 ≤ 45370383750683^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101298649 2000000000 45370383750683 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516286591/1000000000 : ℝ)^4179 ≤ (20829339645641/50000000000000 : ℝ)^3155 := by
    have hnat : (516286591 : ℕ)^4179*50000000000000^3155 ≤ 20829339645641^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516286591 1000000000 20829339645641 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139558401/10000000000 : ℝ), (1101298649/2000000000 : ℝ), (516286591/1000000000 : ℝ)] ![(6485468474021/50000000000000 : ℝ), (45370383750683/100000000000000 : ℝ), (20829339645641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139558401/10000000000 : ℝ)|^4179 ≤ (6485468474021/50000000000000 : ℝ)^3155
        have hw : |(-2139558401/10000000000 : ℝ)|=(2139558401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101298649/2000000000 : ℝ)|^4179 ≤ (45370383750683/100000000000000 : ℝ)^3155
        have hw : |(1101298649/2000000000 : ℝ)|=(1101298649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516286591/1000000000 : ℝ)|^4179 ≤ (20829339645641/50000000000000 : ℝ)^3155
        have hw : |(516286591/1000000000 : ℝ)|=(516286591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167902601/312500000 : ℝ)*x 0 + (-46361041/200000000 : ℝ)*x 1 + (5162868579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167902601/312500000 : ℝ)^4179 ≤ (43917983166787/100000000000000 : ℝ)^3155 := by
    have hnat : (167902601 : ℕ)^4179*100000000000000^3155 ≤ 43917983166787^3155*312500000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167902601 312500000 43917983166787 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46361041/200000000 : ℝ)^4179 ≤ (3605827249091/25000000000000 : ℝ)^3155 := by
    have hnat : (46361041 : ℕ)^4179*25000000000000^3155 ≤ 3605827249091^3155*200000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46361041 200000000 3605827249091 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5162868579/10000000000 : ℝ)^4179 ≤ (41658707816979/100000000000000 : ℝ)^3155 := by
    have hnat : (5162868579 : ℕ)^4179*100000000000000^3155 ≤ 41658707816979^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162868579 10000000000 41658707816979 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167902601/312500000 : ℝ), (-46361041/200000000 : ℝ), (5162868579/10000000000 : ℝ)] ![(43917983166787/100000000000000 : ℝ), (3605827249091/25000000000000 : ℝ), (41658707816979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167902601/312500000 : ℝ)|^4179 ≤ (43917983166787/100000000000000 : ℝ)^3155
        have hw : |(167902601/312500000 : ℝ)|=(167902601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46361041/200000000 : ℝ)|^4179 ≤ (3605827249091/25000000000000 : ℝ)^3155
        have hw : |(-46361041/200000000 : ℝ)|=(46361041/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5162868579/10000000000 : ℝ)|^4179 ≤ (41658707816979/100000000000000 : ℝ)^3155
        have hw : |(5162868579/10000000000 : ℝ)|=(5162868579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372883653/10000000000 : ℝ)*x 0 + (5162867823/10000000000 : ℝ)*x 1 + (-1159026239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372883653/10000000000 : ℝ)^4179 ≤ (5489748465619/12500000000000 : ℝ)^3155 := by
    have hnat : (5372883653 : ℕ)^4179*12500000000000^3155 ≤ 5489748465619^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372883653 10000000000 5489748465619 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162867823/10000000000 : ℝ)^4179 ≤ (20829349868507/50000000000000 : ℝ)^3155 := by
    have hnat : (5162867823 : ℕ)^4179*50000000000000^3155 ≤ 20829349868507^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162867823 10000000000 20829349868507 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159026239/5000000000 : ℝ)^4179 ≤ (2884662504759/20000000000000 : ℝ)^3155 := by
    have hnat : (1159026239 : ℕ)^4179*20000000000000^3155 ≤ 2884662504759^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159026239 5000000000 2884662504759 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372883653/10000000000 : ℝ), (5162867823/10000000000 : ℝ), (-1159026239/5000000000 : ℝ)] ![(5489748465619/12500000000000 : ℝ), (20829349868507/50000000000000 : ℝ), (2884662504759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372883653/10000000000 : ℝ)|^4179 ≤ (5489748465619/12500000000000 : ℝ)^3155
        have hw : |(5372883653/10000000000 : ℝ)|=(5372883653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162867823/10000000000 : ℝ)|^4179 ≤ (20829349868507/50000000000000 : ℝ)^3155
        have hw : |(5162867823/10000000000 : ℝ)|=(5162867823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1159026239/5000000000 : ℝ)|^4179 ≤ (2884662504759/20000000000000 : ℝ)^3155
        have hw : |(-1159026239/5000000000 : ℝ)|=(1159026239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175609393/5000000000 : ℝ)*x 0 + (2010607181/5000000000 : ℝ)*x 1 + (588491593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175609393/5000000000 : ℝ)^4179 ≤ (16606838937409/50000000000000 : ℝ)^3155 := by
    have hnat : (2175609393 : ℕ)^4179*50000000000000^3155 ≤ 16606838937409^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175609393 5000000000 16606838937409 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010607181/5000000000 : ℝ)^4179 ≤ (5983781769713/20000000000000 : ℝ)^3155 := by
    have hnat : (2010607181 : ℕ)^4179*20000000000000^3155 ≤ 5983781769713^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010607181 5000000000 5983781769713 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588491593/1250000000 : ℝ)^4179 ≤ (36867413261353/100000000000000 : ℝ)^3155 := by
    have hnat : (588491593 : ℕ)^4179*100000000000000^3155 ≤ 36867413261353^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588491593 1250000000 36867413261353 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175609393/5000000000 : ℝ), (2010607181/5000000000 : ℝ), (588491593/1250000000 : ℝ)] ![(16606838937409/50000000000000 : ℝ), (5983781769713/20000000000000 : ℝ), (36867413261353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175609393/5000000000 : ℝ)|^4179 ≤ (16606838937409/50000000000000 : ℝ)^3155
        have hw : |(2175609393/5000000000 : ℝ)|=(2175609393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010607181/5000000000 : ℝ)|^4179 ≤ (5983781769713/20000000000000 : ℝ)^3155
        have hw : |(2010607181/5000000000 : ℝ)|=(2010607181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(588491593/1250000000 : ℝ)|^4179 ≤ (36867413261353/100000000000000 : ℝ)^3155
        have hw : |(588491593/1250000000 : ℝ)|=(588491593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139654209/10000000000 : ℝ)*x 0 + (206607931/400000000 : ℝ)*x 1 + (2752069163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139654209/10000000000 : ℝ)^4179 ≤ (12971706300137/100000000000000 : ℝ)^3155 := by
    have hnat : (2139654209 : ℕ)^4179*100000000000000^3155 ≤ 12971706300137^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139654209 10000000000 12971706300137 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206607931/400000000 : ℝ)^4179 ≤ (41683608931427/100000000000000 : ℝ)^3155 := by
    have hnat : (206607931 : ℕ)^4179*100000000000000^3155 ≤ 41683608931427^3155*400000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206607931 400000000 41683608931427 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752069163/5000000000 : ℝ)^4179 ≤ (11336171188353/25000000000000 : ℝ)^3155 := by
    have hnat : (2752069163 : ℕ)^4179*25000000000000^3155 ≤ 11336171188353^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752069163 5000000000 11336171188353 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139654209/10000000000 : ℝ), (206607931/400000000 : ℝ), (2752069163/5000000000 : ℝ)] ![(12971706300137/100000000000000 : ℝ), (41683608931427/100000000000000 : ℝ), (11336171188353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139654209/10000000000 : ℝ)|^4179 ≤ (12971706300137/100000000000000 : ℝ)^3155
        have hw : |(-2139654209/10000000000 : ℝ)|=(2139654209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206607931/400000000 : ℝ)|^4179 ≤ (41683608931427/100000000000000 : ℝ)^3155
        have hw : |(206607931/400000000 : ℝ)|=(206607931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752069163/5000000000 : ℝ)|^4179 ≤ (11336171188353/25000000000000 : ℝ)^3155
        have hw : |(2752069163/5000000000 : ℝ)|=(2752069163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211422519/400000000 : ℝ)*x 0 + (-98839059/500000000 : ℝ)*x 1 + (5504138321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211422519/400000000 : ℝ)^4179 ≤ (42975069696113/100000000000000 : ℝ)^3155 := by
    have hnat : (211422519 : ℕ)^4179*100000000000000^3155 ≤ 42975069696113^3155*400000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211422519 400000000 42975069696113 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98839059/500000000 : ℝ)^4179 ≤ (5840122797509/50000000000000 : ℝ)^3155 := by
    have hnat : (98839059 : ℕ)^4179*50000000000000^3155 ≤ 5840122797509^3155*500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98839059 500000000 5840122797509 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504138321/10000000000 : ℝ)^4179 ≤ (45344684698851/100000000000000 : ℝ)^3155 := by
    have hnat : (5504138321 : ℕ)^4179*100000000000000^3155 ≤ 45344684698851^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504138321 10000000000 45344684698851 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211422519/400000000 : ℝ), (-98839059/500000000 : ℝ), (5504138321/10000000000 : ℝ)] ![(42975069696113/100000000000000 : ℝ), (5840122797509/50000000000000 : ℝ), (45344684698851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211422519/400000000 : ℝ)|^4179 ≤ (42975069696113/100000000000000 : ℝ)^3155
        have hw : |(211422519/400000000 : ℝ)|=(211422519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98839059/500000000 : ℝ)|^4179 ≤ (5840122797509/50000000000000 : ℝ)^3155
        have hw : |(-98839059/500000000 : ℝ)|=(98839059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504138321/10000000000 : ℝ)|^4179 ≤ (45344684698851/100000000000000 : ℝ)^3155
        have hw : |(5504138321/10000000000 : ℝ)|=(5504138321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642781549/5000000000 : ℝ)*x 0 + (1376034579/2500000000 : ℝ)*x 1 + (-1976781017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642781549/5000000000 : ℝ)^4179 ≤ (4297507102077/10000000000000 : ℝ)^3155 := by
    have hnat : (2642781549 : ℕ)^4179*10000000000000^3155 ≤ 4297507102077^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642781549 5000000000 4297507102077 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376034579/2500000000 : ℝ)^4179 ≤ (4534468464429/10000000000000 : ℝ)^3155 := by
    have hnat : (1376034579 : ℕ)^4179*10000000000000^3155 ≤ 4534468464429^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376034579 2500000000 4534468464429 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1976781017/10000000000 : ℝ)^4179 ≤ (5840122159651/50000000000000 : ℝ)^3155 := by
    have hnat : (1976781017 : ℕ)^4179*50000000000000^3155 ≤ 5840122159651^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976781017 10000000000 5840122159651 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642781549/5000000000 : ℝ), (1376034579/2500000000 : ℝ), (-1976781017/10000000000 : ℝ)] ![(4297507102077/10000000000000 : ℝ), (4534468464429/10000000000000 : ℝ), (5840122159651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642781549/5000000000 : ℝ)|^4179 ≤ (4297507102077/10000000000000 : ℝ)^3155
        have hw : |(2642781549/5000000000 : ℝ)|=(2642781549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376034579/2500000000 : ℝ)|^4179 ≤ (4534468464429/10000000000000 : ℝ)^3155
        have hw : |(1376034579/2500000000 : ℝ)|=(1376034579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1976781017/10000000000 : ℝ)|^4179 ≤ (5840122159651/50000000000000 : ℝ)^3155
        have hw : |(-1976781017/10000000000 : ℝ)|=(1976781017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s2_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351411863/10000000000 : ℝ)*x 0 + (1175818511/2500000000 : ℝ)*x 1 + (2012958949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351411863/10000000000 : ℝ)^4179 ≤ (33215630022753/100000000000000 : ℝ)^3155 := by
    have hnat : (4351411863 : ℕ)^4179*100000000000000^3155 ≤ 33215630022753^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351411863 10000000000 33215630022753 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175818511/2500000000 : ℝ)^4179 ≤ (36819098436777/100000000000000 : ℝ)^3155 := by
    have hnat : (1175818511 : ℕ)^4179*100000000000000^3155 ≤ 36819098436777^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175818511 2500000000 36819098436777 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012958949/5000000000 : ℝ)^4179 ≤ (29965271515819/100000000000000 : ℝ)^3155 := by
    have hnat : (2012958949 : ℕ)^4179*100000000000000^3155 ≤ 29965271515819^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012958949 5000000000 29965271515819 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351411863/10000000000 : ℝ), (1175818511/2500000000 : ℝ), (2012958949/5000000000 : ℝ)] ![(33215630022753/100000000000000 : ℝ), (36819098436777/100000000000000 : ℝ), (29965271515819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351411863/10000000000 : ℝ)|^4179 ≤ (33215630022753/100000000000000 : ℝ)^3155
        have hw : |(4351411863/10000000000 : ℝ)|=(4351411863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1175818511/2500000000 : ℝ)|^4179 ≤ (36819098436777/100000000000000 : ℝ)^3155
        have hw : |(1175818511/2500000000 : ℝ)|=(1175818511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012958949/5000000000 : ℝ)|^4179 ≤ (29965271515819/100000000000000 : ℝ)^3155
        have hw : |(2012958949/5000000000 : ℝ)|=(2012958949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3287/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5777/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (885205859566217/100000000000000000000 : ℝ) := by
    have hpowers : (5777/100000 : ℝ)^8357 ≤ (885205859566217/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5777 : ℕ)^8357*100000000000000000000^2048 ≤ 885205859566217^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5777 100000 885205859566217 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5777/100000 : ℝ)) (X := (885205859566217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10167/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (6014745651369477/4000000000000000000 : ℝ) := by
    have hpowers : (10167/50000 : ℝ)^8357 ≤ (6014745651369477/4000000000000000000 : ℝ)^2048 := by
      have hnat : (10167 : ℕ)^8357*4000000000000000000^2048 ≤ 6014745651369477^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10167 50000 6014745651369477 4000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10167/50000 : ℝ)) (X := (6014745651369477/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000885205859566217/50000000000000000000 : ℝ) ≤ (10000043386131037/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50000885205859566217/50000000000000000000 : ℝ)^2048 ≤ (10000043386131037/10000000000000000 : ℝ)^8357 := by
      have hnat : (50000885205859566217 : ℕ)^2048*10000000000000000^8357 ≤ 10000043386131037^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000885205859566217 50000000000000000000 10000043386131037 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043386131037/10000000000000000 : ℝ)) (X := (50000885205859566217/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50075626923571901571/50000000000000000000 : ℝ) ≤ (5001852286574079/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50075626923571901571/50000000000000000000 : ℝ)^2048 ≤ (5001852286574079/5000000000000000 : ℝ)^8357 := by
      have hnat : (50075626923571901571 : ℕ)^2048*5000000000000000^8357 ≤ 5001852286574079^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075626923571901571 50000000000000000000 5001852286574079 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001852286574079/5000000000000000 : ℝ)) (X := (50075626923571901571/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2006014745651369477/2000000000000000000 : ℝ) ≤ (10007365760165279/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (2006014745651369477/2000000000000000000 : ℝ)^2048 ≤ (10007365760165279/10000000000000000 : ℝ)^8357 := by
      have hnat : (2006014745651369477 : ℕ)^2048*10000000000000000^8357 ≤ 10007365760165279^8357*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2006014745651369477 2000000000000000000 10007365760165279 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007365760165279/10000000000000000 : ℝ)) (X := (2006014745651369477/2000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(885205859566217/100000000000000000000 : ℝ) ≤ ((5821133208684547583/5822800000000000000 : ℝ)+2*(3661187017121/1455700000000000 : ℝ)*(5777/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (5821133208684547583/5822800000000000000 : ℝ)+2*(3661187017121/1455700000000000 : ℝ)*(5777/100000 : ℝ)=(10000043386131037/10000000000000000 : ℝ) by norm_num, show 1+2*(885205859566217/100000000000000000000 : ℝ)=(50000885205859566217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6014745651369477/4000000000000000000 : ℝ)+(885205859566217/100000000000000000000 : ℝ) ≤ ((5821133208684547583/5822800000000000000 : ℝ)+(3661187017121/1455700000000000 : ℝ)*((10167/50000 : ℝ)+(5777/100000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (5821133208684547583/5822800000000000000 : ℝ)+(3661187017121/1455700000000000 : ℝ)*((10167/50000 : ℝ)+(5777/100000 : ℝ))=(5001852286574079/5000000000000000 : ℝ) by norm_num, show 1+(6014745651369477/4000000000000000000 : ℝ)+(885205859566217/100000000000000000000 : ℝ)=(50075626923571901571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6014745651369477/4000000000000000000 : ℝ) ≤ ((5821133208684547583/5822800000000000000 : ℝ)+2*(3661187017121/1455700000000000 : ℝ)*(10167/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (5821133208684547583/5822800000000000000 : ℝ)+2*(3661187017121/1455700000000000 : ℝ)*(10167/50000 : ℝ)=(10007365760165279/10000000000000000 : ℝ) by norm_num, show 1+2*(6014745651369477/4000000000000000000 : ℝ)=(2006014745651369477/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5821133208684547583/5822800000000000000 : ℝ)*(X 1 0+X 2 0)+(3661187017121/1455700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5777/100000 : ℝ)) (hi := (10167/50000 : ℝ)) (c := (5821133208684547583/5822800000000000000 : ℝ)) (alpha := (3661187017121/1455700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5821133208684547583/5822800000000000000 : ℝ)*(X 0 1+X 2 1)+(3661187017121/1455700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5777/100000 : ℝ)) (hi := (10167/50000 : ℝ)) (c := (5821133208684547583/5822800000000000000 : ℝ)) (alpha := (3661187017121/1455700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5821133208684547583/5822800000000000000 : ℝ)*(X 0 2+X 1 2)+(3661187017121/1455700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5777/100000 : ℝ)) (hi := (10167/50000 : ℝ)) (c := (5821133208684547583/5822800000000000000 : ℝ)) (alpha := (3661187017121/1455700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139558401/10000000000 : ℝ)*X 0 0+(1101298649/2000000000 : ℝ)*X 0 1+(516286591/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167902601/312500000 : ℝ)*X 1 0+(-46361041/200000000 : ℝ)*X 1 1+(5162868579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372883653/10000000000 : ℝ)*X 2 0+(5162867823/10000000000 : ℝ)*X 2 1+(-1159026239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175609393/5000000000 : ℝ)*X 0 0+(2010607181/5000000000 : ℝ)*X 0 1+(588491593/1250000000 : ℝ)*X 0 2+(2175609393/5000000000 : ℝ)*X 1 0+(2010607181/5000000000 : ℝ)*X 1 1+(588491593/1250000000 : ℝ)*X 1 2+(2175609393/5000000000 : ℝ)*X 2 0+(2010607181/5000000000 : ℝ)*X 2 1+(588491593/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139654209/10000000000 : ℝ)*X 0 0+(206607931/400000000 : ℝ)*X 0 1+(2752069163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211422519/400000000 : ℝ)*X 1 0+(-98839059/500000000 : ℝ)*X 1 1+(5504138321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642781549/5000000000 : ℝ)*X 2 0+(1376034579/2500000000 : ℝ)*X 2 1+(-1976781017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351411863/10000000000 : ℝ)*X 0 0+(1175818511/2500000000 : ℝ)*X 0 1+(2012958949/5000000000 : ℝ)*X 0 2+(4351411863/10000000000 : ℝ)*X 1 0+(1175818511/2500000000 : ℝ)*X 1 1+(2012958949/5000000000 : ℝ)*X 1 2+(4351411863/10000000000 : ℝ)*X 2 0+(1175818511/2500000000 : ℝ)*X 2 1+(2012958949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28895996496971690213694069/4549062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (211097077/50000000000000 : ℝ)*(base19) + (513758789/100000000000000 : ℝ)*(base23) + (15944883/20000000000000 : ℝ)*(upper2) + (331557853/100000000000000 : ℝ)*(upper3) + (153046013/100000000000000 : ℝ)*(upper4) + (34112375373773/1562500000000 : ℝ)*(major0) + (34112375373773/1562500000000 : ℝ)*(major1) + (34112375373773/1562500000000 : ℝ)*(major2) + (2910152674252153/100000000000000 : ℝ)*(sp0) + (145508564024411/5000000000000 : ℝ)*(sp1) + (1455085594461793/50000000000000 : ℝ)*(sp2) + (14562048593419/1000000000000 : ℝ)*(sp3) + (9514215111/50000000000000 : ℝ)*(sp4) + (113657543/1562500000000 : ℝ)*(sp7) + (1456212133424651/100000000000000 : ℝ)*(f.failure) + (1455085851341187/50000000000000 : ℝ)*(f.sum) + (374857727948513/72785000000000000000000000000 : ℝ)*base66 + (2313027721139473/1137265625000000000000000000000 : ℝ)*base67 + (28228015044881409/9098125000000000000000000000000 : ℝ)*base69 + (36294540789677659/9098125000000000000000000000000 : ℝ)*base71 + (2531316187781/568632812500000000000000000 : ℝ)*base74 + (93525742390290159/9098125000000000000000000000000 : ℝ)*base75 + (1048289739536409/9098125000000000000000000000000 : ℝ)*base77 + (3840776044833909/9098125000000000000000000000000 : ℝ)*base79 + (31233862150617/18196250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9851217/1250000000000000000000 : ℝ)*base90 + (9851217/1250000000000000000000 : ℝ)*base92 + (9851217/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (783135552634233093962406507/145570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129732597/10000000000000 : ℝ)*(base19) + (707062197/50000000000000 : ℝ)*(base23) + (5932829/100000000000000 : ℝ)*(upper2) + (156786259/100000000000000 : ℝ)*(upper3) + (117237907/100000000000000 : ℝ)*(upper5) + (2213351374515257/100000000000000 : ℝ)*(major0) + (2213351374515257/100000000000000 : ℝ)*(major1) + (2213351374515257/100000000000000 : ℝ)*(major2) + (6226722041/50000000000000 : ℝ)*(sp1) + (3671985549/25000000000000 : ℝ)*(sp2) + (2950373830965187/100000000000000 : ℝ)*(sp4) + (590072016039027/20000000000000 : ℝ)*(sp5) + (737589432224649/25000000000000 : ℝ)*(sp6) + (1476328738739099/100000000000000 : ℝ)*(sp7) + (1476328738739099/100000000000000 : ℝ)*(f.failure) + (2950373830965187/100000000000000 : ℝ)*(f.sum) + (177120043615793/72785000000000000000000000000 : ℝ)*base66 + (2757979239635681831/582280000000000000000000000000000 : ℝ)*base67 + (1413930216746441831/582280000000000000000000000000000 : ℝ)*base69 + (46771584280281831/582280000000000000000000000000000 : ℝ)*base71 + (33377645997363/72785000000000000000000000000 : ℝ)*base74 + (1884168249573838169/582280000000000000000000000000000 : ℝ)*base76 + (4040995341157121831/582280000000000000000000000000000 : ℝ)*base77 + (4471564519036361831/582280000000000000000000000000000 : ℝ)*base79 + (11125932446727/72785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2879967/1250000000000000000000 : ℝ)*base89 + (2879967/1250000000000000000000 : ℝ)*base91 + (2879967/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1165_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1165_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1165_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1165_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3287/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

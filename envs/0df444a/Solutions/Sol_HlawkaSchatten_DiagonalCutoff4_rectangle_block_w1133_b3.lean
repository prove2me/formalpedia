-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:48.062664+00:00
-- url     : https://prove2.me/submissions/f5d3e0fe-6537-4caf-baf1-8391fda6acc6

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
theorem support_rectangle_w1133_box_0 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-408801723/2000000000 : ℝ)*x 0 + (2688219111/5000000000 : ℝ)*x 1 + (5376438043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408801723/2000000000 : ℝ)^4163 ≤ (12177255026639/100000000000000 : ℝ)^3139 := by
    have hnat : (408801723 : ℕ)^4163*100000000000000^3139 ≤ 12177255026639^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408801723 2000000000 12177255026639 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688219111/5000000000 : ℝ)^4163 ≤ (175645493801/400000000000 : ℝ)^3139 := by
    have hnat : (2688219111 : ℕ)^4163*400000000000^3139 ≤ 175645493801^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688219111 5000000000 175645493801 400000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376438043/10000000000 : ℝ)^4163 ≤ (10977842877843/25000000000000 : ℝ)^3139 := by
    have hnat : (5376438043 : ℕ)^4163*25000000000000^3139 ≤ 10977842877843^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376438043 10000000000 10977842877843 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408801723/2000000000 : ℝ), (2688219111/5000000000 : ℝ), (5376438043/10000000000 : ℝ)] ![(12177255026639/100000000000000 : ℝ), (175645493801/400000000000 : ℝ), (10977842877843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408801723/2000000000 : ℝ)|^4163 ≤ (12177255026639/100000000000000 : ℝ)^3139
        have hw : |(-408801723/2000000000 : ℝ)|=(408801723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688219111/5000000000 : ℝ)|^4163 ≤ (175645493801/400000000000 : ℝ)^3139
        have hw : |(2688219111/5000000000 : ℝ)|=(2688219111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376438043/10000000000 : ℝ)|^4163 ≤ (10977842877843/25000000000000 : ℝ)^3139
        have hw : |(5376438043/10000000000 : ℝ)|=(5376438043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_1 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295898763/10000000000 : ℝ)*x 0 + (-2153211153/10000000000 : ℝ)*x 1 + (2688219161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295898763/10000000000 : ℝ)^4163 ≤ (21520565650769/50000000000000 : ℝ)^3139 := by
    have hnat : (5295898763 : ℕ)^4163*50000000000000^3139 ≤ 21520565650769^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295898763 10000000000 21520565650769 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153211153/10000000000 : ℝ)^4163 ≤ (13047494159721/100000000000000 : ℝ)^3139 := by
    have hnat : (2153211153 : ℕ)^4163*100000000000000^3139 ≤ 13047494159721^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153211153 10000000000 13047494159721 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688219161/5000000000 : ℝ)^4163 ≤ (21955687266711/50000000000000 : ℝ)^3139 := by
    have hnat : (2688219161 : ℕ)^4163*50000000000000^3139 ≤ 21955687266711^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688219161 5000000000 21955687266711 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295898763/10000000000 : ℝ), (-2153211153/10000000000 : ℝ), (2688219161/5000000000 : ℝ)] ![(21520565650769/50000000000000 : ℝ), (13047494159721/100000000000000 : ℝ), (21955687266711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295898763/10000000000 : ℝ)|^4163 ≤ (21520565650769/50000000000000 : ℝ)^3139
        have hw : |(5295898763/10000000000 : ℝ)|=(5295898763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153211153/10000000000 : ℝ)|^4163 ≤ (13047494159721/100000000000000 : ℝ)^3139
        have hw : |(-2153211153/10000000000 : ℝ)|=(2153211153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688219161/5000000000 : ℝ)|^4163 ≤ (21955687266711/50000000000000 : ℝ)^3139
        have hw : |(2688219161/5000000000 : ℝ)|=(2688219161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_2 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059179883/2000000000 : ℝ)*x 0 + (2688219011/5000000000 : ℝ)*x 1 + (-1076605341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059179883/2000000000 : ℝ)^4163 ≤ (43041138329133/100000000000000 : ℝ)^3139 := by
    have hnat : (1059179883 : ℕ)^4163*100000000000000^3139 ≤ 43041138329133^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059179883 2000000000 43041138329133 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688219011/5000000000 : ℝ)^4163 ≤ (21955685641953/50000000000000 : ℝ)^3139 := by
    have hnat : (2688219011 : ℕ)^4163*50000000000000^3139 ≤ 21955685641953^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688219011 5000000000 21955685641953 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076605341/5000000000 : ℝ)^4163 ≤ (13047490374629/100000000000000 : ℝ)^3139 := by
    have hnat : (1076605341 : ℕ)^4163*100000000000000^3139 ≤ 13047490374629^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076605341 5000000000 13047490374629 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059179883/2000000000 : ℝ), (2688219011/5000000000 : ℝ), (-1076605341/5000000000 : ℝ)] ![(43041138329133/100000000000000 : ℝ), (21955685641953/50000000000000 : ℝ), (13047490374629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059179883/2000000000 : ℝ)|^4163 ≤ (43041138329133/100000000000000 : ℝ)^3139
        have hw : |(1059179883/2000000000 : ℝ)|=(1059179883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688219011/5000000000 : ℝ)|^4163 ≤ (21955685641953/50000000000000 : ℝ)^3139
        have hw : |(2688219011/5000000000 : ℝ)|=(2688219011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076605341/5000000000 : ℝ)|^4163 ≤ (13047490374629/100000000000000 : ℝ)^3139
        have hw : |(-1076605341/5000000000 : ℝ)|=(1076605341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_3 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4473587821/10000000000 : ℝ)*x 0 + (4314237863/10000000000 : ℝ)*x 1 + (4314237741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4473587821/10000000000 : ℝ)^4163 ≤ (17205348393413/50000000000000 : ℝ)^3139 := by
    have hnat : (4473587821 : ℕ)^4163*50000000000000^3139 ≤ 17205348393413^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473587821 10000000000 17205348393413 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314237863/10000000000 : ℝ)^4163 ≤ (32794652217587/100000000000000 : ℝ)^3139 := by
    have hnat : (4314237863 : ℕ)^4163*100000000000000^3139 ≤ 32794652217587^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314237863 10000000000 32794652217587 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314237741/10000000000 : ℝ)^4163 ≤ (1311786039507/4000000000000 : ℝ)^3139 := by
    have hnat : (4314237741 : ℕ)^4163*4000000000000^3139 ≤ 1311786039507^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314237741 10000000000 1311786039507 4000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4473587821/10000000000 : ℝ), (4314237863/10000000000 : ℝ), (4314237741/10000000000 : ℝ)] ![(17205348393413/50000000000000 : ℝ), (32794652217587/100000000000000 : ℝ), (1311786039507/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4473587821/10000000000 : ℝ)|^4163 ≤ (17205348393413/50000000000000 : ℝ)^3139
        have hw : |(4473587821/10000000000 : ℝ)|=(4473587821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314237863/10000000000 : ℝ)|^4163 ≤ (32794652217587/100000000000000 : ℝ)^3139
        have hw : |(4314237863/10000000000 : ℝ)|=(4314237863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314237741/10000000000 : ℝ)|^4163 ≤ (1311786039507/4000000000000 : ℝ)^3139
        have hw : |(4314237741/10000000000 : ℝ)|=(4314237741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_4 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-574944967/2500000000 : ℝ)*x 0 + (16503201/31250000 : ℝ)*x 1 + (330063981/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574944967/2500000000 : ℝ)^4163 ≤ (14238246045739/100000000000000 : ℝ)^3139 := by
    have hnat : (574944967 : ℕ)^4163*100000000000000^3139 ≤ 14238246045739^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574944967 2500000000 14238246045739 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16503201/31250000 : ℝ)^4163 ≤ (2144044016339/5000000000000 : ℝ)^3139 := by
    have hnat : (16503201 : ℕ)^4163*5000000000000^3139 ≤ 2144044016339^3139*31250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16503201 31250000 2144044016339 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330063981/625000000 : ℝ)^4163 ≤ (42880873607153/100000000000000 : ℝ)^3139 := by
    have hnat : (330063981 : ℕ)^4163*100000000000000^3139 ≤ 42880873607153^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330063981 625000000 42880873607153 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-574944967/2500000000 : ℝ), (16503201/31250000 : ℝ), (330063981/625000000 : ℝ)] ![(14238246045739/100000000000000 : ℝ), (2144044016339/5000000000000 : ℝ), (42880873607153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-574944967/2500000000 : ℝ)|^4163 ≤ (14238246045739/100000000000000 : ℝ)^3139
        have hw : |(-574944967/2500000000 : ℝ)|=(574944967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16503201/31250000 : ℝ)|^4163 ≤ (2144044016339/5000000000000 : ℝ)^3139
        have hw : |(16503201/31250000 : ℝ)|=(16503201/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330063981/625000000 : ℝ)|^4163 ≤ (42880873607153/100000000000000 : ℝ)^3139
        have hw : |(330063981/625000000 : ℝ)|=(330063981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_5 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363323117/10000000000 : ℝ)*x 0 + (-2190717159/10000000000 : ℝ)*x 1 + (5281023623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363323117/10000000000 : ℝ)^4163 ≤ (43769370848821/100000000000000 : ℝ)^3139 := by
    have hnat : (5363323117 : ℕ)^4163*100000000000000^3139 ≤ 43769370848821^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363323117 10000000000 43769370848821 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190717159/10000000000 : ℝ)^4163 ≤ (13349756310429/100000000000000 : ℝ)^3139 := by
    have hnat : (2190717159 : ℕ)^4163*100000000000000^3139 ≤ 13349756310429^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190717159 10000000000 13349756310429 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281023623/10000000000 : ℝ)^4163 ≤ (42880872821043/100000000000000 : ℝ)^3139 := by
    have hnat : (5281023623 : ℕ)^4163*100000000000000^3139 ≤ 42880872821043^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281023623 10000000000 42880872821043 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363323117/10000000000 : ℝ), (-2190717159/10000000000 : ℝ), (5281023623/10000000000 : ℝ)] ![(43769370848821/100000000000000 : ℝ), (13349756310429/100000000000000 : ℝ), (42880872821043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363323117/10000000000 : ℝ)|^4163 ≤ (43769370848821/100000000000000 : ℝ)^3139
        have hw : |(5363323117/10000000000 : ℝ)|=(5363323117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190717159/10000000000 : ℝ)|^4163 ≤ (13349756310429/100000000000000 : ℝ)^3139
        have hw : |(-2190717159/10000000000 : ℝ)|=(2190717159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281023623/10000000000 : ℝ)|^4163 ≤ (42880872821043/100000000000000 : ℝ)^3139
        have hw : |(5281023623/10000000000 : ℝ)|=(5281023623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_6 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335207681/625000000 : ℝ)*x 0 + (5281024357/10000000000 : ℝ)*x 1 + (-1095358239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335207681/625000000 : ℝ)^4163 ≤ (43769368456917/100000000000000 : ℝ)^3139 := by
    have hnat : (335207681 : ℕ)^4163*100000000000000^3139 ≤ 43769368456917^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335207681 625000000 43769368456917 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281024357/10000000000 : ℝ)^4163 ≤ (2144044036261/5000000000000 : ℝ)^3139 := by
    have hnat : (5281024357 : ℕ)^4163*5000000000000^3139 ≤ 2144044036261^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281024357 10000000000 2144044036261 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095358239/5000000000 : ℝ)^4163 ≤ (13349750806799/100000000000000 : ℝ)^3139 := by
    have hnat : (1095358239 : ℕ)^4163*100000000000000^3139 ≤ 13349750806799^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095358239 5000000000 13349750806799 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335207681/625000000 : ℝ), (5281024357/10000000000 : ℝ), (-1095358239/5000000000 : ℝ)] ![(43769368456917/100000000000000 : ℝ), (2144044036261/5000000000000 : ℝ), (13349750806799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335207681/625000000 : ℝ)|^4163 ≤ (43769368456917/100000000000000 : ℝ)^3139
        have hw : |(335207681/625000000 : ℝ)|=(335207681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281024357/10000000000 : ℝ)|^4163 ≤ (2144044036261/5000000000000 : ℝ)^3139
        have hw : |(5281024357/10000000000 : ℝ)|=(5281024357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095358239/5000000000 : ℝ)|^4163 ≤ (13349750806799/100000000000000 : ℝ)^3139
        have hw : |(-1095358239/5000000000 : ℝ)|=(1095358239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_7 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266121503/625000000 : ℝ)*x 0 + (1105509679/2500000000 : ℝ)*x 1 + (276377427/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266121503/625000000 : ℝ)^4163 ≤ (16114176023911/50000000000000 : ℝ)^3139 := by
    have hnat : (266121503 : ℕ)^4163*50000000000000^3139 ≤ 16114176023911^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266121503 625000000 16114176023911 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105509679/2500000000 : ℝ)^4163 ≤ (33885823379303/100000000000000 : ℝ)^3139 := by
    have hnat : (1105509679 : ℕ)^4163*100000000000000^3139 ≤ 33885823379303^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105509679 2500000000 33885823379303 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276377427/625000000 : ℝ)^4163 ≤ (1694291227909/5000000000000 : ℝ)^3139 := by
    have hnat : (276377427 : ℕ)^4163*5000000000000^3139 ≤ 1694291227909^3139*625000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276377427 625000000 1694291227909 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266121503/625000000 : ℝ), (1105509679/2500000000 : ℝ), (276377427/625000000 : ℝ)] ![(16114176023911/50000000000000 : ℝ), (33885823379303/100000000000000 : ℝ), (1694291227909/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266121503/625000000 : ℝ)|^4163 ≤ (16114176023911/50000000000000 : ℝ)^3139
        have hw : |(266121503/625000000 : ℝ)|=(266121503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105509679/2500000000 : ℝ)|^4163 ≤ (33885823379303/100000000000000 : ℝ)^3139
        have hw : |(1105509679/2500000000 : ℝ)|=(1105509679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276377427/625000000 : ℝ)|^4163 ≤ (1694291227909/5000000000000 : ℝ)^3139
        have hw : |(276377427/625000000 : ℝ)|=(276377427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_8 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-561576161/2500000000 : ℝ)*x 0 + (5216150197/10000000000 : ℝ)*x 1 + (5386046301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (561576161/2500000000 : ℝ)^4163 ≤ (13800845876587/100000000000000 : ℝ)^3139 := by
    have hnat : (561576161 : ℕ)^4163*100000000000000^3139 ≤ 13800845876587^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561576161 2500000000 13800845876587 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216150197/10000000000 : ℝ)^4163 ≤ (4218367830997/10000000000000 : ℝ)^3139 := by
    have hnat : (5216150197 : ℕ)^4163*10000000000000^3139 ≤ 4218367830997^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216150197 10000000000 4218367830997 10000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386046301/10000000000 : ℝ)^4163 ≤ (44015475802811/100000000000000 : ℝ)^3139 := by
    have hnat : (5386046301 : ℕ)^4163*100000000000000^3139 ≤ 44015475802811^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386046301 10000000000 44015475802811 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-561576161/2500000000 : ℝ), (5216150197/10000000000 : ℝ), (5386046301/10000000000 : ℝ)] ![(13800845876587/100000000000000 : ℝ), (4218367830997/10000000000000 : ℝ), (44015475802811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-561576161/2500000000 : ℝ)|^4163 ≤ (13800845876587/100000000000000 : ℝ)^3139
        have hw : |(-561576161/2500000000 : ℝ)|=(561576161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216150197/10000000000 : ℝ)|^4163 ≤ (4218367830997/10000000000000 : ℝ)^3139
        have hw : |(5216150197/10000000000 : ℝ)|=(5216150197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386046301/10000000000 : ℝ)|^4163 ≤ (44015475802811/100000000000000 : ℝ)^3139
        have hw : |(5386046301/10000000000 : ℝ)|=(5386046301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_9 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289106169/10000000000 : ℝ)*x 0 + (-2149364723/10000000000 : ℝ)*x 1 + (5386046257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289106169/10000000000 : ℝ)^4163 ≤ (42967932518137/100000000000000 : ℝ)^3139 := by
    have hnat : (5289106169 : ℕ)^4163*100000000000000^3139 ≤ 42967932518137^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289106169 10000000000 42967932518137 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149364723/10000000000 : ℝ)^4163 ≤ (2603318428819/20000000000000 : ℝ)^3139 := by
    have hnat : (2149364723 : ℕ)^4163*20000000000000^3139 ≤ 2603318428819^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149364723 10000000000 2603318428819 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386046257/10000000000 : ℝ)^4163 ≤ (22007737662969/50000000000000 : ℝ)^3139 := by
    have hnat : (5386046257 : ℕ)^4163*50000000000000^3139 ≤ 22007737662969^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386046257 10000000000 22007737662969 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289106169/10000000000 : ℝ), (-2149364723/10000000000 : ℝ), (5386046257/10000000000 : ℝ)] ![(42967932518137/100000000000000 : ℝ), (2603318428819/20000000000000 : ℝ), (22007737662969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289106169/10000000000 : ℝ)|^4163 ≤ (42967932518137/100000000000000 : ℝ)^3139
        have hw : |(5289106169/10000000000 : ℝ)|=(5289106169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149364723/10000000000 : ℝ)|^4163 ≤ (2603318428819/20000000000000 : ℝ)^3139
        have hw : |(-2149364723/10000000000 : ℝ)|=(2149364723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386046257/10000000000 : ℝ)|^4163 ≤ (22007737662969/50000000000000 : ℝ)^3139
        have hw : |(5386046257/10000000000 : ℝ)|=(5386046257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_10 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057821219/2000000000 : ℝ)*x 0 + (5386046459/10000000000 : ℝ)*x 1 + (-2149364549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057821219/2000000000 : ℝ)^4163 ≤ (2148396586043/5000000000000 : ℝ)^3139 := by
    have hnat : (1057821219 : ℕ)^4163*5000000000000^3139 ≤ 2148396586043^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057821219 2000000000 2148396586043 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386046459/10000000000 : ℝ)^4163 ≤ (2200773875761/5000000000000 : ℝ)^3139 := by
    have hnat : (5386046459 : ℕ)^4163*5000000000000^3139 ≤ 2200773875761^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386046459 10000000000 2200773875761 5000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149364549/10000000000 : ℝ)^4163 ≤ (3254147686649/25000000000000 : ℝ)^3139 := by
    have hnat : (2149364549 : ℕ)^4163*25000000000000^3139 ≤ 3254147686649^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149364549 10000000000 3254147686649 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057821219/2000000000 : ℝ), (5386046459/10000000000 : ℝ), (-2149364549/10000000000 : ℝ)] ![(2148396586043/5000000000000 : ℝ), (2200773875761/5000000000000 : ℝ), (3254147686649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057821219/2000000000 : ℝ)|^4163 ≤ (2148396586043/5000000000000 : ℝ)^3139
        have hw : |(1057821219/2000000000 : ℝ)|=(1057821219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386046459/10000000000 : ℝ)|^4163 ≤ (2200773875761/5000000000000 : ℝ)^3139
        have hw : |(5386046459/10000000000 : ℝ)|=(5386046459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149364549/10000000000 : ℝ)|^4163 ≤ (3254147686649/25000000000000 : ℝ)^3139
        have hw : |(-2149364549/10000000000 : ℝ)|=(2149364549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_11 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2247514889/5000000000 : ℝ)*x 0 + (4303376173/10000000000 : ℝ)*x 1 + (1075844099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247514889/5000000000 : ℝ)^4163 ≤ (34629601969061/100000000000000 : ℝ)^3139 := by
    have hnat : (2247514889 : ℕ)^4163*100000000000000^3139 ≤ 34629601969061^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247514889 5000000000 34629601969061 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303376173/10000000000 : ℝ)^4163 ≤ (16342598941927/50000000000000 : ℝ)^3139 := by
    have hnat : (4303376173 : ℕ)^4163*50000000000000^3139 ≤ 16342598941927^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303376173 10000000000 16342598941927 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075844099/2500000000 : ℝ)^4163 ≤ (32685200130123/100000000000000 : ℝ)^3139 := by
    have hnat : (1075844099 : ℕ)^4163*100000000000000^3139 ≤ 32685200130123^3139*2500000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075844099 2500000000 32685200130123 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2247514889/5000000000 : ℝ), (4303376173/10000000000 : ℝ), (1075844099/2500000000 : ℝ)] ![(34629601969061/100000000000000 : ℝ), (16342598941927/50000000000000 : ℝ), (32685200130123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2247514889/5000000000 : ℝ)|^4163 ≤ (34629601969061/100000000000000 : ℝ)^3139
        have hw : |(2247514889/5000000000 : ℝ)|=(2247514889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303376173/10000000000 : ℝ)|^4163 ≤ (16342598941927/50000000000000 : ℝ)^3139
        have hw : |(4303376173/10000000000 : ℝ)|=(4303376173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075844099/2500000000 : ℝ)|^4163 ≤ (32685200130123/100000000000000 : ℝ)^3139
        have hw : |(1075844099/2500000000 : ℝ)|=(1075844099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_12 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097808813/10000000000 : ℝ)*x 0 + (170000857/312500000 : ℝ)*x 1 + (82390459/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097808813/10000000000 : ℝ)^4163 ≤ (6302072182993/50000000000000 : ℝ)^3139 := by
    have hnat : (2097808813 : ℕ)^4163*50000000000000^3139 ≤ 6302072182993^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097808813 10000000000 6302072182993 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170000857/312500000 : ℝ)^4163 ≤ (22300739591923/50000000000000 : ℝ)^3139 := by
    have hnat : (170000857 : ℕ)^4163*50000000000000^3139 ≤ 22300739591923^3139*312500000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170000857 312500000 22300739591923 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82390459/156250000 : ℝ)^4163 ≤ (10698594108733/25000000000000 : ℝ)^3139 := by
    have hnat : (82390459 : ℕ)^4163*25000000000000^3139 ≤ 10698594108733^3139*156250000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82390459 156250000 10698594108733 25000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097808813/10000000000 : ℝ), (170000857/312500000 : ℝ), (82390459/156250000 : ℝ)] ![(6302072182993/50000000000000 : ℝ), (22300739591923/50000000000000 : ℝ), (10698594108733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097808813/10000000000 : ℝ)|^4163 ≤ (6302072182993/50000000000000 : ℝ)^3139
        have hw : |(-2097808813/10000000000 : ℝ)|=(2097808813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170000857/312500000 : ℝ)|^4163 ≤ (22300739591923/50000000000000 : ℝ)^3139
        have hw : |(170000857/312500000 : ℝ)|=(170000857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82390459/156250000 : ℝ)|^4163 ≤ (10698594108733/25000000000000 : ℝ)^3139
        have hw : |(82390459/156250000 : ℝ)|=(82390459/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_13 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368998287/10000000000 : ℝ)*x 0 + (-2193817667/10000000000 : ℝ)*x 1 + (1054597871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368998287/10000000000 : ℝ)^4163 ≤ (43830804346799/100000000000000 : ℝ)^3139 := by
    have hnat : (5368998287 : ℕ)^4163*100000000000000^3139 ≤ 43830804346799^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368998287 10000000000 43830804346799 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193817667/10000000000 : ℝ)^4163 ≤ (2674963886761/20000000000000 : ℝ)^3139 := by
    have hnat : (2193817667 : ℕ)^4163*20000000000000^3139 ≤ 2674963886761^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193817667 10000000000 2674963886761 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054597871/2000000000 : ℝ)^4163 ≤ (42794376208903/100000000000000 : ℝ)^3139 := by
    have hnat : (1054597871 : ℕ)^4163*100000000000000^3139 ≤ 42794376208903^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054597871 2000000000 42794376208903 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368998287/10000000000 : ℝ), (-2193817667/10000000000 : ℝ), (1054597871/2000000000 : ℝ)] ![(43830804346799/100000000000000 : ℝ), (2674963886761/20000000000000 : ℝ), (42794376208903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368998287/10000000000 : ℝ)|^4163 ≤ (43830804346799/100000000000000 : ℝ)^3139
        have hw : |(5368998287/10000000000 : ℝ)|=(5368998287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193817667/10000000000 : ℝ)|^4163 ≤ (2674963886761/20000000000000 : ℝ)^3139
        have hw : |(-2193817667/10000000000 : ℝ)|=(2193817667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054597871/2000000000 : ℝ)|^4163 ≤ (42794376208903/100000000000000 : ℝ)^3139
        have hw : |(1054597871/2000000000 : ℝ)|=(1054597871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_14 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684499129/5000000000 : ℝ)*x 0 + (2636494659/5000000000 : ℝ)*x 1 + (-438763551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684499129/5000000000 : ℝ)^4163 ≤ (43830804032821/100000000000000 : ℝ)^3139 := by
    have hnat : (2684499129 : ℕ)^4163*100000000000000^3139 ≤ 43830804032821^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684499129 5000000000 43830804032821 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636494659/5000000000 : ℝ)^4163 ≤ (21397187905331/50000000000000 : ℝ)^3139 := by
    have hnat : (2636494659 : ℕ)^4163*50000000000000^3139 ≤ 21397187905331^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636494659 5000000000 21397187905331 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438763551/2000000000 : ℝ)^4163 ≤ (6687410072661/50000000000000 : ℝ)^3139 := by
    have hnat : (438763551 : ℕ)^4163*50000000000000^3139 ≤ 6687410072661^3139*2000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438763551 2000000000 6687410072661 50000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684499129/5000000000 : ℝ), (2636494659/5000000000 : ℝ), (-438763551/2000000000 : ℝ)] ![(43830804032821/100000000000000 : ℝ), (21397187905331/50000000000000 : ℝ), (6687410072661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684499129/5000000000 : ℝ)|^4163 ≤ (43830804032821/100000000000000 : ℝ)^3139
        have hw : |(2684499129/5000000000 : ℝ)|=(2684499129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636494659/5000000000 : ℝ)|^4163 ≤ (21397187905331/50000000000000 : ℝ)^3139
        have hw : |(2636494659/5000000000 : ℝ)|=(2636494659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438763551/2000000000 : ℝ)|^4163 ≤ (6687410072661/50000000000000 : ℝ)^3139
        have hw : |(-438763551/2000000000 : ℝ)|=(438763551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1133_box_15 (p : ℝ) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119777423/5000000000 : ℝ)*x 0 + (4431111187/10000000000 : ℝ)*x 1 + (2215555617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119777423/5000000000 : ℝ)^4163 ≤ (6408777765227/20000000000000 : ℝ)^3139 := by
    have hnat : (2119777423 : ℕ)^4163*20000000000000^3139 ≤ 6408777765227^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119777423 5000000000 6408777765227 20000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431111187/10000000000 : ℝ)^4163 ≤ (33978055337321/100000000000000 : ℝ)^3139 := by
    have hnat : (4431111187 : ℕ)^4163*100000000000000^3139 ≤ 33978055337321^3139*10000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431111187 10000000000 33978055337321 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215555617/5000000000 : ℝ)^4163 ≤ (33978055815289/100000000000000 : ℝ)^3139 := by
    have hnat : (2215555617 : ℕ)^4163*100000000000000^3139 ≤ 33978055815289^3139*5000000000^4163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215555617 5000000000 33978055815289 100000000000000 4163 3139 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4163/1024 : ℝ)) 4163 3139 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119777423/5000000000 : ℝ), (4431111187/10000000000 : ℝ), (2215555617/5000000000 : ℝ)] ![(6408777765227/20000000000000 : ℝ), (33978055337321/100000000000000 : ℝ), (33978055815289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119777423/5000000000 : ℝ)|^4163 ≤ (6408777765227/20000000000000 : ℝ)^3139
        have hw : |(2119777423/5000000000 : ℝ)|=(2119777423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431111187/10000000000 : ℝ)|^4163 ≤ (33978055337321/100000000000000 : ℝ)^3139
        have hw : |(4431111187/10000000000 : ℝ)|=(4431111187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215555617/5000000000 : ℝ)|^4163 ≤ (33978055815289/100000000000000 : ℝ)^3139
        have hw : |(2215555617/5000000000 : ℝ)|=(2215555617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1133_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14823/25000 : ℝ) ∧ (79781/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2597/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5671/50000 : ℝ) ^ (8325/2048 : ℝ) ≤ (14367089190877097/100000000000000000000 : ℝ) := by
    have hpowers : (5671/50000 : ℝ)^8325 ≤ (14367089190877097/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5671 : ℕ)^8325*100000000000000000000^2048 ≤ 14367089190877097^2048*50000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5671 50000 14367089190877097 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5671/50000 : ℝ)) (X := (14367089190877097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (8325/2048 : ℝ) ≤ (34235323037792301/100000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^8325 ≤ (34235323037792301/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14043 : ℕ)^8325*100000000000000000000^2048 ≤ 34235323037792301^2048*100000^8325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 34235323037792301 100000000000000000000 8325 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (34235323037792301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014367089190877097/50000000000000000000 : ℝ) ≤ (10000706801484847/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50014367089190877097/50000000000000000000 : ℝ)^2048 ≤ (10000706801484847/10000000000000000 : ℝ)^8325 := by
      have hnat : (50014367089190877097 : ℕ)^2048*10000000000000000^8325 ≤ 10000706801484847^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014367089190877097 50000000000000000000 10000706801484847 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706801484847/10000000000000000 : ℝ)) (X := (50014367089190877097/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024301206114334699/50000000000000000000 : ℝ) ≤ (10001195429515453/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50024301206114334699/50000000000000000000 : ℝ)^2048 ≤ (10001195429515453/10000000000000000 : ℝ)^8325 := by
      have hnat : (50024301206114334699 : ℕ)^2048*10000000000000000^8325 ≤ 10001195429515453^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024301206114334699 50000000000000000000 10001195429515453 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001195429515453/10000000000000000 : ℝ)) (X := (50024301206114334699/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034235323037792301/50000000000000000000 : ℝ) ≤ (10001684057546059/10000000000000000 : ℝ) ^ (8325/2048 : ℝ) := by
    have hpowers : (50034235323037792301/50000000000000000000 : ℝ)^2048 ≤ (10001684057546059/10000000000000000 : ℝ)^8325 := by
      have hnat : (50034235323037792301 : ℕ)^2048*10000000000000000^8325 ≤ 10001684057546059^8325*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034235323037792301 50000000000000000000 10001684057546059 10000000000000000 2048 8325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001684057546059/10000000000000000 : ℝ)) (X := (50034235323037792301/50000000000000000000 : ℝ)) (by norm_num) 8325 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14367089190877097/100000000000000000000 : ℝ) ≤ ((27000825032564305243/27010000000000000000 : ℝ)+2*(244314015303/135050000000000 : ℝ)*(5671/50000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (27000825032564305243/27010000000000000000 : ℝ)+2*(244314015303/135050000000000 : ℝ)*(5671/50000 : ℝ)=(10000706801484847/10000000000000000 : ℝ) by norm_num, show 1+2*(14367089190877097/100000000000000000000 : ℝ)=(50014367089190877097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34235323037792301/100000000000000000000 : ℝ)+(14367089190877097/100000000000000000000 : ℝ) ≤ ((27000825032564305243/27010000000000000000 : ℝ)+(244314015303/135050000000000 : ℝ)*((14043/100000 : ℝ)+(5671/50000 : ℝ)))^(8325/2048 : ℝ) := by
    rw [show (27000825032564305243/27010000000000000000 : ℝ)+(244314015303/135050000000000 : ℝ)*((14043/100000 : ℝ)+(5671/50000 : ℝ))=(10001195429515453/10000000000000000 : ℝ) by norm_num, show 1+(34235323037792301/100000000000000000000 : ℝ)+(14367089190877097/100000000000000000000 : ℝ)=(50024301206114334699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34235323037792301/100000000000000000000 : ℝ) ≤ ((27000825032564305243/27010000000000000000 : ℝ)+2*(244314015303/135050000000000 : ℝ)*(14043/100000 : ℝ))^(8325/2048 : ℝ) := by
    rw [show (27000825032564305243/27010000000000000000 : ℝ)+2*(244314015303/135050000000000 : ℝ)*(14043/100000 : ℝ)=(10001684057546059/10000000000000000 : ℝ) by norm_num, show 1+2*(34235323037792301/100000000000000000000 : ℝ)=(50034235323037792301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27000825032564305243/27010000000000000000 : ℝ)*(X 1 0+X 2 0)+(244314015303/135050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27000825032564305243/27010000000000000000 : ℝ)) (alpha := (244314015303/135050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27000825032564305243/27010000000000000000 : ℝ)*(X 0 1+X 2 1)+(244314015303/135050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27000825032564305243/27010000000000000000 : ℝ)) (alpha := (244314015303/135050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27000825032564305243/27010000000000000000 : ℝ)*(X 0 2+X 1 2)+(244314015303/135050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8325/2048 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (27000825032564305243/27010000000000000000 : ℝ)) (alpha := (244314015303/135050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-408801723/2000000000 : ℝ)*X 0 0+(2688219111/5000000000 : ℝ)*X 0 1+(5376438043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295898763/10000000000 : ℝ)*X 1 0+(-2153211153/10000000000 : ℝ)*X 1 1+(2688219161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059179883/2000000000 : ℝ)*X 2 0+(2688219011/5000000000 : ℝ)*X 2 1+(-1076605341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4473587821/10000000000 : ℝ)*X 0 0+(4314237863/10000000000 : ℝ)*X 0 1+(4314237741/10000000000 : ℝ)*X 0 2+(4473587821/10000000000 : ℝ)*X 1 0+(4314237863/10000000000 : ℝ)*X 1 1+(4314237741/10000000000 : ℝ)*X 1 2+(4473587821/10000000000 : ℝ)*X 2 0+(4314237863/10000000000 : ℝ)*X 2 1+(4314237741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-574944967/2500000000 : ℝ)*X 0 0+(16503201/31250000 : ℝ)*X 0 1+(330063981/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363323117/10000000000 : ℝ)*X 1 0+(-2190717159/10000000000 : ℝ)*X 1 1+(5281023623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335207681/625000000 : ℝ)*X 2 0+(5281024357/10000000000 : ℝ)*X 2 1+(-1095358239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266121503/625000000 : ℝ)*X 0 0+(1105509679/2500000000 : ℝ)*X 0 1+(276377427/625000000 : ℝ)*X 0 2+(266121503/625000000 : ℝ)*X 1 0+(1105509679/2500000000 : ℝ)*X 1 1+(276377427/625000000 : ℝ)*X 1 2+(266121503/625000000 : ℝ)*X 2 0+(1105509679/2500000000 : ℝ)*X 2 1+(276377427/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-561576161/2500000000 : ℝ)*X 0 0+(5216150197/10000000000 : ℝ)*X 0 1+(5386046301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289106169/10000000000 : ℝ)*X 1 0+(-2149364723/10000000000 : ℝ)*X 1 1+(5386046257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057821219/2000000000 : ℝ)*X 2 0+(5386046459/10000000000 : ℝ)*X 2 1+(-2149364549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2247514889/5000000000 : ℝ)*X 0 0+(4303376173/10000000000 : ℝ)*X 0 1+(1075844099/2500000000 : ℝ)*X 0 2+(2247514889/5000000000 : ℝ)*X 1 0+(4303376173/10000000000 : ℝ)*X 1 1+(1075844099/2500000000 : ℝ)*X 1 2+(2247514889/5000000000 : ℝ)*X 2 0+(4303376173/10000000000 : ℝ)*X 2 1+(1075844099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2097808813/10000000000 : ℝ)*X 0 0+(170000857/312500000 : ℝ)*X 0 1+(82390459/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368998287/10000000000 : ℝ)*X 1 0+(-2193817667/10000000000 : ℝ)*X 1 1+(1054597871/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684499129/5000000000 : ℝ)*X 2 0+(2636494659/5000000000 : ℝ)*X 2 1+(-438763551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2119777423/5000000000 : ℝ)*X 0 0+(4431111187/10000000000 : ℝ)*X 0 1+(2215555617/5000000000 : ℝ)*X 0 2+(2119777423/5000000000 : ℝ)*X 1 0+(4431111187/10000000000 : ℝ)*X 1 1+(2215555617/5000000000 : ℝ)*X 1 2+(2119777423/5000000000 : ℝ)*X 2 0+(4431111187/10000000000 : ℝ)*X 2 1+(2215555617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1133_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-84038368120398168879788922300063/135050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2002653/100000000000000 : ℝ)*(upper0) + (20892453/12500000000000 : ℝ)*(lower2) + (45741867/20000000000000 : ℝ)*(lower3) + (391291974611749/10000000000000 : ℝ)*(major0) + (391291974611749/10000000000000 : ℝ)*(major1) + (391291974611749/10000000000000 : ℝ)*(major2) + (845504837/5000000000000 : ℝ)*(sp1) + (1539923577/25000000000000 : ℝ)*(sp3) + (1306418011003959/25000000000000 : ℝ)*(sp4) + (1306422160458791/25000000000000 : ℝ)*(sp5) + (5225408456378769/100000000000000 : ℝ)*(sp6) + (2620870312540231/100000000000000 : ℝ)*(sp7) + (8376979017/25000000000000 : ℝ)*(sp8) + (59419110627/20000000000000 : ℝ)*(sp14) + (131043823611727/5000000000000 : ℝ)*(f.failure) + (1045141110386381/20000000000000 : ℝ)*(f.sum) + (347354147259/337625000000000000000000000 : ℝ)*base65 + (3233533272107900007/270100000000000000000000000000000 : ℝ)*base67 + (2390691994685100007/270100000000000000000000000000000 : ℝ)*base69 + (1789423999883100007/270100000000000000000000000000000 : ℝ)*base71 + (6039151073021/675250000000000000000000000 : ℝ)*base73 + (1949285086612300007/270100000000000000000000000000000 : ℝ)*base75 + (3294849295958500007/270100000000000000000000000000000 : ℝ)*base77 + (17353202125263200007/270100000000000000000000000000000 : ℝ)*base79 + (125665209849/108040000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2452599/500000000000000000000 : ℝ)*base89 + (2452599/500000000000000000000 : ℝ)*base91 + (2452599/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14823/25000 : ℝ) ≤ (80076533133454296149157597134937/135050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13192787/25000000000000 : ℝ)*(upper0) + (120923571/100000000000000 : ℝ)*(lower1) + (209600997/50000000000000 : ℝ)*(upper4) + (397692550370247/10000000000000 : ℝ)*(major0) + (397692550370247/10000000000000 : ℝ)*(major1) + (397692550370247/10000000000000 : ℝ)*(major2) + (5270327838770817/100000000000000 : ℝ)*(sp0) + (2635168566279463/50000000000000 : ℝ)*(sp1) + (527032592340041/10000000000000 : ℝ)*(sp2) + (1331867683767967/50000000000000 : ℝ)*(sp3) + (1636705871/100000000000000 : ℝ)*(sp5) + (6422932193/50000000000000 : ℝ)*(sp6) + (3051840027/25000000000000 : ℝ)*(sp7) + (546524699/5000000000000 : ℝ)*(sp8) + (1331873787448021/50000000000000 : ℝ)*(f.failure) + (1317584692316199/25000000000000 : ℝ)*(f.sum) + (10984367948159/2701000000000000000000000000 : ℝ)*base66 + (1162128157681105021/270100000000000000000000000000000 : ℝ)*base67 + (1189768501665405021/270100000000000000000000000000000 : ℝ)*base69 + (1120252938212794979/270100000000000000000000000000000 : ℝ)*base72 + (7516664243061/2701000000000000000000000000 : ℝ)*base73 + (551091744916005021/270100000000000000000000000000000 : ℝ)*base75 + (1693483138961105021/270100000000000000000000000000000 : ℝ)*base77 + (2062314132817694979/270100000000000000000000000000000 : ℝ)*base80 + (2729873163429/1350500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (19636877/5000000000000000000000 : ℝ)*base89 + (19636877/5000000000000000000000 : ℝ)*base91 + (19636877/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79781/100000 : ℝ) ≤ (33670947140879078194538039423511/42203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7818589/12500000000000 : ℝ)*(upper0) + (13767527/25000000000000 : ℝ)*(lower3) + (9372267/20000000000000 : ℝ)*(upper4) + (138901840045147/3125000000000 : ℝ)*(major0) + (138901840045147/3125000000000 : ℝ)*(major1) + (138901840045147/3125000000000 : ℝ)*(major2) + (6832004117/10000000000000 : ℝ)*(sp1) + (12588140089/6250000000000 : ℝ)*(sp2) + (322964863/781250000000 : ℝ)*(sp3) + (434067737/12500000000000 : ℝ)*(sp4) + (5885950245666361/100000000000000 : ℝ)*(sp8) + (2942942699083543/50000000000000 : ℝ)*(sp9) + (5885752307966833/100000000000000 : ℝ)*(sp10) + (595425669958317/20000000000000 : ℝ)*(sp11) + (2977169689294049/100000000000000 : ℝ)*(f.failure) + (22992006711751/390625000000 : ℝ)*(f.sum) + (18633484210343/6752500000000000000000000000 : ℝ)*base66 + (167694613708443221/84406250000000000000000000000000 : ℝ)*base67 + (159107350827599471/84406250000000000000000000000000 : ℝ)*base69 + (105731745532068221/84406250000000000000000000000000 : ℝ)*base71 + (3494584436879/13505000000000000000000000000 : ℝ)*base73 + (822231079231818221/84406250000000000000000000000000 : ℝ)*base75 + (132649924108599471/84406250000000000000000000000000 : ℝ)*base77 + (2004308452882255721/84406250000000000000000000000000 : ℝ)*base79 + (40826186010871/13505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (39113287/10000000000000000000000 : ℝ)*base90 + (39113287/10000000000000000000000 : ℝ)*base92 + (39113287/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2597/3125 : ℝ) ≤ (-280572432032287849000211106354849/337625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5034207/100000000000000 : ℝ)*(upper1) + (3634521/25000000000000 : ℝ)*(upper3) + (6517757/12500000000000 : ℝ)*(lower4) + (2239875678509719/50000000000000 : ℝ)*(major0) + (2239875678509719/50000000000000 : ℝ)*(major1) + (2239875678509719/50000000000000 : ℝ)*(major2) + (85828443/20000000000000 : ℝ)*(sp4) + (697656849/2500000000000 : ℝ)*(sp5) + (89189059881/100000000000000 : ℝ)*(sp6) + (4908097879/20000000000000 : ℝ)*(sp7) + (149666554706597/2500000000000 : ℝ)*(sp12) + (1197326942226427/20000000000000 : ℝ)*(sp13) + (2993286714173107/50000000000000 : ℝ)*(sp14) + (600103230829459/20000000000000 : ℝ)*(sp15) + (300054069463669/10000000000000 : ℝ)*(f.failure) + (1197332523481219/20000000000000 : ℝ)*(f.sum) + (2114552488961/6752500000000000000000000000 : ℝ)*base66 + (4463939010872943283/1350500000000000000000000000000000 : ℝ)*base68 + (34727623417765443283/1350500000000000000000000000000000 : ℝ)*base70 + (12813106381717943283/1350500000000000000000000000000000 : ℝ)*base72 + (95684711433/844062500000000000000000000 : ℝ)*base73 + (55715747170242056717/1350500000000000000000000000000000 : ℝ)*base75 + (1496516710029443283/1350500000000000000000000000000000 : ℝ)*base78 + (7189180011847443283/1350500000000000000000000000000000 : ℝ)*base80 + (404434171293741/6752500000000000000000000000 : ℝ)*base82 + (9115347/1000000000000000000000 : ℝ)*base90 + (9115347/1000000000000000000000 : ℝ)*base92 + (9115347/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1133_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (79781/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2597/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1133_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1133_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (79781/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2597/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1133_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8325/2048 : ℝ) ≤ p) (hpb : p ≤ (4163/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149298137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(14823/25000 : ℝ) else (79781/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2597/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1133_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

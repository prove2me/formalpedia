-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:17.078505+00:00
-- url     : https://prove2.me/submissions/652fa53d-52de-4e0f-b6a8-c18d78a46c05

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
theorem support_rectangle_w1185_s3_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214313399/1000000000 : ℝ)*x 0 + (2712449537/5000000000 : ℝ)*x 1 + (654494913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214313399/1000000000 : ℝ)^4189 ≤ (6510103504699/50000000000000 : ℝ)^3165 := by
    have hnat : (214313399 : ℕ)^4189*50000000000000^3165 ≤ 6510103504699^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214313399 1000000000 6510103504699 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712449537/5000000000 : ℝ)^4189 ≤ (22254973931603/50000000000000 : ℝ)^3165 := by
    have hnat : (2712449537 : ℕ)^4189*50000000000000^3165 ≤ 22254973931603^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712449537 5000000000 22254973931603 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654494913/1250000000 : ℝ)^4189 ≤ (21234922556477/50000000000000 : ℝ)^3165 := by
    have hnat : (654494913 : ℕ)^4189*50000000000000^3165 ≤ 21234922556477^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654494913 1250000000 21234922556477 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214313399/1000000000 : ℝ), (2712449537/5000000000 : ℝ), (654494913/1250000000 : ℝ)] ![(6510103504699/50000000000000 : ℝ), (22254973931603/50000000000000 : ℝ), (21234922556477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214313399/1000000000 : ℝ)|^4189 ≤ (6510103504699/50000000000000 : ℝ)^3165
        have hw : |(-214313399/1000000000 : ℝ)|=(214313399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712449537/5000000000 : ℝ)|^4189 ≤ (22254973931603/50000000000000 : ℝ)^3165
        have hw : |(2712449537/5000000000 : ℝ)|=(2712449537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654494913/1250000000 : ℝ)|^4189 ≤ (21234922556477/50000000000000 : ℝ)^3165
        have hw : |(654494913/1250000000 : ℝ)|=(654494913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26763899/50000000 : ℝ)*x 0 + (-2239625951/10000000000 : ℝ)*x 1 + (5235959111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26763899/50000000 : ℝ)^4189 ≤ (21864235970339/50000000000000 : ℝ)^3165 := by
    have hnat : (26763899 : ℕ)^4189*50000000000000^3165 ≤ 21864235970339^3165*50000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26763899 50000000 21864235970339 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239625951/10000000000 : ℝ)^4189 ≤ (13801685004741/100000000000000 : ℝ)^3165 := by
    have hnat : (2239625951 : ℕ)^4189*100000000000000^3165 ≤ 13801685004741^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239625951 10000000000 13801685004741 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235959111/10000000000 : ℝ)^4189 ≤ (2654365190063/6250000000000 : ℝ)^3165 := by
    have hnat : (5235959111 : ℕ)^4189*6250000000000^3165 ≤ 2654365190063^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235959111 10000000000 2654365190063 6250000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26763899/50000000 : ℝ), (-2239625951/10000000000 : ℝ), (5235959111/10000000000 : ℝ)] ![(21864235970339/50000000000000 : ℝ), (13801685004741/100000000000000 : ℝ), (2654365190063/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26763899/50000000 : ℝ)|^4189 ≤ (21864235970339/50000000000000 : ℝ)^3165
        have hw : |(26763899/50000000 : ℝ)|=(26763899/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239625951/10000000000 : ℝ)|^4189 ≤ (13801685004741/100000000000000 : ℝ)^3165
        have hw : |(-2239625951/10000000000 : ℝ)|=(2239625951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235959111/10000000000 : ℝ)|^4189 ≤ (2654365190063/6250000000000 : ℝ)^3165
        have hw : |(5235959111/10000000000 : ℝ)|=(5235959111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334548743/625000000 : ℝ)*x 0 + (1308989767/2500000000 : ℝ)*x 1 + (-2239625891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334548743/625000000 : ℝ)^4189 ≤ (43728472892169/100000000000000 : ℝ)^3165 := by
    have hnat : (334548743 : ℕ)^4189*100000000000000^3165 ≤ 43728472892169^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334548743 625000000 43728472892169 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308989767/2500000000 : ℝ)^4189 ≤ (42469842579383/100000000000000 : ℝ)^3165 := by
    have hnat : (1308989767 : ℕ)^4189*100000000000000^3165 ≤ 42469842579383^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308989767 2500000000 42469842579383 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239625891/10000000000 : ℝ)^4189 ≤ (13801684515363/100000000000000 : ℝ)^3165 := by
    have hnat : (2239625891 : ℕ)^4189*100000000000000^3165 ≤ 13801684515363^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239625891 10000000000 13801684515363 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334548743/625000000 : ℝ), (1308989767/2500000000 : ℝ), (-2239625891/10000000000 : ℝ)] ![(43728472892169/100000000000000 : ℝ), (42469842579383/100000000000000 : ℝ), (13801684515363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334548743/625000000 : ℝ)|^4189 ≤ (43728472892169/100000000000000 : ℝ)^3165
        have hw : |(334548743/625000000 : ℝ)|=(334548743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308989767/2500000000 : ℝ)|^4189 ≤ (42469842579383/100000000000000 : ℝ)^3165
        have hw : |(1308989767/2500000000 : ℝ)|=(1308989767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239625891/10000000000 : ℝ)|^4189 ≤ (13801684515363/100000000000000 : ℝ)^3165
        have hw : |(-2239625891/10000000000 : ℝ)|=(2239625891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089163047/2500000000 : ℝ)*x 0 + (1042794171/2500000000 : ℝ)*x 1 + (91004811/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089163047/2500000000 : ℝ)^4189 ≤ (33296982885221/100000000000000 : ℝ)^3165 := by
    have hnat : (1089163047 : ℕ)^4189*100000000000000^3165 ≤ 33296982885221^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089163047 2500000000 33296982885221 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042794171/2500000000 : ℝ)^4189 ≤ (3143384744569/10000000000000 : ℝ)^3165 := by
    have hnat : (1042794171 : ℕ)^4189*10000000000000^3165 ≤ 3143384744569^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042794171 2500000000 3143384744569 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91004811/200000000 : ℝ)^4189 ≤ (35269169645739/100000000000000 : ℝ)^3165 := by
    have hnat : (91004811 : ℕ)^4189*100000000000000^3165 ≤ 35269169645739^3165*200000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91004811 200000000 35269169645739 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089163047/2500000000 : ℝ), (1042794171/2500000000 : ℝ), (91004811/200000000 : ℝ)] ![(33296982885221/100000000000000 : ℝ), (3143384744569/10000000000000 : ℝ), (35269169645739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089163047/2500000000 : ℝ)|^4189 ≤ (33296982885221/100000000000000 : ℝ)^3165
        have hw : |(1089163047/2500000000 : ℝ)|=(1089163047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042794171/2500000000 : ℝ)|^4189 ≤ (3143384744569/10000000000000 : ℝ)^3165
        have hw : |(1042794171/2500000000 : ℝ)|=(1042794171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91004811/200000000 : ℝ)|^4189 ≤ (35269169645739/100000000000000 : ℝ)^3165
        have hw : |(91004811/200000000 : ℝ)|=(91004811/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17145201/80000000 : ℝ)*x 0 + (5236671409/10000000000 : ℝ)*x 1 + (678022889/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17145201/80000000 : ℝ)^4189 ≤ (6510168374821/50000000000000 : ℝ)^3165 := by
    have hnat : (17145201 : ℕ)^4189*50000000000000^3165 ≤ 6510168374821^3165*80000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17145201 80000000 6510168374821 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236671409/10000000000 : ℝ)^4189 ≤ (42477490062973/100000000000000 : ℝ)^3165 := by
    have hnat : (5236671409 : ℕ)^4189*100000000000000^3165 ≤ 42477490062973^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236671409 10000000000 42477490062973 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678022889/1250000000 : ℝ)^4189 ≤ (11125543294701/25000000000000 : ℝ)^3165 := by
    have hnat : (678022889 : ℕ)^4189*25000000000000^3165 ≤ 11125543294701^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678022889 1250000000 11125543294701 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17145201/80000000 : ℝ), (5236671409/10000000000 : ℝ), (678022889/1250000000 : ℝ)] ![(6510168374821/50000000000000 : ℝ), (42477490062973/100000000000000 : ℝ), (11125543294701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17145201/80000000 : ℝ)|^4189 ≤ (6510168374821/50000000000000 : ℝ)^3165
        have hw : |(-17145201/80000000 : ℝ)|=(17145201/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236671409/10000000000 : ℝ)|^4189 ≤ (42477490062973/100000000000000 : ℝ)^3165
        have hw : |(5236671409/10000000000 : ℝ)|=(5236671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678022889/1250000000 : ℝ)|^4189 ≤ (11125543294701/25000000000000 : ℝ)^3165
        have hw : |(678022889/1250000000 : ℝ)|=(678022889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652382577/5000000000 : ℝ)*x 0 + (-2051401707/10000000000 : ℝ)*x 1 + (5424183057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652382577/5000000000 : ℝ)^4189 ≤ (43210073881541/100000000000000 : ℝ)^3165 := by
    have hnat : (2652382577 : ℕ)^4189*100000000000000^3165 ≤ 43210073881541^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652382577 5000000000 43210073881541 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051401707/10000000000 : ℝ)^4189 ≤ (12287753520689/100000000000000 : ℝ)^3165 := by
    have hnat : (2051401707 : ℕ)^4189*100000000000000^3165 ≤ 12287753520689^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051401707 10000000000 12287753520689 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424183057/10000000000 : ℝ)^4189 ≤ (695346446587/1562500000000 : ℝ)^3165 := by
    have hnat : (5424183057 : ℕ)^4189*1562500000000^3165 ≤ 695346446587^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424183057 10000000000 695346446587 1562500000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652382577/5000000000 : ℝ), (-2051401707/10000000000 : ℝ), (5424183057/10000000000 : ℝ)] ![(43210073881541/100000000000000 : ℝ), (12287753520689/100000000000000 : ℝ), (695346446587/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652382577/5000000000 : ℝ)|^4189 ≤ (43210073881541/100000000000000 : ℝ)^3165
        have hw : |(2652382577/5000000000 : ℝ)|=(2652382577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051401707/10000000000 : ℝ)|^4189 ≤ (12287753520689/100000000000000 : ℝ)^3165
        have hw : |(-2051401707/10000000000 : ℝ)|=(2051401707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424183057/10000000000 : ℝ)|^4189 ≤ (695346446587/1562500000000 : ℝ)^3165
        have hw : |(5424183057/10000000000 : ℝ)|=(5424183057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530476481/1000000000 : ℝ)*x 0 + (2712091717/5000000000 : ℝ)*x 1 + (-2051401659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530476481/1000000000 : ℝ)^4189 ≤ (43210070172907/100000000000000 : ℝ)^3165 := by
    have hnat : (530476481 : ℕ)^4189*100000000000000^3165 ≤ 43210070172907^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530476481 1000000000 43210070172907 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712091717/5000000000 : ℝ)^4189 ≤ (44502176675351/100000000000000 : ℝ)^3165 := by
    have hnat : (2712091717 : ℕ)^4189*100000000000000^3165 ≤ 44502176675351^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712091717 5000000000 44502176675351 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051401659/10000000000 : ℝ)^4189 ≤ (245755062803/2000000000000 : ℝ)^3165 := by
    have hnat : (2051401659 : ℕ)^4189*2000000000000^3165 ≤ 245755062803^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051401659 10000000000 245755062803 2000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530476481/1000000000 : ℝ), (2712091717/5000000000 : ℝ), (-2051401659/10000000000 : ℝ)] ![(43210070172907/100000000000000 : ℝ), (44502176675351/100000000000000 : ℝ), (245755062803/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530476481/1000000000 : ℝ)|^4189 ≤ (43210070172907/100000000000000 : ℝ)^3165
        have hw : |(530476481/1000000000 : ℝ)|=(530476481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712091717/5000000000 : ℝ)|^4189 ≤ (44502176675351/100000000000000 : ℝ)^3165
        have hw : |(2712091717/5000000000 : ℝ)|=(2712091717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051401659/10000000000 : ℝ)|^4189 ≤ (245755062803/2000000000000 : ℝ)^3165
        have hw : |(-2051401659/10000000000 : ℝ)|=(2051401659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s3_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356684833/10000000000 : ℝ)*x 0 + (4548811499/10000000000 : ℝ)*x 1 + (4172613261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356684833/10000000000 : ℝ)^4189 ≤ (4162164138387/12500000000000 : ℝ)^3165 := by
    have hnat : (4356684833 : ℕ)^4189*12500000000000^3165 ≤ 4162164138387^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356684833 10000000000 4162164138387 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4548811499/10000000000 : ℝ)^4189 ≤ (220340687561/625000000000 : ℝ)^3165 := by
    have hnat : (4548811499 : ℕ)^4189*625000000000^3165 ≤ 220340687561^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548811499 10000000000 220340687561 625000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172613261/10000000000 : ℝ)^4189 ≤ (3931022108589/12500000000000 : ℝ)^3165 := by
    have hnat : (4172613261 : ℕ)^4189*12500000000000^3165 ≤ 3931022108589^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172613261 10000000000 3931022108589 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356684833/10000000000 : ℝ), (4548811499/10000000000 : ℝ), (4172613261/10000000000 : ℝ)] ![(4162164138387/12500000000000 : ℝ), (220340687561/625000000000 : ℝ), (3931022108589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356684833/10000000000 : ℝ)|^4189 ≤ (4162164138387/12500000000000 : ℝ)^3165
        have hw : |(4356684833/10000000000 : ℝ)|=(4356684833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4548811499/10000000000 : ℝ)|^4189 ≤ (220340687561/625000000000 : ℝ)^3165
        have hw : |(4548811499/10000000000 : ℝ)|=(4548811499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172613261/10000000000 : ℝ)|^4189 ≤ (3931022108589/12500000000000 : ℝ)^3165
        have hw : |(4172613261/10000000000 : ℝ)|=(4172613261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10759/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (463/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (463/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (463/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (463/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (463/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (463/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (463/5000 : ℝ) ^ (8377/2048 : ℝ) ≤ (2965280778527831/50000000000000000000 : ℝ) := by
    have hpowers : (463/5000 : ℝ)^8377 ≤ (2965280778527831/50000000000000000000 : ℝ)^2048 := by
      have hnat : (463 : ℕ)^8377*50000000000000000000^2048 ≤ 2965280778527831^2048*5000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        463 5000 2965280778527831 50000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (463/5000 : ℝ)) (X := (2965280778527831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8189/50000 : ℝ) ^ (8377/2048 : ℝ) ≤ (30551747741187483/50000000000000000000 : ℝ) := by
    have hpowers : (8189/50000 : ℝ)^8377 ≤ (30551747741187483/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8189 : ℕ)^8377*50000000000000000000^2048 ≤ 30551747741187483^2048*50000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8189 50000 30551747741187483 50000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8189/50000 : ℝ)) (X := (30551747741187483/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002965280778527831/25000000000000000000 : ℝ) ≤ (1000028996647713/1000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25002965280778527831/25000000000000000000 : ℝ)^2048 ≤ (1000028996647713/1000000000000000 : ℝ)^8377 := by
      have hnat : (25002965280778527831 : ℕ)^2048*1000000000000000^8377 ≤ 1000028996647713^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002965280778527831 25000000000000000000 1000028996647713 1000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028996647713/1000000000000000 : ℝ)) (X := (25002965280778527831/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25016758514259857657/25000000000000000000 : ℝ) ≤ (1250204803327299/1250000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25016758514259857657/25000000000000000000 : ℝ)^2048 ≤ (1250204803327299/1250000000000000 : ℝ)^8377 := by
      have hnat : (25016758514259857657 : ℕ)^2048*1250000000000000^8377 ≤ 1250204803327299^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016758514259857657 25000000000000000000 1250204803327299 1250000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250204803327299/1250000000000000 : ℝ)) (X := (25016758514259857657/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030551747741187483/25000000000000000000 : ℝ) ≤ (5001493443379827/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25030551747741187483/25000000000000000000 : ℝ)^2048 ≤ (5001493443379827/5000000000000000 : ℝ)^8377 := by
      have hnat : (25030551747741187483 : ℕ)^2048*5000000000000000^8377 ≤ 5001493443379827^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030551747741187483 25000000000000000000 5001493443379827 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001493443379827/5000000000000000 : ℝ)) (X := (25030551747741187483/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2965280778527831/50000000000000000000 : ℝ) ≤ ((711570904995680391/711800000000000000 : ℝ)+2*(674230070631/355900000000000 : ℝ)*(463/5000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (711570904995680391/711800000000000000 : ℝ)+2*(674230070631/355900000000000 : ℝ)*(463/5000 : ℝ)=(1000028996647713/1000000000000000 : ℝ) by norm_num, show 1+2*(2965280778527831/50000000000000000000 : ℝ)=(25002965280778527831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30551747741187483/50000000000000000000 : ℝ)+(2965280778527831/50000000000000000000 : ℝ) ≤ ((711570904995680391/711800000000000000 : ℝ)+(674230070631/355900000000000 : ℝ)*((8189/50000 : ℝ)+(463/5000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (711570904995680391/711800000000000000 : ℝ)+(674230070631/355900000000000 : ℝ)*((8189/50000 : ℝ)+(463/5000 : ℝ))=(1250204803327299/1250000000000000 : ℝ) by norm_num, show 1+(30551747741187483/50000000000000000000 : ℝ)+(2965280778527831/50000000000000000000 : ℝ)=(25016758514259857657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30551747741187483/50000000000000000000 : ℝ) ≤ ((711570904995680391/711800000000000000 : ℝ)+2*(674230070631/355900000000000 : ℝ)*(8189/50000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (711570904995680391/711800000000000000 : ℝ)+2*(674230070631/355900000000000 : ℝ)*(8189/50000 : ℝ)=(5001493443379827/5000000000000000 : ℝ) by norm_num, show 1+2*(30551747741187483/50000000000000000000 : ℝ)=(25030551747741187483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (711570904995680391/711800000000000000 : ℝ)*(X 1 0+X 2 0)+(674230070631/355900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (463/5000 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (711570904995680391/711800000000000000 : ℝ)) (alpha := (674230070631/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (711570904995680391/711800000000000000 : ℝ)*(X 0 1+X 2 1)+(674230070631/355900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (463/5000 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (711570904995680391/711800000000000000 : ℝ)) (alpha := (674230070631/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (711570904995680391/711800000000000000 : ℝ)*(X 0 2+X 1 2)+(674230070631/355900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (463/5000 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (711570904995680391/711800000000000000 : ℝ)) (alpha := (674230070631/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214313399/1000000000 : ℝ)*X 0 0+(2712449537/5000000000 : ℝ)*X 0 1+(654494913/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26763899/50000000 : ℝ)*X 1 0+(-2239625951/10000000000 : ℝ)*X 1 1+(5235959111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334548743/625000000 : ℝ)*X 2 0+(1308989767/2500000000 : ℝ)*X 2 1+(-2239625891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089163047/2500000000 : ℝ)*X 0 0+(1042794171/2500000000 : ℝ)*X 0 1+(91004811/200000000 : ℝ)*X 0 2+(1089163047/2500000000 : ℝ)*X 1 0+(1042794171/2500000000 : ℝ)*X 1 1+(91004811/200000000 : ℝ)*X 1 2+(1089163047/2500000000 : ℝ)*X 2 0+(1042794171/2500000000 : ℝ)*X 2 1+(91004811/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17145201/80000000 : ℝ)*X 0 0+(5236671409/10000000000 : ℝ)*X 0 1+(678022889/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652382577/5000000000 : ℝ)*X 1 0+(-2051401707/10000000000 : ℝ)*X 1 1+(5424183057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530476481/1000000000 : ℝ)*X 2 0+(2712091717/5000000000 : ℝ)*X 2 1+(-2051401659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356684833/10000000000 : ℝ)*X 0 0+(4548811499/10000000000 : ℝ)*X 0 1+(4172613261/10000000000 : ℝ)*X 0 2+(4356684833/10000000000 : ℝ)*X 1 0+(4548811499/10000000000 : ℝ)*X 1 1+(4172613261/10000000000 : ℝ)*X 1 2+(4356684833/10000000000 : ℝ)*X 2 0+(4548811499/10000000000 : ℝ)*X 2 1+(4172613261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18840163434567088330575303/8897500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (331632439/50000000000000 : ℝ)*(base19) + (692180667/100000000000000 : ℝ)*(base23) + (31097837/100000000000000 : ℝ)*(lower2) + (38380759/100000000000000 : ℝ)*(upper3) + (76802367/100000000000000 : ℝ)*(upper5) + (991349361492189/25000000000000 : ℝ)*(major0) + (991349361492189/25000000000000 : ℝ)*(major1) + (991349361492189/25000000000000 : ℝ)*(major2) + (2646349346769121/50000000000000 : ℝ)*(sp0) + (165397104741679/3125000000000 : ℝ)*(sp1) + (2646353661408969/50000000000000 : ℝ)*(sp2) + (41220036386689/1562500000000 : ℝ)*(sp3) + (9321460363/100000000000000 : ℝ)*(sp4) + (559701071/12500000000000 : ℝ)*(sp7) + (329760850794583/12500000000000 : ℝ)*(f.failure) + (1058541602999721/20000000000000 : ℝ)*(f.sum) + (125515959402379/17795000000000000000000000000 : ℝ)*base66 + (98874984661961101/17795000000000000000000000000000 : ℝ)*base68 + (132217295079243899/17795000000000000000000000000000 : ℝ)*base69 + (197254971439843899/17795000000000000000000000000000 : ℝ)*base71 + (26478689639131/4448750000000000000000000000 : ℝ)*base74 + (101504858596963899/17795000000000000000000000000000 : ℝ)*base75 + (119405924360636101/17795000000000000000000000000000 : ℝ)*base78 + (9213404019883899/17795000000000000000000000000000 : ℝ)*base79 + (13108488777757/8897500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (321027/62500000000000000000 : ℝ)*base89 + (321027/62500000000000000000 : ℝ)*base91 + (321027/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2690815068121763970834363/711800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1355431657/100000000000000 : ℝ)*(base19) + (248247291/20000000000000 : ℝ)*(base23) + (14183073/20000000000000 : ℝ)*(upper3) + (115898833/100000000000000 : ℝ)*(lower4) + (43301161/25000000000000 : ℝ)*(upper5) + (79911691876631/2000000000000 : ℝ)*(major0) + (79911691876631/2000000000000 : ℝ)*(major1) + (79911691876631/2000000000000 : ℝ)*(major2) + (13812638143/50000000000000 : ℝ)*(sp1) + (7269602851/25000000000000 : ℝ)*(sp2) + (1066599889411531/20000000000000 : ℝ)*(sp4) + (5332970466349713/100000000000000 : ℝ)*(sp5) + (1066593825481959/20000000000000 : ℝ)*(sp6) + (1329084807297777/50000000000000 : ℝ)*(sp7) + (1329084807297777/50000000000000 : ℝ)*(f.failure) + (1066599889411531/20000000000000 : ℝ)*(f.sum) + (278220343703/3559000000000000000000000000 : ℝ)*base66 + (6563848998882879/1423600000000000000000000000000 : ℝ)*base68 + (7905738078749679/1423600000000000000000000000000 : ℝ)*base70 + (304174324982321/1423600000000000000000000000000 : ℝ)*base71 + (7204894774661/3559000000000000000000000000 : ℝ)*base74 + (29436310072386879/1423600000000000000000000000000 : ℝ)*base76 + (7327884883822321/1423600000000000000000000000000 : ℝ)*base77 + (3807277662608079/1423600000000000000000000000000 : ℝ)*base80 + (797734801733/711800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1367813/250000000000000000000 : ℝ)*base89 + (1367813/250000000000000000000 : ℝ)*base91 + (1367813/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s4_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145807629/10000000000 : ℝ)*x 0 + (2699952657/5000000000 : ℝ)*x 1 + (1051840573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145807629/10000000000 : ℝ)^4189 ≤ (13041709837913/100000000000000 : ℝ)^3165 := by
    have hnat : (2145807629 : ℕ)^4189*100000000000000^3165 ≤ 13041709837913^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145807629 10000000000 13041709837913 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699952657/5000000000 : ℝ)^4189 ≤ (8847747095043/20000000000000 : ℝ)^3165 := by
    have hnat : (2699952657 : ℕ)^4189*20000000000000^3165 ≤ 8847747095043^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699952657 5000000000 8847747095043 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051840573/2000000000 : ℝ)^4189 ≤ (42719554679837/100000000000000 : ℝ)^3165 := by
    have hnat : (1051840573 : ℕ)^4189*100000000000000^3165 ≤ 42719554679837^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051840573 2000000000 42719554679837 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145807629/10000000000 : ℝ), (2699952657/5000000000 : ℝ), (1051840573/2000000000 : ℝ)] ![(13041709837913/100000000000000 : ℝ), (8847747095043/20000000000000 : ℝ), (42719554679837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145807629/10000000000 : ℝ)|^4189 ≤ (13041709837913/100000000000000 : ℝ)^3165
        have hw : |(-2145807629/10000000000 : ℝ)|=(2145807629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699952657/5000000000 : ℝ)|^4189 ≤ (8847747095043/20000000000000 : ℝ)^3165
        have hw : |(2699952657/5000000000 : ℝ)|=(2699952657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051840573/2000000000 : ℝ)|^4189 ≤ (42719554679837/100000000000000 : ℝ)^3165
        have hw : |(1051840573/2000000000 : ℝ)|=(1051840573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346512509/10000000000 : ℝ)*x 0 + (-2217280407/10000000000 : ℝ)*x 1 + (328700191/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346512509/10000000000 : ℝ)^4189 ≤ (43660720405297/100000000000000 : ℝ)^3165 := by
    have hnat : (5346512509 : ℕ)^4189*100000000000000^3165 ≤ 43660720405297^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346512509 10000000000 43660720405297 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217280407/10000000000 : ℝ)^4189 ≤ (13619722845707/100000000000000 : ℝ)^3165 := by
    have hnat : (2217280407 : ℕ)^4189*100000000000000^3165 ≤ 13619722845707^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217280407 10000000000 13619722845707 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328700191/625000000 : ℝ)^4189 ≤ (42719556733253/100000000000000 : ℝ)^3165 := by
    have hnat : (328700191 : ℕ)^4189*100000000000000^3165 ≤ 42719556733253^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328700191 625000000 42719556733253 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346512509/10000000000 : ℝ), (-2217280407/10000000000 : ℝ), (328700191/625000000 : ℝ)] ![(43660720405297/100000000000000 : ℝ), (13619722845707/100000000000000 : ℝ), (42719556733253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346512509/10000000000 : ℝ)|^4189 ≤ (43660720405297/100000000000000 : ℝ)^3165
        have hw : |(5346512509/10000000000 : ℝ)|=(5346512509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217280407/10000000000 : ℝ)|^4189 ≤ (13619722845707/100000000000000 : ℝ)^3165
        have hw : |(-2217280407/10000000000 : ℝ)|=(2217280407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328700191/625000000 : ℝ)|^4189 ≤ (42719556733253/100000000000000 : ℝ)^3165
        have hw : |(328700191/625000000 : ℝ)|=(328700191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346512227/10000000000 : ℝ)*x 0 + (328700183/625000000 : ℝ)*x 1 + (-2217280951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346512227/10000000000 : ℝ)^4189 ≤ (43660717357359/100000000000000 : ℝ)^3165 := by
    have hnat : (5346512227 : ℕ)^4189*100000000000000^3165 ≤ 43660717357359^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346512227 10000000000 43660717357359 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328700183/625000000 : ℝ)^4189 ≤ (21359777678571/50000000000000 : ℝ)^3165 := by
    have hnat : (328700183 : ℕ)^4189*50000000000000^3165 ≤ 21359777678571^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328700183 625000000 21359777678571 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217280951/10000000000 : ℝ)^4189 ≤ (13619727268363/100000000000000 : ℝ)^3165 := by
    have hnat : (2217280951 : ℕ)^4189*100000000000000^3165 ≤ 13619727268363^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217280951 10000000000 13619727268363 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346512227/10000000000 : ℝ), (328700183/625000000 : ℝ), (-2217280951/10000000000 : ℝ)] ![(43660717357359/100000000000000 : ℝ), (21359777678571/50000000000000 : ℝ), (13619727268363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346512227/10000000000 : ℝ)|^4189 ≤ (43660717357359/100000000000000 : ℝ)^3165
        have hw : |(5346512227/10000000000 : ℝ)|=(5346512227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328700183/625000000 : ℝ)|^4189 ≤ (21359777678571/50000000000000 : ℝ)^3165
        have hw : |(328700183/625000000 : ℝ)|=(328700183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217280951/10000000000 : ℝ)|^4189 ≤ (13619727268363/100000000000000 : ℝ)^3165
        have hw : |(-2217280951/10000000000 : ℝ)|=(2217280951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4358251731/10000000000 : ℝ)*x 0 + (527419887/1250000000 : ℝ)*x 1 + (4501646427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358251731/10000000000 : ℝ)^4189 ≤ (3331316407123/10000000000000 : ℝ)^3165 := by
    have hnat : (4358251731 : ℕ)^4189*10000000000000^3165 ≤ 3331316407123^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358251731 10000000000 3331316407123 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527419887/1250000000 : ℝ)^4189 ≤ (6383064285159/20000000000000 : ℝ)^3165 := by
    have hnat : (527419887 : ℕ)^4189*20000000000000^3165 ≤ 6383064285159^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527419887 1250000000 6383064285159 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501646427/10000000000 : ℝ)^4189 ≤ (1738575724083/5000000000000 : ℝ)^3165 := by
    have hnat : (4501646427 : ℕ)^4189*5000000000000^3165 ≤ 1738575724083^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501646427 10000000000 1738575724083 5000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358251731/10000000000 : ℝ), (527419887/1250000000 : ℝ), (4501646427/10000000000 : ℝ)] ![(3331316407123/10000000000000 : ℝ), (6383064285159/20000000000000 : ℝ), (1738575724083/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358251731/10000000000 : ℝ)|^4189 ≤ (3331316407123/10000000000000 : ℝ)^3165
        have hw : |(4358251731/10000000000 : ℝ)|=(4358251731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527419887/1250000000 : ℝ)|^4189 ≤ (6383064285159/20000000000000 : ℝ)^3165
        have hw : |(527419887/1250000000 : ℝ)|=(527419887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501646427/10000000000 : ℝ)|^4189 ≤ (1738575724083/5000000000000 : ℝ)^3165
        have hw : |(4501646427/10000000000 : ℝ)|=(4501646427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072907057/5000000000 : ℝ)*x 0 + (328724927/625000000 : ℝ)*x 1 + (2699753947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072907057/5000000000 : ℝ)^4189 ≤ (13041762004279/100000000000000 : ℝ)^3165 := by
    have hnat : (1072907057 : ℕ)^4189*100000000000000^3165 ≤ 13041762004279^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072907057 5000000000 13041762004279 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328724927/625000000 : ℝ)^4189 ≤ (5340476464969/12500000000000 : ℝ)^3165 := by
    have hnat : (328724927 : ℕ)^4189*12500000000000^3165 ≤ 5340476464969^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328724927 625000000 5340476464969 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699753947/5000000000 : ℝ)^4189 ≤ (4423442626427/10000000000000 : ℝ)^3165 := by
    have hnat : (2699753947 : ℕ)^4189*10000000000000^3165 ≤ 4423442626427^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699753947 5000000000 4423442626427 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072907057/5000000000 : ℝ), (328724927/625000000 : ℝ), (2699753947/5000000000 : ℝ)] ![(13041762004279/100000000000000 : ℝ), (5340476464969/12500000000000 : ℝ), (4423442626427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072907057/5000000000 : ℝ)|^4189 ≤ (13041762004279/100000000000000 : ℝ)^3165
        have hw : |(-1072907057/5000000000 : ℝ)|=(1072907057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328724927/625000000 : ℝ)|^4189 ≤ (5340476464969/12500000000000 : ℝ)^3165
        have hw : |(328724927/625000000 : ℝ)|=(328724927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699753947/5000000000 : ℝ)|^4189 ≤ (4423442626427/10000000000000 : ℝ)^3165
        have hw : |(2699753947/5000000000 : ℝ)|=(2699753947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062151083/2000000000 : ℝ)*x 0 + (-2076975731/10000000000 : ℝ)*x 1 + (5399507699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062151083/2000000000 : ℝ)^4189 ≤ (10818666537787/25000000000000 : ℝ)^3165 := by
    have hnat : (1062151083 : ℕ)^4189*25000000000000^3165 ≤ 10818666537787^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062151083 2000000000 10818666537787 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076975731/10000000000 : ℝ)^4189 ≤ (12490909689959/100000000000000 : ℝ)^3165 := by
    have hnat : (2076975731 : ℕ)^4189*100000000000000^3165 ≤ 12490909689959^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076975731 10000000000 12490909689959 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399507699/10000000000 : ℝ)^4189 ≤ (44234424149917/100000000000000 : ℝ)^3165 := by
    have hnat : (5399507699 : ℕ)^4189*100000000000000^3165 ≤ 44234424149917^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399507699 10000000000 44234424149917 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062151083/2000000000 : ℝ), (-2076975731/10000000000 : ℝ), (5399507699/10000000000 : ℝ)] ![(10818666537787/25000000000000 : ℝ), (12490909689959/100000000000000 : ℝ), (44234424149917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062151083/2000000000 : ℝ)|^4189 ≤ (10818666537787/25000000000000 : ℝ)^3165
        have hw : |(1062151083/2000000000 : ℝ)|=(1062151083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076975731/10000000000 : ℝ)|^4189 ≤ (12490909689959/100000000000000 : ℝ)^3165
        have hw : |(-2076975731/10000000000 : ℝ)|=(2076975731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399507699/10000000000 : ℝ)|^4189 ≤ (44234424149917/100000000000000 : ℝ)^3165
        have hw : |(5399507699/10000000000 : ℝ)|=(5399507699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212430181/400000000 : ℝ)*x 0 + (5399508749/10000000000 : ℝ)*x 1 + (-1038487753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212430181/400000000 : ℝ)^4189 ≤ (5409332069079/12500000000000 : ℝ)^3165 := by
    have hnat : (212430181 : ℕ)^4189*12500000000000^3165 ≤ 5409332069079^3165*400000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212430181 400000000 5409332069079 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399508749/10000000000 : ℝ)^4189 ≤ (8846887106979/20000000000000 : ℝ)^3165 := by
    have hnat : (5399508749 : ℕ)^4189*20000000000000^3165 ≤ 8846887106979^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399508749 10000000000 8846887106979 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038487753/5000000000 : ℝ)^4189 ≤ (1561363487377/12500000000000 : ℝ)^3165 := by
    have hnat : (1038487753 : ℕ)^4189*12500000000000^3165 ≤ 1561363487377^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038487753 5000000000 1561363487377 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212430181/400000000 : ℝ), (5399508749/10000000000 : ℝ), (-1038487753/5000000000 : ℝ)] ![(5409332069079/12500000000000 : ℝ), (8846887106979/20000000000000 : ℝ), (1561363487377/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212430181/400000000 : ℝ)|^4189 ≤ (5409332069079/12500000000000 : ℝ)^3165
        have hw : |(212430181/400000000 : ℝ)|=(212430181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399508749/10000000000 : ℝ)|^4189 ≤ (8846887106979/20000000000000 : ℝ)^3165
        have hw : |(5399508749/10000000000 : ℝ)|=(5399508749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038487753/5000000000 : ℝ)|^4189 ≤ (1561363487377/12500000000000 : ℝ)^3165
        have hw : |(-1038487753/5000000000 : ℝ)|=(1038487753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s4_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544783167/1250000000 : ℝ)*x 0 + (4500852731/10000000000 : ℝ)*x 1 + (2110077901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544783167/1250000000 : ℝ)^4189 ≤ (3331330170943/10000000000000 : ℝ)^3165 := by
    have hnat : (544783167 : ℕ)^4189*10000000000000^3165 ≤ 3331330170943^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544783167 1250000000 3331330170943 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500852731/10000000000 : ℝ)^4189 ≤ (17381700281257/50000000000000 : ℝ)^3165 := by
    have hnat : (4500852731 : ℕ)^4189*50000000000000^3165 ≤ 17381700281257^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500852731 10000000000 17381700281257 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110077901/5000000000 : ℝ)^4189 ≤ (15961648856039/50000000000000 : ℝ)^3165 := by
    have hnat : (2110077901 : ℕ)^4189*50000000000000^3165 ≤ 15961648856039^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110077901 5000000000 15961648856039 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544783167/1250000000 : ℝ), (4500852731/10000000000 : ℝ), (2110077901/5000000000 : ℝ)] ![(3331330170943/10000000000000 : ℝ), (17381700281257/50000000000000 : ℝ), (15961648856039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544783167/1250000000 : ℝ)|^4189 ≤ (3331330170943/10000000000000 : ℝ)^3165
        have hw : |(544783167/1250000000 : ℝ)|=(544783167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500852731/10000000000 : ℝ)|^4189 ≤ (17381700281257/50000000000000 : ℝ)^3165
        have hw : |(4500852731/10000000000 : ℝ)|=(4500852731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110077901/5000000000 : ℝ)|^4189 ≤ (15961648856039/50000000000000 : ℝ)^3165
        have hw : |(2110077901/5000000000 : ℝ)|=(2110077901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2251/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10759/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (5477666963755889/50000000000000000000 : ℝ) := by
    have hpowers : (10759/100000 : ℝ)^8377 ≤ (5477666963755889/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10759 : ℕ)^8377*50000000000000000000^2048 ≤ 5477666963755889^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10759 100000 5477666963755889 50000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10759/100000 : ℝ)) (X := (5477666963755889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (3989571175531259/10000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^8377 ≤ (3989571175531259/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14757 : ℕ)^8377*10000000000000000000^2048 ≤ 3989571175531259^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 3989571175531259 10000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (3989571175531259/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005477666963755889/25000000000000000000 : ℝ) ≤ (2500133906333137/2500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25005477666963755889/25000000000000000000 : ℝ)^2048 ≤ (2500133906333137/2500000000000000 : ℝ)^8377 := by
      have hnat : (25005477666963755889 : ℕ)^2048*2500000000000000^8377 ≤ 2500133906333137^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005477666963755889 25000000000000000000 2500133906333137 2500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500133906333137/2500000000000000 : ℝ)) (X := (25005477666963755889/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253178190355176523/6250000000000000000 : ℝ) ≤ (500062148109199/500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (6253178190355176523/6250000000000000000 : ℝ)^2048 ≤ (500062148109199/500000000000000 : ℝ)^8377 := by
      have hnat : (6253178190355176523 : ℕ)^2048*500000000000000^8377 ≤ 500062148109199^8377*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253178190355176523 6250000000000000000 500062148109199 500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500062148109199/500000000000000 : ℝ)) (X := (6253178190355176523/6250000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003989571175531259/5000000000000000000 : ℝ) ≤ (2500487574758853/2500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (5003989571175531259/5000000000000000000 : ℝ)^2048 ≤ (2500487574758853/2500000000000000 : ℝ)^8377 := by
      have hnat : (5003989571175531259 : ℕ)^2048*2500000000000000^8377 ≤ 2500487574758853^8377*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003989571175531259 5000000000000000000 2500487574758853 2500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500487574758853/2500000000000000 : ℝ)) (X := (5003989571175531259/5000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5477666963755889/50000000000000000000 : ℝ) ≤ ((4995865119463801641/4997500000000000000 : ℝ)+2*(88417106429/49975000000000 : ℝ)*(10759/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (4995865119463801641/4997500000000000000 : ℝ)+2*(88417106429/49975000000000 : ℝ)*(10759/100000 : ℝ)=(2500133906333137/2500000000000000 : ℝ) by norm_num, show 1+2*(5477666963755889/50000000000000000000 : ℝ)=(25005477666963755889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3989571175531259/10000000000000000000 : ℝ)+(5477666963755889/50000000000000000000 : ℝ) ≤ ((4995865119463801641/4997500000000000000 : ℝ)+(88417106429/49975000000000 : ℝ)*((14757/100000 : ℝ)+(10759/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (4995865119463801641/4997500000000000000 : ℝ)+(88417106429/49975000000000 : ℝ)*((14757/100000 : ℝ)+(10759/100000 : ℝ))=(500062148109199/500000000000000 : ℝ) by norm_num, show 1+(3989571175531259/10000000000000000000 : ℝ)+(5477666963755889/50000000000000000000 : ℝ)=(6253178190355176523/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3989571175531259/10000000000000000000 : ℝ) ≤ ((4995865119463801641/4997500000000000000 : ℝ)+2*(88417106429/49975000000000 : ℝ)*(14757/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (4995865119463801641/4997500000000000000 : ℝ)+2*(88417106429/49975000000000 : ℝ)*(14757/100000 : ℝ)=(2500487574758853/2500000000000000 : ℝ) by norm_num, show 1+2*(3989571175531259/10000000000000000000 : ℝ)=(5003989571175531259/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4995865119463801641/4997500000000000000 : ℝ)*(X 1 0+X 2 0)+(88417106429/49975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4995865119463801641/4997500000000000000 : ℝ)) (alpha := (88417106429/49975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4995865119463801641/4997500000000000000 : ℝ)*(X 0 1+X 2 1)+(88417106429/49975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4995865119463801641/4997500000000000000 : ℝ)) (alpha := (88417106429/49975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4995865119463801641/4997500000000000000 : ℝ)*(X 0 2+X 1 2)+(88417106429/49975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4995865119463801641/4997500000000000000 : ℝ)) (alpha := (88417106429/49975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2145807629/10000000000 : ℝ)*X 0 0+(2699952657/5000000000 : ℝ)*X 0 1+(1051840573/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346512509/10000000000 : ℝ)*X 1 0+(-2217280407/10000000000 : ℝ)*X 1 1+(328700191/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346512227/10000000000 : ℝ)*X 2 0+(328700183/625000000 : ℝ)*X 2 1+(-2217280951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358251731/10000000000 : ℝ)*X 0 0+(527419887/1250000000 : ℝ)*X 0 1+(4501646427/10000000000 : ℝ)*X 0 2+(4358251731/10000000000 : ℝ)*X 1 0+(527419887/1250000000 : ℝ)*X 1 1+(4501646427/10000000000 : ℝ)*X 1 2+(4358251731/10000000000 : ℝ)*X 2 0+(527419887/1250000000 : ℝ)*X 2 1+(4501646427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072907057/5000000000 : ℝ)*X 0 0+(328724927/625000000 : ℝ)*X 0 1+(2699753947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062151083/2000000000 : ℝ)*X 1 0+(-2076975731/10000000000 : ℝ)*X 1 1+(5399507699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212430181/400000000 : ℝ)*X 2 0+(5399508749/10000000000 : ℝ)*X 2 1+(-1038487753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544783167/1250000000 : ℝ)*X 0 0+(4500852731/10000000000 : ℝ)*X 0 1+(2110077901/5000000000 : ℝ)*X 0 2+(544783167/1250000000 : ℝ)*X 1 0+(4500852731/10000000000 : ℝ)*X 1 1+(2110077901/5000000000 : ℝ)*X 1 2+(544783167/1250000000 : ℝ)*X 2 0+(4500852731/10000000000 : ℝ)*X 2 1+(2110077901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2578713271008643426257/1249375000000000000000000000 : ℝ) := by norm_num
    linear_combination (104648077/20000000000000 : ℝ)*(base19) + (157564109/100000000000000 : ℝ)*(base23) + (84846309/100000000000000 : ℝ)*(upper2) + (137608087/100000000000000 : ℝ)*(upper3) + (5324883110328547/100000000000000 : ℝ)*(major0) + (5324883110328547/100000000000000 : ℝ)*(major1) + (5324883110328547/100000000000000 : ℝ)*(major2) + (7107227565923243/100000000000000 : ℝ)*(sp0) + (888405573752261/12500000000000 : ℝ)*(sp1) + (1776805650527587/25000000000000 : ℝ)*(sp2) + (442813210530561/12500000000000 : ℝ)*(sp3) + (17547335229/100000000000000 : ℝ)*(sp4) + (22353584017/100000000000000 : ℝ)*(sp6) + (3838588509/25000000000000 : ℝ)*(sp7) + (885630259649631/25000000000000 : ℝ)*(f.failure) + (7107245113258473/100000000000000 : ℝ)*(f.sum) + (12484153685993/9995000000000000000000000000 : ℝ)*base66 + (2169125153262545627/499750000000000000000000000000000 : ℝ)*base67 + (836895671943704373/499750000000000000000000000000000 : ℝ)*base70 + (1266339566081954373/499750000000000000000000000000000 : ℝ)*base72 + (834013181337/624687500000000000000000000 : ℝ)*base73 + (3211385171558045627/499750000000000000000000000000000 : ℝ)*base75 + (4168582283299704373/499750000000000000000000000000000 : ℝ)*base78 + (1106607754224295627/499750000000000000000000000000000 : ℝ)*base79 + (9522589900929/4997500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (1181861/125000000000000000000 : ℝ)*base90 + (1181861/125000000000000000000 : ℝ)*base92 + (1181861/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9955398711726215893929/1999000000000000000000000000 : ℝ) := by norm_num
    linear_combination (429001183/100000000000000 : ℝ)*(base19) + (97422401/100000000000000 : ℝ)*(upper2) + (57985721/100000000000000 : ℝ)*(upper3) + (122293553/50000000000000 : ℝ)*(lower4) + (66518053/50000000000000 : ℝ)*(upper5) + (535503112520087/10000000000000 : ℝ)*(major0) + (535503112520087/10000000000000 : ℝ)*(major1) + (535503112520087/10000000000000 : ℝ)*(major2) + (370742869/2000000000000 : ℝ)*(sp2) + (2588178377/20000000000000 : ℝ)*(sp3) + (7147484271827501/100000000000000 : ℝ)*(sp4) + (3573741921413159/50000000000000 : ℝ)*(sp5) + (1786866433671013/25000000000000 : ℝ)*(sp6) + (3562564871676011/100000000000000 : ℝ)*(sp7) + (445322226570987/12500000000000 : ℝ)*(f.failure) + (7147484271827501/100000000000000 : ℝ)*(f.sum) + (174311352310899/1999000000000000000000000000 : ℝ)*base66 + (954111008049187767/49975000000000000000000000000000 : ℝ)*base67 + (827640309531362233/49975000000000000000000000000000 : ℝ)*base70 + (476419035118387767/49975000000000000000000000000000 : ℝ)*base71 + (1960917412127/1999000000000000000000000000 : ℝ)*base73 + (652979153196662233/49975000000000000000000000000000 : ℝ)*base76 + (3544533806719612233/49975000000000000000000000000000 : ℝ)*base78 + (666469215092087767/49975000000000000000000000000000 : ℝ)*base79 + (5464412964039/1999000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (454697/62500000000000000000 : ℝ)*base90 + (454697/62500000000000000000 : ℝ)*base92 + (454697/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1185_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s5_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073178131/5000000000 : ℝ)*x 0 + (2696902333/5000000000 : ℝ)*x 1 + (5264943187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073178131/5000000000 : ℝ)^4189 ≤ (2609224661793/20000000000000 : ℝ)^3165 := by
    have hnat : (1073178131 : ℕ)^4189*20000000000000^3165 ≤ 2609224661793^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073178131 5000000000 2609224661793 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696902333/5000000000 : ℝ)^4189 ≤ (1766903906833/4000000000000 : ℝ)^3165 := by
    have hnat : (2696902333 : ℕ)^4189*4000000000000^3165 ≤ 1766903906833^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696902333 5000000000 1766903906833 4000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264943187/10000000000 : ℝ)^4189 ≤ (4278127900509/10000000000000 : ℝ)^3165 := by
    have hnat : (5264943187 : ℕ)^4189*10000000000000^3165 ≤ 4278127900509^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264943187 10000000000 4278127900509 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073178131/5000000000 : ℝ), (2696902333/5000000000 : ℝ), (5264943187/10000000000 : ℝ)] ![(2609224661793/20000000000000 : ℝ), (1766903906833/4000000000000 : ℝ), (4278127900509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073178131/5000000000 : ℝ)|^4189 ≤ (2609224661793/20000000000000 : ℝ)^3165
        have hw : |(-1073178131/5000000000 : ℝ)|=(1073178131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696902333/5000000000 : ℝ)|^4189 ≤ (1766903906833/4000000000000 : ℝ)^3165
        have hw : |(2696902333/5000000000 : ℝ)|=(2696902333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264943187/10000000000 : ℝ)|^4189 ≤ (4278127900509/10000000000000 : ℝ)^3165
        have hw : |(5264943187/10000000000 : ℝ)|=(5264943187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267248821/500000000 : ℝ)*x 0 + (-2211728221/10000000000 : ℝ)*x 1 + (2632471583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248821/500000000 : ℝ)^4189 ≤ (43644118682863/100000000000000 : ℝ)^3165 := by
    have hnat : (267248821 : ℕ)^4189*100000000000000^3165 ≤ 43644118682863^3165*500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248821 500000000 43644118682863 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211728221/10000000000 : ℝ)^4189 ≤ (13574602518059/100000000000000 : ℝ)^3165 := by
    have hnat : (2211728221 : ℕ)^4189*100000000000000^3165 ≤ 13574602518059^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211728221 10000000000 13574602518059 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632471583/5000000000 : ℝ)^4189 ≤ (21390639389621/50000000000000 : ℝ)^3165 := by
    have hnat : (2632471583 : ℕ)^4189*50000000000000^3165 ≤ 21390639389621^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632471583 5000000000 21390639389621 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248821/500000000 : ℝ), (-2211728221/10000000000 : ℝ), (2632471583/5000000000 : ℝ)] ![(43644118682863/100000000000000 : ℝ), (13574602518059/100000000000000 : ℝ), (21390639389621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248821/500000000 : ℝ)|^4189 ≤ (43644118682863/100000000000000 : ℝ)^3165
        have hw : |(267248821/500000000 : ℝ)|=(267248821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211728221/10000000000 : ℝ)|^4189 ≤ (13574602518059/100000000000000 : ℝ)^3165
        have hw : |(-2211728221/10000000000 : ℝ)|=(2211728221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632471583/5000000000 : ℝ)|^4189 ≤ (21390639389621/50000000000000 : ℝ)^3165
        have hw : |(2632471583/5000000000 : ℝ)|=(2632471583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344976421/10000000000 : ℝ)*x 0 + (131623579/250000000 : ℝ)*x 1 + (-2211728229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344976421/10000000000 : ℝ)^4189 ≤ (4364411869367/10000000000000 : ℝ)^3165 := by
    have hnat : (5344976421 : ℕ)^4189*10000000000000^3165 ≤ 4364411869367^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344976421 10000000000 4364411869367 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131623579/250000000 : ℝ)^4189 ≤ (21390639357357/50000000000000 : ℝ)^3165 := by
    have hnat : (131623579 : ℕ)^4189*50000000000000^3165 ≤ 21390639357357^3165*250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131623579 250000000 21390639357357 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211728229/10000000000 : ℝ)^4189 ≤ (6787301291523/50000000000000 : ℝ)^3165 := by
    have hnat : (2211728229 : ℕ)^4189*50000000000000^3165 ≤ 6787301291523^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211728229 10000000000 6787301291523 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344976421/10000000000 : ℝ), (131623579/250000000 : ℝ), (-2211728229/10000000000 : ℝ)] ![(4364411869367/10000000000000 : ℝ), (21390639357357/50000000000000 : ℝ), (6787301291523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344976421/10000000000 : ℝ)|^4189 ≤ (4364411869367/10000000000000 : ℝ)^3165
        have hw : |(5344976421/10000000000 : ℝ)|=(5344976421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131623579/250000000 : ℝ)|^4189 ≤ (21390639357357/50000000000000 : ℝ)^3165
        have hw : |(131623579/250000000 : ℝ)|=(131623579/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211728229/10000000000 : ℝ)|^4189 ≤ (6787301291523/50000000000000 : ℝ)^3165
        have hw : |(-2211728229/10000000000 : ℝ)|=(2211728229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179286507/5000000000 : ℝ)*x 0 + (528899499/1250000000 : ℝ)*x 1 + (4489726657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179286507/5000000000 : ℝ)^4189 ≤ (33316414443797/100000000000000 : ℝ)^3165 := by
    have hnat : (2179286507 : ℕ)^4189*100000000000000^3165 ≤ 33316414443797^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179286507 5000000000 33316414443797 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528899499/1250000000 : ℝ)^4189 ≤ (8008469397277/25000000000000 : ℝ)^3165 := by
    have hnat : (528899499 : ℕ)^4189*25000000000000^3165 ≤ 8008469397277^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528899499 1250000000 8008469397277 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489726657/10000000000 : ℝ)^4189 ≤ (86624269881/250000000000 : ℝ)^3165 := by
    have hnat : (4489726657 : ℕ)^4189*250000000000^3165 ≤ 86624269881^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489726657 10000000000 86624269881 250000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179286507/5000000000 : ℝ), (528899499/1250000000 : ℝ), (4489726657/10000000000 : ℝ)] ![(33316414443797/100000000000000 : ℝ), (8008469397277/25000000000000 : ℝ), (86624269881/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179286507/5000000000 : ℝ)|^4189 ≤ (33316414443797/100000000000000 : ℝ)^3165
        have hw : |(2179286507/5000000000 : ℝ)|=(2179286507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528899499/1250000000 : ℝ)|^4189 ≤ (8008469397277/25000000000000 : ℝ)^3165
        have hw : |(528899499/1250000000 : ℝ)|=(528899499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489726657/10000000000 : ℝ)|^4189 ≤ (86624269881/250000000000 : ℝ)^3165
        have hw : |(4489726657/10000000000 : ℝ)|=(4489726657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073180693/5000000000 : ℝ)*x 0 + (1316318801/2500000000 : ℝ)*x 1 + (2696735713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073180693/5000000000 : ℝ)^4189 ≤ (13046164530637/100000000000000 : ℝ)^3165 := by
    have hnat : (1073180693 : ℕ)^4189*100000000000000^3165 ≤ 13046164530637^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073180693 5000000000 13046164530637 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316318801/2500000000 : ℝ)^4189 ≤ (42784849771761/100000000000000 : ℝ)^3165 := by
    have hnat : (1316318801 : ℕ)^4189*100000000000000^3165 ≤ 42784849771761^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316318801 2500000000 42784849771761 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696735713/5000000000 : ℝ)^4189 ≤ (22084492837847/50000000000000 : ℝ)^3165 := by
    have hnat : (2696735713 : ℕ)^4189*50000000000000^3165 ≤ 22084492837847^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696735713 5000000000 22084492837847 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073180693/5000000000 : ℝ), (1316318801/2500000000 : ℝ), (2696735713/5000000000 : ℝ)] ![(13046164530637/100000000000000 : ℝ), (42784849771761/100000000000000 : ℝ), (22084492837847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073180693/5000000000 : ℝ)|^4189 ≤ (13046164530637/100000000000000 : ℝ)^3165
        have hw : |(-1073180693/5000000000 : ℝ)|=(1073180693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316318801/2500000000 : ℝ)|^4189 ≤ (42784849771761/100000000000000 : ℝ)^3165
        have hw : |(1316318801/2500000000 : ℝ)|=(1316318801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696735713/5000000000 : ℝ)|^4189 ≤ (22084492837847/50000000000000 : ℝ)^3165
        have hw : |(2696735713/5000000000 : ℝ)|=(2696735713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656113531/5000000000 : ℝ)*x 0 + (-1041599939/5000000000 : ℝ)*x 1 + (5393471391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656113531/5000000000 : ℝ)^4189 ≤ (8658107670671/20000000000000 : ℝ)^3165 := by
    have hnat : (2656113531 : ℕ)^4189*20000000000000^3165 ≤ 8658107670671^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656113531 5000000000 8658107670671 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041599939/5000000000 : ℝ)^4189 ≤ (2508095265939/20000000000000 : ℝ)^3165 := by
    have hnat : (1041599939 : ℕ)^4189*20000000000000^3165 ≤ 2508095265939^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041599939 5000000000 2508095265939 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393471391/10000000000 : ℝ)^4189 ≤ (11042246324083/25000000000000 : ℝ)^3165 := by
    have hnat : (5393471391 : ℕ)^4189*25000000000000^3165 ≤ 11042246324083^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393471391 10000000000 11042246324083 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656113531/5000000000 : ℝ), (-1041599939/5000000000 : ℝ), (5393471391/10000000000 : ℝ)] ![(8658107670671/20000000000000 : ℝ), (2508095265939/20000000000000 : ℝ), (11042246324083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656113531/5000000000 : ℝ)|^4189 ≤ (8658107670671/20000000000000 : ℝ)^3165
        have hw : |(2656113531/5000000000 : ℝ)|=(2656113531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041599939/5000000000 : ℝ)|^4189 ≤ (2508095265939/20000000000000 : ℝ)^3165
        have hw : |(-1041599939/5000000000 : ℝ)|=(1041599939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393471391/10000000000 : ℝ)|^4189 ≤ (11042246324083/25000000000000 : ℝ)^3165
        have hw : |(5393471391/10000000000 : ℝ)|=(5393471391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664028359/1250000000 : ℝ)*x 0 + (674183949/1250000000 : ℝ)*x 1 + (-1041599931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664028359/1250000000 : ℝ)^4189 ≤ (865810726081/2000000000000 : ℝ)^3165 := by
    have hnat : (664028359 : ℕ)^4189*2000000000000^3165 ≤ 865810726081^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664028359 1250000000 865810726081 2000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674183949/1250000000 : ℝ)^4189 ≤ (44168987474953/100000000000000 : ℝ)^3165 := by
    have hnat : (674183949 : ℕ)^4189*100000000000000^3165 ≤ 44168987474953^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674183949 1250000000 44168987474953 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041599931/5000000000 : ℝ)^4189 ≤ (1567559525277/12500000000000 : ℝ)^3165 := by
    have hnat : (1041599931 : ℕ)^4189*12500000000000^3165 ≤ 1567559525277^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041599931 5000000000 1567559525277 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664028359/1250000000 : ℝ), (674183949/1250000000 : ℝ), (-1041599931/5000000000 : ℝ)] ![(865810726081/2000000000000 : ℝ), (44168987474953/100000000000000 : ℝ), (1567559525277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664028359/1250000000 : ℝ)|^4189 ≤ (865810726081/2000000000000 : ℝ)^3165
        have hw : |(664028359/1250000000 : ℝ)|=(664028359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674183949/1250000000 : ℝ)|^4189 ≤ (44168987474953/100000000000000 : ℝ)^3165
        have hw : |(674183949/1250000000 : ℝ)|=(674183949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041599931/5000000000 : ℝ)|^4189 ≤ (1567559525277/12500000000000 : ℝ)^3165
        have hw : |(-1041599931/5000000000 : ℝ)|=(1041599931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s5_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871716653/2000000000 : ℝ)*x 0 + (897812101/2000000000 : ℝ)*x 1 + (4231864667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871716653/2000000000 : ℝ)^4189 ≤ (33316518152923/100000000000000 : ℝ)^3165 := by
    have hnat : (871716653 : ℕ)^4189*100000000000000^3165 ≤ 33316518152923^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871716653 2000000000 33316518152923 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897812101/2000000000 : ℝ)^4189 ≤ (3464290371849/10000000000000 : ℝ)^3165 := by
    have hnat : (897812101 : ℕ)^4189*10000000000000^3165 ≤ 3464290371849^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897812101 2000000000 3464290371849 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231864667/10000000000 : ℝ)^4189 ≤ (6408115623969/20000000000000 : ℝ)^3165 := by
    have hnat : (4231864667 : ℕ)^4189*20000000000000^3165 ≤ 6408115623969^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231864667 10000000000 6408115623969 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871716653/2000000000 : ℝ), (897812101/2000000000 : ℝ), (4231864667/10000000000 : ℝ)] ![(33316518152923/100000000000000 : ℝ), (3464290371849/10000000000000 : ℝ), (6408115623969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871716653/2000000000 : ℝ)|^4189 ≤ (33316518152923/100000000000000 : ℝ)^3165
        have hw : |(871716653/2000000000 : ℝ)|=(871716653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897812101/2000000000 : ℝ)|^4189 ≤ (3464290371849/10000000000000 : ℝ)^3165
        have hw : |(897812101/2000000000 : ℝ)|=(897812101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231864667/10000000000 : ℝ)|^4189 ≤ (6408115623969/20000000000000 : ℝ)^3165
        have hw : |(4231864667/10000000000 : ℝ)|=(4231864667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2251/20000 : ℝ) ^ (8377/2048 : ℝ) ≤ (13173103660547849/100000000000000000000 : ℝ) := by
    have hpowers : (2251/20000 : ℝ)^8377 ≤ (13173103660547849/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2251 : ℕ)^8377*100000000000000000000^2048 ≤ 13173103660547849^2048*20000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2251 20000 13173103660547849 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2251/20000 : ℝ)) (X := (13173103660547849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8377/2048 : ℝ) ≤ (1075662856308881/3125000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8377 ≤ (1075662856308881/3125000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8377*3125000000000000000^2048 ≤ 1075662856308881^2048*50000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 1075662856308881 3125000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (1075662856308881/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013173103660547849/50000000000000000000 : ℝ) ≤ (10000644045163147/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50013173103660547849/50000000000000000000 : ℝ)^2048 ≤ (10000644045163147/10000000000000000 : ℝ)^8377 := by
      have hnat : (50013173103660547849 : ℕ)^2048*10000000000000000^8377 ≤ 10000644045163147^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013173103660547849 50000000000000000000 10000644045163147 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644045163147/10000000000000000 : ℝ)) (X := (50013173103660547849/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047594315062432041/100000000000000000000 : ℝ) ≤ (5000581685789547/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (100047594315062432041/100000000000000000000 : ℝ)^2048 ≤ (5000581685789547/5000000000000000 : ℝ)^8377 := by
      have hnat : (100047594315062432041 : ℕ)^2048*5000000000000000^8377 ≤ 5000581685789547^8377*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047594315062432041 100000000000000000000 5000581685789547 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000581685789547/5000000000000000 : ℝ)) (X := (100047594315062432041/100000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563575662856308881/1562500000000000000 : ℝ) ≤ (10001682697995041/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (1563575662856308881/1562500000000000000 : ℝ)^2048 ≤ (10001682697995041/10000000000000000 : ℝ)^8377 := by
      have hnat : (1563575662856308881 : ℕ)^2048*10000000000000000^8377 ≤ 10001682697995041^8377*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563575662856308881 1562500000000000000 10001682697995041 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001682697995041/10000000000000000 : ℝ)) (X := (1563575662856308881/1562500000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13173103660547849/100000000000000000000 : ℝ) ≤ ((29780228572918047943/29790000000000000000 : ℝ)+2*(519326415947/297900000000000 : ℝ)*(2251/20000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (29780228572918047943/29790000000000000000 : ℝ)+2*(519326415947/297900000000000 : ℝ)*(2251/20000 : ℝ)=(10000644045163147/10000000000000000 : ℝ) by norm_num, show 1+2*(13173103660547849/100000000000000000000 : ℝ)=(50013173103660547849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1075662856308881/3125000000000000000 : ℝ)+(13173103660547849/100000000000000000000 : ℝ) ≤ ((29780228572918047943/29790000000000000000 : ℝ)+(519326415947/297900000000000 : ℝ)*((7117/50000 : ℝ)+(2251/20000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (29780228572918047943/29790000000000000000 : ℝ)+(519326415947/297900000000000 : ℝ)*((7117/50000 : ℝ)+(2251/20000 : ℝ))=(5000581685789547/5000000000000000 : ℝ) by norm_num, show 1+(1075662856308881/3125000000000000000 : ℝ)+(13173103660547849/100000000000000000000 : ℝ)=(100047594315062432041/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1075662856308881/3125000000000000000 : ℝ) ≤ ((29780228572918047943/29790000000000000000 : ℝ)+2*(519326415947/297900000000000 : ℝ)*(7117/50000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (29780228572918047943/29790000000000000000 : ℝ)+2*(519326415947/297900000000000 : ℝ)*(7117/50000 : ℝ)=(10001682697995041/10000000000000000 : ℝ) by norm_num, show 1+2*(1075662856308881/3125000000000000000 : ℝ)=(1563575662856308881/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29780228572918047943/29790000000000000000 : ℝ)*(X 1 0+X 2 0)+(519326415947/297900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29780228572918047943/29790000000000000000 : ℝ)) (alpha := (519326415947/297900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29780228572918047943/29790000000000000000 : ℝ)*(X 0 1+X 2 1)+(519326415947/297900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29780228572918047943/29790000000000000000 : ℝ)) (alpha := (519326415947/297900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29780228572918047943/29790000000000000000 : ℝ)*(X 0 2+X 1 2)+(519326415947/297900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (29780228572918047943/29790000000000000000 : ℝ)) (alpha := (519326415947/297900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073178131/5000000000 : ℝ)*X 0 0+(2696902333/5000000000 : ℝ)*X 0 1+(5264943187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267248821/500000000 : ℝ)*X 1 0+(-2211728221/10000000000 : ℝ)*X 1 1+(2632471583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344976421/10000000000 : ℝ)*X 2 0+(131623579/250000000 : ℝ)*X 2 1+(-2211728229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179286507/5000000000 : ℝ)*X 0 0+(528899499/1250000000 : ℝ)*X 0 1+(4489726657/10000000000 : ℝ)*X 0 2+(2179286507/5000000000 : ℝ)*X 1 0+(528899499/1250000000 : ℝ)*X 1 1+(4489726657/10000000000 : ℝ)*X 1 2+(2179286507/5000000000 : ℝ)*X 2 0+(528899499/1250000000 : ℝ)*X 2 1+(4489726657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073180693/5000000000 : ℝ)*X 0 0+(1316318801/2500000000 : ℝ)*X 0 1+(2696735713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656113531/5000000000 : ℝ)*X 1 0+(-1041599939/5000000000 : ℝ)*X 1 1+(5393471391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664028359/1250000000 : ℝ)*X 2 0+(674183949/1250000000 : ℝ)*X 2 1+(-1041599931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871716653/2000000000 : ℝ)*X 0 0+(897812101/2000000000 : ℝ)*X 0 1+(4231864667/10000000000 : ℝ)*X 0 2+(871716653/2000000000 : ℝ)*X 1 0+(897812101/2000000000 : ℝ)*X 1 1+(4231864667/10000000000 : ℝ)*X 1 2+(871716653/2000000000 : ℝ)*X 2 0+(897812101/2000000000 : ℝ)*X 2 1+(4231864667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4240843145335971144303/827500000000000000000000000 : ℝ) := by norm_num
    linear_combination (253839061/25000000000000 : ℝ)*(base19) + (953809889/100000000000000 : ℝ)*(base23) + (8418103/25000000000000 : ℝ)*(lower2) + (13402197/10000000000000 : ℝ)*(upper3) + (15184509/20000000000000 : ℝ)*(upper5) + (1453545608847291/25000000000000 : ℝ)*(major0) + (1453545608847291/25000000000000 : ℝ)*(major1) + (1453545608847291/25000000000000 : ℝ)*(major2) + (1552059695129473/20000000000000 : ℝ)*(sp0) + (388016158562013/5000000000000 : ℝ)*(sp1) + (1552064646557323/20000000000000 : ℝ)*(sp2) + (48350325387043/1250000000000 : ℝ)*(sp3) + (1285547457/5000000000000 : ℝ)*(sp4) + (14482388841/100000000000000 : ℝ)*(sp7) + (96701012833807/2500000000000 : ℝ)*(f.failure) + (1552064837319301/20000000000000 : ℝ)*(f.sum) + (318971932287/1655000000000000000000000000 : ℝ)*base65 + (61867390589430843/82750000000000000000000000000000 : ℝ)*base68 + (493478157788680843/82750000000000000000000000000000 : ℝ)*base70 + (799598473138069157/82750000000000000000000000000000 : ℝ)*base71 + (1446058045063/1655000000000000000000000000 : ℝ)*base74 + (91519883532569157/82750000000000000000000000000000 : ℝ)*base75 + (809453407278180843/82750000000000000000000000000000 : ℝ)*base78 + (473601756598069157/82750000000000000000000000000000 : ℝ)*base79 + (3843455136987/413750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (78117/12500000000000000000 : ℝ)*base90 + (78117/12500000000000000000 : ℝ)*base92 + (78117/12500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1166074389991959815982938453/496500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309995167/50000000000000 : ℝ)*(base19) + (33425767/10000000000000 : ℝ)*(base23) + (3807321/20000000000000 : ℝ)*(upper3) + (2471949/100000000000000 : ℝ)*(lower4) + (48571597/100000000000000 : ℝ)*(upper5) + (5844313102041571/100000000000000 : ℝ)*(major0) + (5844313102041571/100000000000000 : ℝ)*(major1) + (5844313102041571/100000000000000 : ℝ)*(major2) + (1861550827/10000000000000 : ℝ)*(sp1) + (83841197/500000000000 : ℝ)*(sp2) + (7800540379842903/100000000000000 : ℝ)*(sp4) + (7800521144344299/100000000000000 : ℝ)*(sp5) + (975065409668229/12500000000000 : ℝ)*(sp6) + (1944042872976967/50000000000000 : ℝ)*(sp7) + (1944042872976967/50000000000000 : ℝ)*(f.failure) + (7800540379842903/100000000000000 : ℝ)*(f.sum) + (46176495997303/14895000000000000000000000000 : ℝ)*base66 + (4285384506205251283/331000000000000000000000000000000 : ℝ)*base68 + (2685380902600748717/331000000000000000000000000000000 : ℝ)*base69 + (3411039256551251283/331000000000000000000000000000000 : ℝ)*base72 + (3519041022073/14895000000000000000000000000 : ℝ)*base74 + (1340917347280251283/331000000000000000000000000000000 : ℝ)*base76 + (3216600577297251283/331000000000000000000000000000000 : ℝ)*base78 + (6391738322902748717/331000000000000000000000000000000 : ℝ)*base79 + (5992031403107/14895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1095923/250000000000000000000 : ℝ)*base89 + (1095923/250000000000000000000 : ℝ)*base91 + (1095923/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1185_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1185_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1185_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1185_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

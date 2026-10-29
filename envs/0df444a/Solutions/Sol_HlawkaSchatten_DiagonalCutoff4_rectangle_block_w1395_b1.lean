-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1395_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:58.080866+00:00
-- url     : https://prove2.me/submissions/6b1e1a2c-aba1-42b1-b427-2a9d3df1df9c

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
theorem support_rectangle_w1395_s3_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249720661/1250000000 : ℝ)*x 0 + (21175269/39062500 : ℝ)*x 1 + (5236046403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249720661/1250000000 : ℝ)^4355 ≤ (12176464460079/100000000000000 : ℝ)^3331 := by
    have hnat : (249720661 : ℕ)^4355*100000000000000^3331 ≤ 12176464460079^3331*1250000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249720661 1250000000 12176464460079 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21175269/39062500 : ℝ)^4355 ≤ (8981474427839/20000000000000 : ℝ)^3331 := by
    have hnat : (21175269 : ℕ)^4355*20000000000000^3331 ≤ 8981474427839^3331*39062500^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21175269 39062500 8981474427839 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236046403/10000000000 : ℝ)^4355 ≤ (5364520423069/12500000000000 : ℝ)^3331 := by
    have hnat : (5236046403 : ℕ)^4355*12500000000000^3331 ≤ 5364520423069^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236046403 10000000000 5364520423069 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249720661/1250000000 : ℝ), (21175269/39062500 : ℝ), (5236046403/10000000000 : ℝ)] ![(12176464460079/100000000000000 : ℝ), (8981474427839/20000000000000 : ℝ), (5364520423069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249720661/1250000000 : ℝ)|^4355 ≤ (12176464460079/100000000000000 : ℝ)^3331
        have hw : |(-249720661/1250000000 : ℝ)|=(249720661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21175269/39062500 : ℝ)|^4355 ≤ (8981474427839/20000000000000 : ℝ)^3331
        have hw : |(21175269/39062500 : ℝ)|=(21175269/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236046403/10000000000 : ℝ)|^4355 ≤ (5364520423069/12500000000000 : ℝ)^3331
        have hw : |(5236046403/10000000000 : ℝ)|=(5236046403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350819239/10000000000 : ℝ)*x 0 + (-2092107053/10000000000 : ℝ)*x 1 + (5236046437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350819239/10000000000 : ℝ)^4355 ≤ (44150187112271/100000000000000 : ℝ)^3331 := by
    have hnat : (5350819239 : ℕ)^4355*100000000000000^3331 ≤ 44150187112271^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350819239 10000000000 44150187112271 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092107053/10000000000 : ℝ)^4355 ≤ (12933649122859/100000000000000 : ℝ)^3331 := by
    have hnat : (2092107053 : ℕ)^4355*100000000000000^3331 ≤ 12933649122859^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092107053 10000000000 12933649122859 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236046437/10000000000 : ℝ)^4355 ≤ (8583232749779/20000000000000 : ℝ)^3331 := by
    have hnat : (5236046437 : ℕ)^4355*20000000000000^3331 ≤ 8583232749779^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236046437 10000000000 8583232749779 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350819239/10000000000 : ℝ), (-2092107053/10000000000 : ℝ), (5236046437/10000000000 : ℝ)] ![(44150187112271/100000000000000 : ℝ), (12933649122859/100000000000000 : ℝ), (8583232749779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350819239/10000000000 : ℝ)|^4355 ≤ (44150187112271/100000000000000 : ℝ)^3331
        have hw : |(5350819239/10000000000 : ℝ)|=(5350819239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092107053/10000000000 : ℝ)|^4355 ≤ (12933649122859/100000000000000 : ℝ)^3331
        have hw : |(-2092107053/10000000000 : ℝ)|=(2092107053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236046437/10000000000 : ℝ)|^4355 ≤ (8583232749779/20000000000000 : ℝ)^3331
        have hw : |(5236046437/10000000000 : ℝ)|=(5236046437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675409677/5000000000 : ℝ)*x 0 + (523604633/1000000000 : ℝ)*x 1 + (-2092107041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675409677/5000000000 : ℝ)^4355 ≤ (2759386772053/6250000000000 : ℝ)^3331 := by
    have hnat : (2675409677 : ℕ)^4355*6250000000000^3331 ≤ 2759386772053^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675409677 5000000000 2759386772053 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523604633/1000000000 : ℝ)^4355 ≤ (2682260162643/6250000000000 : ℝ)^3331 := by
    have hnat : (523604633 : ℕ)^4355*6250000000000^3331 ≤ 2682260162643^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523604633 1000000000 2682260162643 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092107041/10000000000 : ℝ)^4355 ≤ (3233412256467/25000000000000 : ℝ)^3331 := by
    have hnat : (2092107041 : ℕ)^4355*25000000000000^3331 ≤ 3233412256467^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092107041 10000000000 3233412256467 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675409677/5000000000 : ℝ), (523604633/1000000000 : ℝ), (-2092107041/10000000000 : ℝ)] ![(2759386772053/6250000000000 : ℝ), (2682260162643/6250000000000 : ℝ), (3233412256467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675409677/5000000000 : ℝ)|^4355 ≤ (2759386772053/6250000000000 : ℝ)^3331
        have hw : |(2675409677/5000000000 : ℝ)|=(2675409677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523604633/1000000000 : ℝ)|^4355 ≤ (2682260162643/6250000000000 : ℝ)^3331
        have hw : |(523604633/1000000000 : ℝ)|=(523604633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092107041/10000000000 : ℝ)|^4355 ≤ (3233412256467/25000000000000 : ℝ)^3331
        have hw : |(-2092107041/10000000000 : ℝ)|=(2092107041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312163831/10000000000 : ℝ)*x 0 + (4118859421/10000000000 : ℝ)*x 1 + (902743301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312163831/10000000000 : ℝ)^4355 ≤ (6659245403651/20000000000000 : ℝ)^3331 := by
    have hnat : (4312163831 : ℕ)^4355*20000000000000^3331 ≤ 6659245403651^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312163831 10000000000 6659245403651 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4118859421/10000000000 : ℝ)^4355 ≤ (15679187817809/50000000000000 : ℝ)^3331 := by
    have hnat : (4118859421 : ℕ)^4355*50000000000000^3331 ≤ 15679187817809^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118859421 10000000000 15679187817809 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902743301/2000000000 : ℝ)^4355 ≤ (35345397330887/100000000000000 : ℝ)^3331 := by
    have hnat : (902743301 : ℕ)^4355*100000000000000^3331 ≤ 35345397330887^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902743301 2000000000 35345397330887 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312163831/10000000000 : ℝ), (4118859421/10000000000 : ℝ), (902743301/2000000000 : ℝ)] ![(6659245403651/20000000000000 : ℝ), (15679187817809/50000000000000 : ℝ), (35345397330887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312163831/10000000000 : ℝ)|^4355 ≤ (6659245403651/20000000000000 : ℝ)^3331
        have hw : |(4312163831/10000000000 : ℝ)|=(4312163831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4118859421/10000000000 : ℝ)|^4355 ≤ (15679187817809/50000000000000 : ℝ)^3331
        have hw : |(4118859421/10000000000 : ℝ)|=(4118859421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902743301/2000000000 : ℝ)|^4355 ≤ (35345397330887/100000000000000 : ℝ)^3331
        have hw : |(902743301/2000000000 : ℝ)|=(902743301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62430703/312500000 : ℝ)*x 0 + (5236795381/10000000000 : ℝ)*x 1 + (2710057569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62430703/312500000 : ℝ)^4355 ≤ (12176601586531/100000000000000 : ℝ)^3331 := by
    have hnat : (62430703 : ℕ)^4355*100000000000000^3331 ≤ 12176601586531^3331*312500000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62430703 312500000 12176601586531 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236795381/10000000000 : ℝ)^4355 ≤ (21462094788229/50000000000000 : ℝ)^3331 := by
    have hnat : (5236795381 : ℕ)^4355*50000000000000^3331 ≤ 21462094788229^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236795381 10000000000 21462094788229 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710057569/5000000000 : ℝ)^4355 ≤ (4489920882557/10000000000000 : ℝ)^3331 := by
    have hnat : (2710057569 : ℕ)^4355*10000000000000^3331 ≤ 4489920882557^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710057569 5000000000 4489920882557 10000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62430703/312500000 : ℝ), (5236795381/10000000000 : ℝ), (2710057569/5000000000 : ℝ)] ![(12176601586531/100000000000000 : ℝ), (21462094788229/50000000000000 : ℝ), (4489920882557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62430703/312500000 : ℝ)|^4355 ≤ (12176601586531/100000000000000 : ℝ)^3331
        have hw : |(-62430703/312500000 : ℝ)|=(62430703/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236795381/10000000000 : ℝ)|^4355 ≤ (21462094788229/50000000000000 : ℝ)^3331
        have hw : |(5236795381/10000000000 : ℝ)|=(5236795381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710057569/5000000000 : ℝ)|^4355 ≤ (4489920882557/10000000000000 : ℝ)^3331
        have hw : |(2710057569/5000000000 : ℝ)|=(2710057569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302935633/10000000000 : ℝ)*x 0 + (-1908037801/10000000000 : ℝ)*x 1 + (5420115653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302935633/10000000000 : ℝ)^4355 ≤ (21817174386103/50000000000000 : ℝ)^3331 := by
    have hnat : (5302935633 : ℕ)^4355*50000000000000^3331 ≤ 21817174386103^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302935633 10000000000 21817174386103 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1908037801/10000000000 : ℝ)^4355 ≤ (11466436810331/100000000000000 : ℝ)^3331 := by
    have hnat : (1908037801 : ℕ)^4355*100000000000000^3331 ≤ 11466436810331^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908037801 10000000000 11466436810331 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420115653/10000000000 : ℝ)^4355 ≤ (8979842880643/20000000000000 : ℝ)^3331 := by
    have hnat : (5420115653 : ℕ)^4355*20000000000000^3331 ≤ 8979842880643^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420115653 10000000000 8979842880643 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302935633/10000000000 : ℝ), (-1908037801/10000000000 : ℝ), (5420115653/10000000000 : ℝ)] ![(21817174386103/50000000000000 : ℝ), (11466436810331/100000000000000 : ℝ), (8979842880643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302935633/10000000000 : ℝ)|^4355 ≤ (21817174386103/50000000000000 : ℝ)^3331
        have hw : |(5302935633/10000000000 : ℝ)|=(5302935633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1908037801/10000000000 : ℝ)|^4355 ≤ (11466436810331/100000000000000 : ℝ)^3331
        have hw : |(-1908037801/10000000000 : ℝ)|=(1908037801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420115653/10000000000 : ℝ)|^4355 ≤ (8979842880643/20000000000000 : ℝ)^3331
        have hw : |(5420115653/10000000000 : ℝ)|=(5420115653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651468357/5000000000 : ℝ)*x 0 + (5420114823/10000000000 : ℝ)*x 1 + (-381607493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651468357/5000000000 : ℝ)^4355 ≤ (43634360401447/100000000000000 : ℝ)^3331 := by
    have hnat : (2651468357 : ℕ)^4355*100000000000000^3331 ≤ 43634360401447^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651468357 5000000000 43634360401447 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420114823/10000000000 : ℝ)^4355 ≤ (22449602707/50000000000 : ℝ)^3331 := by
    have hnat : (5420114823 : ℕ)^4355*50000000000^3331 ≤ 22449602707^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420114823 10000000000 22449602707 50000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381607493/2000000000 : ℝ)^4355 ≤ (11466434170389/100000000000000 : ℝ)^3331 := by
    have hnat : (381607493 : ℕ)^4355*100000000000000^3331 ≤ 11466434170389^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381607493 2000000000 11466434170389 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651468357/5000000000 : ℝ), (5420114823/10000000000 : ℝ), (-381607493/2000000000 : ℝ)] ![(43634360401447/100000000000000 : ℝ), (22449602707/50000000000 : ℝ), (11466434170389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651468357/5000000000 : ℝ)|^4355 ≤ (43634360401447/100000000000000 : ℝ)^3331
        have hw : |(2651468357/5000000000 : ℝ)|=(2651468357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420114823/10000000000 : ℝ)|^4355 ≤ (22449602707/50000000000 : ℝ)^3331
        have hw : |(5420114823/10000000000 : ℝ)|=(5420114823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381607493/2000000000 : ℝ)|^4355 ≤ (11466434170389/100000000000000 : ℝ)^3331
        have hw : |(-381607493/2000000000 : ℝ)|=(381607493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s3_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43122007/100000000 : ℝ)*x 0 + (4512115933/10000000000 : ℝ)*x 1 + (4120468097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43122007/100000000 : ℝ)^4355 ≤ (8324149804319/25000000000000 : ℝ)^3331 := by
    have hnat : (43122007 : ℕ)^4355*25000000000000^3331 ≤ 8324149804319^3331*100000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43122007 100000000 8324149804319 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512115933/10000000000 : ℝ)^4355 ≤ (4416126460189/12500000000000 : ℝ)^3331 := by
    have hnat : (4512115933 : ℕ)^4355*12500000000000^3331 ≤ 4416126460189^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512115933 10000000000 4416126460189 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4120468097/10000000000 : ℝ)^4355 ≤ (31374389080399/100000000000000 : ℝ)^3331 := by
    have hnat : (4120468097 : ℕ)^4355*100000000000000^3331 ≤ 31374389080399^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120468097 10000000000 31374389080399 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43122007/100000000 : ℝ), (4512115933/10000000000 : ℝ), (4120468097/10000000000 : ℝ)] ![(8324149804319/25000000000000 : ℝ), (4416126460189/12500000000000 : ℝ), (31374389080399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43122007/100000000 : ℝ)|^4355 ≤ (8324149804319/25000000000000 : ℝ)^3331
        have hw : |(43122007/100000000 : ℝ)|=(43122007/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512115933/10000000000 : ℝ)|^4355 ≤ (4416126460189/12500000000000 : ℝ)^3331
        have hw : |(4512115933/10000000000 : ℝ)|=(4512115933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4120468097/10000000000 : ℝ)|^4355 ≤ (31374389080399/100000000000000 : ℝ)^3331
        have hw : |(4120468097/10000000000 : ℝ)|=(4120468097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14967/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5089/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5089/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5089/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5089/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5089/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5089/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5089/50000 : ℝ) ^ (2177/512 : ℝ) ≤ (6034304735657131/100000000000000000000 : ℝ) := by
    have hpowers : (5089/50000 : ℝ)^2177 ≤ (6034304735657131/100000000000000000000 : ℝ)^512 := by
      have hnat : (5089 : ℕ)^2177*100000000000000000000^512 ≤ 6034304735657131^512*50000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5089 50000 6034304735657131 100000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5089/50000 : ℝ)) (X := (6034304735657131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15909/100000 : ℝ) ^ (2177/512 : ℝ) ≤ (40310942886529817/100000000000000000000 : ℝ) := by
    have hpowers : (15909/100000 : ℝ)^2177 ≤ (40310942886529817/100000000000000000000 : ℝ)^512 := by
      have hnat : (15909 : ℕ)^2177*100000000000000000000^512 ≤ 40310942886529817^512*100000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15909 100000 40310942886529817 100000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15909/100000 : ℝ)) (X := (40310942886529817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006034304735657131/50000000000000000000 : ℝ) ≤ (10000283823743471/10000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (50006034304735657131/50000000000000000000 : ℝ)^512 ≤ (10000283823743471/10000000000000000 : ℝ)^2177 := by
      have hnat : (50006034304735657131 : ℕ)^512*10000000000000000^2177 ≤ 10000283823743471^2177*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006034304735657131 50000000000000000000 10000283823743471 10000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283823743471/10000000000000000 : ℝ)) (X := (50006034304735657131/50000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011586311905546737/25000000000000000000 : ℝ) ≤ (5000544891192917/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (25011586311905546737/25000000000000000000 : ℝ)^512 ≤ (5000544891192917/5000000000000000 : ℝ)^2177 := by
      have hnat : (25011586311905546737 : ℕ)^512*5000000000000000^2177 ≤ 5000544891192917^2177*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011586311905546737 25000000000000000000 5000544891192917 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000544891192917/5000000000000000 : ℝ)) (X := (25011586311905546737/25000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040310942886529817/50000000000000000000 : ℝ) ≤ (10001895741028197/10000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (50040310942886529817/50000000000000000000 : ℝ)^512 ≤ (10001895741028197/10000000000000000 : ℝ)^2177 := by
      have hnat : (50040310942886529817 : ℕ)^512*10000000000000000^2177 ≤ 10001895741028197^2177*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040310942886529817 50000000000000000000 10001895741028197 10000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001895741028197/10000000000000000 : ℝ)) (X := (50040310942886529817/50000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6034304735657131/100000000000000000000 : ℝ) ≤ ((57295220499749891073/57310000000000000000 : ℝ)+2*(805958642363/573100000000000 : ℝ)*(5089/50000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (57295220499749891073/57310000000000000000 : ℝ)+2*(805958642363/573100000000000 : ℝ)*(5089/50000 : ℝ)=(10000283823743471/10000000000000000 : ℝ) by norm_num, show 1+2*(6034304735657131/100000000000000000000 : ℝ)=(50006034304735657131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40310942886529817/100000000000000000000 : ℝ)+(6034304735657131/100000000000000000000 : ℝ) ≤ ((57295220499749891073/57310000000000000000 : ℝ)+(805958642363/573100000000000 : ℝ)*((15909/100000 : ℝ)+(5089/50000 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (57295220499749891073/57310000000000000000 : ℝ)+(805958642363/573100000000000 : ℝ)*((15909/100000 : ℝ)+(5089/50000 : ℝ))=(5000544891192917/5000000000000000 : ℝ) by norm_num, show 1+(40310942886529817/100000000000000000000 : ℝ)+(6034304735657131/100000000000000000000 : ℝ)=(25011586311905546737/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40310942886529817/100000000000000000000 : ℝ) ≤ ((57295220499749891073/57310000000000000000 : ℝ)+2*(805958642363/573100000000000 : ℝ)*(15909/100000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (57295220499749891073/57310000000000000000 : ℝ)+2*(805958642363/573100000000000 : ℝ)*(15909/100000 : ℝ)=(10001895741028197/10000000000000000 : ℝ) by norm_num, show 1+2*(40310942886529817/100000000000000000000 : ℝ)=(50040310942886529817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57295220499749891073/57310000000000000000 : ℝ)*(X 1 0+X 2 0)+(805958642363/573100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5089/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (57295220499749891073/57310000000000000000 : ℝ)) (alpha := (805958642363/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57295220499749891073/57310000000000000000 : ℝ)*(X 0 1+X 2 1)+(805958642363/573100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5089/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (57295220499749891073/57310000000000000000 : ℝ)) (alpha := (805958642363/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57295220499749891073/57310000000000000000 : ℝ)*(X 0 2+X 1 2)+(805958642363/573100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5089/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (57295220499749891073/57310000000000000000 : ℝ)) (alpha := (805958642363/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-249720661/1250000000 : ℝ)*X 0 0+(21175269/39062500 : ℝ)*X 0 1+(5236046403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350819239/10000000000 : ℝ)*X 1 0+(-2092107053/10000000000 : ℝ)*X 1 1+(5236046437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675409677/5000000000 : ℝ)*X 2 0+(523604633/1000000000 : ℝ)*X 2 1+(-2092107041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312163831/10000000000 : ℝ)*X 0 0+(4118859421/10000000000 : ℝ)*X 0 1+(902743301/2000000000 : ℝ)*X 0 2+(4312163831/10000000000 : ℝ)*X 1 0+(4118859421/10000000000 : ℝ)*X 1 1+(902743301/2000000000 : ℝ)*X 1 2+(4312163831/10000000000 : ℝ)*X 2 0+(4118859421/10000000000 : ℝ)*X 2 1+(902743301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-62430703/312500000 : ℝ)*X 0 0+(5236795381/10000000000 : ℝ)*X 0 1+(2710057569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302935633/10000000000 : ℝ)*X 1 0+(-1908037801/10000000000 : ℝ)*X 1 1+(5420115653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651468357/5000000000 : ℝ)*X 2 0+(5420114823/10000000000 : ℝ)*X 2 1+(-381607493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43122007/100000000 : ℝ)*X 0 0+(4512115933/10000000000 : ℝ)*X 0 1+(4120468097/10000000000 : ℝ)*X 0 2+(43122007/100000000 : ℝ)*X 1 0+(4512115933/10000000000 : ℝ)*X 1 1+(4120468097/10000000000 : ℝ)*X 1 2+(43122007/100000000 : ℝ)*X 2 0+(4512115933/10000000000 : ℝ)*X 2 1+(4120468097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16107497467803995687380901967/2865500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113858137/12500000000000 : ℝ)*(base19) + (836439207/100000000000000 : ℝ)*(base23) + (102046199/100000000000000 : ℝ)*(lower2) + (7516671/5000000000000 : ℝ)*(upper3) + (20439351/50000000000000 : ℝ)*(upper5) + (3971603340695493/100000000000000 : ℝ)*(major0) + (3971603340695493/100000000000000 : ℝ)*(major1) + (3971603340695493/100000000000000 : ℝ)*(major2) + (5410614939849393/100000000000000 : ℝ)*(sp0) + (5410630435606989/100000000000000 : ℝ)*(sp1) + (2705315255016439/50000000000000 : ℝ)*(sp2) + (1266283605877517/50000000000000 : ℝ)*(sp3) + (4101655673/25000000000000 : ℝ)*(sp4) + (63486329/800000000000 : ℝ)*(sp7) + (2532575147546159/100000000000000 : ℝ)*(f.failure) + (1082126269294417/20000000000000 : ℝ)*(f.sum) + (8809303630431/28655000000000000000000000000 : ℝ)*base66 + (13242743707274933989/5731000000000000000000000000000000 : ℝ)*base67 + (15537278212462066011/5731000000000000000000000000000000 : ℝ)*base70 + (17702759228567066011/5731000000000000000000000000000000 : ℝ)*base72 + (114720567267951/28655000000000000000000000000 : ℝ)*base74 + (19794570577920066011/5731000000000000000000000000000000 : ℝ)*base76 + (2771552484938066011/5731000000000000000000000000000000 : ℝ)*base78 + (68301305823458933989/5731000000000000000000000000000000 : ℝ)*base79 + (17961363636947/3581875000000000000000000000 : ℝ)*base82 + (55997/40000000000000000000 : ℝ)*base89 + (55997/40000000000000000000 : ℝ)*base91 + (55997/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1824633973481408158753441533/358187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49405699/2000000000000 : ℝ)*(base19) + (1007959723/25000000000000 : ℝ)*(base23) + (58971683/12500000000000 : ℝ)*(upper3) + (31505039/25000000000000 : ℝ)*(lower4) + (19582499/6250000000000 : ℝ)*(upper5) + (1001033717196493/25000000000000 : ℝ)*(major0) + (1001033717196493/25000000000000 : ℝ)*(major1) + (1001033717196493/25000000000000 : ℝ)*(major2) + (51095909423/100000000000000 : ℝ)*(sp1) + (74567280763/100000000000000 : ℝ)*(sp2) + (5454950017400003/100000000000000 : ℝ)*(sp4) + (545489645120563/10000000000000 : ℝ)*(sp5) + (5454871418280349/100000000000000 : ℝ)*(sp6) + (319164943796179/12500000000000 : ℝ)*(sp7) + (319164943796179/12500000000000 : ℝ)*(f.failure) + (5454950017400003/100000000000000 : ℝ)*(f.sum) + (15155264957119/7163750000000000000000000000 : ℝ)*base65 + (1379784830366256989/1432750000000000000000000000000000 : ℝ)*base67 + (16585259532369006989/1432750000000000000000000000000000 : ℝ)*base69 + (9646094572034256989/1432750000000000000000000000000000 : ℝ)*base71 + (62212182268749/28655000000000000000000000000 : ℝ)*base74 + (8279526363484756989/1432750000000000000000000000000000 : ℝ)*base75 + (10588675865751506989/1432750000000000000000000000000000 : ℝ)*base77 + (5254530910857243011/1432750000000000000000000000000000 : ℝ)*base80 + (41279108459689/7163750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48343/5000000000000000000 : ℝ)*base90 + (48343/5000000000000000000 : ℝ)*base92 + (48343/5000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1395_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14967/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1395_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1395_s4_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-499712961/2500000000 : ℝ)*x 0 + (169116523/312500000 : ℝ)*x 1 + (5244471977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499712961/2500000000 : ℝ)^4355 ≤ (6092561839149/50000000000000 : ℝ)^3331 := by
    have hnat : (499712961 : ℕ)^4355*50000000000000^3331 ≤ 6092561839149^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499712961 2500000000 6092561839149 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169116523/312500000 : ℝ)^4355 ≤ (44808402512529/100000000000000 : ℝ)^3331 := by
    have hnat : (169116523 : ℕ)^4355*100000000000000^3331 ≤ 44808402512529^3331*312500000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169116523 312500000 44808402512529 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244471977/10000000000 : ℝ)^4355 ≤ (10751618447483/25000000000000 : ℝ)^3331 := by
    have hnat : (5244471977 : ℕ)^4355*25000000000000^3331 ≤ 10751618447483^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244471977 10000000000 10751618447483 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499712961/2500000000 : ℝ), (169116523/312500000 : ℝ), (5244471977/10000000000 : ℝ)] ![(6092561839149/50000000000000 : ℝ), (44808402512529/100000000000000 : ℝ), (10751618447483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499712961/2500000000 : ℝ)|^4355 ≤ (6092561839149/50000000000000 : ℝ)^3331
        have hw : |(-499712961/2500000000 : ℝ)|=(499712961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169116523/312500000 : ℝ)|^4355 ≤ (44808402512529/100000000000000 : ℝ)^3331
        have hw : |(169116523/312500000 : ℝ)|=(169116523/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244471977/10000000000 : ℝ)|^4355 ≤ (10751618447483/25000000000000 : ℝ)^3331
        have hw : |(5244471977/10000000000 : ℝ)|=(5244471977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674236029/5000000000 : ℝ)*x 0 + (-1042030727/5000000000 : ℝ)*x 1 + (2622235969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674236029/5000000000 : ℝ)^4355 ≤ (137890213481/312500000000 : ℝ)^3331 := by
    have hnat : (2674236029 : ℕ)^4355*312500000000^3331 ≤ 137890213481^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674236029 5000000000 137890213481 312500000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042030727/5000000000 : ℝ)^4355 ≤ (2573731659273/20000000000000 : ℝ)^3331 := by
    have hnat : (1042030727 : ℕ)^4355*20000000000000^3331 ≤ 2573731659273^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042030727 5000000000 2573731659273 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622235969/5000000000 : ℝ)^4355 ≤ (43006473371803/100000000000000 : ℝ)^3331 := by
    have hnat : (2622235969 : ℕ)^4355*100000000000000^3331 ≤ 43006473371803^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622235969 5000000000 43006473371803 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674236029/5000000000 : ℝ), (-1042030727/5000000000 : ℝ), (2622235969/5000000000 : ℝ)] ![(137890213481/312500000000 : ℝ), (2573731659273/20000000000000 : ℝ), (43006473371803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674236029/5000000000 : ℝ)|^4355 ≤ (137890213481/312500000000 : ℝ)^3331
        have hw : |(2674236029/5000000000 : ℝ)|=(2674236029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042030727/5000000000 : ℝ)|^4355 ≤ (2573731659273/20000000000000 : ℝ)^3331
        have hw : |(-1042030727/5000000000 : ℝ)|=(1042030727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622235969/5000000000 : ℝ)|^4355 ≤ (43006473371803/100000000000000 : ℝ)^3331
        have hw : |(2622235969/5000000000 : ℝ)|=(2622235969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674235981/5000000000 : ℝ)*x 0 + (1048894393/2000000000 : ℝ)*x 1 + (-1042030773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674235981/5000000000 : ℝ)^4355 ≤ (44124867278447/100000000000000 : ℝ)^3331 := by
    have hnat : (2674235981 : ℕ)^4355*100000000000000^3331 ≤ 44124867278447^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674235981 5000000000 44124867278447 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048894393/2000000000 : ℝ)^4355 ≤ (43006473661277/100000000000000 : ℝ)^3331 := by
    have hnat : (1048894393 : ℕ)^4355*100000000000000^3331 ≤ 43006473661277^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048894393 2000000000 43006473661277 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042030773/5000000000 : ℝ)^4355 ≤ (12868659039083/100000000000000 : ℝ)^3331 := by
    have hnat : (1042030773 : ℕ)^4355*100000000000000^3331 ≤ 12868659039083^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042030773 5000000000 12868659039083 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674235981/5000000000 : ℝ), (1048894393/2000000000 : ℝ), (-1042030773/5000000000 : ℝ)] ![(44124867278447/100000000000000 : ℝ), (43006473661277/100000000000000 : ℝ), (12868659039083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674235981/5000000000 : ℝ)|^4355 ≤ (44124867278447/100000000000000 : ℝ)^3331
        have hw : |(2674235981/5000000000 : ℝ)|=(2674235981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048894393/2000000000 : ℝ)|^4355 ≤ (43006473661277/100000000000000 : ℝ)^3331
        have hw : |(1048894393/2000000000 : ℝ)|=(1048894393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042030773/5000000000 : ℝ)|^4355 ≤ (12868659039083/100000000000000 : ℝ)^3331
        have hw : |(-1042030773/5000000000 : ℝ)|=(1042030773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539103581/1250000000 : ℝ)*x 0 + (4137542097/10000000000 : ℝ)*x 1 + (2247435977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539103581/1250000000 : ℝ)^4355 ≤ (33302938612693/100000000000000 : ℝ)^3331 := by
    have hnat : (539103581 : ℕ)^4355*100000000000000^3331 ≤ 33302938612693^3331*1250000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539103581 1250000000 33302938612693 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137542097/10000000000 : ℝ)^4355 ≤ (31544469290671/100000000000000 : ℝ)^3331 := by
    have hnat : (4137542097 : ℕ)^4355*100000000000000^3331 ≤ 31544469290671^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137542097 10000000000 31544469290671 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247435977/5000000000 : ℝ)^4355 ≤ (4394074010117/12500000000000 : ℝ)^3331 := by
    have hnat : (2247435977 : ℕ)^4355*12500000000000^3331 ≤ 4394074010117^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247435977 5000000000 4394074010117 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539103581/1250000000 : ℝ), (4137542097/10000000000 : ℝ), (2247435977/5000000000 : ℝ)] ![(33302938612693/100000000000000 : ℝ), (31544469290671/100000000000000 : ℝ), (4394074010117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539103581/1250000000 : ℝ)|^4355 ≤ (33302938612693/100000000000000 : ℝ)^3331
        have hw : |(539103581/1250000000 : ℝ)|=(539103581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137542097/10000000000 : ℝ)|^4355 ≤ (31544469290671/100000000000000 : ℝ)^3331
        have hw : |(4137542097/10000000000 : ℝ)|=(4137542097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247435977/5000000000 : ℝ)|^4355 ≤ (4394074010117/12500000000000 : ℝ)^3331
        have hw : |(2247435977/5000000000 : ℝ)|=(2247435977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998864473/10000000000 : ℝ)*x 0 + (524508561/1000000000 : ℝ)*x 1 + (5411111677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998864473/10000000000 : ℝ)^4355 ≤ (6092612166289/50000000000000 : ℝ)^3331 := by
    have hnat : (1998864473 : ℕ)^4355*50000000000000^3331 ≤ 6092612166289^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998864473 10000000000 6092612166289 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524508561/1000000000 : ℝ)^4355 ≤ (43013052823617/100000000000000 : ℝ)^3331 := by
    have hnat : (524508561 : ℕ)^4355*100000000000000^3331 ≤ 43013052823617^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524508561 1000000000 43013052823617 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411111677/10000000000 : ℝ)^4355 ≤ (44801722826531/100000000000000 : ℝ)^3331 := by
    have hnat : (5411111677 : ℕ)^4355*100000000000000^3331 ≤ 44801722826531^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411111677 10000000000 44801722826531 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998864473/10000000000 : ℝ), (524508561/1000000000 : ℝ), (5411111677/10000000000 : ℝ)] ![(6092612166289/50000000000000 : ℝ), (43013052823617/100000000000000 : ℝ), (44801722826531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998864473/10000000000 : ℝ)|^4355 ≤ (6092612166289/50000000000000 : ℝ)^3331
        have hw : |(-1998864473/10000000000 : ℝ)|=(1998864473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524508561/1000000000 : ℝ)|^4355 ≤ (43013052823617/100000000000000 : ℝ)^3331
        have hw : |(524508561/1000000000 : ℝ)|=(524508561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411111677/10000000000 : ℝ)|^4355 ≤ (44801722826531/100000000000000 : ℝ)^3331
        have hw : |(5411111677/10000000000 : ℝ)|=(5411111677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652569467/5000000000 : ℝ)*x 0 + (-383484341/2000000000 : ℝ)*x 1 + (5411111913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652569467/5000000000 : ℝ)^4355 ≤ (43658053077571/100000000000000 : ℝ)^3331 := by
    have hnat : (2652569467 : ℕ)^4355*100000000000000^3331 ≤ 43658053077571^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652569467 5000000000 43658053077571 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383484341/2000000000 : ℝ)^4355 ≤ (5770110762209/50000000000000 : ℝ)^3331 := by
    have hnat : (383484341 : ℕ)^4355*50000000000000^3331 ≤ 5770110762209^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383484341 2000000000 5770110762209 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411111913/10000000000 : ℝ)^4355 ≤ (22400862690597/50000000000000 : ℝ)^3331 := by
    have hnat : (5411111913 : ℕ)^4355*50000000000000^3331 ≤ 22400862690597^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411111913 10000000000 22400862690597 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652569467/5000000000 : ℝ), (-383484341/2000000000 : ℝ), (5411111913/10000000000 : ℝ)] ![(43658053077571/100000000000000 : ℝ), (5770110762209/50000000000000 : ℝ), (22400862690597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652569467/5000000000 : ℝ)|^4355 ≤ (43658053077571/100000000000000 : ℝ)^3331
        have hw : |(2652569467/5000000000 : ℝ)|=(2652569467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383484341/2000000000 : ℝ)|^4355 ≤ (5770110762209/50000000000000 : ℝ)^3331
        have hw : |(-383484341/2000000000 : ℝ)|=(383484341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411111913/10000000000 : ℝ)|^4355 ≤ (22400862690597/50000000000000 : ℝ)^3331
        have hw : |(5411111913/10000000000 : ℝ)|=(5411111913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326284709/2500000000 : ℝ)*x 0 + (216444473/400000000 : ℝ)*x 1 + (-47935549/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326284709/2500000000 : ℝ)^4355 ≤ (43658052023167/100000000000000 : ℝ)^3331 := by
    have hnat : (1326284709 : ℕ)^4355*100000000000000^3331 ≤ 43658052023167^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326284709 2500000000 43658052023167 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216444473/400000000 : ℝ)^4355 ≤ (700026944197/1562500000000 : ℝ)^3331 := by
    have hnat : (216444473 : ℕ)^4355*1562500000000^3331 ≤ 700026944197^3331*400000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216444473 400000000 700026944197 1562500000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47935549/250000000 : ℝ)^4355 ≤ (11540223530969/100000000000000 : ℝ)^3331 := by
    have hnat : (47935549 : ℕ)^4355*100000000000000^3331 ≤ 11540223530969^3331*250000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47935549 250000000 11540223530969 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326284709/2500000000 : ℝ), (216444473/400000000 : ℝ), (-47935549/250000000 : ℝ)] ![(43658052023167/100000000000000 : ℝ), (700026944197/1562500000000 : ℝ), (11540223530969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326284709/2500000000 : ℝ)|^4355 ≤ (43658052023167/100000000000000 : ℝ)^3331
        have hw : |(1326284709/2500000000 : ℝ)|=(1326284709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216444473/400000000 : ℝ)|^4355 ≤ (700026944197/1562500000000 : ℝ)^3331
        have hw : |(216444473/400000000 : ℝ)|=(216444473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47935549/250000000 : ℝ)|^4355 ≤ (11540223530969/100000000000000 : ℝ)^3331
        have hw : |(-47935549/250000000 : ℝ)|=(47935549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s4_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269553449/625000000 : ℝ)*x 0 + (2246780259/5000000000 : ℝ)*x 1 + (1034715089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269553449/625000000 : ℝ)^4355 ≤ (2081450406929/6250000000000 : ℝ)^3331 := by
    have hnat : (269553449 : ℕ)^4355*6250000000000^3331 ≤ 2081450406929^3331*625000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269553449 625000000 2081450406929 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246780259/5000000000 : ℝ)^4355 ≤ (8784795887643/25000000000000 : ℝ)^3331 := by
    have hnat : (2246780259 : ℕ)^4355*25000000000000^3331 ≤ 8784795887643^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246780259 5000000000 8784795887643 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034715089/2500000000 : ℝ)^4355 ≤ (1972350620327/6250000000000 : ℝ)^3331 := by
    have hnat : (1034715089 : ℕ)^4355*6250000000000^3331 ≤ 1972350620327^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034715089 2500000000 1972350620327 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269553449/625000000 : ℝ), (2246780259/5000000000 : ℝ), (1034715089/2500000000 : ℝ)] ![(2081450406929/6250000000000 : ℝ), (8784795887643/25000000000000 : ℝ), (1972350620327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269553449/625000000 : ℝ)|^4355 ≤ (2081450406929/6250000000000 : ℝ)^3331
        have hw : |(269553449/625000000 : ℝ)|=(269553449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246780259/5000000000 : ℝ)|^4355 ≤ (8784795887643/25000000000000 : ℝ)^3331
        have hw : |(2246780259/5000000000 : ℝ)|=(2246780259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034715089/2500000000 : ℝ)|^4355 ≤ (1972350620327/6250000000000 : ℝ)^3331
        have hw : |(1034715089/2500000000 : ℝ)|=(1034715089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5527/50000 : ℝ) ^ (2177/512 : ℝ) ≤ (4286073204229253/50000000000000000000 : ℝ) := by
    have hpowers : (5527/50000 : ℝ)^2177 ≤ (4286073204229253/50000000000000000000 : ℝ)^512 := by
      have hnat : (5527 : ℕ)^2177*50000000000000000000^512 ≤ 4286073204229253^512*50000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5527 50000 4286073204229253 50000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5527/50000 : ℝ)) (X := (4286073204229253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14967/100000 : ℝ) ^ (2177/512 : ℝ) ≤ (31096510646122021/100000000000000000000 : ℝ) := by
    have hpowers : (14967/100000 : ℝ)^2177 ≤ (31096510646122021/100000000000000000000 : ℝ)^512 := by
      have hnat : (14967 : ℕ)^2177*100000000000000000000^512 ≤ 31096510646122021^512*100000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14967 100000 31096510646122021 100000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14967/100000 : ℝ)) (X := (31096510646122021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004286073204229253/25000000000000000000 : ℝ) ≤ (2500100795848577/2500000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (25004286073204229253/25000000000000000000 : ℝ)^512 ≤ (2500100795848577/2500000000000000 : ℝ)^2177 := by
      have hnat : (25004286073204229253 : ℕ)^512*2500000000000000^2177 ≤ 2500100795848577^2177*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004286073204229253 25000000000000000000 2500100795848577 2500000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100795848577/2500000000000000 : ℝ)) (X := (25004286073204229253/25000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039668657054580527/100000000000000000000 : ℝ) ≤ (10000932809928219/10000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (100039668657054580527/100000000000000000000 : ℝ)^512 ≤ (10000932809928219/10000000000000000 : ℝ)^2177 := by
      have hnat : (100039668657054580527 : ℕ)^512*10000000000000000^2177 ≤ 10000932809928219^2177*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039668657054580527 100000000000000000000 10000932809928219 10000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000932809928219/10000000000000000 : ℝ)) (X := (100039668657054580527/100000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031096510646122021/50000000000000000000 : ℝ) ≤ (1000146243646213/1000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (50031096510646122021/50000000000000000000 : ℝ)^512 ≤ (1000146243646213/1000000000000000 : ℝ)^2177 := by
      have hnat : (50031096510646122021 : ℕ)^512*1000000000000000^2177 ≤ 1000146243646213^2177*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031096510646122021 50000000000000000000 1000146243646213 1000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000146243646213/1000000000000000 : ℝ)) (X := (50031096510646122021/50000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4286073204229253/50000000000000000000 : ℝ) ≤ ((1222495896037819463/1222812500000000000 : ℝ)+2*(529626533911/391300000000000 : ℝ)*(5527/50000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (1222495896037819463/1222812500000000000 : ℝ)+2*(529626533911/391300000000000 : ℝ)*(5527/50000 : ℝ)=(2500100795848577/2500000000000000 : ℝ) by norm_num, show 1+2*(4286073204229253/50000000000000000000 : ℝ)=(25004286073204229253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31096510646122021/100000000000000000000 : ℝ)+(4286073204229253/50000000000000000000 : ℝ) ≤ ((1222495896037819463/1222812500000000000 : ℝ)+(529626533911/391300000000000 : ℝ)*((14967/100000 : ℝ)+(5527/50000 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (1222495896037819463/1222812500000000000 : ℝ)+(529626533911/391300000000000 : ℝ)*((14967/100000 : ℝ)+(5527/50000 : ℝ))=(10000932809928219/10000000000000000 : ℝ) by norm_num, show 1+(31096510646122021/100000000000000000000 : ℝ)+(4286073204229253/50000000000000000000 : ℝ)=(100039668657054580527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31096510646122021/100000000000000000000 : ℝ) ≤ ((1222495896037819463/1222812500000000000 : ℝ)+2*(529626533911/391300000000000 : ℝ)*(14967/100000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (1222495896037819463/1222812500000000000 : ℝ)+2*(529626533911/391300000000000 : ℝ)*(14967/100000 : ℝ)=(1000146243646213/1000000000000000 : ℝ) by norm_num, show 1+2*(31096510646122021/100000000000000000000 : ℝ)=(50031096510646122021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1222495896037819463/1222812500000000000 : ℝ)*(X 1 0+X 2 0)+(529626533911/391300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14967/100000 : ℝ)) (c := (1222495896037819463/1222812500000000000 : ℝ)) (alpha := (529626533911/391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1222495896037819463/1222812500000000000 : ℝ)*(X 0 1+X 2 1)+(529626533911/391300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14967/100000 : ℝ)) (c := (1222495896037819463/1222812500000000000 : ℝ)) (alpha := (529626533911/391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1222495896037819463/1222812500000000000 : ℝ)*(X 0 2+X 1 2)+(529626533911/391300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (14967/100000 : ℝ)) (c := (1222495896037819463/1222812500000000000 : ℝ)) (alpha := (529626533911/391300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-499712961/2500000000 : ℝ)*X 0 0+(169116523/312500000 : ℝ)*X 0 1+(5244471977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674236029/5000000000 : ℝ)*X 1 0+(-1042030727/5000000000 : ℝ)*X 1 1+(2622235969/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674235981/5000000000 : ℝ)*X 2 0+(1048894393/2000000000 : ℝ)*X 2 1+(-1042030773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539103581/1250000000 : ℝ)*X 0 0+(4137542097/10000000000 : ℝ)*X 0 1+(2247435977/5000000000 : ℝ)*X 0 2+(539103581/1250000000 : ℝ)*X 1 0+(4137542097/10000000000 : ℝ)*X 1 1+(2247435977/5000000000 : ℝ)*X 1 2+(539103581/1250000000 : ℝ)*X 2 0+(4137542097/10000000000 : ℝ)*X 2 1+(2247435977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1998864473/10000000000 : ℝ)*X 0 0+(524508561/1000000000 : ℝ)*X 0 1+(5411111677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652569467/5000000000 : ℝ)*X 1 0+(-383484341/2000000000 : ℝ)*X 1 1+(5411111913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326284709/2500000000 : ℝ)*X 2 0+(216444473/400000000 : ℝ)*X 2 1+(-47935549/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269553449/625000000 : ℝ)*X 0 0+(2246780259/5000000000 : ℝ)*X 0 1+(1034715089/2500000000 : ℝ)*X 0 2+(269553449/625000000 : ℝ)*X 1 0+(2246780259/5000000000 : ℝ)*X 1 1+(1034715089/2500000000 : ℝ)*X 1 2+(269553449/625000000 : ℝ)*X 2 0+(2246780259/5000000000 : ℝ)*X 2 1+(1034715089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4226283899448884712084159/955322265625000000000000000000 : ℝ) := by norm_num
    linear_combination (810126527/100000000000000 : ℝ)*(base19) + (363304781/50000000000000 : ℝ)*(base23) + (383119/2500000000000 : ℝ)*(lower2) + (114534111/100000000000000 : ℝ)*(upper3) + (14026529/50000000000000 : ℝ)*(lower4) + (68573578194403/1562500000000 : ℝ)*(major0) + (68573578194403/1562500000000 : ℝ)*(major1) + (68573578194403/1562500000000 : ℝ)*(major2) + (2989425899838457/50000000000000 : ℝ)*(sp0) + (5978865836327817/100000000000000 : ℝ)*(sp1) + (2989432959922391/50000000000000 : ℝ)*(sp2) + (1399271164775377/50000000000000 : ℝ)*(sp3) + (1484677743/10000000000000 : ℝ)*(sp4) + (888541397/10000000000000 : ℝ)*(sp7) + (699637803741181/25000000000000 : ℝ)*(f.failure) + (747358330806793/12500000000000 : ℝ)*(f.sum) + (86498912174611/9782500000000000000000000000 : ℝ)*base65 + (266009554677753701/30570312500000000000000000000000 : ℝ)*base68 + (197086344691947163/15285156250000000000000000000000 : ℝ)*base70 + (225594007494378701/30570312500000000000000000000000 : ℝ)*base72 + (1849497614957/1222812500000000000000000000 : ℝ)*base73 + (9190042338340049/30570312500000000000000000000000 : ℝ)*base75 + (194822729707634663/15285156250000000000000000000000 : ℝ)*base78 + (16457809130040913/15285156250000000000000000000000 : ℝ)*base80 + (271943027261/611406250000000000000000000 : ℝ)*base81 + (41223/10000000000000000000 : ℝ)*base89 + (41223/10000000000000000000 : ℝ)*base91 + (41223/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (703760174975370638500971711/61140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1958424593/100000000000000 : ℝ)*(base19) + (1816970149/100000000000000 : ℝ)*(base23) + (173521/500000000000 : ℝ)*(upper2) + (60616779/25000000000000 : ℝ)*(upper3) + (343931141/100000000000000 : ℝ)*(upper5) + (2210608144113379/50000000000000 : ℝ)*(major0) + (2210608144113379/50000000000000 : ℝ)*(major1) + (2210608144113379/50000000000000 : ℝ)*(major2) + (47910376813/100000000000000 : ℝ)*(sp1) + (9051375309/25000000000000 : ℝ)*(sp2) + (1505788008716323/25000000000000 : ℝ)*(sp4) + (6023102166063887/100000000000000 : ℝ)*(sp5) + (6023114012393907/100000000000000 : ℝ)*(sp6) + (704820039476083/25000000000000 : ℝ)*(sp7) + (704820039476083/25000000000000 : ℝ)*(f.failure) + (1505788008716323/25000000000000 : ℝ)*(f.sum) + (21113796774179/9782500000000000000000000000 : ℝ)*base65 + (239022836264694449/30570312500000000000000000000000 : ℝ)*base68 + (211117178328288199/30570312500000000000000000000000 : ℝ)*base70 + (94795544229163199/30570312500000000000000000000000 : ℝ)*base72 + (29812729095003/19565000000000000000000000000 : ℝ)*base73 + (1362940634336779523/61140625000000000000000000000000 : ℝ)*base76 + (70985846311475699/30570312500000000000000000000000 : ℝ)*base78 + (254445290531498273/61140625000000000000000000000000 : ℝ)*base80 + (11928628253251/9782500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (27511/10000000000000000000 : ℝ)*base90 + (27511/10000000000000000000 : ℝ)*base92 + (27511/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1395_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1395_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1395_s5_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-999511833/5000000000 : ℝ)*x 0 + (5410218657/10000000000 : ℝ)*x 1 + (1049173769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999511833/5000000000 : ℝ)^4355 ≤ (3046623283013/25000000000000 : ℝ)^3331 := by
    have hnat : (999511833 : ℕ)^4355*25000000000000^3331 ≤ 3046623283013^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999511833 5000000000 3046623283013 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410218657/10000000000 : ℝ)^4355 ≤ (11198014066847/25000000000000 : ℝ)^3331 := by
    have hnat : (5410218657 : ℕ)^4355*25000000000000^3331 ≤ 11198014066847^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410218657 10000000000 11198014066847 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049173769/2000000000 : ℝ)^4355 ≤ (43021450579911/100000000000000 : ℝ)^3331 := by
    have hnat : (1049173769 : ℕ)^4355*100000000000000^3331 ≤ 43021450579911^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049173769 2000000000 43021450579911 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999511833/5000000000 : ℝ), (5410218657/10000000000 : ℝ), (1049173769/2000000000 : ℝ)] ![(3046623283013/25000000000000 : ℝ), (11198014066847/25000000000000 : ℝ), (43021450579911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999511833/5000000000 : ℝ)|^4355 ≤ (3046623283013/25000000000000 : ℝ)^3331
        have hw : |(-999511833/5000000000 : ℝ)|=(999511833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410218657/10000000000 : ℝ)|^4355 ≤ (11198014066847/25000000000000 : ℝ)^3331
        have hw : |(5410218657/10000000000 : ℝ)|=(5410218657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049173769/2000000000 : ℝ)|^4355 ≤ (43021450579911/100000000000000 : ℝ)^3331
        have hw : |(1049173769/2000000000 : ℝ)|=(1049173769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348082761/10000000000 : ℝ)*x 0 + (-2082724207/10000000000 : ℝ)*x 1 + (163933449/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348082761/10000000000 : ℝ)^4355 ≤ (22060334668847/50000000000000 : ℝ)^3331 := by
    have hnat : (5348082761 : ℕ)^4355*50000000000000^3331 ≤ 22060334668847^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348082761 10000000000 22060334668847 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082724207/10000000000 : ℝ)^4355 ≤ (12857863733367/100000000000000 : ℝ)^3331 := by
    have hnat : (2082724207 : ℕ)^4355*100000000000000^3331 ≤ 12857863733367^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082724207 10000000000 12857863733367 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163933449/312500000 : ℝ)^4355 ≤ (21510733454859/50000000000000 : ℝ)^3331 := by
    have hnat : (163933449 : ℕ)^4355*50000000000000^3331 ≤ 21510733454859^3331*312500000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163933449 312500000 21510733454859 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348082761/10000000000 : ℝ), (-2082724207/10000000000 : ℝ), (163933449/312500000 : ℝ)] ![(22060334668847/50000000000000 : ℝ), (12857863733367/100000000000000 : ℝ), (21510733454859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348082761/10000000000 : ℝ)|^4355 ≤ (22060334668847/50000000000000 : ℝ)^3331
        have hw : |(5348082761/10000000000 : ℝ)|=(5348082761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082724207/10000000000 : ℝ)|^4355 ≤ (12857863733367/100000000000000 : ℝ)^3331
        have hw : |(-2082724207/10000000000 : ℝ)|=(2082724207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163933449/312500000 : ℝ)|^4355 ≤ (21510733454859/50000000000000 : ℝ)^3331
        have hw : |(163933449/312500000 : ℝ)|=(163933449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348083301/10000000000 : ℝ)*x 0 + (5245869297/10000000000 : ℝ)*x 1 + (-2082724909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348083301/10000000000 : ℝ)^4355 ≤ (8824135032419/20000000000000 : ℝ)^3331 := by
    have hnat : (5348083301 : ℕ)^4355*20000000000000^3331 ≤ 8824135032419^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348083301 10000000000 8824135032419 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245869297/10000000000 : ℝ)^4355 ≤ (21510727713157/50000000000000 : ℝ)^3331 := by
    have hnat : (5245869297 : ℕ)^4355*50000000000000^3331 ≤ 21510727713157^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245869297 10000000000 21510727713157 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082724909/10000000000 : ℝ)^4355 ≤ (1607233674939/12500000000000 : ℝ)^3331 := by
    have hnat : (2082724909 : ℕ)^4355*12500000000000^3331 ≤ 1607233674939^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082724909 10000000000 1607233674939 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348083301/10000000000 : ℝ), (5245869297/10000000000 : ℝ), (-2082724909/10000000000 : ℝ)] ![(8824135032419/20000000000000 : ℝ), (21510727713157/50000000000000 : ℝ), (1607233674939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348083301/10000000000 : ℝ)|^4355 ≤ (8824135032419/20000000000000 : ℝ)^3331
        have hw : |(5348083301/10000000000 : ℝ)|=(5348083301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245869297/10000000000 : ℝ)|^4355 ≤ (21510727713157/50000000000000 : ℝ)^3331
        have hw : |(5245869297/10000000000 : ℝ)|=(5245869297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082724909/10000000000 : ℝ)|^4355 ≤ (1607233674939/12500000000000 : ℝ)^3331
        have hw : |(-2082724909/10000000000 : ℝ)|=(2082724909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312932883/10000000000 : ℝ)*x 0 + (4140636379/10000000000 : ℝ)*x 1 + (2245875937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312932883/10000000000 : ℝ)^4355 ≤ (2081499433481/6250000000000 : ℝ)^3331 := by
    have hnat : (4312932883 : ℕ)^4355*6250000000000^3331 ≤ 2081499433481^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312932883 10000000000 2081499433481 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4140636379/10000000000 : ℝ)^4355 ≤ (3946914458159/12500000000000 : ℝ)^3331 := by
    have hnat : (4140636379 : ℕ)^4355*12500000000000^3331 ≤ 3946914458159^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140636379 10000000000 3946914458159 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245875937/5000000000 : ℝ)^4355 ≤ (1756034669211/5000000000000 : ℝ)^3331 := by
    have hnat : (2245875937 : ℕ)^4355*5000000000000^3331 ≤ 1756034669211^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245875937 5000000000 1756034669211 5000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312932883/10000000000 : ℝ), (4140636379/10000000000 : ℝ), (2245875937/5000000000 : ℝ)] ![(2081499433481/6250000000000 : ℝ), (3946914458159/12500000000000 : ℝ), (1756034669211/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312932883/10000000000 : ℝ)|^4355 ≤ (2081499433481/6250000000000 : ℝ)^3331
        have hw : |(4312932883/10000000000 : ℝ)|=(4312932883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4140636379/10000000000 : ℝ)|^4355 ≤ (3946914458159/12500000000000 : ℝ)^3331
        have hw : |(4140636379/10000000000 : ℝ)|=(4140636379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245875937/5000000000 : ℝ)|^4355 ≤ (1756034669211/5000000000000 : ℝ)^3331
        have hw : |(2245875937/5000000000 : ℝ)|=(2245875937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-999517741/5000000000 : ℝ)*x 0 + (524646229/1000000000 : ℝ)*x 1 + (5409622093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999517741/5000000000 : ℝ)^4355 ≤ (12186587309131/100000000000000 : ℝ)^3331 := by
    have hnat : (999517741 : ℕ)^4355*100000000000000^3331 ≤ 12186587309131^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999517741 5000000000 12186587309131 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524646229/1000000000 : ℝ)^4355 ≤ (5378476710769/12500000000000 : ℝ)^3331 := by
    have hnat : (524646229 : ℕ)^4355*12500000000000^3331 ≤ 5378476710769^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524646229 1000000000 5378476710769 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409622093/10000000000 : ℝ)^4355 ≤ (44785598990787/100000000000000 : ℝ)^3331 := by
    have hnat : (5409622093 : ℕ)^4355*100000000000000^3331 ≤ 44785598990787^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409622093 10000000000 44785598990787 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999517741/5000000000 : ℝ), (524646229/1000000000 : ℝ), (5409622093/10000000000 : ℝ)] ![(12186587309131/100000000000000 : ℝ), (5378476710769/12500000000000 : ℝ), (44785598990787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999517741/5000000000 : ℝ)|^4355 ≤ (12186587309131/100000000000000 : ℝ)^3331
        have hw : |(-999517741/5000000000 : ℝ)|=(999517741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524646229/1000000000 : ℝ)|^4355 ≤ (5378476710769/12500000000000 : ℝ)^3331
        have hw : |(524646229/1000000000 : ℝ)|=(524646229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409622093/10000000000 : ℝ)|^4355 ≤ (44785598990787/100000000000000 : ℝ)^3331
        have hw : |(5409622093/10000000000 : ℝ)|=(5409622093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326375923/2500000000 : ℝ)*x 0 + (-191897217/1000000000 : ℝ)*x 1 + (5409622091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326375923/2500000000 : ℝ)^4355 ≤ (436619776337/1000000000000 : ℝ)^3331 := by
    have hnat : (1326375923 : ℕ)^4355*1000000000000^3331 ≤ 436619776337^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326375923 2500000000 436619776337 1000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191897217/1000000000 : ℝ)^4355 ≤ (5776211691193/50000000000000 : ℝ)^3331 := by
    have hnat : (191897217 : ℕ)^4355*50000000000000^3331 ≤ 5776211691193^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191897217 1000000000 5776211691193 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409622091/10000000000 : ℝ)^4355 ≤ (44785598969139/100000000000000 : ℝ)^3331 := by
    have hnat : (5409622091 : ℕ)^4355*100000000000000^3331 ≤ 44785598969139^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409622091 10000000000 44785598969139 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326375923/2500000000 : ℝ), (-191897217/1000000000 : ℝ), (5409622091/10000000000 : ℝ)] ![(436619776337/1000000000000 : ℝ), (5776211691193/50000000000000 : ℝ), (44785598969139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326375923/2500000000 : ℝ)|^4355 ≤ (436619776337/1000000000000 : ℝ)^3331
        have hw : |(1326375923/2500000000 : ℝ)|=(1326375923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191897217/1000000000 : ℝ)|^4355 ≤ (5776211691193/50000000000000 : ℝ)^3331
        have hw : |(-191897217/1000000000 : ℝ)|=(191897217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409622091/10000000000 : ℝ)|^4355 ≤ (44785598969139/100000000000000 : ℝ)^3331
        have hw : |(5409622091/10000000000 : ℝ)|=(5409622091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331593981/625000000 : ℝ)*x 0 + (5409622089/10000000000 : ℝ)*x 1 + (-1918972167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331593981/625000000 : ℝ)^4355 ≤ (43661977676737/100000000000000 : ℝ)^3331 := by
    have hnat : (331593981 : ℕ)^4355*100000000000000^3331 ≤ 43661977676737^3331*625000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331593981 625000000 43661977676737 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409622089/10000000000 : ℝ)^4355 ≤ (44785598947491/100000000000000 : ℝ)^3331 := by
    have hnat : (5409622089 : ℕ)^4355*100000000000000^3331 ≤ 44785598947491^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409622089 10000000000 44785598947491 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918972167/10000000000 : ℝ)^4355 ≤ (5776211679387/50000000000000 : ℝ)^3331 := by
    have hnat : (1918972167 : ℕ)^4355*50000000000000^3331 ≤ 5776211679387^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918972167 10000000000 5776211679387 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331593981/625000000 : ℝ), (5409622089/10000000000 : ℝ), (-1918972167/10000000000 : ℝ)] ![(43661977676737/100000000000000 : ℝ), (44785598947491/100000000000000 : ℝ), (5776211679387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331593981/625000000 : ℝ)|^4355 ≤ (43661977676737/100000000000000 : ℝ)^3331
        have hw : |(331593981/625000000 : ℝ)|=(331593981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409622089/10000000000 : ℝ)|^4355 ≤ (44785598947491/100000000000000 : ℝ)^3331
        have hw : |(5409622089/10000000000 : ℝ)|=(5409622089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918972167/10000000000 : ℝ)|^4355 ≤ (5776211679387/50000000000000 : ℝ)^3331
        have hw : |(-1918972167/10000000000 : ℝ)|=(1918972167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s5_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33694981/78125000 : ℝ)*x 0 + (4490486133/10000000000 : ℝ)*x 1 + (2070954539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33694981/78125000 : ℝ)^4355 ≤ (16652120074327/50000000000000 : ℝ)^3331 := by
    have hnat : (33694981 : ℕ)^4355*50000000000000^3331 ≤ 16652120074327^3331*78125000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33694981 78125000 16652120074327 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490486133/10000000000 : ℝ)^4355 ≤ (35107754796157/100000000000000 : ℝ)^3331 := by
    have hnat : (4490486133 : ℕ)^4355*100000000000000^3331 ≤ 35107754796157^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490486133 10000000000 35107754796157 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070954539/5000000000 : ℝ)^4355 ≤ (3948500630477/12500000000000 : ℝ)^3331 := by
    have hnat : (2070954539 : ℕ)^4355*12500000000000^3331 ≤ 3948500630477^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070954539 5000000000 3948500630477 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33694981/78125000 : ℝ), (4490486133/10000000000 : ℝ), (2070954539/5000000000 : ℝ)] ![(16652120074327/50000000000000 : ℝ), (35107754796157/100000000000000 : ℝ), (3948500630477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33694981/78125000 : ℝ)|^4355 ≤ (16652120074327/50000000000000 : ℝ)^3331
        have hw : |(33694981/78125000 : ℝ)|=(33694981/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490486133/10000000000 : ℝ)|^4355 ≤ (35107754796157/100000000000000 : ℝ)^3331
        have hw : |(4490486133/10000000000 : ℝ)|=(4490486133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070954539/5000000000 : ℝ)|^4355 ≤ (3948500630477/12500000000000 : ℝ)^3331
        have hw : |(2070954539/5000000000 : ℝ)|=(2070954539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (352/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1843/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (2177/512 : ℝ) ≤ (1836313612981359/20000000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^2177 ≤ (1836313612981359/20000000000000000000 : ℝ)^512 := by
      have hnat : (5617 : ℕ)^2177*20000000000000000000^512 ≤ 1836313612981359^512*50000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 1836313612981359 20000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (1836313612981359/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (2177/512 : ℝ) ≤ (2944386318961897/10000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^2177 ≤ (2944386318961897/10000000000000000000 : ℝ)^512 := by
      have hnat : (1847 : ℕ)^2177*10000000000000000000^512 ≤ 2944386318961897^512*12500^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 2944386318961897 10000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (2944386318961897/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001836313612981359/10000000000000000000 : ℝ) ≤ (500021592249767/500000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (10001836313612981359/10000000000000000000 : ℝ)^512 ≤ (500021592249767/500000000000000 : ℝ)^2177 := by
      have hnat : (10001836313612981359 : ℕ)^512*500000000000000^2177 ≤ 500021592249767^2177*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001836313612981359 10000000000000000000 500021592249767 500000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021592249767/500000000000000 : ℝ)) (X := (10001836313612981359/10000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007725086250905153/20000000000000000000 : ℝ) ≤ (10000908282057537/10000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (20007725086250905153/20000000000000000000 : ℝ)^512 ≤ (10000908282057537/10000000000000000 : ℝ)^2177 := by
      have hnat : (20007725086250905153 : ℕ)^512*10000000000000000^2177 ≤ 10000908282057537^2177*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007725086250905153 20000000000000000000 10000908282057537 10000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000908282057537/10000000000000000 : ℝ)) (X := (20007725086250905153/20000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002944386318961897/5000000000000000000 : ℝ) ≤ (5000692359559867/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (5002944386318961897/5000000000000000000 : ℝ)^512 ≤ (5000692359559867/5000000000000000 : ℝ)^2177 := by
      have hnat : (5002944386318961897 : ℕ)^512*5000000000000000^2177 ≤ 5000692359559867^2177*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002944386318961897 5000000000000000000 5000692359559867 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000692359559867/5000000000000000 : ℝ)) (X := (5002944386318961897/5000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1836313612981359/20000000000000000000 : ℝ) ≤ ((8852706251765013021/8855000000000000000 : ℝ)+2*(476437062197/354200000000000 : ℝ)*(5617/50000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (8852706251765013021/8855000000000000000 : ℝ)+2*(476437062197/354200000000000 : ℝ)*(5617/50000 : ℝ)=(500021592249767/500000000000000 : ℝ) by norm_num, show 1+2*(1836313612981359/20000000000000000000 : ℝ)=(10001836313612981359/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2944386318961897/10000000000000000000 : ℝ)+(1836313612981359/20000000000000000000 : ℝ) ≤ ((8852706251765013021/8855000000000000000 : ℝ)+(476437062197/354200000000000 : ℝ)*((1847/12500 : ℝ)+(5617/50000 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (8852706251765013021/8855000000000000000 : ℝ)+(476437062197/354200000000000 : ℝ)*((1847/12500 : ℝ)+(5617/50000 : ℝ))=(10000908282057537/10000000000000000 : ℝ) by norm_num, show 1+(2944386318961897/10000000000000000000 : ℝ)+(1836313612981359/20000000000000000000 : ℝ)=(20007725086250905153/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2944386318961897/10000000000000000000 : ℝ) ≤ ((8852706251765013021/8855000000000000000 : ℝ)+2*(476437062197/354200000000000 : ℝ)*(1847/12500 : ℝ))^(2177/512 : ℝ) := by
    rw [show (8852706251765013021/8855000000000000000 : ℝ)+2*(476437062197/354200000000000 : ℝ)*(1847/12500 : ℝ)=(5000692359559867/5000000000000000 : ℝ) by norm_num, show 1+2*(2944386318961897/10000000000000000000 : ℝ)=(5002944386318961897/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8852706251765013021/8855000000000000000 : ℝ)*(X 1 0+X 2 0)+(476437062197/354200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8852706251765013021/8855000000000000000 : ℝ)) (alpha := (476437062197/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8852706251765013021/8855000000000000000 : ℝ)*(X 0 1+X 2 1)+(476437062197/354200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8852706251765013021/8855000000000000000 : ℝ)) (alpha := (476437062197/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8852706251765013021/8855000000000000000 : ℝ)*(X 0 2+X 1 2)+(476437062197/354200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8852706251765013021/8855000000000000000 : ℝ)) (alpha := (476437062197/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-999511833/5000000000 : ℝ)*X 0 0+(5410218657/10000000000 : ℝ)*X 0 1+(1049173769/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348082761/10000000000 : ℝ)*X 1 0+(-2082724207/10000000000 : ℝ)*X 1 1+(163933449/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348083301/10000000000 : ℝ)*X 2 0+(5245869297/10000000000 : ℝ)*X 2 1+(-2082724909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312932883/10000000000 : ℝ)*X 0 0+(4140636379/10000000000 : ℝ)*X 0 1+(2245875937/5000000000 : ℝ)*X 0 2+(4312932883/10000000000 : ℝ)*X 1 0+(4140636379/10000000000 : ℝ)*X 1 1+(2245875937/5000000000 : ℝ)*X 1 2+(4312932883/10000000000 : ℝ)*X 2 0+(4140636379/10000000000 : ℝ)*X 2 1+(2245875937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-999517741/5000000000 : ℝ)*X 0 0+(524646229/1000000000 : ℝ)*X 0 1+(5409622093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326375923/2500000000 : ℝ)*X 1 0+(-191897217/1000000000 : ℝ)*X 1 1+(5409622091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331593981/625000000 : ℝ)*X 2 0+(5409622089/10000000000 : ℝ)*X 2 1+(-1918972167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33694981/78125000 : ℝ)*X 0 0+(4490486133/10000000000 : ℝ)*X 0 1+(2070954539/5000000000 : ℝ)*X 0 2+(33694981/78125000 : ℝ)*X 1 0+(4490486133/10000000000 : ℝ)*X 1 1+(2070954539/5000000000 : ℝ)*X 1 2+(33694981/78125000 : ℝ)*X 2 0+(4490486133/10000000000 : ℝ)*X 2 1+(2070954539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (640819466896230736168269297/221375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (793208917/100000000000000 : ℝ)*(base23) + (20677983/100000000000000 : ℝ)*(lower2) + (41260457/20000000000000 : ℝ)*(upper3) + (82663311/50000000000000 : ℝ)*(lower4) + (4466378071370781/100000000000000 : ℝ)*(major0) + (4466378071370781/100000000000000 : ℝ)*(major1) + (4466378071370781/100000000000000 : ℝ)*(major2) + (3042316774537139/50000000000000 : ℝ)*(sp0) + (1216935508346951/20000000000000 : ℝ)*(sp1) + (304233261957219/5000000000000 : ℝ)*(sp2) + (1424035091702087/50000000000000 : ℝ)*(sp3) + (43992660477/100000000000000 : ℝ)*(sp4) + (11509381457/100000000000000 : ℝ)*(sp6) + (8321111829/100000000000000 : ℝ)*(sp7) + (712019626129001/25000000000000 : ℝ)*(f.failure) + (1216935508346951/20000000000000 : ℝ)*(f.sum) + (285649243609063/17710000000000000000000000000 : ℝ)*base66 + (1057802844132266343/126500000000000000000000000000000 : ℝ)*base67 + (1622111396137266343/126500000000000000000000000000000 : ℝ)*base69 + (711660672952733657/126500000000000000000000000000000 : ℝ)*base72 + (25836335628077/17710000000000000000000000000 : ℝ)*base73 + (1015916746158766343/126500000000000000000000000000000 : ℝ)*base75 + (2103811257576766343/126500000000000000000000000000000 : ℝ)*base77 + (3228797418171766343/126500000000000000000000000000000 : ℝ)*base79 + (4052361213567/17710000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (34283/10000000000000000000 : ℝ)*base89 + (34283/10000000000000000000 : ℝ)*base91 + (34283/10000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2253161363720643256713/316250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1252699683/100000000000000 : ℝ)*(base19) + (689961199/50000000000000 : ℝ)*(base23) + (601211/400000000000 : ℝ)*(upper3) + (6887961/12500000000000 : ℝ)*(lower4) + (3780049/2500000000000 : ℝ)*(upper5) + (2249441372430749/50000000000000 : ℝ)*(major0) + (2249441372430749/50000000000000 : ℝ)*(major1) + (2249441372430749/50000000000000 : ℝ)*(major2) + (25862808877/100000000000000 : ℝ)*(sp1) + (28197588843/100000000000000 : ℝ)*(sp2) + (766119933661027/12500000000000 : ℝ)*(sp4) + (766116544222457/12500000000000 : ℝ)*(sp5) + (245157195671079/4000000000000 : ℝ)*(sp6) + (179300361434213/6250000000000 : ℝ)*(sp7) + (179300361434213/6250000000000 : ℝ)*(f.failure) + (766119933661027/12500000000000 : ℝ)*(f.sum) + (247704909401/1265000000000000000000000000 : ℝ)*base66 + (387732874957341753/63250000000000000000000000000000 : ℝ)*base68 + (651119406036658247/63250000000000000000000000000000 : ℝ)*base69 + (157110519338408247/63250000000000000000000000000000 : ℝ)*base71 + (3009716292123/632500000000000000000000000 : ℝ)*base74 + (442313788971341753/63250000000000000000000000000000 : ℝ)*base76 + (195158493967908247/63250000000000000000000000000000 : ℝ)*base77 + (764682603711841753/63250000000000000000000000000000 : ℝ)*base80 + (3638854424399/1265000000000000000000000000 : ℝ)*base81 + (16721/2500000000000000000 : ℝ)*base90 + (16721/2500000000000000000 : ℝ)*base92 + (16721/2500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1395_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1395_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1395_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1395_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1395_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1395_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1395_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

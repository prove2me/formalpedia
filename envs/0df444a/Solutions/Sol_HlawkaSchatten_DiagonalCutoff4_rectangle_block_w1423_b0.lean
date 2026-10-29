-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:10.299642+00:00
-- url     : https://prove2.me/submissions/08d61881-e25b-4fbe-bde1-51b7b1be6e00

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
theorem support_rectangle_w1423_s0_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881107863/5000000000 : ℝ)*x 0 + (2981330471/5000000000 : ℝ)*x 1 + (965972757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881107863/5000000000 : ℝ)^4383 ≤ (10380498126961/100000000000000 : ℝ)^3359 := by
    have hnat : (881107863 : ℕ)^4383*100000000000000^3359 ≤ 10380498126961^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881107863 5000000000 10380498126961 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981330471/5000000000 : ℝ)^4383 ≤ (25465513979817/50000000000000 : ℝ)^3359 := by
    have hnat : (2981330471 : ℕ)^4383*50000000000000^3359 ≤ 25465513979817^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981330471 5000000000 25465513979817 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965972757/2000000000 : ℝ)^4383 ≤ (7737694779353/20000000000000 : ℝ)^3359 := by
    have hnat : (965972757 : ℕ)^4383*20000000000000^3359 ≤ 7737694779353^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965972757 2000000000 7737694779353 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881107863/5000000000 : ℝ), (2981330471/5000000000 : ℝ), (965972757/2000000000 : ℝ)] ![(10380498126961/100000000000000 : ℝ), (25465513979817/50000000000000 : ℝ), (7737694779353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881107863/5000000000 : ℝ)|^4383 ≤ (10380498126961/100000000000000 : ℝ)^3359
        have hw : |(-881107863/5000000000 : ℝ)|=(881107863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981330471/5000000000 : ℝ)|^4383 ≤ (25465513979817/50000000000000 : ℝ)^3359
        have hw : |(2981330471/5000000000 : ℝ)|=(2981330471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965972757/2000000000 : ℝ)|^4383 ≤ (7737694779353/20000000000000 : ℝ)^3359
        have hw : |(965972757/2000000000 : ℝ)|=(965972757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (137319169/250000000 : ℝ)*x 0 + (-300299439/1250000000 : ℝ)*x 1 + (1207466047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137319169/250000000 : ℝ)^4383 ≤ (45757870706879/100000000000000 : ℝ)^3359 := by
    have hnat : (137319169 : ℕ)^4383*100000000000000^3359 ≤ 45757870706879^3359*250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137319169 250000000 45757870706879 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300299439/1250000000 : ℝ)^4383 ≤ (7776825579561/50000000000000 : ℝ)^3359 := by
    have hnat : (300299439 : ℕ)^4383*50000000000000^3359 ≤ 7776825579561^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300299439 1250000000 7776825579561 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207466047/2500000000 : ℝ)^4383 ≤ (19344239054503/50000000000000 : ℝ)^3359 := by
    have hnat : (1207466047 : ℕ)^4383*50000000000000^3359 ≤ 19344239054503^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207466047 2500000000 19344239054503 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(137319169/250000000 : ℝ), (-300299439/1250000000 : ℝ), (1207466047/2500000000 : ℝ)] ![(45757870706879/100000000000000 : ℝ), (7776825579561/50000000000000 : ℝ), (19344239054503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(137319169/250000000 : ℝ)|^4383 ≤ (45757870706879/100000000000000 : ℝ)^3359
        have hw : |(137319169/250000000 : ℝ)|=(137319169/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300299439/1250000000 : ℝ)|^4383 ≤ (7776825579561/50000000000000 : ℝ)^3359
        have hw : |(-300299439/1250000000 : ℝ)|=(300299439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207466047/2500000000 : ℝ)|^4383 ≤ (19344239054503/50000000000000 : ℝ)^3359
        have hw : |(1207466047/2500000000 : ℝ)|=(1207466047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5492767139/10000000000 : ℝ)*x 0 + (4829864021/10000000000 : ℝ)*x 1 + (-75074851/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492767139/10000000000 : ℝ)^4383 ≤ (2859867176667/6250000000000 : ℝ)^3359 := by
    have hnat : (5492767139 : ℕ)^4383*6250000000000^3359 ≤ 2859867176667^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492767139 10000000000 2859867176667 6250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4829864021/10000000000 : ℝ)^4383 ≤ (38688476363487/100000000000000 : ℝ)^3359 := by
    have hnat : (4829864021 : ℕ)^4383*100000000000000^3359 ≤ 38688476363487^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829864021 10000000000 38688476363487 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75074851/312500000 : ℝ)^4383 ≤ (15553648793707/100000000000000 : ℝ)^3359 := by
    have hnat : (75074851 : ℕ)^4383*100000000000000^3359 ≤ 15553648793707^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75074851 312500000 15553648793707 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492767139/10000000000 : ℝ), (4829864021/10000000000 : ℝ), (-75074851/312500000 : ℝ)] ![(2859867176667/6250000000000 : ℝ), (38688476363487/100000000000000 : ℝ), (15553648793707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492767139/10000000000 : ℝ)|^4383 ≤ (2859867176667/6250000000000 : ℝ)^3359
        have hw : |(5492767139/10000000000 : ℝ)|=(5492767139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4829864021/10000000000 : ℝ)|^4383 ≤ (38688476363487/100000000000000 : ℝ)^3359
        have hw : |(4829864021/10000000000 : ℝ)|=(4829864021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75074851/312500000 : ℝ)|^4383 ≤ (15553648793707/100000000000000 : ℝ)^3359
        have hw : |(-75074851/312500000 : ℝ)|=(75074851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166862507/10000000000 : ℝ)*x 0 + (387938713/1250000000 : ℝ)*x 1 + (5548743101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166862507/10000000000 : ℝ)^4383 ≤ (7977136122437/25000000000000 : ℝ)^3359 := by
    have hnat : (4166862507 : ℕ)^4383*25000000000000^3359 ≤ 7977136122437^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166862507 10000000000 7977136122437 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387938713/1250000000 : ℝ)^4383 ≤ (21724169803111/100000000000000 : ℝ)^3359 := by
    have hnat : (387938713 : ℕ)^4383*100000000000000^3359 ≤ 21724169803111^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387938713 1250000000 21724169803111 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5548743101/10000000000 : ℝ)^4383 ≤ (46367285697083/100000000000000 : ℝ)^3359 := by
    have hnat : (5548743101 : ℕ)^4383*100000000000000^3359 ≤ 46367285697083^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548743101 10000000000 46367285697083 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166862507/10000000000 : ℝ), (387938713/1250000000 : ℝ), (5548743101/10000000000 : ℝ)] ![(7977136122437/25000000000000 : ℝ), (21724169803111/100000000000000 : ℝ), (46367285697083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166862507/10000000000 : ℝ)|^4383 ≤ (7977136122437/25000000000000 : ℝ)^3359
        have hw : |(4166862507/10000000000 : ℝ)|=(4166862507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387938713/1250000000 : ℝ)|^4383 ≤ (21724169803111/100000000000000 : ℝ)^3359
        have hw : |(387938713/1250000000 : ℝ)|=(387938713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5548743101/10000000000 : ℝ)|^4383 ≤ (46367285697083/100000000000000 : ℝ)^3359
        have hw : |(5548743101/10000000000 : ℝ)|=(5548743101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220782749/1250000000 : ℝ)*x 0 + (971772143/2000000000 : ℝ)*x 1 + (2966314323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220782749/1250000000 : ℝ)^4383 ≤ (2082322010771/20000000000000 : ℝ)^3359 := by
    have hnat : (220782749 : ℕ)^4383*20000000000000^3359 ≤ 2082322010771^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220782749 1250000000 2082322010771 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971772143/2000000000 : ℝ)^4383 ≤ (38991832908739/100000000000000 : ℝ)^3359 := by
    have hnat : (971772143 : ℕ)^4383*100000000000000^3359 ≤ 38991832908739^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971772143 2000000000 38991832908739 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2966314323/5000000000 : ℝ)^4383 ≤ (10119311403933/20000000000000 : ℝ)^3359 := by
    have hnat : (2966314323 : ℕ)^4383*20000000000000^3359 ≤ 10119311403933^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966314323 5000000000 10119311403933 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220782749/1250000000 : ℝ), (971772143/2000000000 : ℝ), (2966314323/5000000000 : ℝ)] ![(2082322010771/20000000000000 : ℝ), (38991832908739/100000000000000 : ℝ), (10119311403933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220782749/1250000000 : ℝ)|^4383 ≤ (2082322010771/20000000000000 : ℝ)^3359
        have hw : |(-220782749/1250000000 : ℝ)|=(220782749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(971772143/2000000000 : ℝ)|^4383 ≤ (38991832908739/100000000000000 : ℝ)^3359
        have hw : |(971772143/2000000000 : ℝ)|=(971772143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2966314323/5000000000 : ℝ)|^4383 ≤ (10119311403933/20000000000000 : ℝ)^3359
        have hw : |(2966314323/5000000000 : ℝ)|=(2966314323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295902287/2500000000 : ℝ)*x 0 + (-1299630463/10000000000 : ℝ)*x 1 + (2966314363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295902287/2500000000 : ℝ)^4383 ≤ (42426493220927/100000000000000 : ℝ)^3359 := by
    have hnat : (1295902287 : ℕ)^4383*100000000000000^3359 ≤ 42426493220927^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295902287 2500000000 42426493220927 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299630463/10000000000 : ℝ)^4383 ≤ (6976948847601/100000000000000 : ℝ)^3359 := by
    have hnat : (1299630463 : ℕ)^4383*100000000000000^3359 ≤ 6976948847601^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299630463 10000000000 6976948847601 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2966314363/5000000000 : ℝ)^4383 ≤ (25298278954971/50000000000000 : ℝ)^3359 := by
    have hnat : (2966314363 : ℕ)^4383*50000000000000^3359 ≤ 25298278954971^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966314363 5000000000 25298278954971 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295902287/2500000000 : ℝ), (-1299630463/10000000000 : ℝ), (2966314363/5000000000 : ℝ)] ![(42426493220927/100000000000000 : ℝ), (6976948847601/100000000000000 : ℝ), (25298278954971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295902287/2500000000 : ℝ)|^4383 ≤ (42426493220927/100000000000000 : ℝ)^3359
        have hw : |(1295902287/2500000000 : ℝ)|=(1295902287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1299630463/10000000000 : ℝ)|^4383 ≤ (6976948847601/100000000000000 : ℝ)^3359
        have hw : |(-1299630463/10000000000 : ℝ)|=(1299630463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2966314363/5000000000 : ℝ)|^4383 ≤ (25298278954971/50000000000000 : ℝ)^3359
        have hw : |(2966314363/5000000000 : ℝ)|=(2966314363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183609167/10000000000 : ℝ)*x 0 + (5932628557/10000000000 : ℝ)*x 1 + (-259926141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183609167/10000000000 : ℝ)^4383 ≤ (10606623355961/25000000000000 : ℝ)^3359 := by
    have hnat : (5183609167 : ℕ)^4383*25000000000000^3359 ≤ 10606623355961^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183609167 10000000000 10606623355961 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5932628557/10000000000 : ℝ)^4383 ≤ (3162284751827/6250000000000 : ℝ)^3359 := by
    have hnat : (5932628557 : ℕ)^4383*6250000000000^3359 ≤ 3162284751827^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5932628557 10000000000 3162284751827 6250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259926141/2000000000 : ℝ)^4383 ≤ (6976950542807/100000000000000 : ℝ)^3359 := by
    have hnat : (259926141 : ℕ)^4383*100000000000000^3359 ≤ 6976950542807^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259926141 2000000000 6976950542807 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183609167/10000000000 : ℝ), (5932628557/10000000000 : ℝ), (-259926141/2000000000 : ℝ)] ![(10606623355961/25000000000000 : ℝ), (3162284751827/6250000000000 : ℝ), (6976950542807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183609167/10000000000 : ℝ)|^4383 ≤ (10606623355961/25000000000000 : ℝ)^3359
        have hw : |(5183609167/10000000000 : ℝ)|=(5183609167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5932628557/10000000000 : ℝ)|^4383 ≤ (3162284751827/6250000000000 : ℝ)^3359
        have hw : |(5932628557/10000000000 : ℝ)|=(5932628557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259926141/2000000000 : ℝ)|^4383 ≤ (6976950542807/100000000000000 : ℝ)^3359
        have hw : |(-259926141/2000000000 : ℝ)|=(259926141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s0_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4175598691/10000000000 : ℝ)*x 0 + (21944603/40000000 : ℝ)*x 1 + (3168337199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175598691/10000000000 : ℝ)^4383 ≤ (7998966425853/25000000000000 : ℝ)^3359 := by
    have hnat : (4175598691 : ℕ)^4383*25000000000000^3359 ≤ 7998966425853^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175598691 10000000000 7998966425853 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21944603/40000000 : ℝ)^4383 ≤ (4568596679739/10000000000000 : ℝ)^3359 := by
    have hnat : (21944603 : ℕ)^4383*10000000000000^3359 ≤ 4568596679739^3359*40000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21944603 40000000 4568596679739 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168337199/10000000000 : ℝ)^4383 ≤ (11159083742213/50000000000000 : ℝ)^3359 := by
    have hnat : (3168337199 : ℕ)^4383*50000000000000^3359 ≤ 11159083742213^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168337199 10000000000 11159083742213 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175598691/10000000000 : ℝ), (21944603/40000000 : ℝ), (3168337199/10000000000 : ℝ)] ![(7998966425853/25000000000000 : ℝ), (4568596679739/10000000000000 : ℝ), (11159083742213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175598691/10000000000 : ℝ)|^4383 ≤ (7998966425853/25000000000000 : ℝ)^3359
        have hw : |(4175598691/10000000000 : ℝ)|=(4175598691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21944603/40000000 : ℝ)|^4383 ≤ (4568596679739/10000000000000 : ℝ)^3359
        have hw : |(21944603/40000000 : ℝ)|=(21944603/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168337199/10000000000 : ℝ)|^4383 ≤ (11159083742213/50000000000000 : ℝ)^3359
        have hw : |(3168337199/10000000000 : ℝ)|=(3168337199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (401/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26299/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2191/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2191 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2191*1^512 ≤ 0^512*1^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2191/512 : ℝ) ≤ (1981967663100880993/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2191 ≤ (1981967663100880993/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2191*100000000000000000000^512 ≤ 1981967663100880993^512*5^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1981967663100880993 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1981967663100880993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2191 := by
      have hnat : (1 : ℕ)^512*1^2191 ≤ 1^2191*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (101981967663100880993/100000000000000000000 : ℝ) ≤ (5022983795866221/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (101981967663100880993/100000000000000000000 : ℝ)^512 ≤ (5022983795866221/5000000000000000 : ℝ)^2191 := by
      have hnat : (101981967663100880993 : ℕ)^512*5000000000000000^2191 ≤ 5022983795866221^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101981967663100880993 100000000000000000000 5022983795866221 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022983795866221/5000000000000000 : ℝ)) (X := (101981967663100880993/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (51981967663100880993/50000000000000000000 : ℝ) ≤ (2522983795866221/2500000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (51981967663100880993/50000000000000000000 : ℝ)^512 ≤ (2522983795866221/2500000000000000 : ℝ)^2191 := by
      have hnat : (51981967663100880993 : ℕ)^512*2500000000000000^2191 ≤ 2522983795866221^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51981967663100880993 50000000000000000000 2522983795866221 2500000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522983795866221/2500000000000000 : ℝ)) (X := (51981967663100880993/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22983795866221/2000000000000000 : ℝ)*(0 : ℝ))^(2191/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(22983795866221/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1981967663100880993/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22983795866221/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (1 : ℝ)+(22983795866221/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5022983795866221/5000000000000000 : ℝ) by norm_num, show 1+(1981967663100880993/100000000000000000000 : ℝ)+(0 : ℝ)=(101981967663100880993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1981967663100880993/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22983795866221/2000000000000000 : ℝ)*(2/5 : ℝ))^(2191/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(22983795866221/2000000000000000 : ℝ)*(2/5 : ℝ)=(2522983795866221/2500000000000000 : ℝ) by norm_num, show 1+2*(1981967663100880993/100000000000000000000 : ℝ)=(51981967663100880993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22983795866221/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22983795866221/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22983795866221/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22983795866221/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22983795866221/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22983795866221/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-881107863/5000000000 : ℝ)*X 0 0+(2981330471/5000000000 : ℝ)*X 0 1+(965972757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((137319169/250000000 : ℝ)*X 1 0+(-300299439/1250000000 : ℝ)*X 1 1+(1207466047/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5492767139/10000000000 : ℝ)*X 2 0+(4829864021/10000000000 : ℝ)*X 2 1+(-75074851/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166862507/10000000000 : ℝ)*X 0 0+(387938713/1250000000 : ℝ)*X 0 1+(5548743101/10000000000 : ℝ)*X 0 2+(4166862507/10000000000 : ℝ)*X 1 0+(387938713/1250000000 : ℝ)*X 1 1+(5548743101/10000000000 : ℝ)*X 1 2+(4166862507/10000000000 : ℝ)*X 2 0+(387938713/1250000000 : ℝ)*X 2 1+(5548743101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220782749/1250000000 : ℝ)*X 0 0+(971772143/2000000000 : ℝ)*X 0 1+(2966314323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1295902287/2500000000 : ℝ)*X 1 0+(-1299630463/10000000000 : ℝ)*X 1 1+(2966314363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183609167/10000000000 : ℝ)*X 2 0+(5932628557/10000000000 : ℝ)*X 2 1+(-259926141/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4175598691/10000000000 : ℝ)*X 0 0+(21944603/40000000 : ℝ)*X 0 1+(3168337199/10000000000 : ℝ)*X 0 2+(4175598691/10000000000 : ℝ)*X 1 0+(21944603/40000000 : ℝ)*X 1 1+(3168337199/10000000000 : ℝ)*X 1 2+(4175598691/10000000000 : ℝ)*X 2 0+(21944603/40000000 : ℝ)*X 2 1+(3168337199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6150590856614765949/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1478170997/100000000000000 : ℝ)*(base19) + (1507592233/100000000000000 : ℝ)*(base23) + (163543307/100000000000000 : ℝ)*(upper3) + (8648477/50000000000000 : ℝ)*(upper4) + (91533/40000000000 : ℝ)*(upper5) + (322936370109153/50000000000000 : ℝ)*(major0) + (322936370109153/50000000000000 : ℝ)*(major1) + (322936370109153/50000000000000 : ℝ)*(major2) + (441387736976513/50000000000000 : ℝ)*(sp0) + (110347470690939/12500000000000 : ℝ)*(sp1) + (220694934026569/25000000000000 : ℝ)*(sp2) + (408961475896973/100000000000000 : ℝ)*(sp3) + (5769745483/100000000000000 : ℝ)*(sp4) + (1277910713/50000000000000 : ℝ)*(sp7) + (408964031718399/100000000000000 : ℝ)*(f.failure) + (220695310924627/25000000000000 : ℝ)*(f.sum) + (128610827629187/50000000000000000000000000000 : ℝ)*base66 + (63972677279187/100000000000000000000000000000 : ℝ)*base68 + (929525108120813/100000000000000000000000000000 : ℝ)*base69 + (194666624079187/100000000000000000000000000000 : ℝ)*base72 + (23590511779187/50000000000000000000000000000 : ℝ)*base74 + (580118025320813/100000000000000000000000000000 : ℝ)*base75 + (520797051520813/100000000000000000000000000000 : ℝ)*base77 + (164588826820813/100000000000000000000000000000 : ℝ)*base79 + (215133804870813/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8977923/1250000000000000000000 : ℝ)*base90 + (8977923/1250000000000000000000 : ℝ)*base92 + (8977923/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40834814147762604046473/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360735253/100000000000000 : ℝ)*(base19) + (18138089/5000000000000 : ℝ)*(base23) + (47293991/50000000000000 : ℝ)*(base32) + (198003/312500000000 : ℝ)*(upper3) + (4964483/50000000000000 : ℝ)*(upper5) + (681370261347871/100000000000000 : ℝ)*(major0) + (681370261347871/100000000000000 : ℝ)*(major1) + (681370261347871/100000000000000 : ℝ)*(major2) + (41175543/5000000000000 : ℝ)*(sp1) + (6251979/781250000000 : ℝ)*(sp2) + (29103110886123/3125000000000 : ℝ)*(sp4) + (931298364109823/100000000000000 : ℝ)*(sp5) + (931298385340843/100000000000000 : ℝ)*(sp6) + (2157204126527/500000000000 : ℝ)*(sp7) + (215720459946691/50000000000000 : ℝ)*(f.failure) + (29103110886123/3125000000000 : ℝ)*(f.sum) + (87179229634509/100000000000000000000000000000 : ℝ)*base66 + (771395388834509/200000000000000000000000000000 : ℝ)*base68 + (1574757992034509/200000000000000000000000000000 : ℝ)*base70 + (800435701634509/200000000000000000000000000000 : ℝ)*base72 + (199439703934509/100000000000000000000000000000 : ℝ)*base74 + (849540896434509/200000000000000000000000000000 : ℝ)*base76 + (92094749365491/200000000000000000000000000000 : ℝ)*base77 + (347067238565491/200000000000000000000000000000 : ℝ)*base79 + (556212730934509/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6723993/625000000000000000000 : ℝ)*base89 + (6723993/625000000000000000000 : ℝ)*base91 + (6723993/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_s1_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935427163/10000000000 : ℝ)*x 0 + (5607629953/10000000000 : ℝ)*x 1 + (5073862461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935427163/10000000000 : ℝ)^4383 ≤ (1173137371721/10000000000000 : ℝ)^3359 := by
    have hnat : (1935427163 : ℕ)^4383*10000000000000^3359 ≤ 1173137371721^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935427163 10000000000 1173137371721 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607629953/10000000000 : ℝ)^4383 ≤ (940208264841/2000000000000 : ℝ)^3359 := by
    have hnat : (5607629953 : ℕ)^4383*2000000000000^3359 ≤ 940208264841^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607629953 10000000000 940208264841 2000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073862461/10000000000 : ℝ)^4383 ≤ (1289319157097/3125000000000 : ℝ)^3359 := by
    have hnat : (5073862461 : ℕ)^4383*3125000000000^3359 ≤ 1289319157097^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073862461 10000000000 1289319157097 3125000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935427163/10000000000 : ℝ), (5607629953/10000000000 : ℝ), (5073862461/10000000000 : ℝ)] ![(1173137371721/10000000000000 : ℝ), (940208264841/2000000000000 : ℝ), (1289319157097/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935427163/10000000000 : ℝ)|^4383 ≤ (1173137371721/10000000000000 : ℝ)^3359
        have hw : |(-1935427163/10000000000 : ℝ)|=(1935427163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607629953/10000000000 : ℝ)|^4383 ≤ (940208264841/2000000000000 : ℝ)^3359
        have hw : |(5607629953/10000000000 : ℝ)|=(5607629953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073862461/10000000000 : ℝ)|^4383 ≤ (1289319157097/3125000000000 : ℝ)^3359
        have hw : |(5073862461/10000000000 : ℝ)|=(5073862461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397409921/10000000000 : ℝ)*x 0 + (-554598253/2500000000 : ℝ)*x 1 + (5073863593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397409921/10000000000 : ℝ)^4383 ≤ (44724080189427/100000000000000 : ℝ)^3359 := by
    have hnat : (5397409921 : ℕ)^4383*100000000000000^3359 ≤ 44724080189427^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397409921 10000000000 44724080189427 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554598253/2500000000 : ℝ)^4383 ≤ (14017694757351/100000000000000 : ℝ)^3359 := by
    have hnat : (554598253 : ℕ)^4383*100000000000000^3359 ≤ 14017694757351^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554598253 2500000000 14017694757351 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073863593/10000000000 : ℝ)^4383 ≤ (41258225038117/100000000000000 : ℝ)^3359 := by
    have hnat : (5073863593 : ℕ)^4383*100000000000000^3359 ≤ 41258225038117^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073863593 10000000000 41258225038117 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397409921/10000000000 : ℝ), (-554598253/2500000000 : ℝ), (5073863593/10000000000 : ℝ)] ![(44724080189427/100000000000000 : ℝ), (14017694757351/100000000000000 : ℝ), (41258225038117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397409921/10000000000 : ℝ)|^4383 ≤ (44724080189427/100000000000000 : ℝ)^3359
        have hw : |(5397409921/10000000000 : ℝ)|=(5397409921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554598253/2500000000 : ℝ)|^4383 ≤ (14017694757351/100000000000000 : ℝ)^3359
        have hw : |(-554598253/2500000000 : ℝ)|=(554598253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073863593/10000000000 : ℝ)|^4383 ≤ (41258225038117/100000000000000 : ℝ)^3359
        have hw : |(5073863593/10000000000 : ℝ)|=(5073863593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269870541/500000000 : ℝ)*x 0 + (507386259/1000000000 : ℝ)*x 1 + (-554598281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269870541/500000000 : ℝ)^4383 ≤ (44724089909671/100000000000000 : ℝ)^3359 := by
    have hnat : (269870541 : ℕ)^4383*100000000000000^3359 ≤ 44724089909671^3359*500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269870541 500000000 44724089909671 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507386259/1000000000 : ℝ)^4383 ≤ (825164287917/2000000000000 : ℝ)^3359 := by
    have hnat : (507386259 : ℕ)^4383*2000000000000^3359 ≤ 825164287917^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507386259 1000000000 825164287917 2000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554598281/2500000000 : ℝ)^4383 ≤ (1401769568081/10000000000000 : ℝ)^3359 := by
    have hnat : (554598281 : ℕ)^4383*10000000000000^3359 ≤ 1401769568081^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554598281 2500000000 1401769568081 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269870541/500000000 : ℝ), (507386259/1000000000 : ℝ), (-554598281/2500000000 : ℝ)] ![(44724089909671/100000000000000 : ℝ), (825164287917/2000000000000 : ℝ), (1401769568081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269870541/500000000 : ℝ)|^4383 ≤ (44724089909671/100000000000000 : ℝ)^3359
        have hw : |(269870541/500000000 : ℝ)|=(269870541/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507386259/1000000000 : ℝ)|^4383 ≤ (825164287917/2000000000000 : ℝ)^3359
        have hw : |(507386259/1000000000 : ℝ)|=(507386259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554598281/2500000000 : ℝ)|^4383 ≤ (1401769568081/10000000000000 : ℝ)^3359
        have hw : |(-554598281/2500000000 : ℝ)|=(554598281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213886523/500000000 : ℝ)*x 0 + (3736358431/10000000000 : ℝ)*x 1 + (4888535953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213886523/500000000 : ℝ)^4383 ≤ (33020820048779/100000000000000 : ℝ)^3359 := by
    have hnat : (213886523 : ℕ)^4383*100000000000000^3359 ≤ 33020820048779^3359*500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213886523 500000000 33020820048779 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736358431/10000000000 : ℝ)^4383 ≤ (13838159895059/50000000000000 : ℝ)^3359 := by
    have hnat : (3736358431 : ℕ)^4383*50000000000000^3359 ≤ 13838159895059^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736358431 10000000000 13838159895059 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4888535953/10000000000 : ℝ)^4383 ≤ (39302860144559/100000000000000 : ℝ)^3359 := by
    have hnat : (4888535953 : ℕ)^4383*100000000000000^3359 ≤ 39302860144559^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888535953 10000000000 39302860144559 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213886523/500000000 : ℝ), (3736358431/10000000000 : ℝ), (4888535953/10000000000 : ℝ)] ![(33020820048779/100000000000000 : ℝ), (13838159895059/50000000000000 : ℝ), (39302860144559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213886523/500000000 : ℝ)|^4383 ≤ (33020820048779/100000000000000 : ℝ)^3359
        have hw : |(213886523/500000000 : ℝ)|=(213886523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3736358431/10000000000 : ℝ)|^4383 ≤ (13838159895059/50000000000000 : ℝ)^3359
        have hw : |(3736358431/10000000000 : ℝ)|=(3736358431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4888535953/10000000000 : ℝ)|^4383 ≤ (39302860144559/100000000000000 : ℝ)^3359
        have hw : |(4888535953/10000000000 : ℝ)|=(4888535953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935833409/10000000000 : ℝ)*x 0 + (1270037723/2500000000 : ℝ)*x 1 + (5601234379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935833409/10000000000 : ℝ)^4383 ≤ (2933646726969/25000000000000 : ℝ)^3359 := by
    have hnat : (1935833409 : ℕ)^4383*25000000000000^3359 ≤ 2933646726969^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935833409 10000000000 2933646726969 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270037723/2500000000 : ℝ)^4383 ≤ (8264989723383/20000000000000 : ℝ)^3359 := by
    have hnat : (1270037723 : ℕ)^4383*20000000000000^3359 ≤ 8264989723383^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270037723 2500000000 8264989723383 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5601234379/10000000000 : ℝ)^4383 ≤ (46940464454513/100000000000000 : ℝ)^3359 := by
    have hnat : (5601234379 : ℕ)^4383*100000000000000^3359 ≤ 46940464454513^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601234379 10000000000 46940464454513 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935833409/10000000000 : ℝ), (1270037723/2500000000 : ℝ), (5601234379/10000000000 : ℝ)] ![(2933646726969/25000000000000 : ℝ), (8264989723383/20000000000000 : ℝ), (46940464454513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935833409/10000000000 : ℝ)|^4383 ≤ (2933646726969/25000000000000 : ℝ)^3359
        have hw : |(-1935833409/10000000000 : ℝ)|=(1935833409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270037723/2500000000 : ℝ)|^4383 ≤ (8264989723383/20000000000000 : ℝ)^3359
        have hw : |(1270037723/2500000000 : ℝ)|=(1270037723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5601234379/10000000000 : ℝ)|^4383 ≤ (46940464454513/100000000000000 : ℝ)^3359
        have hw : |(5601234379/10000000000 : ℝ)|=(5601234379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258013733/10000000000 : ℝ)*x 0 + (-338204341/2000000000 : ℝ)*x 1 + (560123439/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258013733/10000000000 : ℝ)^4383 ≤ (1728914322241/4000000000000 : ℝ)^3359 := by
    have hnat : (5258013733 : ℕ)^4383*4000000000000^3359 ≤ 1728914322241^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258013733 10000000000 1728914322241 4000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338204341/2000000000 : ℝ)^4383 ≤ (9836677351409/100000000000000 : ℝ)^3359 := by
    have hnat : (338204341 : ℕ)^4383*100000000000000^3359 ≤ 9836677351409^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338204341 2000000000 9836677351409 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560123439/1000000000 : ℝ)^4383 ≤ (46940464574799/100000000000000 : ℝ)^3359 := by
    have hnat : (560123439 : ℕ)^4383*100000000000000^3359 ≤ 46940464574799^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560123439 1000000000 46940464574799 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258013733/10000000000 : ℝ), (-338204341/2000000000 : ℝ), (560123439/1000000000 : ℝ)] ![(1728914322241/4000000000000 : ℝ), (9836677351409/100000000000000 : ℝ), (46940464574799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258013733/10000000000 : ℝ)|^4383 ≤ (1728914322241/4000000000000 : ℝ)^3359
        have hw : |(5258013733/10000000000 : ℝ)|=(5258013733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338204341/2000000000 : ℝ)|^4383 ≤ (9836677351409/100000000000000 : ℝ)^3359
        have hw : |(-338204341/2000000000 : ℝ)|=(338204341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560123439/1000000000 : ℝ)|^4383 ≤ (46940464574799/100000000000000 : ℝ)^3359
        have hw : |(560123439/1000000000 : ℝ)|=(560123439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629006849/5000000000 : ℝ)*x 0 + (2800617177/5000000000 : ℝ)*x 1 + (-845510903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629006849/5000000000 : ℝ)^4383 ≤ (21611428840301/50000000000000 : ℝ)^3359 := by
    have hnat : (2629006849 : ℕ)^4383*50000000000000^3359 ≤ 21611428840301^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629006849 5000000000 21611428840301 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800617177/5000000000 : ℝ)^4383 ≤ (23470232090567/50000000000000 : ℝ)^3359 := by
    have hnat : (2800617177 : ℕ)^4383*50000000000000^3359 ≤ 23470232090567^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800617177 5000000000 23470232090567 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845510903/5000000000 : ℝ)^4383 ≤ (614792382377/6250000000000 : ℝ)^3359 := by
    have hnat : (845510903 : ℕ)^4383*6250000000000^3359 ≤ 614792382377^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845510903 5000000000 614792382377 6250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629006849/5000000000 : ℝ), (2800617177/5000000000 : ℝ), (-845510903/5000000000 : ℝ)] ![(21611428840301/50000000000000 : ℝ), (23470232090567/50000000000000 : ℝ), (614792382377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629006849/5000000000 : ℝ)|^4383 ≤ (21611428840301/50000000000000 : ℝ)^3359
        have hw : |(2629006849/5000000000 : ℝ)|=(2629006849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800617177/5000000000 : ℝ)|^4383 ≤ (23470232090567/50000000000000 : ℝ)^3359
        have hw : |(2800617177/5000000000 : ℝ)|=(2800617177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-845510903/5000000000 : ℝ)|^4383 ≤ (614792382377/6250000000000 : ℝ)^3359
        have hw : |(-845510903/5000000000 : ℝ)|=(845510903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s1_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278607653/10000000000 : ℝ)*x 0 + (1218740707/2500000000 : ℝ)*x 1 + (937540597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278607653/10000000000 : ℝ)^4383 ≤ (6605931164707/20000000000000 : ℝ)^3359 := by
    have hnat : (4278607653 : ℕ)^4383*20000000000000^3359 ≤ 6605931164707^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278607653 10000000000 6605931164707 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1218740707/2500000000 : ℝ)^4383 ≤ (3916052809583/10000000000000 : ℝ)^3359 := by
    have hnat : (1218740707 : ℕ)^4383*10000000000000^3359 ≤ 3916052809583^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218740707 2500000000 3916052809583 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937540597/2500000000 : ℝ)^4383 ≤ (13904908034939/50000000000000 : ℝ)^3359 := by
    have hnat : (937540597 : ℕ)^4383*50000000000000^3359 ≤ 13904908034939^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937540597 2500000000 13904908034939 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278607653/10000000000 : ℝ), (1218740707/2500000000 : ℝ), (937540597/2500000000 : ℝ)] ![(6605931164707/20000000000000 : ℝ), (3916052809583/10000000000000 : ℝ), (13904908034939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278607653/10000000000 : ℝ)|^4383 ≤ (6605931164707/20000000000000 : ℝ)^3359
        have hw : |(4278607653/10000000000 : ℝ)|=(4278607653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1218740707/2500000000 : ℝ)|^4383 ≤ (3916052809583/10000000000000 : ℝ)^3359
        have hw : |(1218740707/2500000000 : ℝ)|=(1218740707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937540597/2500000000 : ℝ)|^4383 ≤ (13904908034939/50000000000000 : ℝ)^3359
        have hw : |(937540597/2500000000 : ℝ)|=(937540597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (3801/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9443/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (401/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (401/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (401/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (401/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (401/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (401/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (401/20000 : ℝ) ^ (2191/512 : ℝ) ≤ (5423046885659/100000000000000000000 : ℝ) := by
    have hpowers : (401/20000 : ℝ)^2191 ≤ (5423046885659/100000000000000000000 : ℝ)^512 := by
      have hnat : (401 : ℕ)^2191*100000000000000000000^512 ≤ 5423046885659^512*20000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401 20000 5423046885659 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (401/20000 : ℝ)) (X := (5423046885659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26299/100000 : ℝ) ^ (2191/512 : ℝ) ≤ (329418345300617599/100000000000000000000 : ℝ) := by
    have hpowers : (26299/100000 : ℝ)^2191 ≤ (329418345300617599/100000000000000000000 : ℝ)^512 := by
      have hnat : (26299 : ℕ)^2191*100000000000000000000^512 ≤ 329418345300617599^512*100000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26299 100000 329418345300617599 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26299/100000 : ℝ)) (X := (329418345300617599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005423046885659/50000000000000000000 : ℝ) ≤ (5000000126727517/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50000005423046885659/50000000000000000000 : ℝ)^512 ≤ (5000000126727517/5000000000000000 : ℝ)^2191 := by
      have hnat : (50000005423046885659 : ℕ)^512*5000000000000000^2191 ≤ 5000000126727517^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005423046885659 50000000000000000000 5000000126727517 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000126727517/5000000000000000 : ℝ)) (X := (50000005423046885659/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50164711884173751629/50000000000000000000 : ℝ) ≤ (500384419192051/500000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50164711884173751629/50000000000000000000 : ℝ)^512 ≤ (500384419192051/500000000000000 : ℝ)^2191 := by
      have hnat : (50164711884173751629 : ℕ)^512*500000000000000^2191 ≤ 500384419192051^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50164711884173751629 50000000000000000000 500384419192051 500000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500384419192051/500000000000000 : ℝ)) (X := (50164711884173751629/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50329418345300617599/50000000000000000000 : ℝ) ≤ (5007688257113503/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50329418345300617599/50000000000000000000 : ℝ)^512 ≤ (5007688257113503/5000000000000000 : ℝ)^2191 := by
      have hnat : (50329418345300617599 : ℕ)^512*5000000000000000^2191 ≤ 5007688257113503^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50329418345300617599 50000000000000000000 5007688257113503 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007688257113503/5000000000000000 : ℝ)) (X := (50329418345300617599/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5423046885659/100000000000000000000 : ℝ) ≤ ((10121215698107866339/10122500000000000000 : ℝ)+2*(1281355064331/404900000000000 : ℝ)*(401/20000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (10121215698107866339/10122500000000000000 : ℝ)+2*(1281355064331/404900000000000 : ℝ)*(401/20000 : ℝ)=(5000000126727517/5000000000000000 : ℝ) by norm_num, show 1+2*(5423046885659/100000000000000000000 : ℝ)=(50000005423046885659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(329418345300617599/100000000000000000000 : ℝ)+(5423046885659/100000000000000000000 : ℝ) ≤ ((10121215698107866339/10122500000000000000 : ℝ)+(1281355064331/404900000000000 : ℝ)*((26299/100000 : ℝ)+(401/20000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (10121215698107866339/10122500000000000000 : ℝ)+(1281355064331/404900000000000 : ℝ)*((26299/100000 : ℝ)+(401/20000 : ℝ))=(500384419192051/500000000000000 : ℝ) by norm_num, show 1+(329418345300617599/100000000000000000000 : ℝ)+(5423046885659/100000000000000000000 : ℝ)=(50164711884173751629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(329418345300617599/100000000000000000000 : ℝ) ≤ ((10121215698107866339/10122500000000000000 : ℝ)+2*(1281355064331/404900000000000 : ℝ)*(26299/100000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (10121215698107866339/10122500000000000000 : ℝ)+2*(1281355064331/404900000000000 : ℝ)*(26299/100000 : ℝ)=(5007688257113503/5000000000000000 : ℝ) by norm_num, show 1+2*(329418345300617599/100000000000000000000 : ℝ)=(50329418345300617599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10121215698107866339/10122500000000000000 : ℝ)*(X 1 0+X 2 0)+(1281355064331/404900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (401/20000 : ℝ)) (hi := (26299/100000 : ℝ)) (c := (10121215698107866339/10122500000000000000 : ℝ)) (alpha := (1281355064331/404900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10121215698107866339/10122500000000000000 : ℝ)*(X 0 1+X 2 1)+(1281355064331/404900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (401/20000 : ℝ)) (hi := (26299/100000 : ℝ)) (c := (10121215698107866339/10122500000000000000 : ℝ)) (alpha := (1281355064331/404900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10121215698107866339/10122500000000000000 : ℝ)*(X 0 2+X 1 2)+(1281355064331/404900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (401/20000 : ℝ)) (hi := (26299/100000 : ℝ)) (c := (10121215698107866339/10122500000000000000 : ℝ)) (alpha := (1281355064331/404900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1935427163/10000000000 : ℝ)*X 0 0+(5607629953/10000000000 : ℝ)*X 0 1+(5073862461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397409921/10000000000 : ℝ)*X 1 0+(-554598253/2500000000 : ℝ)*X 1 1+(5073863593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((269870541/500000000 : ℝ)*X 2 0+(507386259/1000000000 : ℝ)*X 2 1+(-554598281/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213886523/500000000 : ℝ)*X 0 0+(3736358431/10000000000 : ℝ)*X 0 1+(4888535953/10000000000 : ℝ)*X 0 2+(213886523/500000000 : ℝ)*X 1 0+(3736358431/10000000000 : ℝ)*X 1 1+(4888535953/10000000000 : ℝ)*X 1 2+(213886523/500000000 : ℝ)*X 2 0+(3736358431/10000000000 : ℝ)*X 2 1+(4888535953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1935833409/10000000000 : ℝ)*X 0 0+(1270037723/2500000000 : ℝ)*X 0 1+(5601234379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258013733/10000000000 : ℝ)*X 1 0+(-338204341/2000000000 : ℝ)*X 1 1+(560123439/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629006849/5000000000 : ℝ)*X 2 0+(2800617177/5000000000 : ℝ)*X 2 1+(-845510903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278607653/10000000000 : ℝ)*X 0 0+(1218740707/2500000000 : ℝ)*X 0 1+(937540597/2500000000 : ℝ)*X 0 2+(4278607653/10000000000 : ℝ)*X 1 0+(1218740707/2500000000 : ℝ)*X 1 1+(937540597/2500000000 : ℝ)*X 1 2+(4278607653/10000000000 : ℝ)*X 2 0+(1218740707/2500000000 : ℝ)*X 2 1+(937540597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (452811710441461214271722097/63265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23387487/100000000000000 : ℝ)*(base1) + (300144181/25000000000000 : ℝ)*(base19) + (378157241/25000000000000 : ℝ)*(base23) + (66459789/50000000000000 : ℝ)*(upper3) + (9499089/6250000000000 : ℝ)*(upper5) + (342678759320991/25000000000000 : ℝ)*(major0) + (342678759320991/25000000000000 : ℝ)*(major1) + (342678759320991/25000000000000 : ℝ)*(major2) + (936743049195091/50000000000000 : ℝ)*(sp0) + (936748682468167/50000000000000 : ℝ)*(sp1) + (936748526442047/50000000000000 : ℝ)*(sp2) + (17358526870561/2000000000000 : ℝ)*(sp3) + (12490510363/100000000000000 : ℝ)*(sp4) + (1225890579/25000000000000 : ℝ)*(sp7) + (216982817619463/25000000000000 : ℝ)*(f.failure) + (936749282756529/50000000000000 : ℝ)*(f.sum) + (70896393784591/20245000000000000000000000000 : ℝ)*base66 + (1917106209496953051/253062500000000000000000000000000 : ℝ)*base68 + (90948448780984449/253062500000000000000000000000000 : ℝ)*base69 + (2276070942720578051/253062500000000000000000000000000 : ℝ)*base72 + (29735108251733/10122500000000000000000000000 : ℝ)*base74 + (1521910113754453051/253062500000000000000000000000000 : ℝ)*base76 + (883348424585203051/253062500000000000000000000000000 : ℝ)*base78 + (3020111562914578051/253062500000000000000000000000000 : ℝ)*base80 + (3965262044703/10122500000000000000000000000 : ℝ)*base82 + (1223051/312500000000000000000 : ℝ)*base90 + (1223051/312500000000000000000 : ℝ)*base92 + (1223051/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1129293242110286352287556549/253062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3416783/10000000000000 : ℝ)*(base1) + (959514981/100000000000000 : ℝ)*(base19) + (940283919/100000000000000 : ℝ)*(base23) + (110354077/100000000000000 : ℝ)*(upper3) + (23412353/25000000000000 : ℝ)*(upper5) + (702031202048599/50000000000000 : ℝ)*(major0) + (702031202048599/50000000000000 : ℝ)*(major1) + (702031202048599/50000000000000 : ℝ)*(major2) + (2793924679/50000000000000 : ℝ)*(sp1) + (5344266777/100000000000000 : ℝ)*(sp2) + (959539002029327/50000000000000 : ℝ)*(sp4) + (959535711263243/50000000000000 : ℝ)*(sp5) + (1919071685340129/100000000000000 : ℝ)*(sp6) + (444523327692747/50000000000000 : ℝ)*(sp7) + (222261672388331/25000000000000 : ℝ)*(f.failure) + (239884746236353/12500000000000 : ℝ)*(f.sum) + (30432397264491/10122500000000000000000000000 : ℝ)*base66 + (1228157796219065939/506125000000000000000000000000000 : ℝ)*base68 + (1249176731189315939/506125000000000000000000000000000 : ℝ)*base70 + (4398505633314315939/506125000000000000000000000000000 : ℝ)*base72 + (5878007192679/2530625000000000000000000000 : ℝ)*base74 + (1490300232368315939/506125000000000000000000000000000 : ℝ)*base76 + (4575903066323565939/506125000000000000000000000000000 : ℝ)*base78 + (616427146678065939/506125000000000000000000000000000 : ℝ)*base80 + (12030097491553/5061250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2285713/312500000000000000000 : ℝ)*base89 + (2285713/312500000000000000000 : ℝ)*base91 + (2285713/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3801/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9443/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_s2_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969005379/10000000000 : ℝ)*x 0 + (2729761227/5000000000 : ℝ)*x 1 + (5200363509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969005379/10000000000 : ℝ)^4383 ≤ (1199765063449/10000000000000 : ℝ)^3359 := by
    have hnat : (1969005379 : ℕ)^4383*10000000000000^3359 ≤ 1199765063449^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969005379 10000000000 1199765063449 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729761227/5000000000 : ℝ)^4383 ≤ (113492083703/250000000000 : ℝ)^3359 := by
    have hnat : (2729761227 : ℕ)^4383*250000000000^3359 ≤ 113492083703^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729761227 5000000000 113492083703 250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200363509/10000000000 : ℝ)^4383 ≤ (42605515868397/100000000000000 : ℝ)^3359 := by
    have hnat : (5200363509 : ℕ)^4383*100000000000000^3359 ≤ 42605515868397^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200363509 10000000000 42605515868397 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969005379/10000000000 : ℝ), (2729761227/5000000000 : ℝ), (5200363509/10000000000 : ℝ)] ![(1199765063449/10000000000000 : ℝ), (113492083703/250000000000 : ℝ), (42605515868397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969005379/10000000000 : ℝ)|^4383 ≤ (1199765063449/10000000000000 : ℝ)^3359
        have hw : |(-1969005379/10000000000 : ℝ)|=(1969005379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729761227/5000000000 : ℝ)|^4383 ≤ (113492083703/250000000000 : ℝ)^3359
        have hw : |(2729761227/5000000000 : ℝ)|=(2729761227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200363509/10000000000 : ℝ)|^4383 ≤ (42605515868397/100000000000000 : ℝ)^3359
        have hw : |(5200363509/10000000000 : ℝ)|=(5200363509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167516281/312500000 : ℝ)*x 0 + (-525594229/2500000000 : ℝ)*x 1 + (1300090857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167516281/312500000 : ℝ)^4383 ≤ (2770352671959/6250000000000 : ℝ)^3359 := by
    have hnat : (167516281 : ℕ)^4383*6250000000000^3359 ≤ 2770352671959^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167516281 312500000 2770352671959 6250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525594229/2500000000 : ℝ)^4383 ≤ (13068842228109/100000000000000 : ℝ)^3359 := by
    have hnat : (525594229 : ℕ)^4383*100000000000000^3359 ≤ 13068842228109^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525594229 2500000000 13068842228109 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300090857/2500000000 : ℝ)^4383 ≤ (1704220600099/4000000000000 : ℝ)^3359 := by
    have hnat : (1300090857 : ℕ)^4383*4000000000000^3359 ≤ 1704220600099^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300090857 2500000000 1704220600099 4000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167516281/312500000 : ℝ), (-525594229/2500000000 : ℝ), (1300090857/2500000000 : ℝ)] ![(2770352671959/6250000000000 : ℝ), (13068842228109/100000000000000 : ℝ), (1704220600099/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167516281/312500000 : ℝ)|^4383 ≤ (2770352671959/6250000000000 : ℝ)^3359
        have hw : |(167516281/312500000 : ℝ)|=(167516281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525594229/2500000000 : ℝ)|^4383 ≤ (13068842228109/100000000000000 : ℝ)^3359
        have hw : |(-525594229/2500000000 : ℝ)|=(525594229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300090857/2500000000 : ℝ)|^4383 ≤ (1704220600099/4000000000000 : ℝ)^3359
        have hw : |(1300090857/2500000000 : ℝ)|=(1300090857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680260321/5000000000 : ℝ)*x 0 + (325022739/625000000 : ℝ)*x 1 + (-2102376859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680260321/5000000000 : ℝ)^4383 ≤ (11081409743737/25000000000000 : ℝ)^3359 := by
    have hnat : (2680260321 : ℕ)^4383*25000000000000^3359 ≤ 11081409743737^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680260321 5000000000 11081409743737 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325022739/625000000 : ℝ)^4383 ≤ (4260551923587/10000000000000 : ℝ)^3359 := by
    have hnat : (325022739 : ℕ)^4383*10000000000000^3359 ≤ 4260551923587^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325022739 625000000 4260551923587 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102376859/10000000000 : ℝ)^4383 ≤ (1633605220721/12500000000000 : ℝ)^3359 := by
    have hnat : (2102376859 : ℕ)^4383*12500000000000^3359 ≤ 1633605220721^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102376859 10000000000 1633605220721 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680260321/5000000000 : ℝ), (325022739/625000000 : ℝ), (-2102376859/10000000000 : ℝ)] ![(11081409743737/25000000000000 : ℝ), (4260551923587/10000000000000 : ℝ), (1633605220721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680260321/5000000000 : ℝ)|^4383 ≤ (11081409743737/25000000000000 : ℝ)^3359
        have hw : |(2680260321/5000000000 : ℝ)|=(2680260321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325022739/625000000 : ℝ)|^4383 ≤ (4260551923587/10000000000000 : ℝ)^3359
        have hw : |(325022739/625000000 : ℝ)|=(325022739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102376859/10000000000 : ℝ)|^4383 ≤ (1633605220721/12500000000000 : ℝ)^3359
        have hw : |(-2102376859/10000000000 : ℝ)|=(2102376859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075355019/2500000000 : ℝ)*x 0 + (4029897107/10000000000 : ℝ)*x 1 + (2294656143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075355019/2500000000 : ℝ)^4383 ≤ (1039363566029/3125000000000 : ℝ)^3359 := by
    have hnat : (1075355019 : ℕ)^4383*3125000000000^3359 ≤ 1039363566029^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075355019 2500000000 1039363566029 3125000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029897107/10000000000 : ℝ)^4383 ≤ (30546874508697/100000000000000 : ℝ)^3359 := by
    have hnat : (4029897107 : ℕ)^4383*100000000000000^3359 ≤ 30546874508697^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029897107 10000000000 30546874508697 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294656143/5000000000 : ℝ)^4383 ≤ (18096745681139/50000000000000 : ℝ)^3359 := by
    have hnat : (2294656143 : ℕ)^4383*50000000000000^3359 ≤ 18096745681139^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294656143 5000000000 18096745681139 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075355019/2500000000 : ℝ), (4029897107/10000000000 : ℝ), (2294656143/5000000000 : ℝ)] ![(1039363566029/3125000000000 : ℝ), (30546874508697/100000000000000 : ℝ), (18096745681139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075355019/2500000000 : ℝ)|^4383 ≤ (1039363566029/3125000000000 : ℝ)^3359
        have hw : |(1075355019/2500000000 : ℝ)|=(1075355019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029897107/10000000000 : ℝ)|^4383 ≤ (30546874508697/100000000000000 : ℝ)^3359
        have hw : |(4029897107/10000000000 : ℝ)|=(4029897107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2294656143/5000000000 : ℝ)|^4383 ≤ (18096745681139/50000000000000 : ℝ)^3359
        have hw : |(2294656143/5000000000 : ℝ)|=(2294656143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393810427/2000000000 : ℝ)*x 0 + (2600927487/5000000000 : ℝ)*x 1 + (5458018549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393810427/2000000000 : ℝ)^4383 ≤ (5999011191697/50000000000000 : ℝ)^3359 := by
    have hnat : (393810427 : ℕ)^4383*50000000000000^3359 ≤ 5999011191697^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393810427 2000000000 5999011191697 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600927487/5000000000 : ℝ)^4383 ≤ (21310730454747/50000000000000 : ℝ)^3359 := by
    have hnat : (2600927487 : ℕ)^4383*50000000000000^3359 ≤ 21310730454747^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600927487 5000000000 21310730454747 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458018549/10000000000 : ℝ)^4383 ≤ (45380516698199/100000000000000 : ℝ)^3359 := by
    have hnat : (5458018549 : ℕ)^4383*100000000000000^3359 ≤ 45380516698199^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458018549 10000000000 45380516698199 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393810427/2000000000 : ℝ), (2600927487/5000000000 : ℝ), (5458018549/10000000000 : ℝ)] ![(5999011191697/50000000000000 : ℝ), (21310730454747/50000000000000 : ℝ), (45380516698199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393810427/2000000000 : ℝ)|^4383 ≤ (5999011191697/50000000000000 : ℝ)^3359
        have hw : |(-393810427/2000000000 : ℝ)|=(393810427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600927487/5000000000 : ℝ)|^4383 ≤ (21310730454747/50000000000000 : ℝ)^3359
        have hw : |(2600927487/5000000000 : ℝ)|=(2600927487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458018549/10000000000 : ℝ)|^4383 ≤ (45380516698199/100000000000000 : ℝ)^3359
        have hw : |(5458018549/10000000000 : ℝ)|=(5458018549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293169343/10000000000 : ℝ)*x 0 + (-922360811/5000000000 : ℝ)*x 1 + (545801887/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293169343/10000000000 : ℝ)^4383 ≤ (21800167124697/50000000000000 : ℝ)^3359 := by
    have hnat : (5293169343 : ℕ)^4383*50000000000000^3359 ≤ 21800167124697^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293169343 10000000000 21800167124697 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922360811/5000000000 : ℝ)^4383 ≤ (5509572781253/50000000000000 : ℝ)^3359 := by
    have hnat : (922360811 : ℕ)^4383*50000000000000^3359 ≤ 5509572781253^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922360811 5000000000 5509572781253 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545801887/1000000000 : ℝ)^4383 ≤ (22690260090389/50000000000000 : ℝ)^3359 := by
    have hnat : (545801887 : ℕ)^4383*50000000000000^3359 ≤ 22690260090389^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545801887 1000000000 22690260090389 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293169343/10000000000 : ℝ), (-922360811/5000000000 : ℝ), (545801887/1000000000 : ℝ)] ![(21800167124697/50000000000000 : ℝ), (5509572781253/50000000000000 : ℝ), (22690260090389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293169343/10000000000 : ℝ)|^4383 ≤ (21800167124697/50000000000000 : ℝ)^3359
        have hw : |(5293169343/10000000000 : ℝ)|=(5293169343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922360811/5000000000 : ℝ)|^4383 ≤ (5509572781253/50000000000000 : ℝ)^3359
        have hw : |(-922360811/5000000000 : ℝ)|=(922360811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545801887/1000000000 : ℝ)|^4383 ≤ (22690260090389/50000000000000 : ℝ)^3359
        have hw : |(545801887/1000000000 : ℝ)|=(545801887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323292323/2500000000 : ℝ)*x 0 + (5458018849/10000000000 : ℝ)*x 1 + (-46118043/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323292323/2500000000 : ℝ)^4383 ≤ (10900083425309/25000000000000 : ℝ)^3359 := by
    have hnat : (1323292323 : ℕ)^4383*25000000000000^3359 ≤ 10900083425309^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323292323 2500000000 10900083425309 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458018849/10000000000 : ℝ)^4383 ≤ (22690259976473/50000000000000 : ℝ)^3359 := by
    have hnat : (5458018849 : ℕ)^4383*50000000000000^3359 ≤ 22690259976473^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458018849 10000000000 22690259976473 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46118043/250000000 : ℝ)^4383 ≤ (220382926527/2000000000000 : ℝ)^3359 := by
    have hnat : (46118043 : ℕ)^4383*2000000000000^3359 ≤ 220382926527^3359*250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46118043 250000000 220382926527 2000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323292323/2500000000 : ℝ), (5458018849/10000000000 : ℝ), (-46118043/250000000 : ℝ)] ![(10900083425309/25000000000000 : ℝ), (22690259976473/50000000000000 : ℝ), (220382926527/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323292323/2500000000 : ℝ)|^4383 ≤ (10900083425309/25000000000000 : ℝ)^3359
        have hw : |(1323292323/2500000000 : ℝ)|=(1323292323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458018849/10000000000 : ℝ)|^4383 ≤ (22690259976473/50000000000000 : ℝ)^3359
        have hw : |(5458018849/10000000000 : ℝ)|=(5458018849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46118043/250000000 : ℝ)|^4383 ≤ (220382926527/2000000000000 : ℝ)^3359
        have hw : |(-46118043/250000000 : ℝ)|=(46118043/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s2_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075380187/2500000000 : ℝ)*x 0 + (229304651/500000000 : ℝ)*x 1 + (4033143057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075380187/2500000000 : ℝ)^4383 ≤ (33260649840689/100000000000000 : ℝ)^3359 := by
    have hnat : (1075380187 : ℕ)^4383*100000000000000^3359 ≤ 33260649840689^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075380187 2500000000 33260649840689 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229304651/500000000 : ℝ)^4383 ≤ (36160366448863/100000000000000 : ℝ)^3359 := by
    have hnat : (229304651 : ℕ)^4383*100000000000000^3359 ≤ 36160366448863^3359*500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229304651 500000000 36160366448863 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033143057/10000000000 : ℝ)^4383 ≤ (7644745926017/25000000000000 : ℝ)^3359 := by
    have hnat : (4033143057 : ℕ)^4383*25000000000000^3359 ≤ 7644745926017^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033143057 10000000000 7644745926017 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075380187/2500000000 : ℝ), (229304651/500000000 : ℝ), (4033143057/10000000000 : ℝ)] ![(33260649840689/100000000000000 : ℝ), (36160366448863/100000000000000 : ℝ), (7644745926017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075380187/2500000000 : ℝ)|^4383 ≤ (33260649840689/100000000000000 : ℝ)^3359
        have hw : |(1075380187/2500000000 : ℝ)|=(1075380187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229304651/500000000 : ℝ)|^4383 ≤ (36160366448863/100000000000000 : ℝ)^3359
        have hw : |(229304651/500000000 : ℝ)|=(229304651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033143057/10000000000 : ℝ)|^4383 ≤ (7644745926017/25000000000000 : ℝ)^3359
        have hw : |(4033143057/10000000000 : ℝ)|=(4033143057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9443/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3801/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2067/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7909/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9443/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3801/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9443/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3801/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9443/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3801/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9443/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3801/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9443/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3801/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9443/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3801/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3801/50000 : ℝ) ^ (2191/512 : ℝ) ≤ (813070333545883/50000000000000000000 : ℝ) := by
    have hpowers : (3801/50000 : ℝ)^2191 ≤ (813070333545883/50000000000000000000 : ℝ)^512 := by
      have hnat : (3801 : ℕ)^2191*50000000000000000000^512 ≤ 813070333545883^512*50000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3801 50000 813070333545883 50000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3801/50000 : ℝ)) (X := (813070333545883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9443/50000 : ℝ) ^ (2191/512 : ℝ) ≤ (79870812312202097/100000000000000000000 : ℝ) := by
    have hpowers : (9443/50000 : ℝ)^2191 ≤ (79870812312202097/100000000000000000000 : ℝ)^512 := by
      have hnat : (9443 : ℕ)^2191*100000000000000000000^512 ≤ 79870812312202097^512*50000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9443 50000 79870812312202097 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9443/50000 : ℝ)) (X := (79870812312202097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000813070333545883/25000000000000000000 : ℝ) ≤ (5000037999710023/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (25000813070333545883/25000000000000000000 : ℝ)^512 ≤ (5000037999710023/5000000000000000 : ℝ)^2191 := by
      have hnat : (25000813070333545883 : ℕ)^512*5000000000000000^2191 ≤ 5000037999710023^2191*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000813070333545883 25000000000000000000 5000037999710023 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037999710023/5000000000000000 : ℝ)) (X := (25000813070333545883/25000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081496952979293863/100000000000000000000 : ℝ) ≤ (10001903852878849/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (100081496952979293863/100000000000000000000 : ℝ)^512 ≤ (10001903852878849/10000000000000000 : ℝ)^2191 := by
      have hnat : (100081496952979293863 : ℕ)^512*10000000000000000^2191 ≤ 10001903852878849^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081496952979293863 100000000000000000000 10001903852878849 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001903852878849/10000000000000000 : ℝ)) (X := (100081496952979293863/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50079870812312202097/50000000000000000000 : ℝ) ≤ (2500932926584413/2500000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50079870812312202097/50000000000000000000 : ℝ)^512 ≤ (2500932926584413/2500000000000000 : ℝ)^2191 := by
      have hnat : (50079870812312202097 : ℕ)^512*2500000000000000^2191 ≤ 2500932926584413^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50079870812312202097 50000000000000000000 2500932926584413 2500000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500932926584413/2500000000000000 : ℝ)) (X := (50079870812312202097/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(813070333545883/50000000000000000000 : ℝ) ≤ ((4029038103338148509/4030000000000000000 : ℝ)+2*(1827853458803/1128400000000000 : ℝ)*(3801/50000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (4029038103338148509/4030000000000000000 : ℝ)+2*(1827853458803/1128400000000000 : ℝ)*(3801/50000 : ℝ)=(5000037999710023/5000000000000000 : ℝ) by norm_num, show 1+2*(813070333545883/50000000000000000000 : ℝ)=(25000813070333545883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79870812312202097/100000000000000000000 : ℝ)+(813070333545883/50000000000000000000 : ℝ) ≤ ((4029038103338148509/4030000000000000000 : ℝ)+(1827853458803/1128400000000000 : ℝ)*((9443/50000 : ℝ)+(3801/50000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (4029038103338148509/4030000000000000000 : ℝ)+(1827853458803/1128400000000000 : ℝ)*((9443/50000 : ℝ)+(3801/50000 : ℝ))=(10001903852878849/10000000000000000 : ℝ) by norm_num, show 1+(79870812312202097/100000000000000000000 : ℝ)+(813070333545883/50000000000000000000 : ℝ)=(100081496952979293863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79870812312202097/100000000000000000000 : ℝ) ≤ ((4029038103338148509/4030000000000000000 : ℝ)+2*(1827853458803/1128400000000000 : ℝ)*(9443/50000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (4029038103338148509/4030000000000000000 : ℝ)+2*(1827853458803/1128400000000000 : ℝ)*(9443/50000 : ℝ)=(2500932926584413/2500000000000000 : ℝ) by norm_num, show 1+2*(79870812312202097/100000000000000000000 : ℝ)=(50079870812312202097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4029038103338148509/4030000000000000000 : ℝ)*(X 1 0+X 2 0)+(1827853458803/1128400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (3801/50000 : ℝ)) (hi := (9443/50000 : ℝ)) (c := (4029038103338148509/4030000000000000000 : ℝ)) (alpha := (1827853458803/1128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4029038103338148509/4030000000000000000 : ℝ)*(X 0 1+X 2 1)+(1827853458803/1128400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (3801/50000 : ℝ)) (hi := (9443/50000 : ℝ)) (c := (4029038103338148509/4030000000000000000 : ℝ)) (alpha := (1827853458803/1128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4029038103338148509/4030000000000000000 : ℝ)*(X 0 2+X 1 2)+(1827853458803/1128400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (3801/50000 : ℝ)) (hi := (9443/50000 : ℝ)) (c := (4029038103338148509/4030000000000000000 : ℝ)) (alpha := (1827853458803/1128400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1969005379/10000000000 : ℝ)*X 0 0+(2729761227/5000000000 : ℝ)*X 0 1+(5200363509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167516281/312500000 : ℝ)*X 1 0+(-525594229/2500000000 : ℝ)*X 1 1+(1300090857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680260321/5000000000 : ℝ)*X 2 0+(325022739/625000000 : ℝ)*X 2 1+(-2102376859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075355019/2500000000 : ℝ)*X 0 0+(4029897107/10000000000 : ℝ)*X 0 1+(2294656143/5000000000 : ℝ)*X 0 2+(1075355019/2500000000 : ℝ)*X 1 0+(4029897107/10000000000 : ℝ)*X 1 1+(2294656143/5000000000 : ℝ)*X 1 2+(1075355019/2500000000 : ℝ)*X 2 0+(4029897107/10000000000 : ℝ)*X 2 1+(2294656143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-393810427/2000000000 : ℝ)*X 0 0+(2600927487/5000000000 : ℝ)*X 0 1+(5458018549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293169343/10000000000 : ℝ)*X 1 0+(-922360811/5000000000 : ℝ)*X 1 1+(545801887/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323292323/2500000000 : ℝ)*X 2 0+(5458018849/10000000000 : ℝ)*X 2 1+(-46118043/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075380187/2500000000 : ℝ)*X 0 0+(229304651/500000000 : ℝ)*X 0 1+(4033143057/10000000000 : ℝ)*X 0 2+(1075380187/2500000000 : ℝ)*X 1 0+(229304651/500000000 : ℝ)*X 1 1+(4033143057/10000000000 : ℝ)*X 1 2+(1075380187/2500000000 : ℝ)*X 2 0+(229304651/500000000 : ℝ)*X 2 1+(4033143057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112779551782049175382851/11284000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1503527433/100000000000000 : ℝ)*(base19) + (992406529/100000000000000 : ℝ)*(base23) + (17366749/12500000000000 : ℝ)*(lower2) + (73821611/25000000000000 : ℝ)*(upper3) + (44444739/50000000000000 : ℝ)*(upper5) + (564626832689807/20000000000000 : ℝ)*(major0) + (564626832689807/20000000000000 : ℝ)*(major1) + (564626832689807/20000000000000 : ℝ)*(major2) + (1929327708341621/50000000000000 : ℝ)*(sp0) + (1929334623744979/50000000000000 : ℝ)*(sp1) + (1929334879305431/50000000000000 : ℝ)*(sp2) + (178758803633847/10000000000000 : ℝ)*(sp3) + (306686683/2000000000000 : ℝ)*(sp4) + (4603193717/50000000000000 : ℝ)*(sp7) + (357519448545181/20000000000000 : ℝ)*(f.failure) + (241166921938587/6250000000000 : ℝ)*(f.sum) + (36639849593/2256800000000000000000000000 : ℝ)*base65 + (3379538129118240659/564200000000000000000000000000000 : ℝ)*base68 + (181941789460159341/564200000000000000000000000000000 : ℝ)*base69 + (1001890861668240659/564200000000000000000000000000000 : ℝ)*base72 + (47583084945493/11284000000000000000000000000 : ℝ)*base73 + (403282247416959341/564200000000000000000000000000000 : ℝ)*base75 + (904969803033840659/564200000000000000000000000000000 : ℝ)*base78 + (1033533662737759341/564200000000000000000000000000000 : ℝ)*base79 + (57830782042221/11284000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1678263/250000000000000000000 : ℝ)*base89 + (1678263/250000000000000000000 : ℝ)*base91 + (1678263/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78976378970831304285018057/10850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11725887/1562500000000 : ℝ)*(base19) + (878035703/100000000000000 : ℝ)*(base23) + (19046849/10000000000000 : ℝ)*(upper3) + (1897783/2500000000000 : ℝ)*(lower4) + (117800179/100000000000000 : ℝ)*(upper5) + (285611748684377/10000000000000 : ℝ)*(major0) + (285611748684377/10000000000000 : ℝ)*(major1) + (285611748684377/10000000000000 : ℝ)*(major2) + (1337532471/12500000000000 : ℝ)*(sp1) + (12411854879/100000000000000 : ℝ)*(sp2) + (780750516017883/20000000000000 : ℝ)*(sp4) + (48796764117161/1250000000000 : ℝ)*(sp5) + (1951869645099417/50000000000000 : ℝ)*(sp6) + (113030134435447/6250000000000 : ℝ)*(sp7) + (113030134435447/6250000000000 : ℝ)*(f.failure) + (780750516017883/20000000000000 : ℝ)*(f.sum) + (16466473721051/5642000000000000000000000000 : ℝ)*base66 + (1721152184652282251/282100000000000000000000000000000 : ℝ)*base67 + (2039348784109382251/282100000000000000000000000000000 : ℝ)*base69 + (187047772794082251/282100000000000000000000000000000 : ℝ)*base71 + (5495793846533/5642000000000000000000000000 : ℝ)*base74 + (1259440604704482251/282100000000000000000000000000000 : ℝ)*base75 + (852169005479082251/282100000000000000000000000000000 : ℝ)*base77 + (1259405501873082251/282100000000000000000000000000000 : ℝ)*base79 + (823418255753/1128400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (525519/78125000000000000000 : ℝ)*base90 + (525519/78125000000000000000 : ℝ)*base92 + (525519/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1423_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9443/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3801/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1423_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1423_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1423_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1423_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

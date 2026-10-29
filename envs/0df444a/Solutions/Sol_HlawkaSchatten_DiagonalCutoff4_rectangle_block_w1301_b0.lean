-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:40.775367+00:00
-- url     : https://prove2.me/submissions/3ff76b79-102d-4f65-a31a-b7860d15950c

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
theorem support_rectangle_w1301_s0_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91681723/500000000 : ℝ)*x 0 + (1503703401/2500000000 : ℝ)*x 1 + (1200258287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91681723/500000000 : ℝ)^4261 ≤ (10721793356109/100000000000000 : ℝ)^3237 := by
    have hnat : (91681723 : ℕ)^4261*100000000000000^3237 ≤ 10721793356109^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91681723 500000000 10721793356109 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503703401/2500000000 : ℝ)^4261 ≤ (25606534933857/50000000000000 : ℝ)^3237 := by
    have hnat : (1503703401 : ℕ)^4261*50000000000000^3237 ≤ 25606534933857^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503703401 2500000000 25606534933857 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200258287/2500000000 : ℝ)^4261 ≤ (9516284190023/25000000000000 : ℝ)^3237 := by
    have hnat : (1200258287 : ℕ)^4261*25000000000000^3237 ≤ 9516284190023^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200258287 2500000000 9516284190023 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91681723/500000000 : ℝ), (1503703401/2500000000 : ℝ), (1200258287/2500000000 : ℝ)] ![(10721793356109/100000000000000 : ℝ), (25606534933857/50000000000000 : ℝ), (9516284190023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91681723/500000000 : ℝ)|^4261 ≤ (10721793356109/100000000000000 : ℝ)^3237
        have hw : |(-91681723/500000000 : ℝ)|=(91681723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1503703401/2500000000 : ℝ)|^4261 ≤ (25606534933857/50000000000000 : ℝ)^3237
        have hw : |(1503703401/2500000000 : ℝ)|=(1503703401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200258287/2500000000 : ℝ)|^4261 ≤ (9516284190023/25000000000000 : ℝ)^3237
        have hw : |(1200258287/2500000000 : ℝ)|=(1200258287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5506408547/10000000000 : ℝ)*x 0 + (-12628123/50000000 : ℝ)*x 1 + (7681653/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506408547/10000000000 : ℝ)^4261 ≤ (22796289327773/50000000000000 : ℝ)^3237 := by
    have hnat : (5506408547 : ℕ)^4261*50000000000000^3237 ≤ 22796289327773^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506408547 10000000000 22796289327773 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12628123/50000000 : ℝ)^4261 ≤ (16342284807737/100000000000000 : ℝ)^3237 := by
    have hnat : (12628123 : ℕ)^4261*100000000000000^3237 ≤ 16342284807737^3237*50000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12628123 50000000 16342284807737 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7681653/16000000 : ℝ)^4261 ≤ (2379071032503/6250000000000 : ℝ)^3237 := by
    have hnat : (7681653 : ℕ)^4261*6250000000000^3237 ≤ 2379071032503^3237*16000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7681653 16000000 2379071032503 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506408547/10000000000 : ℝ), (-12628123/50000000 : ℝ), (7681653/16000000 : ℝ)] ![(22796289327773/50000000000000 : ℝ), (16342284807737/100000000000000 : ℝ), (2379071032503/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506408547/10000000000 : ℝ)|^4261 ≤ (22796289327773/50000000000000 : ℝ)^3237
        have hw : |(5506408547/10000000000 : ℝ)|=(5506408547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12628123/50000000 : ℝ)|^4261 ≤ (16342284807737/100000000000000 : ℝ)^3237
        have hw : |(-12628123/50000000 : ℝ)|=(12628123/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7681653/16000000 : ℝ)|^4261 ≤ (2379071032503/6250000000000 : ℝ)^3237
        have hw : |(7681653/16000000 : ℝ)|=(7681653/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753204257/5000000000 : ℝ)*x 0 + (4801033167/10000000000 : ℝ)*x 1 + (-2525624591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753204257/5000000000 : ℝ)^4261 ≤ (712384035873/1562500000000 : ℝ)^3237 := by
    have hnat : (2753204257 : ℕ)^4261*1562500000000^3237 ≤ 712384035873^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753204257 5000000000 712384035873 1562500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4801033167/10000000000 : ℝ)^4261 ≤ (9516284239597/25000000000000 : ℝ)^3237 := by
    have hnat : (4801033167 : ℕ)^4261*25000000000000^3237 ≤ 9516284239597^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801033167 10000000000 9516284239597 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525624591/10000000000 : ℝ)^4261 ≤ (16342284731079/100000000000000 : ℝ)^3237 := by
    have hnat : (2525624591 : ℕ)^4261*100000000000000^3237 ≤ 16342284731079^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525624591 10000000000 16342284731079 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753204257/5000000000 : ℝ), (4801033167/10000000000 : ℝ), (-2525624591/10000000000 : ℝ)] ![(712384035873/1562500000000 : ℝ), (9516284239597/25000000000000 : ℝ), (16342284731079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753204257/5000000000 : ℝ)|^4261 ≤ (712384035873/1562500000000 : ℝ)^3237
        have hw : |(2753204257/5000000000 : ℝ)|=(2753204257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4801033167/10000000000 : ℝ)|^4261 ≤ (9516284239597/25000000000000 : ℝ)^3237
        have hw : |(4801033167/10000000000 : ℝ)|=(4801033167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2525624591/10000000000 : ℝ)|^4261 ≤ (16342284731079/100000000000000 : ℝ)^3237
        have hw : |(-2525624591/10000000000 : ℝ)|=(2525624591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209247559/500000000 : ℝ)*x 0 + (1554429601/5000000000 : ℝ)*x 1 + (87688239/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209247559/500000000 : ℝ)^4261 ≤ (31769843008669/100000000000000 : ℝ)^3237 := by
    have hnat : (209247559 : ℕ)^4261*100000000000000^3237 ≤ 31769843008669^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209247559 500000000 31769843008669 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554429601/5000000000 : ℝ)^4261 ≤ (859308878773/4000000000000 : ℝ)^3237 := by
    have hnat : (1554429601 : ℕ)^4261*4000000000000^3237 ≤ 859308878773^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554429601 5000000000 859308878773 4000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87688239/156250000 : ℝ)^4261 ≤ (11686858751781/25000000000000 : ℝ)^3237 := by
    have hnat : (87688239 : ℕ)^4261*25000000000000^3237 ≤ 11686858751781^3237*156250000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87688239 156250000 11686858751781 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209247559/500000000 : ℝ), (1554429601/5000000000 : ℝ), (87688239/156250000 : ℝ)] ![(31769843008669/100000000000000 : ℝ), (859308878773/4000000000000 : ℝ), (11686858751781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209247559/500000000 : ℝ)|^4261 ≤ (31769843008669/100000000000000 : ℝ)^3237
        have hw : |(209247559/500000000 : ℝ)|=(209247559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554429601/5000000000 : ℝ)|^4261 ≤ (859308878773/4000000000000 : ℝ)^3237
        have hw : |(1554429601/5000000000 : ℝ)|=(1554429601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87688239/156250000 : ℝ)|^4261 ≤ (11686858751781/25000000000000 : ℝ)^3237
        have hw : |(87688239/156250000 : ℝ)|=(87688239/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73532333/400000000 : ℝ)*x 0 + (4832346823/10000000000 : ℝ)*x 1 + (1196477227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73532333/400000000 : ℝ)^4261 ≤ (10757782757907/100000000000000 : ℝ)^3237 := by
    have hnat : (73532333 : ℕ)^4261*100000000000000^3237 ≤ 10757782757907^3237*400000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73532333 400000000 10757782757907 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4832346823/10000000000 : ℝ)^4261 ≤ (1535691343233/4000000000000 : ℝ)^3237 := by
    have hnat : (4832346823 : ℕ)^4261*4000000000000^3237 ≤ 1535691343233^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832346823 10000000000 1535691343233 4000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196477227/2000000000 : ℝ)^4261 ≤ (50849933648277/100000000000000 : ℝ)^3237 := by
    have hnat : (1196477227 : ℕ)^4261*100000000000000^3237 ≤ 50849933648277^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196477227 2000000000 50849933648277 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73532333/400000000 : ℝ), (4832346823/10000000000 : ℝ), (1196477227/2000000000 : ℝ)] ![(10757782757907/100000000000000 : ℝ), (1535691343233/4000000000000 : ℝ), (50849933648277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73532333/400000000 : ℝ)|^4261 ≤ (10757782757907/100000000000000 : ℝ)^3237
        have hw : |(-73532333/400000000 : ℝ)|=(73532333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4832346823/10000000000 : ℝ)|^4261 ≤ (1535691343233/4000000000000 : ℝ)^3237
        have hw : |(4832346823/10000000000 : ℝ)|=(4832346823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196477227/2000000000 : ℝ)|^4261 ≤ (50849933648277/100000000000000 : ℝ)^3237
        have hw : |(1196477227/2000000000 : ℝ)|=(1196477227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646987287/1250000000 : ℝ)*x 0 + (-134426883/1000000000 : ℝ)*x 1 + (2991194401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646987287/1250000000 : ℝ)^4261 ≤ (8404992325389/20000000000000 : ℝ)^3237 := by
    have hnat : (646987287 : ℕ)^4261*20000000000000^3237 ≤ 8404992325389^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646987287 1250000000 8404992325389 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134426883/1000000000 : ℝ)^4261 ≤ (1781268719847/25000000000000 : ℝ)^3237 := by
    have hnat : (134426883 : ℕ)^4261*25000000000000^3237 ≤ 1781268719847^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134426883 1000000000 1781268719847 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991194401/5000000000 : ℝ)^4261 ≤ (397265339757/781250000000 : ℝ)^3237 := by
    have hnat : (2991194401 : ℕ)^4261*781250000000^3237 ≤ 397265339757^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991194401 5000000000 397265339757 781250000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646987287/1250000000 : ℝ), (-134426883/1000000000 : ℝ), (2991194401/5000000000 : ℝ)] ![(8404992325389/20000000000000 : ℝ), (1781268719847/25000000000000 : ℝ), (397265339757/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646987287/1250000000 : ℝ)|^4261 ≤ (8404992325389/20000000000000 : ℝ)^3237
        have hw : |(646987287/1250000000 : ℝ)|=(646987287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134426883/1000000000 : ℝ)|^4261 ≤ (1781268719847/25000000000000 : ℝ)^3237
        have hw : |(-134426883/1000000000 : ℝ)|=(134426883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991194401/5000000000 : ℝ)|^4261 ≤ (397265339757/781250000000 : ℝ)^3237
        have hw : |(2991194401/5000000000 : ℝ)|=(2991194401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5175899619/10000000000 : ℝ)*x 0 + (186949577/312500000 : ℝ)*x 1 + (-168033819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175899619/10000000000 : ℝ)^4261 ≤ (42024975766973/100000000000000 : ℝ)^3237 := by
    have hnat : (5175899619 : ℕ)^4261*100000000000000^3237 ≤ 42024975766973^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175899619 10000000000 42024975766973 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186949577/312500000 : ℝ)^4261 ≤ (50849937329403/100000000000000 : ℝ)^3237 := by
    have hnat : (186949577 : ℕ)^4261*100000000000000^3237 ≤ 50849937329403^3237*312500000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186949577 312500000 50849937329403 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168033819/1250000000 : ℝ)^4261 ≤ (7125086893879/100000000000000 : ℝ)^3237 := by
    have hnat : (168033819 : ℕ)^4261*100000000000000^3237 ≤ 7125086893879^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168033819 1250000000 7125086893879 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175899619/10000000000 : ℝ), (186949577/312500000 : ℝ), (-168033819/1250000000 : ℝ)] ![(42024975766973/100000000000000 : ℝ), (50849937329403/100000000000000 : ℝ), (7125086893879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175899619/10000000000 : ℝ)|^4261 ≤ (42024975766973/100000000000000 : ℝ)^3237
        have hw : |(5175899619/10000000000 : ℝ)|=(5175899619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186949577/312500000 : ℝ)|^4261 ≤ (50849937329403/100000000000000 : ℝ)^3237
        have hw : |(186949577/312500000 : ℝ)|=(186949577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168033819/1250000000 : ℝ)|^4261 ≤ (7125086893879/100000000000000 : ℝ)^3237
        have hw : |(-168033819/1250000000 : ℝ)|=(168033819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s0_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097298257/5000000000 : ℝ)*x 0 + (5547477023/10000000000 : ℝ)*x 1 + (3175726707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097298257/5000000000 : ℝ)^4261 ≤ (15933131710863/50000000000000 : ℝ)^3237 := by
    have hnat : (2097298257 : ℕ)^4261*50000000000000^3237 ≤ 15933131710863^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097298257 5000000000 15933131710863 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5547477023/10000000000 : ℝ)^4261 ≤ (46040719275351/100000000000000 : ℝ)^3237 := by
    have hnat : (5547477023 : ℕ)^4261*100000000000000^3237 ≤ 46040719275351^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547477023 10000000000 46040719275351 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3175726707/10000000000 : ℝ)^4261 ≤ (4418603458283/20000000000000 : ℝ)^3237 := by
    have hnat : (3175726707 : ℕ)^4261*20000000000000^3237 ≤ 4418603458283^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175726707 10000000000 4418603458283 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097298257/5000000000 : ℝ), (5547477023/10000000000 : ℝ), (3175726707/10000000000 : ℝ)] ![(15933131710863/50000000000000 : ℝ), (46040719275351/100000000000000 : ℝ), (4418603458283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097298257/5000000000 : ℝ)|^4261 ≤ (15933131710863/50000000000000 : ℝ)^3237
        have hw : |(2097298257/5000000000 : ℝ)|=(2097298257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5547477023/10000000000 : ℝ)|^4261 ≤ (46040719275351/100000000000000 : ℝ)^3237
        have hw : |(5547477023/10000000000 : ℝ)|=(5547477023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3175726707/10000000000 : ℝ)|^4261 ≤ (4418603458283/20000000000000 : ℝ)^3237
        have hw : |(3175726707/10000000000 : ℝ)|=(3175726707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (551/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27169/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1065/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1065 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1065*1^256 ≤ 0^256*1^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1065/256 : ℝ) ≤ (55264646253737527/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1065 ≤ (55264646253737527/2500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1065*2500000000000000000^256 ≤ 55264646253737527^256*5^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 55264646253737527 2500000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (55264646253737527/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1065 := by
      have hnat : (1 : ℕ)^256*1^1065 ≤ 1^1065*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (2555264646253737527/2500000000000000000 : ℝ) ≤ (10052696642049071/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (2555264646253737527/2500000000000000000 : ℝ)^256 ≤ (10052696642049071/10000000000000000 : ℝ)^1065 := by
      have hnat : (2555264646253737527 : ℕ)^256*10000000000000000^1065 ≤ 10052696642049071^1065*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2555264646253737527 2500000000000000000 10052696642049071 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052696642049071/10000000000000000 : ℝ)) (X := (2555264646253737527/2500000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1305264646253737527/1250000000000000000 : ℝ) ≤ (5052696642049071/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (1305264646253737527/1250000000000000000 : ℝ)^256 ≤ (5052696642049071/5000000000000000 : ℝ)^1065 := by
      have hnat : (1305264646253737527 : ℕ)^256*5000000000000000^1065 ≤ 5052696642049071^1065*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1305264646253737527 1250000000000000000 5052696642049071 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052696642049071/5000000000000000 : ℝ)) (X := (1305264646253737527/1250000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(52696642049071/4000000000000000 : ℝ)*(0 : ℝ))^(1065/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(52696642049071/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55264646253737527/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(52696642049071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (1 : ℝ)+(52696642049071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10052696642049071/10000000000000000 : ℝ) by norm_num, show 1+(55264646253737527/2500000000000000000 : ℝ)+(0 : ℝ)=(2555264646253737527/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55264646253737527/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(52696642049071/4000000000000000 : ℝ)*(2/5 : ℝ))^(1065/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(52696642049071/4000000000000000 : ℝ)*(2/5 : ℝ)=(5052696642049071/5000000000000000 : ℝ) by norm_num, show 1+2*(55264646253737527/2500000000000000000 : ℝ)=(1305264646253737527/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(52696642049071/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52696642049071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(52696642049071/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52696642049071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(52696642049071/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52696642049071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-91681723/500000000 : ℝ)*X 0 0+(1503703401/2500000000 : ℝ)*X 0 1+(1200258287/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5506408547/10000000000 : ℝ)*X 1 0+(-12628123/50000000 : ℝ)*X 1 1+(7681653/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2753204257/5000000000 : ℝ)*X 2 0+(4801033167/10000000000 : ℝ)*X 2 1+(-2525624591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209247559/500000000 : ℝ)*X 0 0+(1554429601/5000000000 : ℝ)*X 0 1+(87688239/156250000 : ℝ)*X 0 2+(209247559/500000000 : ℝ)*X 1 0+(1554429601/5000000000 : ℝ)*X 1 1+(87688239/156250000 : ℝ)*X 1 2+(209247559/500000000 : ℝ)*X 2 0+(1554429601/5000000000 : ℝ)*X 2 1+(87688239/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-73532333/400000000 : ℝ)*X 0 0+(4832346823/10000000000 : ℝ)*X 0 1+(1196477227/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646987287/1250000000 : ℝ)*X 1 0+(-134426883/1000000000 : ℝ)*X 1 1+(2991194401/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175899619/10000000000 : ℝ)*X 2 0+(186949577/312500000 : ℝ)*X 2 1+(-168033819/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097298257/5000000000 : ℝ)*X 0 0+(5547477023/10000000000 : ℝ)*X 0 1+(3175726707/10000000000 : ℝ)*X 0 2+(2097298257/5000000000 : ℝ)*X 1 0+(5547477023/10000000000 : ℝ)*X 1 1+(3175726707/10000000000 : ℝ)*X 1 2+(2097298257/5000000000 : ℝ)*X 2 0+(5547477023/10000000000 : ℝ)*X 2 1+(3175726707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201493822595412826836009/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (596971/1000000000000 : ℝ)*(base1) + (1220380379/100000000000000 : ℝ)*(base19) + (1215442861/100000000000000 : ℝ)*(base23) + (71217501/50000000000000 : ℝ)*(upper3) + (143081251/100000000000000 : ℝ)*(upper5) + (611687099900493/100000000000000 : ℝ)*(major0) + (611687099900493/100000000000000 : ℝ)*(major1) + (611687099900493/100000000000000 : ℝ)*(major2) + (411937962097799/50000000000000 : ℝ)*(sp0) + (41193927524757/5000000000000 : ℝ)*(sp1) + (411939277716329/50000000000000 : ℝ)*(sp2) + (1560516918641/390625000000 : ℝ)*(sp3) + (3906377021/100000000000000 : ℝ)*(sp4) + (1870144747/100000000000000 : ℝ)*(sp7) + (199747130506971/50000000000000 : ℝ)*(f.failure) + (823879770875519/100000000000000 : ℝ)*(f.sum) + (549831943507997/200000000000000000000000000000 : ℝ)*base66 + (1482574296107997/400000000000000000000000000000 : ℝ)*base68 + (2434195030507997/400000000000000000000000000000 : ℝ)*base70 + (1530215004107997/400000000000000000000000000000 : ℝ)*base72 + (986562591507997/200000000000000000000000000000 : ℝ)*base74 + (547874505092003/400000000000000000000000000000 : ℝ)*base75 + (1124970456907997/400000000000000000000000000000 : ℝ)*base78 + (129013660507997/400000000000000000000000000000 : ℝ)*base80 + (1223439810307997/200000000000000000000000000000 : ℝ)*base82 + (9891807/2500000000000000000000 : ℝ)*base90 + (9891807/2500000000000000000000 : ℝ)*base92 + (9891807/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20577829352883705581463/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3874193/781250000000 : ℝ)*(base1) + (150736669/25000000000000 : ℝ)*(base19) + (762914431/100000000000000 : ℝ)*(base23) + (15321991/25000000000000 : ℝ)*(upper3) + (16139585392749/2500000000000 : ℝ)*(major0) + (16139585392749/2500000000000 : ℝ)*(major1) + (16139585392749/2500000000000 : ℝ)*(major2) + (983555671/100000000000000 : ℝ)*(sp1) + (8044279/100000000000000 : ℝ)*(sp2) + (21669201/2500000000000 : ℝ)*(sp3) + (10869189584891/1250000000000 : ℝ)*(sp4) + (869533084392229/100000000000000 : ℝ)*(sp5) + (434766949967933/50000000000000 : ℝ)*(sp6) + (421630660675069/100000000000000 : ℝ)*(sp7) + (421632023339813/100000000000000 : ℝ)*(f.failure) + (54345916930911/6250000000000 : ℝ)*(f.sum) + (11358712256179/5000000000000000000000000000 : ℝ)*base65 + (22076805483821/10000000000000000000000000000 : ℝ)*base68 + (14201238643821/10000000000000000000000000000 : ℝ)*base70 + (22845080716179/10000000000000000000000000000 : ℝ)*base71 + (3974090601179/5000000000000000000000000000 : ℝ)*base73 + (40072425973821/10000000000000000000000000000 : ℝ)*base76 + (15224565673821/10000000000000000000000000000 : ℝ)*base78 + (7056965253821/10000000000000000000000000000 : ℝ)*base80 + (18034142076179/5000000000000000000000000000 : ℝ)*base81 + (4933279/5000000000000000000000 : ℝ)*base89 + (4933279/5000000000000000000000 : ℝ)*base91 + (4933279/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1301_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s1_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506094359/2500000000 : ℝ)*x 0 + (5661026931/10000000000 : ℝ)*x 1 + (314543699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506094359/2500000000 : ℝ)^4261 ≤ (6106778268383/50000000000000 : ℝ)^3237 := by
    have hnat : (506094359 : ℕ)^4261*50000000000000^3237 ≤ 6106778268383^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506094359 2500000000 6106778268383 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5661026931/10000000000 : ℝ)^4261 ≤ (23642616245721/50000000000000 : ℝ)^3237 := by
    have hnat : (5661026931 : ℕ)^4261*50000000000000^3237 ≤ 23642616245721^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661026931 10000000000 23642616245721 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314543699/625000000 : ℝ)^4261 ≤ (20250605476361/50000000000000 : ℝ)^3237 := by
    have hnat : (314543699 : ℕ)^4261*50000000000000^3237 ≤ 20250605476361^3237*625000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314543699 625000000 20250605476361 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506094359/2500000000 : ℝ), (5661026931/10000000000 : ℝ), (314543699/625000000 : ℝ)] ![(6106778268383/50000000000000 : ℝ), (23642616245721/50000000000000 : ℝ), (20250605476361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506094359/2500000000 : ℝ)|^4261 ≤ (6106778268383/50000000000000 : ℝ)^3237
        have hw : |(-506094359/2500000000 : ℝ)|=(506094359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5661026931/10000000000 : ℝ)|^4261 ≤ (23642616245721/50000000000000 : ℝ)^3237
        have hw : |(5661026931/10000000000 : ℝ)|=(5661026931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314543699/625000000 : ℝ)|^4261 ≤ (20250605476361/50000000000000 : ℝ)^3237
        have hw : |(314543699/625000000 : ℝ)|=(314543699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410029541/10000000000 : ℝ)*x 0 + (-2360876727/10000000000 : ℝ)*x 1 + (314543713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410029541/10000000000 : ℝ)^4261 ≤ (44545044588721/100000000000000 : ℝ)^3237 := by
    have hnat : (5410029541 : ℕ)^4261*100000000000000^3237 ≤ 44545044588721^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410029541 10000000000 44545044588721 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360876727/10000000000 : ℝ)^4261 ≤ (7476871030151/50000000000000 : ℝ)^3237 := by
    have hnat : (2360876727 : ℕ)^4261*50000000000000^3237 ≤ 7476871030151^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360876727 10000000000 7476871030151 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314543713/625000000 : ℝ)^4261 ≤ (20250606662823/50000000000000 : ℝ)^3237 := by
    have hnat : (314543713 : ℕ)^4261*50000000000000^3237 ≤ 20250606662823^3237*625000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314543713 625000000 20250606662823 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410029541/10000000000 : ℝ), (-2360876727/10000000000 : ℝ), (314543713/625000000 : ℝ)] ![(44545044588721/100000000000000 : ℝ), (7476871030151/50000000000000 : ℝ), (20250606662823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410029541/10000000000 : ℝ)|^4261 ≤ (44545044588721/100000000000000 : ℝ)^3237
        have hw : |(5410029541/10000000000 : ℝ)|=(5410029541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2360876727/10000000000 : ℝ)|^4261 ≤ (7476871030151/50000000000000 : ℝ)^3237
        have hw : |(-2360876727/10000000000 : ℝ)|=(2360876727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314543713/625000000 : ℝ)|^4261 ≤ (20250606662823/50000000000000 : ℝ)^3237
        have hw : |(314543713/625000000 : ℝ)|=(314543713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082005949/2000000000 : ℝ)*x 0 + (5032699051/10000000000 : ℝ)*x 1 + (-1180438459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082005949/2000000000 : ℝ)^4261 ≤ (11136261699943/25000000000000 : ℝ)^3237 := by
    have hnat : (1082005949 : ℕ)^4261*25000000000000^3237 ≤ 11136261699943^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082005949 2000000000 11136261699943 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032699051/10000000000 : ℝ)^4261 ≤ (20250604771899/50000000000000 : ℝ)^3237 := by
    have hnat : (5032699051 : ℕ)^4261*50000000000000^3237 ≤ 20250604771899^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032699051 10000000000 20250604771899 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180438459/5000000000 : ℝ)^4261 ≤ (9346089783/62500000000 : ℝ)^3237 := by
    have hnat : (1180438459 : ℕ)^4261*62500000000^3237 ≤ 9346089783^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180438459 5000000000 9346089783 62500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082005949/2000000000 : ℝ), (5032699051/10000000000 : ℝ), (-1180438459/5000000000 : ℝ)] ![(11136261699943/25000000000000 : ℝ), (20250604771899/50000000000000 : ℝ), (9346089783/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082005949/2000000000 : ℝ)|^4261 ≤ (11136261699943/25000000000000 : ℝ)^3237
        have hw : |(1082005949/2000000000 : ℝ)|=(1082005949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032699051/10000000000 : ℝ)|^4261 ≤ (20250604771899/50000000000000 : ℝ)^3237
        have hw : |(5032699051/10000000000 : ℝ)|=(5032699051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1180438459/5000000000 : ℝ)|^4261 ≤ (9346089783/62500000000 : ℝ)^3237
        have hw : |(-1180438459/5000000000 : ℝ)|=(1180438459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537445337/1250000000 : ℝ)*x 0 + (1848861433/5000000000 : ℝ)*x 1 + (4993527423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537445337/1250000000 : ℝ)^4261 ≤ (6584016040479/20000000000000 : ℝ)^3237 := by
    have hnat : (537445337 : ℕ)^4261*20000000000000^3237 ≤ 6584016040479^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537445337 1250000000 6584016040479 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848861433/5000000000 : ℝ)^4261 ≤ (5398631933141/20000000000000 : ℝ)^3237 := by
    have hnat : (1848861433 : ℕ)^4261*20000000000000^3237 ≤ 5398631933141^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848861433 5000000000 5398631933141 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4993527423/10000000000 : ℝ)^4261 ≤ (8017352023823/20000000000000 : ℝ)^3237 := by
    have hnat : (4993527423 : ℕ)^4261*20000000000000^3237 ≤ 8017352023823^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993527423 10000000000 8017352023823 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537445337/1250000000 : ℝ), (1848861433/5000000000 : ℝ), (4993527423/10000000000 : ℝ)] ![(6584016040479/20000000000000 : ℝ), (5398631933141/20000000000000 : ℝ), (8017352023823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537445337/1250000000 : ℝ)|^4261 ≤ (6584016040479/20000000000000 : ℝ)^3237
        have hw : |(537445337/1250000000 : ℝ)|=(537445337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1848861433/5000000000 : ℝ)|^4261 ≤ (5398631933141/20000000000000 : ℝ)^3237
        have hw : |(1848861433/5000000000 : ℝ)|=(1848861433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4993527423/10000000000 : ℝ)|^4261 ≤ (8017352023823/20000000000000 : ℝ)^3237
        have hw : |(4993527423/10000000000 : ℝ)|=(4993527423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101249759/500000000 : ℝ)*x 0 + (504083519/1000000000 : ℝ)*x 1 + (176648063/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101249759/500000000 : ℝ)^4261 ≤ (6109231389517/50000000000000 : ℝ)^3237 := by
    have hnat : (101249759 : ℕ)^4261*50000000000000^3237 ≤ 6109231389517^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101249759 500000000 6109231389517 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504083519/1000000000 : ℝ)^4261 ≤ (10146855262087/25000000000000 : ℝ)^3237 := by
    have hnat : (504083519 : ℕ)^4261*25000000000000^3237 ≤ 10146855262087^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504083519 1000000000 10146855262087 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176648063/312500000 : ℝ)^4261 ≤ (47194116164787/100000000000000 : ℝ)^3237 := by
    have hnat : (176648063 : ℕ)^4261*100000000000000^3237 ≤ 47194116164787^3237*312500000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176648063 312500000 47194116164787 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101249759/500000000 : ℝ), (504083519/1000000000 : ℝ), (176648063/312500000 : ℝ)] ![(6109231389517/50000000000000 : ℝ), (10146855262087/25000000000000 : ℝ), (47194116164787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101249759/500000000 : ℝ)|^4261 ≤ (6109231389517/50000000000000 : ℝ)^3237
        have hw : |(-101249759/500000000 : ℝ)|=(101249759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504083519/1000000000 : ℝ)|^4261 ≤ (10146855262087/25000000000000 : ℝ)^3237
        have hw : |(504083519/1000000000 : ℝ)|=(504083519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176648063/312500000 : ℝ)|^4261 ≤ (47194116164787/100000000000000 : ℝ)^3237
        have hw : |(176648063/312500000 : ℝ)|=(176648063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5247561523/10000000000 : ℝ)*x 0 + (-87041869/500000000 : ℝ)*x 1 + (226109551/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247561523/10000000000 : ℝ)^4261 ≤ (668633744909/1562500000000 : ℝ)^3237 := by
    have hnat : (5247561523 : ℕ)^4261*1562500000000^3237 ≤ 668633744909^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247561523 10000000000 668633744909 1562500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87041869/500000000 : ℝ)^4261 ≤ (10013315800673/100000000000000 : ℝ)^3237 := by
    have hnat : (87041869 : ℕ)^4261*100000000000000^3237 ≤ 10013315800673^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87041869 500000000 10013315800673 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226109551/400000000 : ℝ)^4261 ≤ (235970622531/500000000000 : ℝ)^3237 := by
    have hnat : (226109551 : ℕ)^4261*500000000000^3237 ≤ 235970622531^3237*400000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226109551 400000000 235970622531 500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247561523/10000000000 : ℝ), (-87041869/500000000 : ℝ), (226109551/400000000 : ℝ)] ![(668633744909/1562500000000 : ℝ), (10013315800673/100000000000000 : ℝ), (235970622531/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247561523/10000000000 : ℝ)|^4261 ≤ (668633744909/1562500000000 : ℝ)^3237
        have hw : |(5247561523/10000000000 : ℝ)|=(5247561523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87041869/500000000 : ℝ)|^4261 ≤ (10013315800673/100000000000000 : ℝ)^3237
        have hw : |(-87041869/500000000 : ℝ)|=(87041869/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226109551/400000000 : ℝ)|^4261 ≤ (235970622531/500000000000 : ℝ)^3237
        have hw : |(226109551/400000000 : ℝ)|=(226109551/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32797259/62500000 : ℝ)*x 0 + (141318459/250000000 : ℝ)*x 1 + (-1740838101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32797259/62500000 : ℝ)^4261 ≤ (21396279391609/50000000000000 : ℝ)^3237 := by
    have hnat : (32797259 : ℕ)^4261*50000000000000^3237 ≤ 21396279391609^3237*62500000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32797259 62500000 21396279391609 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141318459/250000000 : ℝ)^4261 ≤ (11798529986337/25000000000000 : ℝ)^3237 := by
    have hnat : (141318459 : ℕ)^4261*25000000000000^3237 ≤ 11798529986337^3237*250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141318459 250000000 11798529986337 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1740838101/10000000000 : ℝ)^4261 ≤ (312916289369/3125000000000 : ℝ)^3237 := by
    have hnat : (1740838101 : ℕ)^4261*3125000000000^3237 ≤ 312916289369^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740838101 10000000000 312916289369 3125000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32797259/62500000 : ℝ), (141318459/250000000 : ℝ), (-1740838101/10000000000 : ℝ)] ![(21396279391609/50000000000000 : ℝ), (11798529986337/25000000000000 : ℝ), (312916289369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32797259/62500000 : ℝ)|^4261 ≤ (21396279391609/50000000000000 : ℝ)^3237
        have hw : |(32797259/62500000 : ℝ)|=(32797259/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141318459/250000000 : ℝ)|^4261 ≤ (11798529986337/25000000000000 : ℝ)^3237
        have hw : |(141318459/250000000 : ℝ)|=(141318459/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1740838101/10000000000 : ℝ)|^4261 ≤ (312916289369/3125000000000 : ℝ)^3237
        have hw : |(-1740838101/10000000000 : ℝ)|=(1740838101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s1_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300835801/10000000000 : ℝ)*x 0 + (2488374551/5000000000 : ℝ)*x 1 + (3714816313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300835801/10000000000 : ℝ)^4261 ≤ (32932912073697/100000000000000 : ℝ)^3237 := by
    have hnat : (4300835801 : ℕ)^4261*100000000000000^3237 ≤ 32932912073697^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300835801 10000000000 32932912073697 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488374551/5000000000 : ℝ)^4261 ≤ (39909553555261/100000000000000 : ℝ)^3237 := by
    have hnat : (2488374551 : ℕ)^4261*100000000000000^3237 ≤ 39909553555261^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488374551 5000000000 39909553555261 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3714816313/10000000000 : ℝ)^4261 ≤ (3394691794413/12500000000000 : ℝ)^3237 := by
    have hnat : (3714816313 : ℕ)^4261*12500000000000^3237 ≤ 3394691794413^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714816313 10000000000 3394691794413 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300835801/10000000000 : ℝ), (2488374551/5000000000 : ℝ), (3714816313/10000000000 : ℝ)] ![(32932912073697/100000000000000 : ℝ), (39909553555261/100000000000000 : ℝ), (3394691794413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300835801/10000000000 : ℝ)|^4261 ≤ (32932912073697/100000000000000 : ℝ)^3237
        have hw : |(4300835801/10000000000 : ℝ)|=(4300835801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2488374551/5000000000 : ℝ)|^4261 ≤ (39909553555261/100000000000000 : ℝ)^3237
        have hw : |(2488374551/5000000000 : ℝ)|=(2488374551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3714816313/10000000000 : ℝ)|^4261 ≤ (3394691794413/12500000000000 : ℝ)^3237
        have hw : |(3714816313/10000000000 : ℝ)|=(3714816313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3249/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9889/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/50000 : ℝ) ^ (1065/256 : ℝ) ≤ (716423006757/100000000000000000000 : ℝ) := by
    have hpowers : (551/50000 : ℝ)^1065 ≤ (716423006757/100000000000000000000 : ℝ)^256 := by
      have hnat : (551 : ℕ)^1065*100000000000000000000^256 ≤ 716423006757^256*50000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 50000 716423006757 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/50000 : ℝ)) (X := (716423006757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (27169/100000 : ℝ) ^ (1065/256 : ℝ) ≤ (442239951525207451/100000000000000000000 : ℝ) := by
    have hpowers : (27169/100000 : ℝ)^1065 ≤ (442239951525207451/100000000000000000000 : ℝ)^256 := by
      have hnat : (27169 : ℕ)^1065*100000000000000000000^256 ≤ 442239951525207451^256*100000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27169 100000 442239951525207451 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27169/100000 : ℝ)) (X := (442239951525207451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000716423006757/50000000000000000000 : ℝ) ≤ (250000000861053/250000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50000000716423006757/50000000000000000000 : ℝ)^256 ≤ (250000000861053/250000000000000 : ℝ)^1065 := by
      have hnat : (50000000716423006757 : ℕ)^256*250000000000000^1065 ≤ 250000000861053^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000716423006757 50000000000000000000 250000000861053 250000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000000861053/250000000000000 : ℝ)) (X := (50000000716423006757/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1569410010436690847/1562500000000000000 : ℝ) ≤ (10010612576494659/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (1569410010436690847/1562500000000000000 : ℝ)^256 ≤ (10010612576494659/10000000000000000 : ℝ)^1065 := by
      have hnat : (1569410010436690847 : ℕ)^256*10000000000000000^1065 ≤ 10010612576494659^1065*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1569410010436690847 1562500000000000000 10010612576494659 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010612576494659/10000000000000000 : ℝ)) (X := (1569410010436690847/1562500000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50442239951525207451/50000000000000000000 : ℝ) ≤ (5010612559273599/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50442239951525207451/50000000000000000000 : ℝ)^256 ≤ (5010612559273599/5000000000000000 : ℝ)^1065 := by
      have hnat : (50442239951525207451 : ℕ)^256*5000000000000000^1065 ≤ 5010612559273599^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50442239951525207451 50000000000000000000 5010612559273599 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010612559273599/5000000000000000 : ℝ)) (X := (50442239951525207451/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(716423006757/100000000000000000000 : ℝ) ≤ ((21720550904593245507/21722500000000000000 : ℝ)+2*(3537514017513/868900000000000 : ℝ)*(551/50000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (21720550904593245507/21722500000000000000 : ℝ)+2*(3537514017513/868900000000000 : ℝ)*(551/50000 : ℝ)=(250000000861053/250000000000000 : ℝ) by norm_num, show 1+2*(716423006757/100000000000000000000 : ℝ)=(50000000716423006757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(442239951525207451/100000000000000000000 : ℝ)+(716423006757/100000000000000000000 : ℝ) ≤ ((21720550904593245507/21722500000000000000 : ℝ)+(3537514017513/868900000000000 : ℝ)*((27169/100000 : ℝ)+(551/50000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (21720550904593245507/21722500000000000000 : ℝ)+(3537514017513/868900000000000 : ℝ)*((27169/100000 : ℝ)+(551/50000 : ℝ))=(10010612576494659/10000000000000000 : ℝ) by norm_num, show 1+(442239951525207451/100000000000000000000 : ℝ)+(716423006757/100000000000000000000 : ℝ)=(1569410010436690847/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(442239951525207451/100000000000000000000 : ℝ) ≤ ((21720550904593245507/21722500000000000000 : ℝ)+2*(3537514017513/868900000000000 : ℝ)*(27169/100000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (21720550904593245507/21722500000000000000 : ℝ)+2*(3537514017513/868900000000000 : ℝ)*(27169/100000 : ℝ)=(5010612559273599/5000000000000000 : ℝ) by norm_num, show 1+2*(442239951525207451/100000000000000000000 : ℝ)=(50442239951525207451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21720550904593245507/21722500000000000000 : ℝ)*(X 1 0+X 2 0)+(3537514017513/868900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (551/50000 : ℝ)) (hi := (27169/100000 : ℝ)) (c := (21720550904593245507/21722500000000000000 : ℝ)) (alpha := (3537514017513/868900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21720550904593245507/21722500000000000000 : ℝ)*(X 0 1+X 2 1)+(3537514017513/868900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (551/50000 : ℝ)) (hi := (27169/100000 : ℝ)) (c := (21720550904593245507/21722500000000000000 : ℝ)) (alpha := (3537514017513/868900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21720550904593245507/21722500000000000000 : ℝ)*(X 0 2+X 1 2)+(3537514017513/868900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (551/50000 : ℝ)) (hi := (27169/100000 : ℝ)) (c := (21720550904593245507/21722500000000000000 : ℝ)) (alpha := (3537514017513/868900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506094359/2500000000 : ℝ)*X 0 0+(5661026931/10000000000 : ℝ)*X 0 1+(314543699/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5410029541/10000000000 : ℝ)*X 1 0+(-2360876727/10000000000 : ℝ)*X 1 1+(314543713/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082005949/2000000000 : ℝ)*X 2 0+(5032699051/10000000000 : ℝ)*X 2 1+(-1180438459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537445337/1250000000 : ℝ)*X 0 0+(1848861433/5000000000 : ℝ)*X 0 1+(4993527423/10000000000 : ℝ)*X 0 2+(537445337/1250000000 : ℝ)*X 1 0+(1848861433/5000000000 : ℝ)*X 1 1+(4993527423/10000000000 : ℝ)*X 1 2+(537445337/1250000000 : ℝ)*X 2 0+(1848861433/5000000000 : ℝ)*X 2 1+(4993527423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101249759/500000000 : ℝ)*X 0 0+(504083519/1000000000 : ℝ)*X 0 1+(176648063/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247561523/10000000000 : ℝ)*X 1 0+(-87041869/500000000 : ℝ)*X 1 1+(226109551/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((32797259/62500000 : ℝ)*X 2 0+(141318459/250000000 : ℝ)*X 2 1+(-1740838101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300835801/10000000000 : ℝ)*X 0 0+(2488374551/5000000000 : ℝ)*X 0 1+(3714816313/10000000000 : ℝ)*X 0 2+(4300835801/10000000000 : ℝ)*X 1 0+(2488374551/5000000000 : ℝ)*X 1 1+(3714816313/10000000000 : ℝ)*X 1 2+(4300835801/10000000000 : ℝ)*X 2 0+(2488374551/5000000000 : ℝ)*X 2 1+(3714816313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4111646191064745259967488479/1086125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32147119/100000000000000 : ℝ)*(base1) + (150220741/25000000000000 : ℝ)*(base19) + (660896059/100000000000000 : ℝ)*(base23) + (56506047/50000000000000 : ℝ)*(upper3) + (10729091/20000000000000 : ℝ)*(upper5) + (295407223015619/25000000000000 : ℝ)*(major0) + (295407223015619/25000000000000 : ℝ)*(major1) + (1181628892062477/100000000000000 : ℝ)*(major2) + (63661192798677/4000000000000 : ℝ)*(sp0) + (1591532492152397/100000000000000 : ℝ)*(sp1) + (795766216069651/50000000000000 : ℝ)*(sp2) + (154344547041117/20000000000000 : ℝ)*(sp3) + (661043111/20000000000000 : ℝ)*(sp4) + (359509973/20000000000000 : ℝ)*(sp7) + (77172456490257/10000000000000 : ℝ)*(f.failure) + (1591533093035361/100000000000000 : ℝ)*(f.sum) + (250968439457639/86890000000000000000000000000 : ℝ)*base65 + (625278678999142583/543062500000000000000000000000000 : ℝ)*base67 + (16721906521518240839/2172250000000000000000000000000000 : ℝ)*base69 + (1452542710387919917/543062500000000000000000000000000 : ℝ)*base72 + (474226351529199/86890000000000000000000000000 : ℝ)*base73 + (8358411893182240839/2172250000000000000000000000000000 : ℝ)*base75 + (1126863116294688667/543062500000000000000000000000000 : ℝ)*base78 + (994284305319876167/543062500000000000000000000000000 : ℝ)*base80 + (10280458079763/2715312500000000000000000000 : ℝ)*base81 + (7994531/500000000000000000000 : ℝ)*base89 + (7994531/500000000000000000000 : ℝ)*base91 + (2994531/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (653750395846954889621318247/135765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204036903/25000000000000 : ℝ)*(base19) + (83673559/10000000000000 : ℝ)*(base23) + (42055037/100000000000000 : ℝ)*(upper2) + (41651069/25000000000000 : ℝ)*(upper3) + (9858489/10000000000000 : ℝ)*(upper5) + (303335090250607/25000000000000 : ℝ)*(major0) + (303335090250607/25000000000000 : ℝ)*(major1) + (303335090250607/25000000000000 : ℝ)*(major2) + (5035738627/100000000000000 : ℝ)*(sp1) + (493384743/12500000000000 : ℝ)*(sp2) + (817122581407653/50000000000000 : ℝ)*(sp4) + (1634239310929067/100000000000000 : ℝ)*(sp5) + (408560094750443/25000000000000 : ℝ)*(sp6) + (99054424834999/12500000000000 : ℝ)*(sp7) + (99054424834999/12500000000000 : ℝ)*(f.failure) + (817122581407653/50000000000000 : ℝ)*(f.sum) + (65404408870569/10861250000000000000000000000 : ℝ)*base66 + (288242113351797749/543062500000000000000000000000000 : ℝ)*base67 + (3232484788138952251/543062500000000000000000000000000 : ℝ)*base70 + (3673495226430952251/543062500000000000000000000000000 : ℝ)*base72 + (10255308921711/43445000000000000000000000000 : ℝ)*base74 + (755160112526764751/543062500000000000000000000000000 : ℝ)*base76 + (3193453343966452251/543062500000000000000000000000000 : ℝ)*base78 + (1953947235562952251/543062500000000000000000000000000 : ℝ)*base80 + (6155262785443/1357656250000000000000000000 : ℝ)*base82 + (5747317/625000000000000000000 : ℝ)*base89 + (5747317/625000000000000000000 : ℝ)*base91 + (5747317/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1301_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3249/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9889/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s2_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068226863/10000000000 : ℝ)*x 0 + (5491513101/10000000000 : ℝ)*x 1 + (5174190753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068226863/10000000000 : ℝ)^4261 ≤ (3140746909103/25000000000000 : ℝ)^3237 := by
    have hnat : (2068226863 : ℕ)^4261*25000000000000^3237 ≤ 3140746909103^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068226863 10000000000 3140746909103 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491513101/10000000000 : ℝ)^4261 ≤ (45430299740571/100000000000000 : ℝ)^3237 := by
    have hnat : (5491513101 : ℕ)^4261*100000000000000^3237 ≤ 45430299740571^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491513101 10000000000 45430299740571 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174190753/10000000000 : ℝ)^4261 ≤ (21003356306331/50000000000000 : ℝ)^3237 := by
    have hnat : (5174190753 : ℕ)^4261*50000000000000^3237 ≤ 21003356306331^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174190753 10000000000 21003356306331 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068226863/10000000000 : ℝ), (5491513101/10000000000 : ℝ), (5174190753/10000000000 : ℝ)] ![(3140746909103/25000000000000 : ℝ), (45430299740571/100000000000000 : ℝ), (21003356306331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068226863/10000000000 : ℝ)|^4261 ≤ (3140746909103/25000000000000 : ℝ)^3237
        have hw : |(-2068226863/10000000000 : ℝ)|=(2068226863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491513101/10000000000 : ℝ)|^4261 ≤ (45430299740571/100000000000000 : ℝ)^3237
        have hw : |(5491513101/10000000000 : ℝ)|=(5491513101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174190753/10000000000 : ℝ)|^4261 ≤ (21003356306331/50000000000000 : ℝ)^3237
        have hw : |(5174190753/10000000000 : ℝ)|=(5174190753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073782637/2000000000 : ℝ)*x 0 + (-69768091/312500000 : ℝ)*x 1 + (5174190607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073782637/2000000000 : ℝ)^4261 ≤ (44099942200697/100000000000000 : ℝ)^3237 := by
    have hnat : (1073782637 : ℕ)^4261*100000000000000^3237 ≤ 44099942200697^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073782637 2000000000 44099942200697 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69768091/312500000 : ℝ)^4261 ≤ (2778669346737/20000000000000 : ℝ)^3237 := by
    have hnat : (69768091 : ℕ)^4261*20000000000000^3237 ≤ 2778669346737^3237*312500000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69768091 312500000 2778669346737 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174190607/10000000000 : ℝ)^4261 ≤ (21003355526199/50000000000000 : ℝ)^3237 := by
    have hnat : (5174190607 : ℕ)^4261*50000000000000^3237 ≤ 21003355526199^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174190607 10000000000 21003355526199 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073782637/2000000000 : ℝ), (-69768091/312500000 : ℝ), (5174190607/10000000000 : ℝ)] ![(44099942200697/100000000000000 : ℝ), (2778669346737/20000000000000 : ℝ), (21003355526199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073782637/2000000000 : ℝ)|^4261 ≤ (44099942200697/100000000000000 : ℝ)^3237
        have hw : |(1073782637/2000000000 : ℝ)|=(1073782637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69768091/312500000 : ℝ)|^4261 ≤ (2778669346737/20000000000000 : ℝ)^3237
        have hw : |(-69768091/312500000 : ℝ)|=(69768091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174190607/10000000000 : ℝ)|^4261 ≤ (21003355526199/50000000000000 : ℝ)^3237
        have hw : |(5174190607/10000000000 : ℝ)|=(5174190607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368912929/10000000000 : ℝ)*x 0 + (5174190783/10000000000 : ℝ)*x 1 + (-111628951/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368912929/10000000000 : ℝ)^4261 ≤ (44099939432733/100000000000000 : ℝ)^3237 := by
    have hnat : (5368912929 : ℕ)^4261*100000000000000^3237 ≤ 44099939432733^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368912929 10000000000 44099939432733 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174190783/10000000000 : ℝ)^4261 ≤ (2625419558329/6250000000000 : ℝ)^3237 := by
    have hnat : (5174190783 : ℕ)^4261*6250000000000^3237 ≤ 2625419558329^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174190783 10000000000 2625419558329 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111628951/500000000 : ℝ)^4261 ≤ (6946673809189/50000000000000 : ℝ)^3237 := by
    have hnat : (111628951 : ℕ)^4261*50000000000000^3237 ≤ 6946673809189^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111628951 500000000 6946673809189 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368912929/10000000000 : ℝ), (5174190783/10000000000 : ℝ), (-111628951/500000000 : ℝ)] ![(44099939432733/100000000000000 : ℝ), (2625419558329/6250000000000 : ℝ), (6946673809189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368912929/10000000000 : ℝ)|^4261 ≤ (44099939432733/100000000000000 : ℝ)^3237
        have hw : |(5368912929/10000000000 : ℝ)|=(5368912929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174190783/10000000000 : ℝ)|^4261 ≤ (2625419558329/6250000000000 : ℝ)^3237
        have hw : |(5174190783/10000000000 : ℝ)|=(5174190783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111628951/500000000 : ℝ)|^4261 ≤ (6946673809189/50000000000000 : ℝ)^3237
        have hw : |(-111628951/500000000 : ℝ)|=(111628951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165039307/5000000000 : ℝ)*x 0 + (1003649801/2500000000 : ℝ)*x 1 + (4669023297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165039307/5000000000 : ℝ)^4261 ≤ (8306996587057/25000000000000 : ℝ)^3237 := by
    have hnat : (2165039307 : ℕ)^4261*25000000000000^3237 ≤ 8306996587057^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165039307 5000000000 8306996587057 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003649801/2500000000 : ℝ)^4261 ≤ (30078588851201/100000000000000 : ℝ)^3237 := by
    have hnat : (1003649801 : ℕ)^4261*100000000000000^3237 ≤ 30078588851201^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003649801 2500000000 30078588851201 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4669023297/10000000000 : ℝ)^4261 ≤ (286667381089/781250000000 : ℝ)^3237 := by
    have hnat : (4669023297 : ℕ)^4261*781250000000^3237 ≤ 286667381089^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669023297 10000000000 286667381089 781250000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165039307/5000000000 : ℝ), (1003649801/2500000000 : ℝ), (4669023297/10000000000 : ℝ)] ![(8306996587057/25000000000000 : ℝ), (30078588851201/100000000000000 : ℝ), (286667381089/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165039307/5000000000 : ℝ)|^4261 ≤ (8306996587057/25000000000000 : ℝ)^3237
        have hw : |(2165039307/5000000000 : ℝ)|=(2165039307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003649801/2500000000 : ℝ)|^4261 ≤ (30078588851201/100000000000000 : ℝ)^3237
        have hw : |(1003649801/2500000000 : ℝ)|=(1003649801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4669023297/10000000000 : ℝ)|^4261 ≤ (286667381089/781250000000 : ℝ)^3237
        have hw : |(4669023297/10000000000 : ℝ)|=(4669023297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034152901/5000000000 : ℝ)*x 0 + (5176275113/10000000000 : ℝ)*x 1 + (5489409401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034152901/5000000000 : ℝ)^4261 ≤ (6281809411553/50000000000000 : ℝ)^3237 := by
    have hnat : (1034152901 : ℕ)^4261*50000000000000^3237 ≤ 6281809411553^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034152901 5000000000 6281809411553 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176275113/10000000000 : ℝ)^4261 ≤ (42028989037601/100000000000000 : ℝ)^3237 := by
    have hnat : (5176275113 : ℕ)^4261*100000000000000^3237 ≤ 42028989037601^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176275113 10000000000 42028989037601 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489409401/10000000000 : ℝ)^4261 ≤ (2270369606209/5000000000000 : ℝ)^3237 := by
    have hnat : (5489409401 : ℕ)^4261*5000000000000^3237 ≤ 2270369606209^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489409401 10000000000 2270369606209 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034152901/5000000000 : ℝ), (5176275113/10000000000 : ℝ), (5489409401/10000000000 : ℝ)] ![(6281809411553/50000000000000 : ℝ), (42028989037601/100000000000000 : ℝ), (2270369606209/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034152901/5000000000 : ℝ)|^4261 ≤ (6281809411553/50000000000000 : ℝ)^3237
        have hw : |(-1034152901/5000000000 : ℝ)|=(1034152901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176275113/10000000000 : ℝ)|^4261 ≤ (42028989037601/100000000000000 : ℝ)^3237
        have hw : |(5176275113/10000000000 : ℝ)|=(5176275113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489409401/10000000000 : ℝ)|^4261 ≤ (2270369606209/5000000000000 : ℝ)^3237
        have hw : |(5489409401/10000000000 : ℝ)|=(5489409401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643749029/5000000000 : ℝ)*x 0 + (-191735957/1000000000 : ℝ)*x 1 + (2744704759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643749029/5000000000 : ℝ)^4261 ≤ (43221771334479/100000000000000 : ℝ)^3237 := by
    have hnat : (2643749029 : ℕ)^4261*100000000000000^3237 ≤ 43221771334479^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643749029 5000000000 43221771334479 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191735957/1000000000 : ℝ)^4261 ≤ (1137083524977/10000000000000 : ℝ)^3237 := by
    have hnat : (191735957 : ℕ)^4261*10000000000000^3237 ≤ 1137083524977^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191735957 1000000000 1137083524977 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744704759/5000000000 : ℝ)^4261 ≤ (2270369669907/5000000000000 : ℝ)^3237 := by
    have hnat : (2744704759 : ℕ)^4261*5000000000000^3237 ≤ 2270369669907^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744704759 5000000000 2270369669907 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643749029/5000000000 : ℝ), (-191735957/1000000000 : ℝ), (2744704759/5000000000 : ℝ)] ![(43221771334479/100000000000000 : ℝ), (1137083524977/10000000000000 : ℝ), (2270369669907/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643749029/5000000000 : ℝ)|^4261 ≤ (43221771334479/100000000000000 : ℝ)^3237
        have hw : |(2643749029/5000000000 : ℝ)|=(2643749029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191735957/1000000000 : ℝ)|^4261 ≤ (1137083524977/10000000000000 : ℝ)^3237
        have hw : |(-191735957/1000000000 : ℝ)|=(191735957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744704759/5000000000 : ℝ)|^4261 ≤ (2270369669907/5000000000000 : ℝ)^3237
        have hw : |(2744704759/5000000000 : ℝ)|=(2744704759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321874551/2500000000 : ℝ)*x 0 + (42886011/78125000 : ℝ)*x 1 + (-1917359523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321874551/2500000000 : ℝ)^4261 ≤ (43221772905471/100000000000000 : ℝ)^3237 := by
    have hnat : (1321874551 : ℕ)^4261*100000000000000^3237 ≤ 43221772905471^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321874551 2500000000 43221772905471 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42886011/78125000 : ℝ)^4261 ≤ (113518480501/250000000000 : ℝ)^3237 := by
    have hnat : (42886011 : ℕ)^4261*250000000000^3237 ≤ 113518480501^3237*78125000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42886011 78125000 113518480501 250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917359523/10000000000 : ℝ)^4261 ≤ (710677180179/6250000000000 : ℝ)^3237 := by
    have hnat : (1917359523 : ℕ)^4261*6250000000000^3237 ≤ 710677180179^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917359523 10000000000 710677180179 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321874551/2500000000 : ℝ), (42886011/78125000 : ℝ), (-1917359523/10000000000 : ℝ)] ![(43221772905471/100000000000000 : ℝ), (113518480501/250000000000 : ℝ), (710677180179/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321874551/2500000000 : ℝ)|^4261 ≤ (43221772905471/100000000000000 : ℝ)^3237
        have hw : |(1321874551/2500000000 : ℝ)|=(1321874551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42886011/78125000 : ℝ)|^4261 ≤ (113518480501/250000000000 : ℝ)^3237
        have hw : |(42886011/78125000 : ℝ)|=(42886011/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1917359523/10000000000 : ℝ)|^4261 ≤ (710677180179/6250000000000 : ℝ)^3237
        have hw : |(-1917359523/10000000000 : ℝ)|=(1917359523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s2_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165120301/5000000000 : ℝ)*x 0 + (36443147/78125000 : ℝ)*x 1 + (10047357/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165120301/5000000000 : ℝ)^4261 ≤ (33229622646569/100000000000000 : ℝ)^3237 := by
    have hnat : (2165120301 : ℕ)^4261*100000000000000^3237 ≤ 33229622646569^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165120301 5000000000 33229622646569 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36443147/78125000 : ℝ)^4261 ≤ (36648942730099/100000000000000 : ℝ)^3237 := by
    have hnat : (36443147 : ℕ)^4261*100000000000000^3237 ≤ 36648942730099^3237*78125000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36443147 78125000 36648942730099 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10047357/25000000 : ℝ)^4261 ≤ (3765179326021/12500000000000 : ℝ)^3237 := by
    have hnat : (10047357 : ℕ)^4261*12500000000000^3237 ≤ 3765179326021^3237*25000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10047357 25000000 3765179326021 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165120301/5000000000 : ℝ), (36443147/78125000 : ℝ), (10047357/25000000 : ℝ)] ![(33229622646569/100000000000000 : ℝ), (36648942730099/100000000000000 : ℝ), (3765179326021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165120301/5000000000 : ℝ)|^4261 ≤ (33229622646569/100000000000000 : ℝ)^3237
        have hw : |(2165120301/5000000000 : ℝ)|=(2165120301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36443147/78125000 : ℝ)|^4261 ≤ (36648942730099/100000000000000 : ℝ)^3237
        have hw : |(36443147/78125000 : ℝ)|=(36443147/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10047357/25000000 : ℝ)|^4261 ≤ (3765179326021/12500000000000 : ℝ)^3237
        have hw : |(10047357/25000000 : ℝ)|=(10047357/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3249/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (957/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16277/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9889/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3249/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9889/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3249/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9889/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3249/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9889/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3249/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9889/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3249/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9889/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3249/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3249/50000 : ℝ) ^ (1065/256 : ℝ) ≤ (1150742301112343/100000000000000000000 : ℝ) := by
    have hpowers : (3249/50000 : ℝ)^1065 ≤ (1150742301112343/100000000000000000000 : ℝ)^256 := by
      have hnat : (3249 : ℕ)^1065*100000000000000000000^256 ≤ 1150742301112343^256*50000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3249 50000 1150742301112343 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3249/50000 : ℝ)) (X := (1150742301112343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9889/50000 : ℝ) ^ (1065/256 : ℝ) ≤ (14754303451268279/12500000000000000000 : ℝ) := by
    have hpowers : (9889/50000 : ℝ)^1065 ≤ (14754303451268279/12500000000000000000 : ℝ)^256 := by
      have hnat : (9889 : ℕ)^1065*12500000000000000000^256 ≤ 14754303451268279^256*50000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9889 50000 14754303451268279 12500000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9889/50000 : ℝ)) (X := (14754303451268279/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001150742301112343/50000000000000000000 : ℝ) ≤ (10000055321587609/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50001150742301112343/50000000000000000000 : ℝ)^256 ≤ (10000055321587609/10000000000000000 : ℝ)^1065 := by
      have hnat : (50001150742301112343 : ℕ)^256*10000000000000000^1065 ≤ 10000055321587609^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001150742301112343 50000000000000000000 10000055321587609 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055321587609/10000000000000000 : ℝ)) (X := (50001150742301112343/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (4004767406796450343/4000000000000000000 : ℝ) ≤ (10002863624530337/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (4004767406796450343/4000000000000000000 : ℝ)^256 ≤ (10002863624530337/10000000000000000 : ℝ)^1065 := by
      have hnat : (4004767406796450343 : ℕ)^256*10000000000000000^1065 ≤ 10002863624530337^1065*4000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4004767406796450343 4000000000000000000 10002863624530337 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002863624530337/10000000000000000 : ℝ)) (X := (4004767406796450343/4000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6264754303451268279/6250000000000000000 : ℝ) ≤ (2001134385494613/2000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (6264754303451268279/6250000000000000000 : ℝ)^256 ≤ (2001134385494613/2000000000000000 : ℝ)^1065 := by
      have hnat : (6264754303451268279 : ℕ)^256*2000000000000000^1065 ≤ 2001134385494613^1065*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6264754303451268279 6250000000000000000 2001134385494613 2000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001134385494613/2000000000000000 : ℝ)) (X := (6264754303451268279/6250000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1150742301112343/100000000000000000000 : ℝ) ≤ ((2074441218213121163/2075000000000000000 : ℝ)+2*(351037867841/166000000000000 : ℝ)*(3249/50000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (2074441218213121163/2075000000000000000 : ℝ)+2*(351037867841/166000000000000 : ℝ)*(3249/50000 : ℝ)=(10000055321587609/10000000000000000 : ℝ) by norm_num, show 1+2*(1150742301112343/100000000000000000000 : ℝ)=(50001150742301112343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14754303451268279/12500000000000000000 : ℝ)+(1150742301112343/100000000000000000000 : ℝ) ≤ ((2074441218213121163/2075000000000000000 : ℝ)+(351037867841/166000000000000 : ℝ)*((9889/50000 : ℝ)+(3249/50000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (2074441218213121163/2075000000000000000 : ℝ)+(351037867841/166000000000000 : ℝ)*((9889/50000 : ℝ)+(3249/50000 : ℝ))=(10002863624530337/10000000000000000 : ℝ) by norm_num, show 1+(14754303451268279/12500000000000000000 : ℝ)+(1150742301112343/100000000000000000000 : ℝ)=(4004767406796450343/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14754303451268279/12500000000000000000 : ℝ) ≤ ((2074441218213121163/2075000000000000000 : ℝ)+2*(351037867841/166000000000000 : ℝ)*(9889/50000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (2074441218213121163/2075000000000000000 : ℝ)+2*(351037867841/166000000000000 : ℝ)*(9889/50000 : ℝ)=(2001134385494613/2000000000000000 : ℝ) by norm_num, show 1+2*(14754303451268279/12500000000000000000 : ℝ)=(6264754303451268279/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2074441218213121163/2075000000000000000 : ℝ)*(X 1 0+X 2 0)+(351037867841/166000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (3249/50000 : ℝ)) (hi := (9889/50000 : ℝ)) (c := (2074441218213121163/2075000000000000000 : ℝ)) (alpha := (351037867841/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2074441218213121163/2075000000000000000 : ℝ)*(X 0 1+X 2 1)+(351037867841/166000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (3249/50000 : ℝ)) (hi := (9889/50000 : ℝ)) (c := (2074441218213121163/2075000000000000000 : ℝ)) (alpha := (351037867841/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2074441218213121163/2075000000000000000 : ℝ)*(X 0 2+X 1 2)+(351037867841/166000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (3249/50000 : ℝ)) (hi := (9889/50000 : ℝ)) (c := (2074441218213121163/2075000000000000000 : ℝ)) (alpha := (351037867841/166000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2068226863/10000000000 : ℝ)*X 0 0+(5491513101/10000000000 : ℝ)*X 0 1+(5174190753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073782637/2000000000 : ℝ)*X 1 0+(-69768091/312500000 : ℝ)*X 1 1+(5174190607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368912929/10000000000 : ℝ)*X 2 0+(5174190783/10000000000 : ℝ)*X 2 1+(-111628951/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165039307/5000000000 : ℝ)*X 0 0+(1003649801/2500000000 : ℝ)*X 0 1+(4669023297/10000000000 : ℝ)*X 0 2+(2165039307/5000000000 : ℝ)*X 1 0+(1003649801/2500000000 : ℝ)*X 1 1+(4669023297/10000000000 : ℝ)*X 1 2+(2165039307/5000000000 : ℝ)*X 2 0+(1003649801/2500000000 : ℝ)*X 2 1+(4669023297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1034152901/5000000000 : ℝ)*X 0 0+(5176275113/10000000000 : ℝ)*X 0 1+(5489409401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643749029/5000000000 : ℝ)*X 1 0+(-191735957/1000000000 : ℝ)*X 1 1+(2744704759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321874551/2500000000 : ℝ)*X 2 0+(42886011/78125000 : ℝ)*X 2 1+(-1917359523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165120301/5000000000 : ℝ)*X 0 0+(36443147/78125000 : ℝ)*X 0 1+(10047357/25000000 : ℝ)*X 0 2+(2165120301/5000000000 : ℝ)*X 1 0+(36443147/78125000 : ℝ)*X 1 1+(10047357/25000000 : ℝ)*X 1 2+(2165120301/5000000000 : ℝ)*X 2 0+(36443147/78125000 : ℝ)*X 2 1+(10047357/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7489624796902909377945681/1296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423105431/20000000000000 : ℝ)*(base19) + (1596887847/100000000000000 : ℝ)*(base23) + (49444297/25000000000000 : ℝ)*(lower2) + (630436577/100000000000000 : ℝ)*(upper3) + (8673637/4000000000000 : ℝ)*(upper5) + (58493648603029/2500000000000 : ℝ)*(major0) + (58493648603029/2500000000000 : ℝ)*(major1) + (58493648603029/2500000000000 : ℝ)*(major2) + (1575693637611717/50000000000000 : ℝ)*(sp0) + (787849021885627/25000000000000 : ℝ)*(sp1) + (393924575772727/12500000000000 : ℝ)*(sp2) + (152807516042259/10000000000000 : ℝ)*(sp3) + (10927846229/100000000000000 : ℝ)*(sp4) + (18332245651/100000000000000 : ℝ)*(sp7) + (1528093492668241/100000000000000 : ℝ)*(f.failure) + (3151398203069663/100000000000000 : ℝ)*(f.sum) + (321090690863/103750000000000000000000000 : ℝ)*base66 + (25616611055647273/5187500000000000000000000000000 : ℝ)*base68 + (40618069308272273/5187500000000000000000000000000 : ℝ)*base70 + (39714344509040227/5187500000000000000000000000000 : ℝ)*base71 + (426488517711/207500000000000000000000000 : ℝ)*base74 + (10738680006709773/5187500000000000000000000000000 : ℝ)*base76 + (737422989209773/5187500000000000000000000000000 : ℝ)*base78 + (19353193556334773/5187500000000000000000000000000 : ℝ)*base80 + (12895721391/51875000000000000000000000 : ℝ)*base81 + (18645603/5000000000000000000000 : ℝ)*base89 + (18645603/5000000000000000000000 : ℝ)*base91 + (18645603/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219545765513932865332796799/20750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2023945133/100000000000000 : ℝ)*(base19) + (238939451/10000000000000 : ℝ)*(base23) + (142406583/50000000000000 : ℝ)*(upper3) + (21522461/20000000000000 : ℝ)*(lower4) + (33488207/20000000000000 : ℝ)*(upper5) + (474203106381209/20000000000000 : ℝ)*(major0) + (474203106381209/20000000000000 : ℝ)*(major1) + (474203106381209/20000000000000 : ℝ)*(major2) + (21111351549/100000000000000 : ℝ)*(sp1) + (25900969973/100000000000000 : ℝ)*(sp2) + (3193514978287797/100000000000000 : ℝ)*(sp4) + (798372960747779/25000000000000 : ℝ)*(sp5) + (638697337584663/20000000000000 : ℝ)*(sp6) + (387128933210081/25000000000000 : ℝ)*(sp7) + (387128933210081/25000000000000 : ℝ)*(f.failure) + (3193514978287797/100000000000000 : ℝ)*(f.sum) + (4494475377871/1660000000000000000000000000 : ℝ)*base66 + (81697155013038567/41500000000000000000000000000000 : ℝ)*base67 + (285241443405038567/41500000000000000000000000000000 : ℝ)*base69 + (251532610170961433/41500000000000000000000000000000 : ℝ)*base72 + (7395472623609/1660000000000000000000000000 : ℝ)*base73 + (38932189944038567/41500000000000000000000000000000 : ℝ)*base75 + (121852616856961433/41500000000000000000000000000000 : ℝ)*base78 + (22052926816038567/41500000000000000000000000000000 : ℝ)*base79 + (2138909288069/1660000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8897677/1250000000000000000000 : ℝ)*base90 + (8897677/1250000000000000000000 : ℝ)*base92 + (8897677/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1301_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9889/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3249/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1301_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1301_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1301_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1301_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

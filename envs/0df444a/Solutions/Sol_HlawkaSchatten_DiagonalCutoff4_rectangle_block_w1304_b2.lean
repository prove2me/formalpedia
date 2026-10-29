-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:37:24.319965+00:00
-- url     : https://prove2.me/submissions/232de7f4-8804-4523-a23e-b288fcce38c4

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
theorem support_rectangle_w1304_s6_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077254019/10000000000 : ℝ)*x 0 + (676836643/1250000000 : ℝ)*x 1 + (1048668353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077254019/10000000000 : ℝ)^533 ≤ (12641034592273/100000000000000 : ℝ)^405 := by
    have hnat : (2077254019 : ℕ)^533*100000000000000^405 ≤ 12641034592273^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077254019 10000000000 12641034592273 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676836643/1250000000 : ℝ)^533 ≤ (2230180600727/5000000000000 : ℝ)^405 := by
    have hnat : (676836643 : ℕ)^533*5000000000000^405 ≤ 2230180600727^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676836643 1250000000 2230180600727 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048668353/2000000000 : ℝ)^533 ≤ (21377676690733/50000000000000 : ℝ)^405 := by
    have hnat : (1048668353 : ℕ)^533*50000000000000^405 ≤ 21377676690733^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048668353 2000000000 21377676690733 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077254019/10000000000 : ℝ), (676836643/1250000000 : ℝ), (1048668353/2000000000 : ℝ)] ![(12641034592273/100000000000000 : ℝ), (2230180600727/5000000000000 : ℝ), (21377676690733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077254019/10000000000 : ℝ)|^533 ≤ (12641034592273/100000000000000 : ℝ)^405
        have hw : |(-2077254019/10000000000 : ℝ)|=(2077254019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676836643/1250000000 : ℝ)|^533 ≤ (2230180600727/5000000000000 : ℝ)^405
        have hw : |(676836643/1250000000 : ℝ)|=(676836643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048668353/2000000000 : ℝ)|^533 ≤ (21377676690733/50000000000000 : ℝ)^405
        have hw : |(1048668353/2000000000 : ℝ)|=(1048668353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349624993/10000000000 : ℝ)*x 0 + (-1082295459/5000000000 : ℝ)*x 1 + (1048668267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349624993/10000000000 : ℝ)^533 ≤ (21949776505181/50000000000000 : ℝ)^405 := by
    have hnat : (5349624993 : ℕ)^533*50000000000000^405 ≤ 21949776505181^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349624993 10000000000 21949776505181 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082295459/5000000000 : ℝ)^533 ≤ (13345098199763/100000000000000 : ℝ)^405 := by
    have hnat : (1082295459 : ℕ)^533*100000000000000^405 ≤ 13345098199763^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082295459 5000000000 13345098199763 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048668267/2000000000 : ℝ)^533 ≤ (5344418595873/12500000000000 : ℝ)^405 := by
    have hnat : (1048668267 : ℕ)^533*12500000000000^405 ≤ 5344418595873^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048668267 2000000000 5344418595873 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349624993/10000000000 : ℝ), (-1082295459/5000000000 : ℝ), (1048668267/2000000000 : ℝ)] ![(21949776505181/50000000000000 : ℝ), (13345098199763/100000000000000 : ℝ), (5344418595873/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349624993/10000000000 : ℝ)|^533 ≤ (21949776505181/50000000000000 : ℝ)^405
        have hw : |(5349624993/10000000000 : ℝ)|=(5349624993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082295459/5000000000 : ℝ)|^533 ≤ (13345098199763/100000000000000 : ℝ)^405
        have hw : |(-1082295459/5000000000 : ℝ)|=(1082295459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048668267/2000000000 : ℝ)|^533 ≤ (5344418595873/12500000000000 : ℝ)^405
        have hw : |(1048668267/2000000000 : ℝ)|=(1048668267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1069924797/2000000000 : ℝ)*x 0 + (1310835421/2500000000 : ℝ)*x 1 + (-2164591799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069924797/2000000000 : ℝ)^533 ≤ (21949771062167/50000000000000 : ℝ)^405 := by
    have hnat : (1069924797 : ℕ)^533*50000000000000^405 ≤ 21949771062167^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069924797 2000000000 21949771062167 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310835421/2500000000 : ℝ)^533 ≤ (42755352512227/100000000000000 : ℝ)^405 := by
    have hnat : (1310835421 : ℕ)^533*100000000000000^405 ≤ 42755352512227^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310835421 2500000000 42755352512227 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164591799/10000000000 : ℝ)^533 ≤ (166813816849/1250000000000 : ℝ)^405 := by
    have hnat : (2164591799 : ℕ)^533*1250000000000^405 ≤ 166813816849^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164591799 10000000000 166813816849 1250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069924797/2000000000 : ℝ), (1310835421/2500000000 : ℝ), (-2164591799/10000000000 : ℝ)] ![(21949771062167/50000000000000 : ℝ), (42755352512227/100000000000000 : ℝ), (166813816849/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069924797/2000000000 : ℝ)|^533 ≤ (21949771062167/50000000000000 : ℝ)^405
        have hw : |(1069924797/2000000000 : ℝ)|=(1069924797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310835421/2500000000 : ℝ)|^533 ≤ (42755352512227/100000000000000 : ℝ)^405
        have hw : |(1310835421/2500000000 : ℝ)|=(1310835421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2164591799/10000000000 : ℝ)|^533 ≤ (166813816849/1250000000000 : ℝ)^405
        have hw : |(-2164591799/10000000000 : ℝ)|=(2164591799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (542081311/1250000000 : ℝ)*x 0 + (416318937/1000000000 : ℝ)*x 1 + (28231083/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542081311/1250000000 : ℝ)^533 ≤ (33302535549083/100000000000000 : ℝ)^405 := by
    have hnat : (542081311 : ℕ)^533*100000000000000^405 ≤ 33302535549083^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542081311 1250000000 33302535549083 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416318937/1000000000 : ℝ)^533 ≤ (31560657385351/100000000000000 : ℝ)^405 := by
    have hnat : (416318937 : ℕ)^533*100000000000000^405 ≤ 31560657385351^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416318937 1000000000 31560657385351 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28231083/62500000 : ℝ)^533 ≤ (17568403524143/50000000000000 : ℝ)^405 := by
    have hnat : (28231083 : ℕ)^533*50000000000000^405 ≤ 17568403524143^405*62500000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28231083 62500000 17568403524143 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542081311/1250000000 : ℝ), (416318937/1000000000 : ℝ), (28231083/62500000 : ℝ)] ![(33302535549083/100000000000000 : ℝ), (31560657385351/100000000000000 : ℝ), (17568403524143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542081311/1250000000 : ℝ)|^533 ≤ (33302535549083/100000000000000 : ℝ)^405
        have hw : |(542081311/1250000000 : ℝ)|=(542081311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416318937/1000000000 : ℝ)|^533 ≤ (31560657385351/100000000000000 : ℝ)^405
        have hw : |(416318937/1000000000 : ℝ)|=(416318937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28231083/62500000 : ℝ)|^533 ≤ (17568403524143/50000000000000 : ℝ)^405
        have hw : |(28231083/62500000 : ℝ)|=(28231083/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077267191/10000000000 : ℝ)*x 0 + (209758133/400000000 : ℝ)*x 1 + (2707039007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077267191/10000000000 : ℝ)^533 ≤ (6320570041873/50000000000000 : ℝ)^405 := by
    have hnat : (2077267191 : ℕ)^533*50000000000000^405 ≤ 6320570041873^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077267191 10000000000 6320570041873 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209758133/400000000 : ℝ)^533 ≤ (21380958184627/50000000000000 : ℝ)^405 := by
    have hnat : (209758133 : ℕ)^533*50000000000000^405 ≤ 21380958184627^405*400000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209758133 400000000 21380958184627 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707039007/5000000000 : ℝ)^533 ≤ (44596943524961/100000000000000 : ℝ)^405 := by
    have hnat : (2707039007 : ℕ)^533*100000000000000^405 ≤ 44596943524961^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707039007 5000000000 44596943524961 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077267191/10000000000 : ℝ), (209758133/400000000 : ℝ), (2707039007/5000000000 : ℝ)] ![(6320570041873/50000000000000 : ℝ), (21380958184627/50000000000000 : ℝ), (44596943524961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077267191/10000000000 : ℝ)|^533 ≤ (6320570041873/50000000000000 : ℝ)^405
        have hw : |(-2077267191/10000000000 : ℝ)|=(2077267191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209758133/400000000 : ℝ)|^533 ≤ (21380958184627/50000000000000 : ℝ)^405
        have hw : |(209758133/400000000 : ℝ)|=(209758133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707039007/5000000000 : ℝ)|^533 ≤ (44596943524961/100000000000000 : ℝ)^405
        have hw : |(2707039007/5000000000 : ℝ)|=(2707039007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326422011/2500000000 : ℝ)*x 0 + (-249231879/1250000000 : ℝ)*x 1 + (5414078013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326422011/2500000000 : ℝ)^533 ≤ (43425667143899/100000000000000 : ℝ)^405 := by
    have hnat : (1326422011 : ℕ)^533*100000000000000^405 ≤ 43425667143899^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326422011 2500000000 43425667143899 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249231879/1250000000 : ℝ)^533 ≤ (5988694662723/50000000000000 : ℝ)^405 := by
    have hnat : (249231879 : ℕ)^533*50000000000000^405 ≤ 5988694662723^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249231879 1250000000 5988694662723 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414078013/10000000000 : ℝ)^533 ≤ (1114923587853/2500000000000 : ℝ)^405 := by
    have hnat : (5414078013 : ℕ)^533*2500000000000^405 ≤ 1114923587853^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414078013 10000000000 1114923587853 2500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326422011/2500000000 : ℝ), (-249231879/1250000000 : ℝ), (5414078013/10000000000 : ℝ)] ![(43425667143899/100000000000000 : ℝ), (5988694662723/50000000000000 : ℝ), (1114923587853/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326422011/2500000000 : ℝ)|^533 ≤ (43425667143899/100000000000000 : ℝ)^405
        have hw : |(1326422011/2500000000 : ℝ)|=(1326422011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249231879/1250000000 : ℝ)|^533 ≤ (5988694662723/50000000000000 : ℝ)^405
        have hw : |(-249231879/1250000000 : ℝ)|=(249231879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414078013/10000000000 : ℝ)|^533 ≤ (1114923587853/2500000000000 : ℝ)^405
        have hw : |(5414078013/10000000000 : ℝ)|=(5414078013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305688047/10000000000 : ℝ)*x 0 + (5414078011/10000000000 : ℝ)*x 1 + (-1993855031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305688047/10000000000 : ℝ)^533 ≤ (21712833588107/50000000000000 : ℝ)^405 := by
    have hnat : (5305688047 : ℕ)^533*50000000000000^405 ≤ 21712833588107^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305688047 10000000000 21712833588107 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414078011/10000000000 : ℝ)^533 ≤ (44596943492439/100000000000000 : ℝ)^405 := by
    have hnat : (5414078011 : ℕ)^533*100000000000000^405 ≤ 44596943492439^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414078011 10000000000 44596943492439 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993855031/10000000000 : ℝ)^533 ≤ (598869465877/5000000000000 : ℝ)^405 := by
    have hnat : (1993855031 : ℕ)^533*5000000000000^405 ≤ 598869465877^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993855031 10000000000 598869465877 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305688047/10000000000 : ℝ), (5414078011/10000000000 : ℝ), (-1993855031/10000000000 : ℝ)] ![(21712833588107/50000000000000 : ℝ), (44596943492439/100000000000000 : ℝ), (598869465877/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305688047/10000000000 : ℝ)|^533 ≤ (21712833588107/50000000000000 : ℝ)^405
        have hw : |(5305688047/10000000000 : ℝ)|=(5305688047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414078011/10000000000 : ℝ)|^533 ≤ (44596943492439/100000000000000 : ℝ)^405
        have hw : |(5414078011/10000000000 : ℝ)|=(5414078011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993855031/10000000000 : ℝ)|^533 ≤ (598869465877/5000000000000 : ℝ)^405
        have hw : |(-1993855031/10000000000 : ℝ)|=(1993855031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s6_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (542084647/1250000000 : ℝ)*x 0 + (2257854749/5000000000 : ℝ)*x 1 + (4164459/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542084647/1250000000 : ℝ)^533 ≤ (33302805268067/100000000000000 : ℝ)^405 := by
    have hnat : (542084647 : ℕ)^533*100000000000000^405 ≤ 33302805268067^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542084647 1250000000 33302805268067 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257854749/5000000000 : ℝ)^533 ≤ (17561934929679/50000000000000 : ℝ)^405 := by
    have hnat : (2257854749 : ℕ)^533*50000000000000^405 ≤ 17561934929679^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257854749 5000000000 17561934929679 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4164459/10000000 : ℝ)^533 ≤ (15786662431751/50000000000000 : ℝ)^405 := by
    have hnat : (4164459 : ℕ)^533*50000000000000^405 ≤ 15786662431751^405*10000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164459 10000000 15786662431751 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542084647/1250000000 : ℝ), (2257854749/5000000000 : ℝ), (4164459/10000000 : ℝ)] ![(33302805268067/100000000000000 : ℝ), (17561934929679/50000000000000 : ℝ), (15786662431751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542084647/1250000000 : ℝ)|^533 ≤ (33302805268067/100000000000000 : ℝ)^405
        have hw : |(542084647/1250000000 : ℝ)|=(542084647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257854749/5000000000 : ℝ)|^533 ≤ (17561934929679/50000000000000 : ℝ)^405
        have hw : |(2257854749/5000000000 : ℝ)|=(2257854749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4164459/10000000 : ℝ)|^533 ≤ (15786662431751/50000000000000 : ℝ)^405
        have hw : |(4164459/10000000 : ℝ)|=(4164459/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (691/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14693/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14693/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5523/50000 : ℝ) ^ (4263/1024 : ℝ) ≤ (5196971757086413/50000000000000000000 : ℝ) := by
    have hpowers : (5523/50000 : ℝ)^4263 ≤ (5196971757086413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5523 : ℕ)^4263*50000000000000000000^1024 ≤ 5196971757086413^1024*50000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5523 50000 5196971757086413 50000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5523/50000 : ℝ)) (X := (5196971757086413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14693/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (34088614175195157/100000000000000000000 : ℝ) := by
    have hpowers : (14693/100000 : ℝ)^4263 ≤ (34088614175195157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14693 : ℕ)^4263*100000000000000000000^1024 ≤ 34088614175195157^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14693 100000 34088614175195157 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14693/100000 : ℝ)) (X := (34088614175195157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005196971757086413/25000000000000000000 : ℝ) ≤ (10000499298978423/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (25005196971757086413/25000000000000000000 : ℝ)^1024 ≤ (10000499298978423/10000000000000000 : ℝ)^4263 := by
      have hnat : (25005196971757086413 : ℕ)^1024*10000000000000000^4263 ≤ 10000499298978423^4263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005196971757086413 25000000000000000000 10000499298978423 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000499298978423/10000000000000000 : ℝ)) (X := (25005196971757086413/25000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044482557689367983/100000000000000000000 : ℝ) ≤ (1250133539888763/1250000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (100044482557689367983/100000000000000000000 : ℝ)^1024 ≤ (1250133539888763/1250000000000000 : ℝ)^4263 := by
      have hnat : (100044482557689367983 : ℕ)^1024*1250000000000000^4263 ≤ 1250133539888763^4263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044482557689367983 100000000000000000000 1250133539888763 1250000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133539888763/1250000000000000 : ℝ)) (X := (100044482557689367983/100000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034088614175195157/50000000000000000000 : ℝ) ≤ (2000327467848357/2000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50034088614175195157/50000000000000000000 : ℝ)^1024 ≤ (2000327467848357/2000000000000000 : ℝ)^4263 := by
      have hnat : (50034088614175195157 : ℕ)^1024*2000000000000000^4263 ≤ 2000327467848357^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034088614175195157 50000000000000000000 2000327467848357 2000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000327467848357/2000000000000000 : ℝ)) (X := (50034088614175195157/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5196971757086413/50000000000000000000 : ℝ) ≤ ((5208464307232173147/5210000000000000000 : ℝ)+2*(569020131681/364700000000000 : ℝ)*(5523/50000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (5208464307232173147/5210000000000000000 : ℝ)+2*(569020131681/364700000000000 : ℝ)*(5523/50000 : ℝ)=(10000499298978423/10000000000000000 : ℝ) by norm_num, show 1+2*(5196971757086413/50000000000000000000 : ℝ)=(25005196971757086413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34088614175195157/100000000000000000000 : ℝ)+(5196971757086413/50000000000000000000 : ℝ) ≤ ((5208464307232173147/5210000000000000000 : ℝ)+(569020131681/364700000000000 : ℝ)*((14693/100000 : ℝ)+(5523/50000 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (5208464307232173147/5210000000000000000 : ℝ)+(569020131681/364700000000000 : ℝ)*((14693/100000 : ℝ)+(5523/50000 : ℝ))=(1250133539888763/1250000000000000 : ℝ) by norm_num, show 1+(34088614175195157/100000000000000000000 : ℝ)+(5196971757086413/50000000000000000000 : ℝ)=(100044482557689367983/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34088614175195157/100000000000000000000 : ℝ) ≤ ((5208464307232173147/5210000000000000000 : ℝ)+2*(569020131681/364700000000000 : ℝ)*(14693/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (5208464307232173147/5210000000000000000 : ℝ)+2*(569020131681/364700000000000 : ℝ)*(14693/100000 : ℝ)=(2000327467848357/2000000000000000 : ℝ) by norm_num, show 1+2*(34088614175195157/100000000000000000000 : ℝ)=(50034088614175195157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5208464307232173147/5210000000000000000 : ℝ)*(X 1 0+X 2 0)+(569020131681/364700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5208464307232173147/5210000000000000000 : ℝ)) (alpha := (569020131681/364700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5208464307232173147/5210000000000000000 : ℝ)*(X 0 1+X 2 1)+(569020131681/364700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5208464307232173147/5210000000000000000 : ℝ)) (alpha := (569020131681/364700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5208464307232173147/5210000000000000000 : ℝ)*(X 0 2+X 1 2)+(569020131681/364700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14693/100000 : ℝ)) (c := (5208464307232173147/5210000000000000000 : ℝ)) (alpha := (569020131681/364700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077254019/10000000000 : ℝ)*X 0 0+(676836643/1250000000 : ℝ)*X 0 1+(1048668353/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349624993/10000000000 : ℝ)*X 1 0+(-1082295459/5000000000 : ℝ)*X 1 1+(1048668267/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069924797/2000000000 : ℝ)*X 2 0+(1310835421/2500000000 : ℝ)*X 2 1+(-2164591799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542081311/1250000000 : ℝ)*X 0 0+(416318937/1000000000 : ℝ)*X 0 1+(28231083/62500000 : ℝ)*X 0 2+(542081311/1250000000 : ℝ)*X 1 0+(416318937/1000000000 : ℝ)*X 1 1+(28231083/62500000 : ℝ)*X 1 2+(542081311/1250000000 : ℝ)*X 2 0+(416318937/1000000000 : ℝ)*X 2 1+(28231083/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2077267191/10000000000 : ℝ)*X 0 0+(209758133/400000000 : ℝ)*X 0 1+(2707039007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326422011/2500000000 : ℝ)*X 1 0+(-249231879/1250000000 : ℝ)*X 1 1+(5414078013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305688047/10000000000 : ℝ)*X 2 0+(5414078011/10000000000 : ℝ)*X 2 1+(-1993855031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542084647/1250000000 : ℝ)*X 0 0+(2257854749/5000000000 : ℝ)*X 0 1+(4164459/10000000 : ℝ)*X 0 2+(542084647/1250000000 : ℝ)*X 1 0+(2257854749/5000000000 : ℝ)*X 1 1+(4164459/10000000 : ℝ)*X 1 2+(542084647/1250000000 : ℝ)*X 2 0+(2257854749/5000000000 : ℝ)*X 2 1+(4164459/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7955812633908540091801680543/911750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1301087267/100000000000000 : ℝ)*(base19) + (38776031/10000000000000 : ℝ)*(base23) + (205543137/100000000000000 : ℝ)*(lower4) + (80101379/50000000000000 : ℝ)*(lower5) + (4331322354432489/100000000000000 : ℝ)*(major0) + (4331322354432489/100000000000000 : ℝ)*(major1) + (4331322354432489/100000000000000 : ℝ)*(major2) + (1167200498130189/20000000000000 : ℝ)*(sp0) + (5836022739396839/100000000000000 : ℝ)*(sp1) + (5835999556817409/100000000000000 : ℝ)*(sp2) + (1413302099215869/50000000000000 : ℝ)*(sp3) + (21549833161/100000000000000 : ℝ)*(sp4) + (6023976597/25000000000000 : ℝ)*(sp6) + (16179086769/100000000000000 : ℝ)*(sp7) + (706655094379627/25000000000000 : ℝ)*(f.failure) + (2918012020242053/50000000000000 : ℝ)*(f.sum) + (23730475630761/18235000000000000000000000000 : ℝ)*base66 + (7390776691276889819/3647000000000000000000000000000000 : ℝ)*base68 + (1938674578099110181/3647000000000000000000000000000000 : ℝ)*base69 + (17880938883912889819/3647000000000000000000000000000000 : ℝ)*base72 + (74288746148691/18235000000000000000000000000 : ℝ)*base74 + (14850654206142889819/3647000000000000000000000000000000 : ℝ)*base76 + (18737626383090889819/3647000000000000000000000000000000 : ℝ)*base78 + (20381316361769889819/3647000000000000000000000000000000 : ℝ)*base80 + (21591327786537/9117500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (37136631/2500000000000000000000 : ℝ)*base89 + (37136631/2500000000000000000000 : ℝ)*base91 + (37136631/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8356545385201122849928666251/911750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (809163787/50000000000000 : ℝ)*(base19) + (882652053/50000000000000 : ℝ)*(base23) + (185755117/100000000000000 : ℝ)*(upper3) + (16264167/25000000000000 : ℝ)*(lower4) + (11768043/6250000000000 : ℝ)*(upper5) + (2181252828266227/50000000000000 : ℝ)*(major0) + (2181252828266227/50000000000000 : ℝ)*(major1) + (2181252828266227/50000000000000 : ℝ)*(major2) + (8138401861/25000000000000 : ℝ)*(sp1) + (35094664901/100000000000000 : ℝ)*(sp2) + (5878040411337703/100000000000000 : ℝ)*(sp4) + (2939003119701343/50000000000000 : ℝ)*(sp5) + (734750443921087/12500000000000 : ℝ)*(sp6) + (2846970596214161/100000000000000 : ℝ)*(sp7) + (2846970596214161/100000000000000 : ℝ)*(f.failure) + (5878040411337703/100000000000000 : ℝ)*(f.sum) + (111280906518631/18235000000000000000000000000 : ℝ)*base66 + (9551442426151955417/1823500000000000000000000000000000 : ℝ)*base68 + (13363666624706544583/1823500000000000000000000000000000 : ℝ)*base69 + (9469767421688455417/1823500000000000000000000000000000 : ℝ)*base72 + (867274927669/284921875000000000000000000 : ℝ)*base74 + (830607403730544583/1823500000000000000000000000000000 : ℝ)*base75 + (2858016872168044583/1823500000000000000000000000000000 : ℝ)*base77 + (4949641421920544583/1823500000000000000000000000000000 : ℝ)*base79 + (15312936368201/18235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25304267/10000000000000000000000 : ℝ)*base90 + (25304267/10000000000000000000000 : ℝ)*base92 + (25304267/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1304_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_s7_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-519315883/2500000000 : ℝ)*x 0 + (1353651341/2500000000 : ℝ)*x 1 + (2621711671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519315883/2500000000 : ℝ)^533 ≤ (49379338983/390625000000 : ℝ)^405 := by
    have hnat : (519315883 : ℕ)^533*390625000000^405 ≤ 49379338983^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519315883 2500000000 49379338983 390625000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353651341/2500000000 : ℝ)^533 ≤ (44602660396143/100000000000000 : ℝ)^405 := by
    have hnat : (1353651341 : ℕ)^533*100000000000000^405 ≤ 44602660396143^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353651341 2500000000 44602660396143 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621711671/5000000000 : ℝ)^533 ≤ (42756228815281/100000000000000 : ℝ)^405 := by
    have hnat : (2621711671 : ℕ)^533*100000000000000^405 ≤ 42756228815281^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621711671 5000000000 42756228815281 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519315883/2500000000 : ℝ), (1353651341/2500000000 : ℝ), (2621711671/5000000000 : ℝ)] ![(49379338983/390625000000 : ℝ), (44602660396143/100000000000000 : ℝ), (42756228815281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519315883/2500000000 : ℝ)|^533 ≤ (49379338983/390625000000 : ℝ)^405
        have hw : |(-519315883/2500000000 : ℝ)|=(519315883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353651341/2500000000 : ℝ)|^533 ≤ (44602660396143/100000000000000 : ℝ)^405
        have hw : |(1353651341/2500000000 : ℝ)|=(1353651341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621711671/5000000000 : ℝ)|^533 ≤ (42756228815281/100000000000000 : ℝ)^405
        have hw : |(2621711671/5000000000 : ℝ)|=(2621711671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349602527/10000000000 : ℝ)*x 0 + (-270563953/1250000000 : ℝ)*x 1 + (655427987/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349602527/10000000000 : ℝ)^533 ≤ (43899310385997/100000000000000 : ℝ)^405 := by
    have hnat : (5349602527 : ℕ)^533*100000000000000^405 ≤ 43899310385997^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349602527 10000000000 43899310385997 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270563953/1250000000 : ℝ)^533 ≤ (3336113709243/25000000000000 : ℝ)^405 := by
    have hnat : (270563953 : ℕ)^533*25000000000000^405 ≤ 3336113709243^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270563953 1250000000 3336113709243 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655427987/1250000000 : ℝ)^533 ≤ (267226467253/625000000000 : ℝ)^405 := by
    have hnat : (655427987 : ℕ)^533*625000000000^405 ≤ 267226467253^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655427987 1250000000 267226467253 625000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349602527/10000000000 : ℝ), (-270563953/1250000000 : ℝ), (655427987/1250000000 : ℝ)] ![(43899310385997/100000000000000 : ℝ), (3336113709243/25000000000000 : ℝ), (267226467253/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349602527/10000000000 : ℝ)|^533 ≤ (43899310385997/100000000000000 : ℝ)^405
        have hw : |(5349602527/10000000000 : ℝ)|=(5349602527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-270563953/1250000000 : ℝ)|^533 ≤ (3336113709243/25000000000000 : ℝ)^405
        have hw : |(-270563953/1250000000 : ℝ)|=(270563953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655427987/1250000000 : ℝ)|^533 ≤ (267226467253/625000000000 : ℝ)^405
        have hw : |(655427987/1250000000 : ℝ)|=(655427987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349601961/10000000000 : ℝ)*x 0 + (655428083/1250000000 : ℝ)*x 1 + (-1082255681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349601961/10000000000 : ℝ)^533 ≤ (21949652136707/50000000000000 : ℝ)^405 := by
    have hnat : (5349601961 : ℕ)^533*50000000000000^405 ≤ 21949652136707^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349601961 10000000000 21949652136707 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655428083/1250000000 : ℝ)^533 ≤ (42756243002201/100000000000000 : ℝ)^405 := by
    have hnat : (655428083 : ℕ)^533*100000000000000^405 ≤ 42756243002201^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655428083 1250000000 42756243002201 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082255681/5000000000 : ℝ)^533 ≤ (13344452711211/100000000000000 : ℝ)^405 := by
    have hnat : (1082255681 : ℕ)^533*100000000000000^405 ≤ 13344452711211^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082255681 5000000000 13344452711211 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349601961/10000000000 : ℝ), (655428083/1250000000 : ℝ), (-1082255681/5000000000 : ℝ)] ![(21949652136707/50000000000000 : ℝ), (42756243002201/100000000000000 : ℝ), (13344452711211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349601961/10000000000 : ℝ)|^533 ≤ (21949652136707/50000000000000 : ℝ)^405
        have hw : |(5349601961/10000000000 : ℝ)|=(5349601961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655428083/1250000000 : ℝ)|^533 ≤ (42756243002201/100000000000000 : ℝ)^405
        have hw : |(655428083/1250000000 : ℝ)|=(655428083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082255681/5000000000 : ℝ)|^533 ≤ (13344452711211/100000000000000 : ℝ)^405
        have hw : |(-1082255681/5000000000 : ℝ)|=(1082255681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2168329279/5000000000 : ℝ)*x 0 + (33306901/80000000 : ℝ)*x 1 + (903359293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168329279/5000000000 : ℝ)^533 ≤ (1040706784609/3125000000000 : ℝ)^405 := by
    have hnat : (2168329279 : ℕ)^533*3125000000000^405 ≤ 1040706784609^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168329279 5000000000 1040706784609 3125000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33306901/80000000 : ℝ)^533 ≤ (7890596482591/25000000000000 : ℝ)^405 := by
    have hnat : (33306901 : ℕ)^533*25000000000000^405 ≤ 7890596482591^405*80000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33306901 80000000 7890596482591 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903359293/2000000000 : ℝ)^533 ≤ (8783749236229/25000000000000 : ℝ)^405 := by
    have hnat : (903359293 : ℕ)^533*25000000000000^405 ≤ 8783749236229^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903359293 2000000000 8783749236229 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168329279/5000000000 : ℝ), (33306901/80000000 : ℝ), (903359293/2000000000 : ℝ)] ![(1040706784609/3125000000000 : ℝ), (7890596482591/25000000000000 : ℝ), (8783749236229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168329279/5000000000 : ℝ)|^533 ≤ (1040706784609/3125000000000 : ℝ)^405
        have hw : |(2168329279/5000000000 : ℝ)|=(2168329279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33306901/80000000 : ℝ)|^533 ≤ (7890596482591/25000000000000 : ℝ)^405
        have hw : |(33306901/80000000 : ℝ)|=(33306901/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903359293/2000000000 : ℝ)|^533 ≤ (8783749236229/25000000000000 : ℝ)^405
        have hw : |(903359293/2000000000 : ℝ)|=(903359293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077275579/10000000000 : ℝ)*x 0 + (1311008583/2500000000 : ℝ)*x 1 + (676748953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077275579/10000000000 : ℝ)^533 ≤ (1264120726139/10000000000000 : ℝ)^405 := by
    have hnat : (2077275579 : ℕ)^533*10000000000000^405 ≤ 1264120726139^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077275579 10000000000 1264120726139 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311008583/2500000000 : ℝ)^533 ≤ (42762785718211/100000000000000 : ℝ)^405 := by
    have hnat : (1311008583 : ℕ)^533*100000000000000^405 ≤ 42762785718211^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311008583 2500000000 42762785718211 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676748953/1250000000 : ℝ)^533 ≤ (44596007009071/100000000000000 : ℝ)^405 := by
    have hnat : (676748953 : ℕ)^533*100000000000000^405 ≤ 44596007009071^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676748953 1250000000 44596007009071 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077275579/10000000000 : ℝ), (1311008583/2500000000 : ℝ), (676748953/1250000000 : ℝ)] ![(1264120726139/10000000000000 : ℝ), (42762785718211/100000000000000 : ℝ), (44596007009071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077275579/10000000000 : ℝ)|^533 ≤ (1264120726139/10000000000000 : ℝ)^405
        have hw : |(-2077275579/10000000000 : ℝ)|=(2077275579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311008583/2500000000 : ℝ)|^533 ≤ (42762785718211/100000000000000 : ℝ)^405
        have hw : |(1311008583/2500000000 : ℝ)|=(1311008583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676748953/1250000000 : ℝ)|^533 ≤ (44596007009071/100000000000000 : ℝ)^405
        have hw : |(676748953/1250000000 : ℝ)|=(676748953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326427339/2500000000 : ℝ)*x 0 + (-1993944303/10000000000 : ℝ)*x 1 + (5413991733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326427339/2500000000 : ℝ)^533 ≤ (43425896706669/100000000000000 : ℝ)^405 := by
    have hnat : (1326427339 : ℕ)^533*100000000000000^405 ≤ 43425896706669^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326427339 2500000000 43425896706669 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993944303/10000000000 : ℝ)^533 ≤ (2395619016181/20000000000000 : ℝ)^405 := by
    have hnat : (1993944303 : ℕ)^533*20000000000000^405 ≤ 2395619016181^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993944303 10000000000 2395619016181 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413991733/10000000000 : ℝ)^533 ≤ (44596008190689/100000000000000 : ℝ)^405 := by
    have hnat : (5413991733 : ℕ)^533*100000000000000^405 ≤ 44596008190689^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413991733 10000000000 44596008190689 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326427339/2500000000 : ℝ), (-1993944303/10000000000 : ℝ), (5413991733/10000000000 : ℝ)] ![(43425896706669/100000000000000 : ℝ), (2395619016181/20000000000000 : ℝ), (44596008190689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326427339/2500000000 : ℝ)|^533 ≤ (43425896706669/100000000000000 : ℝ)^405
        have hw : |(1326427339/2500000000 : ℝ)|=(1326427339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993944303/10000000000 : ℝ)|^533 ≤ (2395619016181/20000000000000 : ℝ)^405
        have hw : |(-1993944303/10000000000 : ℝ)|=(1993944303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413991733/10000000000 : ℝ)|^533 ≤ (44596008190689/100000000000000 : ℝ)^405
        have hw : |(5413991733/10000000000 : ℝ)|=(5413991733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305709593/10000000000 : ℝ)*x 0 + (5413991619/10000000000 : ℝ)*x 1 + (-1993944137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305709593/10000000000 : ℝ)^533 ≤ (43425899259523/100000000000000 : ℝ)^405 := by
    have hnat : (5305709593 : ℕ)^533*100000000000000^405 ≤ 43425899259523^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305709593 10000000000 43425899259523 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413991619/10000000000 : ℝ)^533 ≤ (11149001738717/25000000000000 : ℝ)^405 := by
    have hnat : (5413991619 : ℕ)^533*25000000000000^405 ≤ 11149001738717^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413991619 10000000000 11149001738717 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993944137/10000000000 : ℝ)^533 ≤ (5989046884269/50000000000000 : ℝ)^405 := by
    have hnat : (1993944137 : ℕ)^533*50000000000000^405 ≤ 5989046884269^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993944137 10000000000 5989046884269 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305709593/10000000000 : ℝ), (5413991619/10000000000 : ℝ), (-1993944137/10000000000 : ℝ)] ![(43425899259523/100000000000000 : ℝ), (11149001738717/25000000000000 : ℝ), (5989046884269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305709593/10000000000 : ℝ)|^533 ≤ (43425899259523/100000000000000 : ℝ)^405
        have hw : |(5305709593/10000000000 : ℝ)|=(5305709593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413991619/10000000000 : ℝ)|^533 ≤ (11149001738717/25000000000000 : ℝ)^405
        have hw : |(5413991619/10000000000 : ℝ)|=(5413991619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993944137/10000000000 : ℝ)|^533 ≤ (5989046884269/50000000000000 : ℝ)^405
        have hw : |(-1993944137/10000000000 : ℝ)|=(1993944137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s7_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4336683183/10000000000 : ℝ)*x 0 + (4515535669/10000000000 : ℝ)*x 1 + (260289453/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336683183/10000000000 : ℝ)^533 ≤ (6660573195429/20000000000000 : ℝ)^405 := by
    have hnat : (4336683183 : ℕ)^533*20000000000000^405 ≤ 6660573195429^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336683183 10000000000 6660573195429 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515535669/10000000000 : ℝ)^533 ≤ (17561045240837/50000000000000 : ℝ)^405 := by
    have hnat : (4515535669 : ℕ)^533*50000000000000^405 ≤ 17561045240837^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515535669 10000000000 17561045240837 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260289453/625000000 : ℝ)^533 ≤ (31575043527343/100000000000000 : ℝ)^405 := by
    have hnat : (260289453 : ℕ)^533*100000000000000^405 ≤ 31575043527343^405*625000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260289453 625000000 31575043527343 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336683183/10000000000 : ℝ), (4515535669/10000000000 : ℝ), (260289453/625000000 : ℝ)] ![(6660573195429/20000000000000 : ℝ), (17561045240837/50000000000000 : ℝ), (31575043527343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336683183/10000000000 : ℝ)|^533 ≤ (6660573195429/20000000000000 : ℝ)^405
        have hw : |(4336683183/10000000000 : ℝ)|=(4336683183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515535669/10000000000 : ℝ)|^533 ≤ (17561045240837/50000000000000 : ℝ)^405
        have hw : |(4515535669/10000000000 : ℝ)|=(4515535669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260289453/625000000 : ℝ)|^533 ≤ (31575043527343/100000000000000 : ℝ)^405
        have hw : |(260289453/625000000 : ℝ)|=(260289453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14681/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (691/6250 : ℝ) ^ (4263/1024 : ℝ) ≤ (5216586493128117/50000000000000000000 : ℝ) := by
    have hpowers : (691/6250 : ℝ)^4263 ≤ (5216586493128117/50000000000000000000 : ℝ)^1024 := by
      have hnat : (691 : ℕ)^4263*50000000000000000000^1024 ≤ 5216586493128117^1024*6250^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        691 6250 5216586493128117 50000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (691/6250 : ℝ)) (X := (5216586493128117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14683/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (33992132074659619/100000000000000000000 : ℝ) := by
    have hpowers : (14683/100000 : ℝ)^4263 ≤ (33992132074659619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14683 : ℕ)^4263*100000000000000000000^1024 ≤ 33992132074659619^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14683 100000 33992132074659619 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14683/100000 : ℝ)) (X := (33992132074659619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005216586493128117/25000000000000000000 : ℝ) ≤ (2000100236662903/2000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (25005216586493128117/25000000000000000000 : ℝ)^1024 ≤ (2000100236662903/2000000000000000 : ℝ)^4263 := by
      have hnat : (25005216586493128117 : ℕ)^1024*2000000000000000^4263 ≤ 2000100236662903^4263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005216586493128117 25000000000000000000 2000100236662903 2000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000100236662903/2000000000000000 : ℝ)) (X := (25005216586493128117/25000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044425305060915853/100000000000000000000 : ℝ) ≤ (625066684020593/625000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (100044425305060915853/100000000000000000000 : ℝ)^1024 ≤ (625066684020593/625000000000000 : ℝ)^4263 := by
      have hnat : (100044425305060915853 : ℕ)^1024*625000000000000^4263 ≤ 625066684020593^4263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044425305060915853 100000000000000000000 625066684020593 625000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625066684020593/625000000000000 : ℝ)) (X := (100044425305060915853/100000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033992132074659619/50000000000000000000 : ℝ) ≤ (10001632705344461/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50033992132074659619/50000000000000000000 : ℝ)^1024 ≤ (10001632705344461/10000000000000000 : ℝ)^4263 := by
      have hnat : (50033992132074659619 : ℕ)^1024*10000000000000000^4263 ≤ 10001632705344461^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033992132074659619 50000000000000000000 10001632705344461 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001632705344461/10000000000000000 : ℝ)) (X := (50033992132074659619/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5216586493128117/50000000000000000000 : ℝ) ≤ ((4028811964924295881/4030000000000000000 : ℝ)+2*(62862334997/40300000000000 : ℝ)*(691/6250 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (4028811964924295881/4030000000000000000 : ℝ)+2*(62862334997/40300000000000 : ℝ)*(691/6250 : ℝ)=(2000100236662903/2000000000000000 : ℝ) by norm_num, show 1+2*(5216586493128117/50000000000000000000 : ℝ)=(25005216586493128117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33992132074659619/100000000000000000000 : ℝ)+(5216586493128117/50000000000000000000 : ℝ) ≤ ((4028811964924295881/4030000000000000000 : ℝ)+(62862334997/40300000000000 : ℝ)*((14683/100000 : ℝ)+(691/6250 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (4028811964924295881/4030000000000000000 : ℝ)+(62862334997/40300000000000 : ℝ)*((14683/100000 : ℝ)+(691/6250 : ℝ))=(625066684020593/625000000000000 : ℝ) by norm_num, show 1+(33992132074659619/100000000000000000000 : ℝ)+(5216586493128117/50000000000000000000 : ℝ)=(100044425305060915853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33992132074659619/100000000000000000000 : ℝ) ≤ ((4028811964924295881/4030000000000000000 : ℝ)+2*(62862334997/40300000000000 : ℝ)*(14683/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (4028811964924295881/4030000000000000000 : ℝ)+2*(62862334997/40300000000000 : ℝ)*(14683/100000 : ℝ)=(10001632705344461/10000000000000000 : ℝ) by norm_num, show 1+2*(33992132074659619/100000000000000000000 : ℝ)=(50033992132074659619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4028811964924295881/4030000000000000000 : ℝ)*(X 1 0+X 2 0)+(62862334997/40300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4028811964924295881/4030000000000000000 : ℝ)) (alpha := (62862334997/40300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4028811964924295881/4030000000000000000 : ℝ)*(X 0 1+X 2 1)+(62862334997/40300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4028811964924295881/4030000000000000000 : ℝ)) (alpha := (62862334997/40300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4028811964924295881/4030000000000000000 : ℝ)*(X 0 2+X 1 2)+(62862334997/40300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (4028811964924295881/4030000000000000000 : ℝ)) (alpha := (62862334997/40300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-519315883/2500000000 : ℝ)*X 0 0+(1353651341/2500000000 : ℝ)*X 0 1+(2621711671/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349602527/10000000000 : ℝ)*X 1 0+(-270563953/1250000000 : ℝ)*X 1 1+(655427987/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349601961/10000000000 : ℝ)*X 2 0+(655428083/1250000000 : ℝ)*X 2 1+(-1082255681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168329279/5000000000 : ℝ)*X 0 0+(33306901/80000000 : ℝ)*X 0 1+(903359293/2000000000 : ℝ)*X 0 2+(2168329279/5000000000 : ℝ)*X 1 0+(33306901/80000000 : ℝ)*X 1 1+(903359293/2000000000 : ℝ)*X 1 2+(2168329279/5000000000 : ℝ)*X 2 0+(33306901/80000000 : ℝ)*X 2 1+(903359293/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2077275579/10000000000 : ℝ)*X 0 0+(1311008583/2500000000 : ℝ)*X 0 1+(676748953/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326427339/2500000000 : ℝ)*X 1 0+(-1993944303/10000000000 : ℝ)*X 1 1+(5413991733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305709593/10000000000 : ℝ)*X 2 0+(5413991619/10000000000 : ℝ)*X 2 1+(-1993944137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336683183/10000000000 : ℝ)*X 0 0+(4515535669/10000000000 : ℝ)*X 0 1+(260289453/625000000 : ℝ)*X 0 2+(4336683183/10000000000 : ℝ)*X 1 0+(4515535669/10000000000 : ℝ)*X 1 1+(260289453/625000000 : ℝ)*X 1 2+(4336683183/10000000000 : ℝ)*X 2 0+(4515535669/10000000000 : ℝ)*X 2 1+(260289453/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (252268144649056620422684613/100750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1878417971/100000000000000 : ℝ)*(base19) + (440438371/50000000000000 : ℝ)*(base23) + (8119887/4000000000000 : ℝ)*(lower2) + (398568531/100000000000000 : ℝ)*(upper3) + (320911209/100000000000000 : ℝ)*(upper5) + (2167816944145403/50000000000000 : ℝ)*(major0) + (2167816944145403/50000000000000 : ℝ)*(major1) + (2167816944145403/50000000000000 : ℝ)*(major2) + (5841785619445871/100000000000000 : ℝ)*(sp0) + (5841831730774061/100000000000000 : ℝ)*(sp1) + (584183272831529/10000000000000 : ℝ)*(sp2) + (2829408668222217/100000000000000 : ℝ)*(sp3) + (599871827/1250000000000 : ℝ)*(sp4) + (25415703943/100000000000000 : ℝ)*(sp7) + (35367926049077/1250000000000 : ℝ)*(f.failure) + (182557300287251/3125000000000 : ℝ)*(f.sum) + (1222880291937/2015000000000000000000000000 : ℝ)*base65 + (4259981021253085043/201500000000000000000000000000000 : ℝ)*base67 + (1979392166000585043/201500000000000000000000000000000 : ℝ)*base69 + (2678140302834085043/201500000000000000000000000000000 : ℝ)*base71 + (1403889089919/1007500000000000000000000000 : ℝ)*base74 + (3431949863799585043/201500000000000000000000000000000 : ℝ)*base75 + (1626586046919585043/201500000000000000000000000000000 : ℝ)*base77 + (2260114598959085043/201500000000000000000000000000000 : ℝ)*base79 + (3376959327747/2015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1142519/125000000000000000000 : ℝ)*base90 + (1142519/125000000000000000000 : ℝ)*base92 + (1142519/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95918417239519416109670361/10075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498316529/100000000000000 : ℝ)*(base19) + (1163409/97656250000 : ℝ)*(base23) + (65883/32000000000 : ℝ)*(lower1) + (86777659/100000000000000 : ℝ)*(upper3) + (182231169/100000000000000 : ℝ)*(lower4) + (214317457/100000000000000 : ℝ)*(upper5) + (218339838873991/5000000000000 : ℝ)*(major0) + (218339838873991/5000000000000 : ℝ)*(major1) + (218339838873991/5000000000000 : ℝ)*(major2) + (5241857851/50000000000000 : ℝ)*(sp2) + (5883822256452771/100000000000000 : ℝ)*(sp4) + (2941910879068121/50000000000000 : ℝ)*(sp5) + (5883810581406253/100000000000000 : ℝ)*(sp6) + (2849770981158913/100000000000000 : ℝ)*(sp7) + (2849770981158913/100000000000000 : ℝ)*(f.failure) + (5883822256452771/100000000000000 : ℝ)*(f.sum) + (10289871049/201500000000000000000000000 : ℝ)*base65 + (118583018216681071/20150000000000000000000000000000 : ℝ)*base67 + (375439062772831071/20150000000000000000000000000000 : ℝ)*base69 + (126640228207381071/20150000000000000000000000000000 : ℝ)*base71 + (276578210341/80600000000000000000000000 : ℝ)*base74 + (223707602540531071/20150000000000000000000000000000 : ℝ)*base75 + (52973913752531071/20150000000000000000000000000000 : ℝ)*base77 + (47120362892231071/20150000000000000000000000000000 : ℝ)*base79 + (2237185340591/403000000000000000000000000 : ℝ)*base81 + (51066011/10000000000000000000000 : ℝ)*base90 + (51066011/10000000000000000000000 : ℝ)*base92 + (51066011/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1304_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_box_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906918269/10000000000 : ℝ)*x 0 + (5391519843/10000000000 : ℝ)*x 1 + (5391520023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906918269/10000000000 : ℝ)^533 ≤ (451795050423/4000000000000 : ℝ)^405 := by
    have hnat : (1906918269 : ℕ)^533*4000000000000^405 ≤ 451795050423^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906918269 10000000000 451795050423 4000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391519843/10000000000 : ℝ)^533 ≤ (44352560891483/100000000000000 : ℝ)^405 := by
    have hnat : (5391519843 : ℕ)^533*100000000000000^405 ≤ 44352560891483^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391519843 10000000000 44352560891483 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391520023/10000000000 : ℝ)^533 ≤ (8870512568043/20000000000000 : ℝ)^405 := by
    have hnat : (5391520023 : ℕ)^533*20000000000000^405 ≤ 8870512568043^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391520023 10000000000 8870512568043 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906918269/10000000000 : ℝ), (5391519843/10000000000 : ℝ), (5391520023/10000000000 : ℝ)] ![(451795050423/4000000000000 : ℝ), (44352560891483/100000000000000 : ℝ), (8870512568043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906918269/10000000000 : ℝ)|^533 ≤ (451795050423/4000000000000 : ℝ)^405
        have hw : |(-1906918269/10000000000 : ℝ)|=(1906918269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391519843/10000000000 : ℝ)|^533 ≤ (44352560891483/100000000000000 : ℝ)^405
        have hw : |(5391519843/10000000000 : ℝ)|=(5391519843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391520023/10000000000 : ℝ)|^533 ≤ (8870512568043/20000000000000 : ℝ)^405
        have hw : |(5391520023/10000000000 : ℝ)|=(5391520023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (660572491/1250000000 : ℝ)*x 0 + (-513307853/2500000000 : ℝ)*x 1 + (5391519797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660572491/1250000000 : ℝ)^533 ≤ (43198443731591/100000000000000 : ℝ)^405 := by
    have hnat : (660572491 : ℕ)^533*100000000000000^405 ≤ 43198443731591^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660572491 1250000000 43198443731591 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513307853/2500000000 : ℝ)^533 ≤ (3112248964847/25000000000000 : ℝ)^405 := by
    have hnat : (513307853 : ℕ)^533*25000000000000^405 ≤ 3112248964847^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513307853 2500000000 3112248964847 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391519797/10000000000 : ℝ)^533 ≤ (44352560393473/100000000000000 : ℝ)^405 := by
    have hnat : (5391519797 : ℕ)^533*100000000000000^405 ≤ 44352560393473^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391519797 10000000000 44352560393473 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660572491/1250000000 : ℝ), (-513307853/2500000000 : ℝ), (5391519797/10000000000 : ℝ)] ![(43198443731591/100000000000000 : ℝ), (3112248964847/25000000000000 : ℝ), (44352560393473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660572491/1250000000 : ℝ)|^533 ≤ (43198443731591/100000000000000 : ℝ)^405
        have hw : |(660572491/1250000000 : ℝ)|=(660572491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513307853/2500000000 : ℝ)|^533 ≤ (3112248964847/25000000000000 : ℝ)^405
        have hw : |(-513307853/2500000000 : ℝ)|=(513307853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391519797/10000000000 : ℝ)|^533 ≤ (44352560393473/100000000000000 : ℝ)^405
        have hw : |(5391519797/10000000000 : ℝ)|=(5391519797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5284579727/10000000000 : ℝ)*x 0 + (2695759997/5000000000 : ℝ)*x 1 + (-256653927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284579727/10000000000 : ℝ)^533 ≤ (21599220784621/50000000000000 : ℝ)^405 := by
    have hnat : (5284579727 : ℕ)^533*50000000000000^405 ≤ 21599220784621^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284579727 10000000000 21599220784621 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695759997/5000000000 : ℝ)^533 ≤ (44352562526253/100000000000000 : ℝ)^405 := by
    have hnat : (2695759997 : ℕ)^533*100000000000000^405 ≤ 44352562526253^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695759997 5000000000 44352562526253 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256653927/1250000000 : ℝ)^533 ≤ (6224497945653/50000000000000 : ℝ)^405 := by
    have hnat : (256653927 : ℕ)^533*50000000000000^405 ≤ 6224497945653^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256653927 1250000000 6224497945653 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284579727/10000000000 : ℝ), (2695759997/5000000000 : ℝ), (-256653927/1250000000 : ℝ)] ![(21599220784621/50000000000000 : ℝ), (44352562526253/100000000000000 : ℝ), (6224497945653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284579727/10000000000 : ℝ)|^533 ≤ (21599220784621/50000000000000 : ℝ)^405
        have hw : |(5284579727/10000000000 : ℝ)|=(5284579727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695759997/5000000000 : ℝ)|^533 ≤ (44352562526253/100000000000000 : ℝ)^405
        have hw : |(2695759997/5000000000 : ℝ)|=(2695759997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256653927/1250000000 : ℝ)|^533 ≤ (6224497945653/50000000000000 : ℝ)^405
        have hw : |(-256653927/1250000000 : ℝ)|=(256653927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4485777707/10000000000 : ℝ)*x 0 + (4266073579/10000000000 : ℝ)*x 1 + (4266073789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485777707/10000000000 : ℝ)^533 ≤ (34817796573917/100000000000000 : ℝ)^405 := by
    have hnat : (4485777707 : ℕ)^533*100000000000000^405 ≤ 34817796573917^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485777707 10000000000 34817796573917 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4266073579/10000000000 : ℝ)^533 ≤ (32591100645273/100000000000000 : ℝ)^405 := by
    have hnat : (4266073579 : ℕ)^533*100000000000000^405 ≤ 32591100645273^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266073579 10000000000 32591100645273 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4266073789/10000000000 : ℝ)^533 ≤ (32591102756633/100000000000000 : ℝ)^405 := by
    have hnat : (4266073789 : ℕ)^533*100000000000000^405 ≤ 32591102756633^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266073789 10000000000 32591102756633 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485777707/10000000000 : ℝ), (4266073579/10000000000 : ℝ), (4266073789/10000000000 : ℝ)] ![(34817796573917/100000000000000 : ℝ), (32591100645273/100000000000000 : ℝ), (32591102756633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485777707/10000000000 : ℝ)|^533 ≤ (34817796573917/100000000000000 : ℝ)^405
        have hw : |(4485777707/10000000000 : ℝ)|=(4485777707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4266073579/10000000000 : ℝ)|^533 ≤ (32591100645273/100000000000000 : ℝ)^405
        have hw : |(4266073579/10000000000 : ℝ)|=(4266073579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4266073789/10000000000 : ℝ)|^533 ≤ (32591102756633/100000000000000 : ℝ)^405
        have hw : |(4266073789/10000000000 : ℝ)|=(4266073789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2250367141/10000000000 : ℝ)*x 0 + (5264011851/10000000000 : ℝ)*x 1 + (263200603/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2250367141/10000000000 : ℝ)^533 ≤ (219459044357/1562500000000 : ℝ)^405 := by
    have hnat : (2250367141 : ℕ)^533*1562500000000^405 ≤ 219459044357^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250367141 10000000000 219459044357 1562500000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264011851/10000000000 : ℝ)^533 ≤ (671520460159/1562500000000 : ℝ)^405 := by
    have hnat : (5264011851 : ℕ)^533*1562500000000^405 ≤ 671520460159^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264011851 10000000000 671520460159 1562500000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263200603/500000000 : ℝ)^533 ≤ (2148865584791/5000000000000 : ℝ)^405 := by
    have hnat : (263200603 : ℕ)^533*5000000000000^405 ≤ 2148865584791^405*500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263200603 500000000 2148865584791 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2250367141/10000000000 : ℝ), (5264011851/10000000000 : ℝ), (263200603/500000000 : ℝ)] ![(219459044357/1562500000000 : ℝ), (671520460159/1562500000000 : ℝ), (2148865584791/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2250367141/10000000000 : ℝ)|^533 ≤ (219459044357/1562500000000 : ℝ)^405
        have hw : |(-2250367141/10000000000 : ℝ)|=(2250367141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264011851/10000000000 : ℝ)|^533 ≤ (671520460159/1562500000000 : ℝ)^405
        have hw : |(5264011851/10000000000 : ℝ)|=(5264011851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263200603/500000000 : ℝ)|^533 ≤ (2148865584791/5000000000000 : ℝ)^405
        have hw : |(263200603/500000000 : ℝ)|=(263200603/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5374284073/10000000000 : ℝ)*x 0 + (-526029901/2500000000 : ℝ)*x 1 + (5264012013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374284073/10000000000 : ℝ)^533 ≤ (11041513943041/25000000000000 : ℝ)^405 := by
    have hnat : (5374284073 : ℕ)^533*25000000000000^405 ≤ 11041513943041^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374284073 10000000000 11041513943041 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526029901/2500000000 : ℝ)^533 ≤ (2571326604387/20000000000000 : ℝ)^405 := by
    have hnat : (526029901 : ℕ)^533*20000000000000^405 ≤ 2571326604387^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526029901 2500000000 2571326604387 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264012013/10000000000 : ℝ)^533 ≤ (42977311190819/100000000000000 : ℝ)^405 := by
    have hnat : (5264012013 : ℕ)^533*100000000000000^405 ≤ 42977311190819^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264012013 10000000000 42977311190819 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374284073/10000000000 : ℝ), (-526029901/2500000000 : ℝ), (5264012013/10000000000 : ℝ)] ![(11041513943041/25000000000000 : ℝ), (2571326604387/20000000000000 : ℝ), (42977311190819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374284073/10000000000 : ℝ)|^533 ≤ (11041513943041/25000000000000 : ℝ)^405
        have hw : |(5374284073/10000000000 : ℝ)|=(5374284073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526029901/2500000000 : ℝ)|^533 ≤ (2571326604387/20000000000000 : ℝ)^405
        have hw : |(-526029901/2500000000 : ℝ)|=(526029901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264012013/10000000000 : ℝ)|^533 ≤ (42977311190819/100000000000000 : ℝ)^405
        have hw : |(5264012013/10000000000 : ℝ)|=(5264012013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2687142049/5000000000 : ℝ)*x 0 + (1316002987/2500000000 : ℝ)*x 1 + (-1052059829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687142049/5000000000 : ℝ)^533 ≤ (11041514010637/25000000000000 : ℝ)^405 := by
    have hnat : (2687142049 : ℕ)^533*25000000000000^405 ≤ 11041514010637^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687142049 5000000000 11041514010637 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316002987/2500000000 : ℝ)^533 ≤ (42977310492413/100000000000000 : ℝ)^405 := by
    have hnat : (1316002987 : ℕ)^533*100000000000000^405 ≤ 42977310492413^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316002987 2500000000 42977310492413 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052059829/5000000000 : ℝ)^533 ≤ (1607079182021/12500000000000 : ℝ)^405 := by
    have hnat : (1052059829 : ℕ)^533*12500000000000^405 ≤ 1607079182021^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052059829 5000000000 1607079182021 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687142049/5000000000 : ℝ), (1316002987/2500000000 : ℝ), (-1052059829/5000000000 : ℝ)] ![(11041514010637/25000000000000 : ℝ), (42977310492413/100000000000000 : ℝ), (1607079182021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687142049/5000000000 : ℝ)|^533 ≤ (11041514010637/25000000000000 : ℝ)^405
        have hw : |(2687142049/5000000000 : ℝ)|=(2687142049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316002987/2500000000 : ℝ)|^533 ≤ (42977310492413/100000000000000 : ℝ)^405
        have hw : |(1316002987/2500000000 : ℝ)|=(1316002987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052059829/5000000000 : ℝ)|^533 ≤ (1607079182021/12500000000000 : ℝ)^405
        have hw : |(-1052059829/5000000000 : ℝ)|=(1052059829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4186668229/10000000000 : ℝ)*x 0 + (2207786781/5000000000 : ℝ)*x 1 + (4415573433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186668229/10000000000 : ℝ)^533 ≤ (7948777546317/25000000000000 : ℝ)^405 := by
    have hnat : (4186668229 : ℕ)^533*25000000000000^405 ≤ 7948777546317^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186668229 10000000000 7948777546317 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207786781/5000000000 : ℝ)^533 ≤ (3410244554901/10000000000000 : ℝ)^405 := by
    have hnat : (2207786781 : ℕ)^533*10000000000000^405 ≤ 3410244554901^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207786781 5000000000 3410244554901 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415573433/10000000000 : ℝ)^533 ≤ (8525611059459/25000000000000 : ℝ)^405 := by
    have hnat : (4415573433 : ℕ)^533*25000000000000^405 ≤ 8525611059459^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415573433 10000000000 8525611059459 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186668229/10000000000 : ℝ), (2207786781/5000000000 : ℝ), (4415573433/10000000000 : ℝ)] ![(7948777546317/25000000000000 : ℝ), (3410244554901/10000000000000 : ℝ), (8525611059459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186668229/10000000000 : ℝ)|^533 ≤ (7948777546317/25000000000000 : ℝ)^405
        have hw : |(4186668229/10000000000 : ℝ)|=(4186668229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207786781/5000000000 : ℝ)|^533 ≤ (3410244554901/10000000000000 : ℝ)^405
        have hw : |(2207786781/5000000000 : ℝ)|=(2207786781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415573433/10000000000 : ℝ)|^533 ≤ (8525611059459/25000000000000 : ℝ)^405
        have hw : |(4415573433/10000000000 : ℝ)|=(4415573433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_8 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089174523/5000000000 : ℝ)*x 0 + (5176415329/10000000000 : ℝ)*x 1 + (1081110883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089174523/5000000000 : ℝ)^533 ≤ (13456839271339/100000000000000 : ℝ)^405 := by
    have hnat : (1089174523 : ℕ)^533*100000000000000^405 ≤ 13456839271339^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089174523 5000000000 13456839271339 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176415329/10000000000 : ℝ)^533 ≤ (42038595006503/100000000000000 : ℝ)^405 := by
    have hnat : (5176415329 : ℕ)^533*100000000000000^405 ≤ 42038595006503^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176415329 10000000000 42038595006503 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081110883/2000000000 : ℝ)^533 ≤ (44504565710487/100000000000000 : ℝ)^405 := by
    have hnat : (1081110883 : ℕ)^533*100000000000000^405 ≤ 44504565710487^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081110883 2000000000 44504565710487 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089174523/5000000000 : ℝ), (5176415329/10000000000 : ℝ), (1081110883/2000000000 : ℝ)] ![(13456839271339/100000000000000 : ℝ), (42038595006503/100000000000000 : ℝ), (44504565710487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089174523/5000000000 : ℝ)|^533 ≤ (13456839271339/100000000000000 : ℝ)^405
        have hw : |(-1089174523/5000000000 : ℝ)|=(1089174523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176415329/10000000000 : ℝ)|^533 ≤ (42038595006503/100000000000000 : ℝ)^405
        have hw : |(5176415329/10000000000 : ℝ)|=(5176415329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081110883/2000000000 : ℝ)|^533 ≤ (44504565710487/100000000000000 : ℝ)^405
        have hw : |(1081110883/2000000000 : ℝ)|=(1081110883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_9 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (82417193/156250000 : ℝ)*x 0 + (-1023747399/5000000000 : ℝ)*x 1 + (5405554569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82417193/156250000 : ℝ)^533 ≤ (8618438217523/20000000000000 : ℝ)^405 := by
    have hnat : (82417193 : ℕ)^533*20000000000000^405 ≤ 8618438217523^405*156250000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82417193 156250000 8618438217523 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023747399/5000000000 : ℝ)^533 ≤ (12403241516137/100000000000000 : ℝ)^405 := by
    have hnat : (1023747399 : ℕ)^533*100000000000000^405 ≤ 12403241516137^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023747399 5000000000 12403241516137 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405554569/10000000000 : ℝ)^533 ≤ (22252283689553/50000000000000 : ℝ)^405 := by
    have hnat : (5405554569 : ℕ)^533*50000000000000^405 ≤ 22252283689553^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405554569 10000000000 22252283689553 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82417193/156250000 : ℝ), (-1023747399/5000000000 : ℝ), (5405554569/10000000000 : ℝ)] ![(8618438217523/20000000000000 : ℝ), (12403241516137/100000000000000 : ℝ), (22252283689553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82417193/156250000 : ℝ)|^533 ≤ (8618438217523/20000000000000 : ℝ)^405
        have hw : |(82417193/156250000 : ℝ)|=(82417193/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023747399/5000000000 : ℝ)|^533 ≤ (12403241516137/100000000000000 : ℝ)^405
        have hw : |(-1023747399/5000000000 : ℝ)|=(1023747399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405554569/10000000000 : ℝ)|^533 ≤ (22252283689553/50000000000000 : ℝ)^405
        have hw : |(5405554569/10000000000 : ℝ)|=(5405554569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_10 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5274700427/10000000000 : ℝ)*x 0 + (2702777297/5000000000 : ℝ)*x 1 + (-2047494663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274700427/10000000000 : ℝ)^533 ≤ (8618438378797/20000000000000 : ℝ)^405 := by
    have hnat : (5274700427 : ℕ)^533*20000000000000^405 ≤ 8618438378797^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274700427 10000000000 8618438378797 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702777297/5000000000 : ℝ)^533 ≤ (8900913529997/20000000000000 : ℝ)^405 := by
    have hnat : (2702777297 : ℕ)^533*20000000000000^405 ≤ 8900913529997^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702777297 5000000000 8900913529997 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047494663/10000000000 : ℝ)^533 ≤ (6201620219937/50000000000000 : ℝ)^405 := by
    have hnat : (2047494663 : ℕ)^533*50000000000000^405 ≤ 6201620219937^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047494663 10000000000 6201620219937 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274700427/10000000000 : ℝ), (2702777297/5000000000 : ℝ), (-2047494663/10000000000 : ℝ)] ![(8618438378797/20000000000000 : ℝ), (8900913529997/20000000000000 : ℝ), (6201620219937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274700427/10000000000 : ℝ)|^533 ≤ (8618438378797/20000000000000 : ℝ)^405
        have hw : |(5274700427/10000000000 : ℝ)|=(5274700427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702777297/5000000000 : ℝ)|^533 ≤ (8900913529997/20000000000000 : ℝ)^405
        have hw : |(2702777297/5000000000 : ℝ)|=(2702777297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047494663/10000000000 : ℝ)|^533 ≤ (6201620219937/50000000000000 : ℝ)^405
        have hw : |(-2047494663/10000000000 : ℝ)|=(2047494663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_11 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4518139661/10000000000 : ℝ)*x 0 + (2124802531/5000000000 : ℝ)*x 1 + (4249605093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4518139661/10000000000 : ℝ)^533 ≤ (7029749633943/20000000000000 : ℝ)^405 := by
    have hnat : (4518139661 : ℕ)^533*20000000000000^405 ≤ 7029749633943^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518139661 10000000000 7029749633943 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124802531/5000000000 : ℝ)^533 ≤ (6485125149849/20000000000000 : ℝ)^405 := by
    have hnat : (2124802531 : ℕ)^533*20000000000000^405 ≤ 6485125149849^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124802531 5000000000 6485125149849 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249605093/10000000000 : ℝ)^533 ≤ (32425626060541/100000000000000 : ℝ)^405 := by
    have hnat : (4249605093 : ℕ)^533*100000000000000^405 ≤ 32425626060541^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249605093 10000000000 32425626060541 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4518139661/10000000000 : ℝ), (2124802531/5000000000 : ℝ), (4249605093/10000000000 : ℝ)] ![(7029749633943/20000000000000 : ℝ), (6485125149849/20000000000000 : ℝ), (32425626060541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4518139661/10000000000 : ℝ)|^533 ≤ (7029749633943/20000000000000 : ℝ)^405
        have hw : |(4518139661/10000000000 : ℝ)|=(4518139661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124802531/5000000000 : ℝ)|^533 ≤ (6485125149849/20000000000000 : ℝ)^405
        have hw : |(2124802531/5000000000 : ℝ)|=(2124802531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249605093/10000000000 : ℝ)|^533 ≤ (32425626060541/100000000000000 : ℝ)^405
        have hw : |(4249605093/10000000000 : ℝ)|=(4249605093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_12 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-989675291/5000000000 : ℝ)*x 0 + (5476822633/10000000000 : ℝ)*x 1 + (2626488019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989675291/5000000000 : ℝ)^533 ≤ (1482856676903/12500000000000 : ℝ)^405 := by
    have hnat : (989675291 : ℕ)^533*12500000000000^405 ≤ 1482856676903^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989675291 5000000000 1482856676903 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476822633/10000000000 : ℝ)^533 ≤ (45278374386511/100000000000000 : ℝ)^405 := by
    have hnat : (5476822633 : ℕ)^533*100000000000000^405 ≤ 45278374386511^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476822633 10000000000 45278374386511 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626488019/5000000000 : ℝ)^533 ≤ (4285877218253/10000000000000 : ℝ)^405 := by
    have hnat : (2626488019 : ℕ)^533*10000000000000^405 ≤ 4285877218253^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626488019 5000000000 4285877218253 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989675291/5000000000 : ℝ), (5476822633/10000000000 : ℝ), (2626488019/5000000000 : ℝ)] ![(1482856676903/12500000000000 : ℝ), (45278374386511/100000000000000 : ℝ), (4285877218253/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989675291/5000000000 : ℝ)|^533 ≤ (1482856676903/12500000000000 : ℝ)^405
        have hw : |(-989675291/5000000000 : ℝ)|=(989675291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476822633/10000000000 : ℝ)|^533 ≤ (45278374386511/100000000000000 : ℝ)^405
        have hw : |(5476822633/10000000000 : ℝ)|=(5476822633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626488019/5000000000 : ℝ)|^533 ≤ (4285877218253/10000000000000 : ℝ)^405
        have hw : |(2626488019/5000000000 : ℝ)|=(2626488019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_13 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (538204571/1000000000 : ℝ)*x 0 + (-1054208883/5000000000 : ℝ)*x 1 + (1313244031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538204571/1000000000 : ℝ)^533 ≤ (44250019668359/100000000000000 : ℝ)^405 := by
    have hnat : (538204571 : ℕ)^533*100000000000000^405 ≤ 44250019668359^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538204571 1000000000 44250019668359 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054208883/5000000000 : ℝ)^533 ≤ (1289120720241/10000000000000 : ℝ)^405 := by
    have hnat : (1054208883 : ℕ)^533*10000000000000^405 ≤ 1289120720241^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054208883 5000000000 1289120720241 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313244031/2500000000 : ℝ)^533 ≤ (21429386552981/50000000000000 : ℝ)^405 := by
    have hnat : (1313244031 : ℕ)^533*50000000000000^405 ≤ 21429386552981^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313244031 2500000000 21429386552981 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538204571/1000000000 : ℝ), (-1054208883/5000000000 : ℝ), (1313244031/2500000000 : ℝ)] ![(44250019668359/100000000000000 : ℝ), (1289120720241/10000000000000 : ℝ), (21429386552981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538204571/1000000000 : ℝ)|^533 ≤ (44250019668359/100000000000000 : ℝ)^405
        have hw : |(538204571/1000000000 : ℝ)|=(538204571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054208883/5000000000 : ℝ)|^533 ≤ (1289120720241/10000000000000 : ℝ)^405
        have hw : |(-1054208883/5000000000 : ℝ)|=(1054208883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313244031/2500000000 : ℝ)|^533 ≤ (21429386552981/50000000000000 : ℝ)^405
        have hw : |(1313244031/2500000000 : ℝ)|=(1313244031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_14 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5382045467/10000000000 : ℝ)*x 0 + (5252976567/10000000000 : ℝ)*x 1 + (-2108417503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382045467/10000000000 : ℝ)^533 ≤ (5531252129879/12500000000000 : ℝ)^405 := by
    have hnat : (5382045467 : ℕ)^533*12500000000000^405 ≤ 5531252129879^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382045467 10000000000 5531252129879 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252976567/10000000000 : ℝ)^533 ≤ (42858777862711/100000000000000 : ℝ)^405 := by
    have hnat : (5252976567 : ℕ)^533*100000000000000^405 ≤ 42858777862711^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252976567 10000000000 42858777862711 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108417503/10000000000 : ℝ)^533 ≤ (12891205086171/100000000000000 : ℝ)^405 := by
    have hnat : (2108417503 : ℕ)^533*100000000000000^405 ≤ 12891205086171^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108417503 10000000000 12891205086171 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382045467/10000000000 : ℝ), (5252976567/10000000000 : ℝ), (-2108417503/10000000000 : ℝ)] ![(5531252129879/12500000000000 : ℝ), (42858777862711/100000000000000 : ℝ), (12891205086171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382045467/10000000000 : ℝ)|^533 ≤ (5531252129879/12500000000000 : ℝ)^405
        have hw : |(5382045467/10000000000 : ℝ)|=(5382045467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252976567/10000000000 : ℝ)|^533 ≤ (42858777862711/100000000000000 : ℝ)^405
        have hw : |(5252976567/10000000000 : ℝ)|=(5252976567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108417503/10000000000 : ℝ)|^533 ≤ (12891205086171/100000000000000 : ℝ)^405
        have hw : |(-2108417503/10000000000 : ℝ)|=(2108417503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_box_15 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (208016729/500000000 : ℝ)*x 0 + (4428501169/10000000000 : ℝ)*x 1 + (1107125603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208016729/500000000 : ℝ)^533 ≤ (1576608937559/5000000000000 : ℝ)^405 := by
    have hnat : (208016729 : ℕ)^533*5000000000000^405 ≤ 1576608937559^405*500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208016729 500000000 1576608937559 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4428501169/10000000000 : ℝ)^533 ≤ (6846780858339/20000000000000 : ℝ)^405 := by
    have hnat : (4428501169 : ℕ)^533*20000000000000^405 ≤ 6846780858339^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4428501169 10000000000 6846780858339 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107125603/2500000000 : ℝ)^533 ≤ (34233916937399/100000000000000 : ℝ)^405 := by
    have hnat : (1107125603 : ℕ)^533*100000000000000^405 ≤ 34233916937399^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107125603 2500000000 34233916937399 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208016729/500000000 : ℝ), (4428501169/10000000000 : ℝ), (1107125603/2500000000 : ℝ)] ![(1576608937559/5000000000000 : ℝ), (6846780858339/20000000000000 : ℝ), (34233916937399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208016729/500000000 : ℝ)|^533 ≤ (1576608937559/5000000000000 : ℝ)^405
        have hw : |(208016729/500000000 : ℝ)|=(208016729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4428501169/10000000000 : ℝ)|^533 ≤ (6846780858339/20000000000000 : ℝ)^405
        have hw : |(4428501169/10000000000 : ℝ)|=(4428501169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107125603/2500000000 : ℝ)|^533 ≤ (34233916937399/100000000000000 : ℝ)^405
        have hw : |(1107125603/2500000000 : ℝ)|=(1107125603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31421/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14717/25000 : ℝ) ∧ (79729/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84203/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5529/50000 : ℝ) ^ (4263/1024 : ℝ) ≤ (10441032361029529/100000000000000000000 : ℝ) := by
    have hpowers : (5529/50000 : ℝ)^4263 ≤ (10441032361029529/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5529 : ℕ)^4263*100000000000000000000^1024 ≤ 10441032361029529^1024*50000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5529 50000 10441032361029529 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5529/50000 : ℝ)) (X := (10441032361029529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14681/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (33972860579085879/100000000000000000000 : ℝ) := by
    have hpowers : (14681/100000 : ℝ)^4263 ≤ (33972860579085879/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14681 : ℕ)^4263*100000000000000000000^1024 ≤ 33972860579085879^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14681 100000 33972860579085879 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14681/100000 : ℝ)) (X := (33972860579085879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010441032361029529/50000000000000000000 : ℝ) ≤ (10000501560829109/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50010441032361029529/50000000000000000000 : ℝ)^1024 ≤ (10000501560829109/10000000000000000 : ℝ)^4263 := by
      have hnat : (50010441032361029529 : ℕ)^1024*10000000000000000^4263 ≤ 10000501560829109^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010441032361029529 50000000000000000000 10000501560829109 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000501560829109/10000000000000000 : ℝ)) (X := (50010441032361029529/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252775868308757213/6250000000000000000 : ℝ) ≤ (2500266667573873/2500000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (6252775868308757213/6250000000000000000 : ℝ)^1024 ≤ (2500266667573873/2500000000000000 : ℝ)^4263 := by
      have hnat : (6252775868308757213 : ℕ)^1024*2500000000000000^4263 ≤ 2500266667573873^4263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252775868308757213 6250000000000000000 2500266667573873 2500000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500266667573873/2500000000000000 : ℝ)) (X := (6252775868308757213/6250000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033972860579085879/50000000000000000000 : ℝ) ≤ (16002610847619/16000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50033972860579085879/50000000000000000000 : ℝ)^1024 ≤ (16002610847619/16000000000000 : ℝ)^4263 := by
      have hnat : (50033972860579085879 : ℕ)^1024*16000000000000^4263 ≤ 16002610847619^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033972860579085879 50000000000000000000 16002610847619 16000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16002610847619/16000000000000 : ℝ)) (X := (50033972860579085879/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10441032361029529/100000000000000000000 : ℝ) ≤ ((36219319193925335479/36230000000000000000 : ℝ)+2*(565109466383/362300000000000 : ℝ)*(5529/50000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (36219319193925335479/36230000000000000000 : ℝ)+2*(565109466383/362300000000000 : ℝ)*(5529/50000 : ℝ)=(10000501560829109/10000000000000000 : ℝ) by norm_num, show 1+2*(10441032361029529/100000000000000000000 : ℝ)=(50010441032361029529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33972860579085879/100000000000000000000 : ℝ)+(10441032361029529/100000000000000000000 : ℝ) ≤ ((36219319193925335479/36230000000000000000 : ℝ)+(565109466383/362300000000000 : ℝ)*((14681/100000 : ℝ)+(5529/50000 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (36219319193925335479/36230000000000000000 : ℝ)+(565109466383/362300000000000 : ℝ)*((14681/100000 : ℝ)+(5529/50000 : ℝ))=(2500266667573873/2500000000000000 : ℝ) by norm_num, show 1+(33972860579085879/100000000000000000000 : ℝ)+(10441032361029529/100000000000000000000 : ℝ)=(6252775868308757213/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33972860579085879/100000000000000000000 : ℝ) ≤ ((36219319193925335479/36230000000000000000 : ℝ)+2*(565109466383/362300000000000 : ℝ)*(14681/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (36219319193925335479/36230000000000000000 : ℝ)+2*(565109466383/362300000000000 : ℝ)*(14681/100000 : ℝ)=(16002610847619/16000000000000 : ℝ) by norm_num, show 1+2*(33972860579085879/100000000000000000000 : ℝ)=(50033972860579085879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36219319193925335479/36230000000000000000 : ℝ)*(X 1 0+X 2 0)+(565109466383/362300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (36219319193925335479/36230000000000000000 : ℝ)) (alpha := (565109466383/362300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36219319193925335479/36230000000000000000 : ℝ)*(X 0 1+X 2 1)+(565109466383/362300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (36219319193925335479/36230000000000000000 : ℝ)) (alpha := (565109466383/362300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36219319193925335479/36230000000000000000 : ℝ)*(X 0 2+X 1 2)+(565109466383/362300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (5529/50000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (36219319193925335479/36230000000000000000 : ℝ)) (alpha := (565109466383/362300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1906918269/10000000000 : ℝ)*X 0 0+(5391519843/10000000000 : ℝ)*X 0 1+(5391520023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660572491/1250000000 : ℝ)*X 1 0+(-513307853/2500000000 : ℝ)*X 1 1+(5391519797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284579727/10000000000 : ℝ)*X 2 0+(2695759997/5000000000 : ℝ)*X 2 1+(-256653927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4485777707/10000000000 : ℝ)*X 0 0+(4266073579/10000000000 : ℝ)*X 0 1+(4266073789/10000000000 : ℝ)*X 0 2+(4485777707/10000000000 : ℝ)*X 1 0+(4266073579/10000000000 : ℝ)*X 1 1+(4266073789/10000000000 : ℝ)*X 1 2+(4485777707/10000000000 : ℝ)*X 2 0+(4266073579/10000000000 : ℝ)*X 2 1+(4266073789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2250367141/10000000000 : ℝ)*X 0 0+(5264011851/10000000000 : ℝ)*X 0 1+(263200603/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374284073/10000000000 : ℝ)*X 1 0+(-526029901/2500000000 : ℝ)*X 1 1+(5264012013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2687142049/5000000000 : ℝ)*X 2 0+(1316002987/2500000000 : ℝ)*X 2 1+(-1052059829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186668229/10000000000 : ℝ)*X 0 0+(2207786781/5000000000 : ℝ)*X 0 1+(4415573433/10000000000 : ℝ)*X 0 2+(4186668229/10000000000 : ℝ)*X 1 0+(2207786781/5000000000 : ℝ)*X 1 1+(4415573433/10000000000 : ℝ)*X 1 2+(4186668229/10000000000 : ℝ)*X 2 0+(2207786781/5000000000 : ℝ)*X 2 1+(4415573433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1089174523/5000000000 : ℝ)*X 0 0+(5176415329/10000000000 : ℝ)*X 0 1+(1081110883/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((82417193/156250000 : ℝ)*X 1 0+(-1023747399/5000000000 : ℝ)*X 1 1+(5405554569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274700427/10000000000 : ℝ)*X 2 0+(2702777297/5000000000 : ℝ)*X 2 1+(-2047494663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4518139661/10000000000 : ℝ)*X 0 0+(2124802531/5000000000 : ℝ)*X 0 1+(4249605093/10000000000 : ℝ)*X 0 2+(4518139661/10000000000 : ℝ)*X 1 0+(2124802531/5000000000 : ℝ)*X 1 1+(4249605093/10000000000 : ℝ)*X 1 2+(4518139661/10000000000 : ℝ)*X 2 0+(2124802531/5000000000 : ℝ)*X 2 1+(4249605093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-989675291/5000000000 : ℝ)*X 0 0+(5476822633/10000000000 : ℝ)*X 0 1+(2626488019/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538204571/1000000000 : ℝ)*X 1 0+(-1054208883/5000000000 : ℝ)*X 1 1+(1313244031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382045467/10000000000 : ℝ)*X 2 0+(5252976567/10000000000 : ℝ)*X 2 1+(-2108417503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((208016729/500000000 : ℝ)*X 0 0+(4428501169/10000000000 : ℝ)*X 0 1+(1107125603/2500000000 : ℝ)*X 0 2+(208016729/500000000 : ℝ)*X 1 0+(4428501169/10000000000 : ℝ)*X 1 1+(1107125603/2500000000 : ℝ)*X 1 2+(208016729/500000000 : ℝ)*X 2 0+(4428501169/10000000000 : ℝ)*X 2 1+(1107125603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31421/50000 : ℝ) ≤ (-227669118252327968847149203780911/362300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4184211/12500000000000 : ℝ)*(upper1) + (777363/5000000000000 : ℝ)*(lower4) + (2374891/100000000000000 : ℝ)*(upper5) + (575537011623197/20000000000000 : ℝ)*(major0) + (575537011623197/20000000000000 : ℝ)*(major1) + (575537011623197/20000000000000 : ℝ)*(major2) + (88392243/6250000000000 : ℝ)*(sp2) + (2134788579/100000000000000 : ℝ)*(sp3) + (779667475078363/20000000000000 : ℝ)*(sp4) + (974580911518059/25000000000000 : ℝ)*(sp5) + (1949169236889073/50000000000000 : ℝ)*(sp6) + (234746842686783/12500000000000 : ℝ)*(sp7) + (1256331109/50000000000000 : ℝ)*(sp12) + (16241981797/100000000000000 : ℝ)*(sp13) + (938988438141421/50000000000000 : ℝ)*(f.failure) + (1949169944027017/50000000000000 : ℝ)*(f.sum) + (2745610066237/3623000000000000000000000000 : ℝ)*base65 + (1088609750275806363/724600000000000000000000000000000 : ℝ)*base67 + (5328580566735593637/724600000000000000000000000000000 : ℝ)*base70 + (1282066054403593637/724600000000000000000000000000000 : ℝ)*base72 + (507346369649/1811500000000000000000000000 : ℝ)*base74 + (86960482949206363/724600000000000000000000000000000 : ℝ)*base75 + (6175439691539193637/724600000000000000000000000000000 : ℝ)*base78 + (4617335207040793637/724600000000000000000000000000000 : ℝ)*base80 + (1261434352609/362300000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (36127487/5000000000000000000000 : ℝ)*base90 + (36127487/5000000000000000000000 : ℝ)*base92 + (36127487/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14717/25000 : ℝ) ≤ (66652312277210628337678694269653/113218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5810451/25000000000000 : ℝ)*(lower1) + (40349403/100000000000000 : ℝ)*(lower4) + (3466329/50000000000000 : ℝ)*(lower5) + (184069416369681/6250000000000 : ℝ)*(major0) + (184069416369681/6250000000000 : ℝ)*(major1) + (184069416369681/6250000000000 : ℝ)*(major2) + (987153381254819/25000000000000 : ℝ)*(sp0) + (123393544001367/3125000000000 : ℝ)*(sp1) + (78972350412863/2000000000000 : ℝ)*(sp2) + (1921977340766959/100000000000000 : ℝ)*(sp3) + (1525910069/100000000000000 : ℝ)*(sp6) + (295071043/20000000000000 : ℝ)*(sp7) + (6409627369/25000000000000 : ℝ)*(sp9) + (690191743/12500000000000 : ℝ)*(sp12) + (960989408061087/50000000000000 : ℝ)*(f.failure) + (197430952327661/5000000000000 : ℝ)*(f.sum) + (21690951443657/4528750000000000000000000000 : ℝ)*base65 + (485898020455550301/226437500000000000000000000000000 : ℝ)*base68 + (361841487415387199/226437500000000000000000000000000 : ℝ)*base69 + (2260539111870512199/226437500000000000000000000000000 : ℝ)*base71 + (13605451546057/18115000000000000000000000000 : ℝ)*base74 + (1066752381260612801/226437500000000000000000000000000 : ℝ)*base76 + (1763441586380262199/226437500000000000000000000000000 : ℝ)*base77 + (2035438867737199699/226437500000000000000000000000000 : ℝ)*base79 + (10410813250549/2264375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16273989/5000000000000000000000 : ℝ)*base90 + (16273989/5000000000000000000000 : ℝ)*base92 + (16273989/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79729/100000 : ℝ) ≤ (361083704457349964786746543028967/452875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158338473/100000000000000 : ℝ)*(lower3) + (5619953/12500000000000 : ℝ)*(upper4) + (9993403/10000000000000 : ℝ)*(lower5) + (1629341255488691/50000000000000 : ℝ)*(major0) + (1629341255488691/50000000000000 : ℝ)*(major1) + (1629341255488691/50000000000000 : ℝ)*(major2) + (7687048763/100000000000000 : ℝ)*(sp0) + (42098123789/25000000000000 : ℝ)*(sp1) + (180774932363/100000000000000 : ℝ)*(sp2) + (8092855599/10000000000000 : ℝ)*(sp3) + (109104110755281/2500000000000 : ℝ)*(sp8) + (4364003724764847/100000000000000 : ℝ)*(sp9) + (109099783558191/2500000000000 : ℝ)*(sp10) + (26581685418491/1250000000000 : ℝ)*(sp11) + (212661576203527/10000000000000 : ℝ)*(f.failure) + (1091043029315001/25000000000000 : ℝ)*(f.sum) + (3469278102161/18115000000000000000000000000 : ℝ)*base65 + (22429258676467632011/1811500000000000000000000000000000 : ℝ)*base68 + (3366284740592367989/1811500000000000000000000000000000 : ℝ)*base69 + (12328494419972132011/1811500000000000000000000000000000 : ℝ)*base72 + (65440188953387/9057500000000000000000000000 : ℝ)*base74 + (25066173517156632011/1811500000000000000000000000000000 : ℝ)*base76 + (20235605455265632011/1811500000000000000000000000000000 : ℝ)*base78 + (16813865570717132011/1811500000000000000000000000000000 : ℝ)*base80 + (1393556953243/566093750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12283331/1000000000000000000000 : ℝ)*base89 + (12283331/1000000000000000000000 : ℝ)*base91 + (12283331/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84203/100000 : ℝ) ≤ (-190660775433797005754105925223431/226437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177482187/50000000000000 : ℝ)*(lower0) + (324811691/50000000000000 : ℝ)*(lower1) + (10821413/20000000000000 : ℝ)*(lower2) + (411840194626763/12500000000000 : ℝ)*(major0) + (411840194626763/12500000000000 : ℝ)*(major1) + (411840194626763/12500000000000 : ℝ)*(major2) + (1136340527/6250000000000 : ℝ)*(sp0) + (782081976953/100000000000000 : ℝ)*(sp5) + (4472867511/781250000000 : ℝ)*(sp6) + (47127967707/100000000000000 : ℝ)*(sp7) + (4467356819631837/100000000000000 : ℝ)*(sp12) + (1116648229775829/25000000000000 : ℝ)*(sp13) + (2233401237019431/50000000000000 : ℝ)*(sp14) + (430017542118761/20000000000000 : ℝ)*(sp15) + (268766854820189/12500000000000 : ℝ)*(f.failure) + (4467375001080269/100000000000000 : ℝ)*(f.sum) + (16117166995183/18115000000000000000000000000 : ℝ)*base66 + (4383193842383724477/452875000000000000000000000000000 : ℝ)*base67 + (272022599532349477/452875000000000000000000000000000 : ℝ)*base69 + (2010274506910224477/452875000000000000000000000000000 : ℝ)*base71 + (1008129841428933/18115000000000000000000000000 : ℝ)*base74 + (1265862298068224477/452875000000000000000000000000000 : ℝ)*base75 + (1895919375390650523/452875000000000000000000000000000 : ℝ)*base78 + (1738719024871650523/452875000000000000000000000000000 : ℝ)*base80 + (151377541667617/18115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9455183/1250000000000000000000 : ℝ)*base90 + (9455183/1250000000000000000000 : ℝ)*base92 + (9455183/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1304_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14717/25000 : ℝ) else (79729/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84203/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1304_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1304_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14717/25000 : ℝ) else (79729/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84203/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1304_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1304_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1304_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14717/25000 : ℝ) else (79729/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84203/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

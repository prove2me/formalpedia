-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1160_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:32.360234+00:00
-- url     : https://prove2.me/submissions/00a18b1b-d8ba-46a3-b065-de3b66f734db

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
theorem support_rectangle_w1160_s3_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215470033/1000000000 : ℝ)*x 0 + (5427343511/10000000000 : ℝ)*x 1 + (2616876159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215470033/1000000000 : ℝ)^8353 ≤ (13087495857947/100000000000000 : ℝ)^6305 := by
    have hnat : (215470033 : ℕ)^8353*100000000000000^6305 ≤ 13087495857947^6305*1000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215470033 1000000000 13087495857947 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427343511/10000000000 : ℝ)^8353 ≤ (11125397890169/25000000000000 : ℝ)^6305 := by
    have hnat : (5427343511 : ℕ)^8353*25000000000000^6305 ≤ 11125397890169^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427343511 10000000000 11125397890169 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616876159/5000000000 : ℝ)^8353 ≤ (21205456283503/50000000000000 : ℝ)^6305 := by
    have hnat : (2616876159 : ℕ)^8353*50000000000000^6305 ≤ 21205456283503^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616876159 5000000000 21205456283503 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215470033/1000000000 : ℝ), (5427343511/10000000000 : ℝ), (2616876159/5000000000 : ℝ)] ![(13087495857947/100000000000000 : ℝ), (11125397890169/25000000000000 : ℝ), (21205456283503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215470033/1000000000 : ℝ)|^8353 ≤ (13087495857947/100000000000000 : ℝ)^6305
        have hw : |(-215470033/1000000000 : ℝ)|=(215470033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427343511/10000000000 : ℝ)|^8353 ≤ (11125397890169/25000000000000 : ℝ)^6305
        have hw : |(5427343511/10000000000 : ℝ)|=(5427343511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616876159/5000000000 : ℝ)|^8353 ≤ (21205456283503/50000000000000 : ℝ)^6305
        have hw : |(2616876159/5000000000 : ℝ)|=(2616876159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353362947/10000000000 : ℝ)*x 0 + (-35212797/156250000 : ℝ)*x 1 + (5233752127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353362947/10000000000 : ℝ)^8353 ≤ (43699733006543/100000000000000 : ℝ)^6305 := by
    have hnat : (5353362947 : ℕ)^8353*100000000000000^6305 ≤ 43699733006543^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353362947 10000000000 43699733006543 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35212797/156250000 : ℝ)^8353 ≤ (13889356462221/100000000000000 : ℝ)^6305 := by
    have hnat : (35212797 : ℕ)^8353*100000000000000^6305 ≤ 13889356462221^6305*156250000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35212797 156250000 13889356462221 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233752127/10000000000 : ℝ)^8353 ≤ (2650681907283/6250000000000 : ℝ)^6305 := by
    have hnat : (5233752127 : ℕ)^8353*6250000000000^6305 ≤ 2650681907283^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233752127 10000000000 2650681907283 6250000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353362947/10000000000 : ℝ), (-35212797/156250000 : ℝ), (5233752127/10000000000 : ℝ)] ![(43699733006543/100000000000000 : ℝ), (13889356462221/100000000000000 : ℝ), (2650681907283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353362947/10000000000 : ℝ)|^8353 ≤ (43699733006543/100000000000000 : ℝ)^6305
        have hw : |(5353362947/10000000000 : ℝ)|=(5353362947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35212797/156250000 : ℝ)|^8353 ≤ (13889356462221/100000000000000 : ℝ)^6305
        have hw : |(-35212797/156250000 : ℝ)|=(35212797/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233752127/10000000000 : ℝ)|^8353 ≤ (2650681907283/6250000000000 : ℝ)^6305
        have hw : |(5233752127/10000000000 : ℝ)|=(5233752127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338340757/2500000000 : ℝ)*x 0 + (5233752157/10000000000 : ℝ)*x 1 + (-1126809431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338340757/2500000000 : ℝ)^8353 ≤ (43699733882523/100000000000000 : ℝ)^6305 := by
    have hnat : (1338340757 : ℕ)^8353*100000000000000^6305 ≤ 43699733882523^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338340757 2500000000 43699733882523 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233752157/10000000000 : ℝ)^8353 ≤ (662670481853/1562500000000 : ℝ)^6305 := by
    have hnat : (5233752157 : ℕ)^8353*1562500000000^6305 ≤ 662670481853^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233752157 10000000000 662670481853 1562500000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126809431/5000000000 : ℝ)^8353 ≤ (13889355270123/100000000000000 : ℝ)^6305 := by
    have hnat : (1126809431 : ℕ)^8353*100000000000000^6305 ≤ 13889355270123^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126809431 5000000000 13889355270123 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338340757/2500000000 : ℝ), (5233752157/10000000000 : ℝ), (-1126809431/5000000000 : ℝ)] ![(43699733882523/100000000000000 : ℝ), (662670481853/1562500000000 : ℝ), (13889355270123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338340757/2500000000 : ℝ)|^8353 ≤ (43699733882523/100000000000000 : ℝ)^6305
        have hw : |(1338340757/2500000000 : ℝ)|=(1338340757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233752157/10000000000 : ℝ)|^8353 ≤ (662670481853/1562500000000 : ℝ)^6305
        have hw : |(5233752157/10000000000 : ℝ)|=(5233752157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126809431/5000000000 : ℝ)|^8353 ≤ (13889355270123/100000000000000 : ℝ)^6305
        have hw : |(-1126809431/5000000000 : ℝ)|=(1126809431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179999401/5000000000 : ℝ)*x 0 + (1042746171/2500000000 : ℝ)*x 1 + (4557489567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179999401/5000000000 : ℝ)^8353 ≤ (33295363953199/100000000000000 : ℝ)^6305 := by
    have hnat : (2179999401 : ℕ)^8353*100000000000000^6305 ≤ 33295363953199^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179999401 5000000000 33295363953199 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042746171/2500000000 : ℝ)^8353 ≤ (31396692482237/100000000000000 : ℝ)^6305 := by
    have hnat : (1042746171 : ℕ)^8353*100000000000000^6305 ≤ 31396692482237^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042746171 2500000000 31396692482237 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4557489567/10000000000 : ℝ)^8353 ≤ (1103373236209/3125000000000 : ℝ)^6305 := by
    have hnat : (4557489567 : ℕ)^8353*3125000000000^6305 ≤ 1103373236209^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557489567 10000000000 1103373236209 3125000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179999401/5000000000 : ℝ), (1042746171/2500000000 : ℝ), (4557489567/10000000000 : ℝ)] ![(33295363953199/100000000000000 : ℝ), (31396692482237/100000000000000 : ℝ), (1103373236209/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179999401/5000000000 : ℝ)|^8353 ≤ (33295363953199/100000000000000 : ℝ)^6305
        have hw : |(2179999401/5000000000 : ℝ)|=(2179999401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042746171/2500000000 : ℝ)|^8353 ≤ (31396692482237/100000000000000 : ℝ)^6305
        have hw : |(1042746171/2500000000 : ℝ)|=(1042746171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4557489567/10000000000 : ℝ)|^8353 ≤ (1103373236209/3125000000000 : ℝ)^6305
        have hw : |(4557489567/10000000000 : ℝ)|=(4557489567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16833731/78125000 : ℝ)*x 0 + (2617247127/5000000000 : ℝ)*x 1 + (2713298737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16833731/78125000 : ℝ)^8353 ≤ (13087634570099/100000000000000 : ℝ)^6305 := by
    have hnat : (16833731 : ℕ)^8353*100000000000000^6305 ≤ 13087634570099^6305*78125000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16833731 78125000 13087634570099 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617247127/5000000000 : ℝ)^8353 ≤ (42418877796339/100000000000000 : ℝ)^6305 := by
    have hnat : (2617247127 : ℕ)^8353*100000000000000^6305 ≤ 42418877796339^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617247127 5000000000 42418877796339 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713298737/5000000000 : ℝ)^8353 ≤ (22246743809611/50000000000000 : ℝ)^6305 := by
    have hnat : (2713298737 : ℕ)^8353*50000000000000^6305 ≤ 22246743809611^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713298737 5000000000 22246743809611 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16833731/78125000 : ℝ), (2617247127/5000000000 : ℝ), (2713298737/5000000000 : ℝ)] ![(13087634570099/100000000000000 : ℝ), (42418877796339/100000000000000 : ℝ), (22246743809611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16833731/78125000 : ℝ)|^8353 ≤ (13087634570099/100000000000000 : ℝ)^6305
        have hw : |(-16833731/78125000 : ℝ)|=(16833731/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617247127/5000000000 : ℝ)|^8353 ≤ (42418877796339/100000000000000 : ℝ)^6305
        have hw : |(2617247127/5000000000 : ℝ)|=(2617247127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713298737/5000000000 : ℝ)|^8353 ≤ (22246743809611/50000000000000 : ℝ)^6305
        have hw : |(2713298737/5000000000 : ℝ)|=(2713298737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132606337/250000000 : ℝ)*x 0 + (-1030386817/5000000000 : ℝ)*x 1 + (678324687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132606337/250000000 : ℝ)^8353 ≤ (21584713936863/50000000000000 : ℝ)^6305 := by
    have hnat : (132606337 : ℕ)^8353*50000000000000^6305 ≤ 21584713936863^6305*250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132606337 250000000 21584713936863 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030386817/5000000000 : ℝ)^8353 ≤ (12337084254807/100000000000000 : ℝ)^6305 := by
    have hnat : (1030386817 : ℕ)^8353*100000000000000^6305 ≤ 12337084254807^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030386817 5000000000 12337084254807 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678324687/1250000000 : ℝ)^8353 ≤ (8898697571639/20000000000000 : ℝ)^6305 := by
    have hnat : (678324687 : ℕ)^8353*20000000000000^6305 ≤ 8898697571639^6305*1250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678324687 1250000000 8898697571639 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132606337/250000000 : ℝ), (-1030386817/5000000000 : ℝ), (678324687/1250000000 : ℝ)] ![(21584713936863/50000000000000 : ℝ), (12337084254807/100000000000000 : ℝ), (8898697571639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132606337/250000000 : ℝ)|^8353 ≤ (21584713936863/50000000000000 : ℝ)^6305
        have hw : |(132606337/250000000 : ℝ)|=(132606337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030386817/5000000000 : ℝ)|^8353 ≤ (12337084254807/100000000000000 : ℝ)^6305
        have hw : |(-1030386817/5000000000 : ℝ)|=(1030386817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678324687/1250000000 : ℝ)|^8353 ≤ (8898697571639/20000000000000 : ℝ)^6305
        have hw : |(678324687/1250000000 : ℝ)|=(678324687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304253357/10000000000 : ℝ)*x 0 + (5426597711/10000000000 : ℝ)*x 1 + (-1030386753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304253357/10000000000 : ℝ)^8353 ≤ (43169426547509/100000000000000 : ℝ)^6305 := by
    have hnat : (5304253357 : ℕ)^8353*100000000000000^6305 ≤ 43169426547509^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304253357 10000000000 43169426547509 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426597711/10000000000 : ℝ)^8353 ≤ (44493490193613/100000000000000 : ℝ)^6305 := by
    have hnat : (5426597711 : ℕ)^8353*100000000000000^6305 ≤ 44493490193613^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426597711 10000000000 44493490193613 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030386753/5000000000 : ℝ)^8353 ≤ (12337083239611/100000000000000 : ℝ)^6305 := by
    have hnat : (1030386753 : ℕ)^8353*100000000000000^6305 ≤ 12337083239611^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030386753 5000000000 12337083239611 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304253357/10000000000 : ℝ), (5426597711/10000000000 : ℝ), (-1030386753/5000000000 : ℝ)] ![(43169426547509/100000000000000 : ℝ), (44493490193613/100000000000000 : ℝ), (12337083239611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304253357/10000000000 : ℝ)|^8353 ≤ (43169426547509/100000000000000 : ℝ)^6305
        have hw : |(5304253357/10000000000 : ℝ)|=(5304253357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426597711/10000000000 : ℝ)|^8353 ≤ (44493490193613/100000000000000 : ℝ)^6305
        have hw : |(5426597711/10000000000 : ℝ)|=(5426597711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030386753/5000000000 : ℝ)|^8353 ≤ (12337083239611/100000000000000 : ℝ)^6305
        have hw : |(-1030386753/5000000000 : ℝ)|=(1030386753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s3_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872006647/2000000000 : ℝ)*x 0 + (4556008307/10000000000 : ℝ)*x 1 + (2086237051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872006647/2000000000 : ℝ)^8353 ≤ (33295712314743/100000000000000 : ℝ)^6305 := by
    have hnat : (872006647 : ℕ)^8353*100000000000000^6305 ≤ 33295712314743^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872006647 2000000000 33295712314743 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4556008307/10000000000 : ℝ)^8353 ≤ (4411592643331/12500000000000 : ℝ)^6305 := by
    have hnat : (4556008307 : ℕ)^8353*12500000000000^6305 ≤ 4411592643331^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556008307 10000000000 4411592643331 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086237051/5000000000 : ℝ)^8353 ≤ (6282309303681/20000000000000 : ℝ)^6305 := by
    have hnat : (2086237051 : ℕ)^8353*20000000000000^6305 ≤ 6282309303681^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086237051 5000000000 6282309303681 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872006647/2000000000 : ℝ), (4556008307/10000000000 : ℝ), (2086237051/5000000000 : ℝ)] ![(33295712314743/100000000000000 : ℝ), (4411592643331/12500000000000 : ℝ), (6282309303681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872006647/2000000000 : ℝ)|^8353 ≤ (33295712314743/100000000000000 : ℝ)^6305
        have hw : |(872006647/2000000000 : ℝ)|=(872006647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4556008307/10000000000 : ℝ)|^8353 ≤ (4411592643331/12500000000000 : ℝ)^6305
        have hw : |(4556008307/10000000000 : ℝ)|=(4556008307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086237051/5000000000 : ℝ)|^8353 ≤ (6282309303681/20000000000000 : ℝ)^6305
        have hw : |(2086237051/5000000000 : ℝ)|=(2086237051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (334/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2957/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16449/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16449/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16449/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16449/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16449/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16449/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9151/100000 : ℝ) ^ (261/64 : ℝ) ≤ (2908767148238163/50000000000000000000 : ℝ) := by
    have hpowers : (9151/100000 : ℝ)^261 ≤ (2908767148238163/50000000000000000000 : ℝ)^64 := by
      have hnat : (9151 : ℕ)^261*50000000000000000000^64 ≤ 2908767148238163^64*100000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9151 100000 2908767148238163 50000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9151/100000 : ℝ)) (X := (2908767148238163/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (16449/100000 : ℝ) ^ (261/64 : ℝ) ≤ (63579762442524251/100000000000000000000 : ℝ) := by
    have hpowers : (16449/100000 : ℝ)^261 ≤ (63579762442524251/100000000000000000000 : ℝ)^64 := by
      have hnat : (16449 : ℕ)^261*100000000000000000000^64 ≤ 63579762442524251^64*100000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16449 100000 63579762442524251 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16449/100000 : ℝ)) (X := (63579762442524251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002908767148238163/25000000000000000000 : ℝ) ≤ (2500071322959267/2500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (25002908767148238163/25000000000000000000 : ℝ)^64 ≤ (2500071322959267/2500000000000000 : ℝ)^261 := by
      have hnat : (25002908767148238163 : ℕ)^64*2500000000000000^261 ≤ 2500071322959267^261*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002908767148238163 25000000000000000000 2500071322959267 2500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071322959267/2500000000000000 : ℝ)) (X := (25002908767148238163/25000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100069397296739000577/100000000000000000000 : ℝ) ≤ (10001701250668997/10000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (100069397296739000577/100000000000000000000 : ℝ)^64 ≤ (10001701250668997/10000000000000000 : ℝ)^261 := by
      have hnat : (100069397296739000577 : ℕ)^64*10000000000000000^261 ≤ 10001701250668997^261*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100069397296739000577 100000000000000000000 10001701250668997 10000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001701250668997/10000000000000000 : ℝ)) (X := (100069397296739000577/100000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063579762442524251/50000000000000000000 : ℝ) ≤ (5001558604750463/5000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50063579762442524251/50000000000000000000 : ℝ)^64 ≤ (5001558604750463/5000000000000000 : ℝ)^261 := by
      have hnat : (50063579762442524251 : ℕ)^64*5000000000000000^261 ≤ 5001558604750463^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063579762442524251 50000000000000000000 5001558604750463 5000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001558604750463/5000000000000000 : ℝ)) (X := (50063579762442524251/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2908767148238163/50000000000000000000 : ℝ) ≤ ((36478083590642478853/36490000000000000000 : ℝ)+2*(1415958831929/729800000000000 : ℝ)*(9151/100000 : ℝ))^(261/64 : ℝ) := by
    rw [show (36478083590642478853/36490000000000000000 : ℝ)+2*(1415958831929/729800000000000 : ℝ)*(9151/100000 : ℝ)=(2500071322959267/2500000000000000 : ℝ) by norm_num, show 1+2*(2908767148238163/50000000000000000000 : ℝ)=(25002908767148238163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63579762442524251/100000000000000000000 : ℝ)+(2908767148238163/50000000000000000000 : ℝ) ≤ ((36478083590642478853/36490000000000000000 : ℝ)+(1415958831929/729800000000000 : ℝ)*((16449/100000 : ℝ)+(9151/100000 : ℝ)))^(261/64 : ℝ) := by
    rw [show (36478083590642478853/36490000000000000000 : ℝ)+(1415958831929/729800000000000 : ℝ)*((16449/100000 : ℝ)+(9151/100000 : ℝ))=(10001701250668997/10000000000000000 : ℝ) by norm_num, show 1+(63579762442524251/100000000000000000000 : ℝ)+(2908767148238163/50000000000000000000 : ℝ)=(100069397296739000577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63579762442524251/100000000000000000000 : ℝ) ≤ ((36478083590642478853/36490000000000000000 : ℝ)+2*(1415958831929/729800000000000 : ℝ)*(16449/100000 : ℝ))^(261/64 : ℝ) := by
    rw [show (36478083590642478853/36490000000000000000 : ℝ)+2*(1415958831929/729800000000000 : ℝ)*(16449/100000 : ℝ)=(5001558604750463/5000000000000000 : ℝ) by norm_num, show 1+2*(63579762442524251/100000000000000000000 : ℝ)=(50063579762442524251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36478083590642478853/36490000000000000000 : ℝ)*(X 1 0+X 2 0)+(1415958831929/729800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (9151/100000 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (36478083590642478853/36490000000000000000 : ℝ)) (alpha := (1415958831929/729800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36478083590642478853/36490000000000000000 : ℝ)*(X 0 1+X 2 1)+(1415958831929/729800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (9151/100000 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (36478083590642478853/36490000000000000000 : ℝ)) (alpha := (1415958831929/729800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36478083590642478853/36490000000000000000 : ℝ)*(X 0 2+X 1 2)+(1415958831929/729800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (9151/100000 : ℝ)) (hi := (16449/100000 : ℝ)) (c := (36478083590642478853/36490000000000000000 : ℝ)) (alpha := (1415958831929/729800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215470033/1000000000 : ℝ)*X 0 0+(5427343511/10000000000 : ℝ)*X 0 1+(2616876159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353362947/10000000000 : ℝ)*X 1 0+(-35212797/156250000 : ℝ)*X 1 1+(5233752127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338340757/2500000000 : ℝ)*X 2 0+(5233752157/10000000000 : ℝ)*X 2 1+(-1126809431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179999401/5000000000 : ℝ)*X 0 0+(1042746171/2500000000 : ℝ)*X 0 1+(4557489567/10000000000 : ℝ)*X 0 2+(2179999401/5000000000 : ℝ)*X 1 0+(1042746171/2500000000 : ℝ)*X 1 1+(4557489567/10000000000 : ℝ)*X 1 2+(2179999401/5000000000 : ℝ)*X 2 0+(1042746171/2500000000 : ℝ)*X 2 1+(4557489567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16833731/78125000 : ℝ)*X 0 0+(2617247127/5000000000 : ℝ)*X 0 1+(2713298737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132606337/250000000 : ℝ)*X 1 0+(-1030386817/5000000000 : ℝ)*X 1 1+(678324687/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304253357/10000000000 : ℝ)*X 2 0+(5426597711/10000000000 : ℝ)*X 2 1+(-1030386753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872006647/2000000000 : ℝ)*X 0 0+(4556008307/10000000000 : ℝ)*X 0 1+(2086237051/5000000000 : ℝ)*X 0 2+(872006647/2000000000 : ℝ)*X 1 0+(4556008307/10000000000 : ℝ)*X 1 1+(2086237051/5000000000 : ℝ)*X 1 2+(872006647/2000000000 : ℝ)*X 2 0+(4556008307/10000000000 : ℝ)*X 2 1+(2086237051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174227826839903852118257073/45612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (534201621/50000000000000 : ℝ)*(base19) + (1039062359/100000000000000 : ℝ)*(base23) + (57548243/100000000000000 : ℝ)*(lower2) + (2943301/6250000000000 : ℝ)*(upper3) + (137556271/100000000000000 : ℝ)*(upper5) + (96910787090747/2500000000000 : ℝ)*(major0) + (96910787090747/2500000000000 : ℝ)*(major1) + (96910787090747/2500000000000 : ℝ)*(major2) + (1291384586936479/25000000000000 : ℝ)*(sp0) + (645694515904599/12500000000000 : ℝ)*(sp1) + (2582778078288837/50000000000000 : ℝ)*(sp2) + (103491911567131/4000000000000 : ℝ)*(sp3) + (18847894117/100000000000000 : ℝ)*(sp4) + (7855116823/100000000000000 : ℝ)*(sp7) + (1293652822147549/50000000000000 : ℝ)*(f.failure) + (2582778597820017/50000000000000 : ℝ)*(f.sum) + (18308364966279/3649000000000000000000000000 : ℝ)*base66 + (605564502582748191/91225000000000000000000000000000 : ℝ)*base67 + (33943278698201809/91225000000000000000000000000000 : ℝ)*base70 + (140550306321651809/91225000000000000000000000000000 : ℝ)*base72 + (3927317360973/3649000000000000000000000000 : ℝ)*base74 + (1793761363594751809/91225000000000000000000000000000 : ℝ)*base76 + (981087498930451809/91225000000000000000000000000000 : ℝ)*base78 + (886602452593348191/91225000000000000000000000000000 : ℝ)*base79 + (1827064288243/729800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15499019/5000000000000000000000 : ℝ)*base89 + (15499019/5000000000000000000000 : ℝ)*base91 + (15499019/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (475098064943992394624947563/44500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1066955083/50000000000000 : ℝ)*(base19) + (286029091/12500000000000 : ℝ)*(base23) + (239274753/100000000000000 : ℝ)*(upper3) + (27887609/25000000000000 : ℝ)*(lower4) + (120282733/50000000000000 : ℝ)*(upper5) + (3906430576318637/100000000000000 : ℝ)*(major0) + (3906430576318637/100000000000000 : ℝ)*(major1) + (3906430576318637/100000000000000 : ℝ)*(major2) + (19396380451/50000000000000 : ℝ)*(sp1) + (4578392789/10000000000000 : ℝ)*(sp2) + (2602766200799829/50000000000000 : ℝ)*(sp4) + (520549147492859/10000000000000 : ℝ)*(sp5) + (5205484329439041/100000000000000 : ℝ)*(sp6) + (651832098789727/25000000000000 : ℝ)*(sp7) + (651832098789727/25000000000000 : ℝ)*(f.failure) + (2602766200799829/50000000000000 : ℝ)*(f.sum) + (2140416541387/890000000000000000000000000 : ℝ)*base66 + (458699093843632521/89000000000000000000000000000000 : ℝ)*base67 + (430780311336367479/89000000000000000000000000000000 : ℝ)*base70 + (467762861010367479/89000000000000000000000000000000 : ℝ)*base72 + (3207671917453/890000000000000000000000000 : ℝ)*base73 + (578863696785632521/89000000000000000000000000000000 : ℝ)*base75 + (400040105517367479/89000000000000000000000000000000 : ℝ)*base78 + (414856264817367479/89000000000000000000000000000000 : ℝ)*base80 + (238574770553/890000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14743463/2500000000000000000000 : ℝ)*base90 + (14743463/2500000000000000000000 : ℝ)*base92 + (14743463/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1160_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (334/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1160_s4_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431511401/2000000000 : ℝ)*x 0 + (337565331/625000000 : ℝ)*x 1 + (2629090733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431511401/2000000000 : ℝ)^8353 ≤ (13110488102969/100000000000000 : ℝ)^6305 := by
    have hnat : (431511401 : ℕ)^8353*100000000000000^6305 ≤ 13110488102969^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431511401 2000000000 13110488102969 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337565331/625000000 : ℝ)^8353 ≤ (44216141845629/100000000000000 : ℝ)^6305 := by
    have hnat : (337565331 : ℕ)^8353*100000000000000^6305 ≤ 44216141845629^6305*625000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337565331 625000000 44216141845629 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629090733/5000000000 : ℝ)^8353 ≤ (21336685012677/50000000000000 : ℝ)^6305 := by
    have hnat : (2629090733 : ℕ)^8353*50000000000000^6305 ≤ 21336685012677^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629090733 5000000000 21336685012677 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431511401/2000000000 : ℝ), (337565331/625000000 : ℝ), (2629090733/5000000000 : ℝ)] ![(13110488102969/100000000000000 : ℝ), (44216141845629/100000000000000 : ℝ), (21336685012677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431511401/2000000000 : ℝ)|^8353 ≤ (13110488102969/100000000000000 : ℝ)^6305
        have hw : |(-431511401/2000000000 : ℝ)|=(431511401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337565331/625000000 : ℝ)|^8353 ≤ (44216141845629/100000000000000 : ℝ)^6305
        have hw : |(337565331/625000000 : ℝ)|=(337565331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629090733/5000000000 : ℝ)|^8353 ≤ (21336685012677/50000000000000 : ℝ)^6305
        have hw : |(2629090733/5000000000 : ℝ)|=(2629090733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346784823/10000000000 : ℝ)*x 0 + (-446029131/2000000000 : ℝ)*x 1 + (5258181661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346784823/10000000000 : ℝ)^8353 ≤ (43628607587607/100000000000000 : ℝ)^6305 := by
    have hnat : (5346784823 : ℕ)^8353*100000000000000^6305 ≤ 43628607587607^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346784823 10000000000 43628607587607 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446029131/2000000000 : ℝ)^8353 ≤ (13698020273017/100000000000000 : ℝ)^6305 := by
    have hnat : (446029131 : ℕ)^8353*100000000000000^6305 ≤ 13698020273017^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446029131 2000000000 13698020273017 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258181661/10000000000 : ℝ)^8353 ≤ (42673372121943/100000000000000 : ℝ)^6305 := by
    have hnat : (5258181661 : ℕ)^8353*100000000000000^6305 ≤ 42673372121943^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258181661 10000000000 42673372121943 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346784823/10000000000 : ℝ), (-446029131/2000000000 : ℝ), (5258181661/10000000000 : ℝ)] ![(43628607587607/100000000000000 : ℝ), (13698020273017/100000000000000 : ℝ), (42673372121943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346784823/10000000000 : ℝ)|^8353 ≤ (43628607587607/100000000000000 : ℝ)^6305
        have hw : |(5346784823/10000000000 : ℝ)|=(5346784823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446029131/2000000000 : ℝ)|^8353 ≤ (13698020273017/100000000000000 : ℝ)^6305
        have hw : |(-446029131/2000000000 : ℝ)|=(446029131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258181661/10000000000 : ℝ)|^8353 ≤ (42673372121943/100000000000000 : ℝ)^6305
        have hw : |(5258181661/10000000000 : ℝ)|=(5258181661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346784827/10000000000 : ℝ)*x 0 + (5258181719/10000000000 : ℝ)*x 1 + (-2230145573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346784827/10000000000 : ℝ)^8353 ≤ (85212124279/195312500000 : ℝ)^6305 := by
    have hnat : (5346784827 : ℕ)^8353*195312500000^6305 ≤ 85212124279^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346784827 10000000000 85212124279 195312500000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258181719/10000000000 : ℝ)^8353 ≤ (5334171593193/12500000000000 : ℝ)^6305 := by
    have hnat : (5258181719 : ℕ)^8353*12500000000000^6305 ≤ 5334171593193^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258181719 10000000000 5334171593193 12500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230145573/10000000000 : ℝ)^8353 ≤ (3424504901439/25000000000000 : ℝ)^6305 := by
    have hnat : (2230145573 : ℕ)^8353*25000000000000^6305 ≤ 3424504901439^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230145573 10000000000 3424504901439 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346784827/10000000000 : ℝ), (5258181719/10000000000 : ℝ), (-2230145573/10000000000 : ℝ)] ![(85212124279/195312500000 : ℝ), (5334171593193/12500000000000 : ℝ), (3424504901439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346784827/10000000000 : ℝ)|^8353 ≤ (85212124279/195312500000 : ℝ)^6305
        have hw : |(5346784827/10000000000 : ℝ)|=(5346784827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258181719/10000000000 : ℝ)|^8353 ≤ (5334171593193/12500000000000 : ℝ)^6305
        have hw : |(5258181719/10000000000 : ℝ)|=(5258181719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230145573/10000000000 : ℝ)|^8353 ≤ (3424504901439/25000000000000 : ℝ)^6305
        have hw : |(-2230145573/10000000000 : ℝ)|=(2230145573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218085351/500000000 : ℝ)*x 0 + (1055350637/2500000000 : ℝ)*x 1 + (4506630079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218085351/500000000 : ℝ)^8353 ≤ (6662529443031/20000000000000 : ℝ)^6305 := by
    have hnat : (218085351 : ℕ)^8353*20000000000000^6305 ≤ 6662529443031^6305*500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218085351 500000000 6662529443031 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055350637/2500000000 : ℝ)^8353 ≤ (31900467465671/100000000000000 : ℝ)^6305 := by
    have hnat : (1055350637 : ℕ)^8353*100000000000000^6305 ≤ 31900467465671^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055350637 2500000000 31900467465671 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506630079/10000000000 : ℝ)^8353 ≤ (34786885301341/100000000000000 : ℝ)^6305 := by
    have hnat : (4506630079 : ℕ)^8353*100000000000000^6305 ≤ 34786885301341^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506630079 10000000000 34786885301341 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218085351/500000000 : ℝ), (1055350637/2500000000 : ℝ), (4506630079/10000000000 : ℝ)] ![(6662529443031/20000000000000 : ℝ), (31900467465671/100000000000000 : ℝ), (34786885301341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218085351/500000000 : ℝ)|^8353 ≤ (6662529443031/20000000000000 : ℝ)^6305
        have hw : |(218085351/500000000 : ℝ)|=(218085351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055350637/2500000000 : ℝ)|^8353 ≤ (31900467465671/100000000000000 : ℝ)^6305
        have hw : |(1055350637/2500000000 : ℝ)|=(1055350637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506630079/10000000000 : ℝ)|^8353 ≤ (34786885301341/100000000000000 : ℝ)^6305
        have hw : |(4506630079/10000000000 : ℝ)|=(4506630079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157564109/10000000000 : ℝ)*x 0 + (5258586209/10000000000 : ℝ)*x 1 + (270031939/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157564109/10000000000 : ℝ)^8353 ≤ (6555272646291/50000000000000 : ℝ)^6305 := by
    have hnat : (2157564109 : ℕ)^8353*50000000000000^6305 ≤ 6555272646291^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157564109 10000000000 6555272646291 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258586209/10000000000 : ℝ)^8353 ≤ (21338860885671/50000000000000 : ℝ)^6305 := by
    have hnat : (5258586209 : ℕ)^8353*50000000000000^6305 ≤ 21338860885671^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258586209 10000000000 21338860885671 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270031939/500000000 : ℝ)^8353 ≤ (4421173292023/10000000000000 : ℝ)^6305 := by
    have hnat : (270031939 : ℕ)^8353*10000000000000^6305 ≤ 4421173292023^6305*500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270031939 500000000 4421173292023 10000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157564109/10000000000 : ℝ), (5258586209/10000000000 : ℝ), (270031939/500000000 : ℝ)] ![(6555272646291/50000000000000 : ℝ), (21338860885671/50000000000000 : ℝ), (4421173292023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157564109/10000000000 : ℝ)|^8353 ≤ (6555272646291/50000000000000 : ℝ)^6305
        have hw : |(-2157564109/10000000000 : ℝ)|=(2157564109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258586209/10000000000 : ℝ)|^8353 ≤ (21338860885671/50000000000000 : ℝ)^6305
        have hw : |(5258586209/10000000000 : ℝ)|=(5258586209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270031939/500000000 : ℝ)|^8353 ≤ (4421173292023/10000000000000 : ℝ)^6305
        have hw : |(270031939/500000000 : ℝ)|=(270031939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655272033/5000000000 : ℝ)*x 0 + (-2087688137/10000000000 : ℝ)*x 1 + (2700319347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655272033/5000000000 : ℝ)^8353 ≤ (43237267607853/100000000000000 : ℝ)^6305 := by
    have hnat : (2655272033 : ℕ)^8353*100000000000000^6305 ≤ 43237267607853^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655272033 5000000000 43237267607853 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087688137/10000000000 : ℝ)^8353 ≤ (12551000386433/100000000000000 : ℝ)^6305 := by
    have hnat : (2087688137 : ℕ)^8353*100000000000000^6305 ≤ 12551000386433^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087688137 10000000000 12551000386433 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700319347/5000000000 : ℝ)^8353 ≤ (44211731987517/100000000000000 : ℝ)^6305 := by
    have hnat : (2700319347 : ℕ)^8353*100000000000000^6305 ≤ 44211731987517^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700319347 5000000000 44211731987517 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655272033/5000000000 : ℝ), (-2087688137/10000000000 : ℝ), (2700319347/5000000000 : ℝ)] ![(43237267607853/100000000000000 : ℝ), (12551000386433/100000000000000 : ℝ), (44211731987517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655272033/5000000000 : ℝ)|^8353 ≤ (43237267607853/100000000000000 : ℝ)^6305
        have hw : |(2655272033/5000000000 : ℝ)|=(2655272033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087688137/10000000000 : ℝ)|^8353 ≤ (12551000386433/100000000000000 : ℝ)^6305
        have hw : |(-2087688137/10000000000 : ℝ)|=(2087688137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700319347/5000000000 : ℝ)|^8353 ≤ (44211731987517/100000000000000 : ℝ)^6305
        have hw : |(2700319347/5000000000 : ℝ)|=(2700319347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310543859/10000000000 : ℝ)*x 0 + (540063871/1000000000 : ℝ)*x 1 + (-417537679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310543859/10000000000 : ℝ)^8353 ≤ (43237265375067/100000000000000 : ℝ)^6305 := by
    have hnat : (5310543859 : ℕ)^8353*100000000000000^6305 ≤ 43237265375067^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310543859 10000000000 43237265375067 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540063871/1000000000 : ℝ)^8353 ≤ (8842346432209/20000000000000 : ℝ)^6305 := by
    have hnat : (540063871 : ℕ)^8353*20000000000000^6305 ≤ 8842346432209^6305*1000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540063871 1000000000 8842346432209 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417537679/2000000000 : ℝ)^8353 ≤ (12551002441329/100000000000000 : ℝ)^6305 := by
    have hnat : (417537679 : ℕ)^8353*100000000000000^6305 ≤ 12551002441329^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417537679 2000000000 12551002441329 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310543859/10000000000 : ℝ), (540063871/1000000000 : ℝ), (-417537679/2000000000 : ℝ)] ![(43237265375067/100000000000000 : ℝ), (8842346432209/20000000000000 : ℝ), (12551002441329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310543859/10000000000 : ℝ)|^8353 ≤ (43237265375067/100000000000000 : ℝ)^6305
        have hw : |(5310543859/10000000000 : ℝ)|=(5310543859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540063871/1000000000 : ℝ)|^8353 ≤ (8842346432209/20000000000000 : ℝ)^6305
        have hw : |(540063871/1000000000 : ℝ)|=(540063871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417537679/2000000000 : ℝ)|^8353 ≤ (12551002441329/100000000000000 : ℝ)^6305
        have hw : |(-417537679/2000000000 : ℝ)|=(417537679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s4_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090430141/2500000000 : ℝ)*x 0 + (4505821839/10000000000 : ℝ)*x 1 + (4222214399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090430141/2500000000 : ℝ)^8353 ≤ (16656392129133/50000000000000 : ℝ)^6305 := by
    have hnat : (1090430141 : ℕ)^8353*50000000000000^6305 ≤ 16656392129133^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090430141 2500000000 16656392129133 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505821839/10000000000 : ℝ)^8353 ≤ (8694655047473/25000000000000 : ℝ)^6305 := by
    have hnat : (4505821839 : ℕ)^8353*25000000000000^6305 ≤ 8694655047473^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505821839 10000000000 8694655047473 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222214399/10000000000 : ℝ)^8353 ≤ (31908595538081/100000000000000 : ℝ)^6305 := by
    have hnat : (4222214399 : ℕ)^8353*100000000000000^6305 ≤ 31908595538081^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222214399 10000000000 31908595538081 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090430141/2500000000 : ℝ), (4505821839/10000000000 : ℝ), (4222214399/10000000000 : ℝ)] ![(16656392129133/50000000000000 : ℝ), (8694655047473/25000000000000 : ℝ), (31908595538081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090430141/2500000000 : ℝ)|^8353 ≤ (16656392129133/50000000000000 : ℝ)^6305
        have hw : |(1090430141/2500000000 : ℝ)|=(1090430141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505821839/10000000000 : ℝ)|^8353 ≤ (8694655047473/25000000000000 : ℝ)^6305
        have hw : |(4505821839/10000000000 : ℝ)|=(4505821839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222214399/10000000000 : ℝ)|^8353 ≤ (31908595538081/100000000000000 : ℝ)^6305
        have hw : |(4222214399/10000000000 : ℝ)|=(4222214399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (334/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11209/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (334/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (334/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (334/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2957/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (334/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (334/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2957/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (334/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (334/3125 : ℝ) ^ (261/64 : ℝ) ≤ (684854529810311/6250000000000000000 : ℝ) := by
    have hpowers : (334/3125 : ℝ)^261 ≤ (684854529810311/6250000000000000000 : ℝ)^64 := by
      have hnat : (334 : ℕ)^261*6250000000000000000^64 ≤ 684854529810311^64*3125^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        334 3125 684854529810311 6250000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (334/3125 : ℝ)) (X := (684854529810311/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2957/20000 : ℝ) ^ (261/64 : ℝ) ≤ (128610855898229/312500000000000000 : ℝ) := by
    have hpowers : (2957/20000 : ℝ)^261 ≤ (128610855898229/312500000000000000 : ℝ)^64 := by
      have hnat : (2957 : ℕ)^261*312500000000000000^64 ≤ 128610855898229^64*20000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 20000 128610855898229 312500000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/20000 : ℝ)) (X := (128610855898229/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125684854529810311/3125000000000000000 : ℝ) ≤ (10000537343328771/10000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (3125684854529810311/3125000000000000000 : ℝ)^64 ≤ (10000537343328771/10000000000000000 : ℝ)^261 := by
      have hnat : (3125684854529810311 : ℕ)^64*10000000000000000^261 ≤ 10000537343328771^261*3125000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125684854529810311 3125000000000000000 10000537343328771 10000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537343328771/10000000000000000 : ℝ)) (X := (3125684854529810311/3125000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253257071647774891/6250000000000000000 : ℝ) ≤ (5000638809505341/5000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (6253257071647774891/6250000000000000000 : ℝ)^64 ≤ (5000638809505341/5000000000000000 : ℝ)^261 := by
      have hnat : (6253257071647774891 : ℕ)^64*5000000000000000^261 ≤ 5000638809505341^261*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253257071647774891 6250000000000000000 5000638809505341 5000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000638809505341/5000000000000000 : ℝ)) (X := (6253257071647774891/6250000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (156378610855898229/156250000000000000 : ℝ) ≤ (10002017894692593/10000000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (156378610855898229/156250000000000000 : ℝ)^64 ≤ (10002017894692593/10000000000000000 : ℝ)^261 := by
      have hnat : (156378610855898229 : ℕ)^64*10000000000000000^261 ≤ 10002017894692593^261*156250000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156378610855898229 156250000000000000 10002017894692593 10000000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002017894692593/10000000000000000 : ℝ)) (X := (156378610855898229/156250000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(684854529810311/6250000000000000000 : ℝ) ≤ ((40956377362641445251/40970000000000000000 : ℝ)+2*(740275681911/409700000000000 : ℝ)*(334/3125 : ℝ))^(261/64 : ℝ) := by
    rw [show (40956377362641445251/40970000000000000000 : ℝ)+2*(740275681911/409700000000000 : ℝ)*(334/3125 : ℝ)=(10000537343328771/10000000000000000 : ℝ) by norm_num, show 1+2*(684854529810311/6250000000000000000 : ℝ)=(3125684854529810311/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(128610855898229/312500000000000000 : ℝ)+(684854529810311/6250000000000000000 : ℝ) ≤ ((40956377362641445251/40970000000000000000 : ℝ)+(740275681911/409700000000000 : ℝ)*((2957/20000 : ℝ)+(334/3125 : ℝ)))^(261/64 : ℝ) := by
    rw [show (40956377362641445251/40970000000000000000 : ℝ)+(740275681911/409700000000000 : ℝ)*((2957/20000 : ℝ)+(334/3125 : ℝ))=(5000638809505341/5000000000000000 : ℝ) by norm_num, show 1+(128610855898229/312500000000000000 : ℝ)+(684854529810311/6250000000000000000 : ℝ)=(6253257071647774891/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(128610855898229/312500000000000000 : ℝ) ≤ ((40956377362641445251/40970000000000000000 : ℝ)+2*(740275681911/409700000000000 : ℝ)*(2957/20000 : ℝ))^(261/64 : ℝ) := by
    rw [show (40956377362641445251/40970000000000000000 : ℝ)+2*(740275681911/409700000000000 : ℝ)*(2957/20000 : ℝ)=(10002017894692593/10000000000000000 : ℝ) by norm_num, show 1+2*(128610855898229/312500000000000000 : ℝ)=(156378610855898229/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40956377362641445251/40970000000000000000 : ℝ)*(X 1 0+X 2 0)+(740275681911/409700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (334/3125 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (40956377362641445251/40970000000000000000 : ℝ)) (alpha := (740275681911/409700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40956377362641445251/40970000000000000000 : ℝ)*(X 0 1+X 2 1)+(740275681911/409700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (334/3125 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (40956377362641445251/40970000000000000000 : ℝ)) (alpha := (740275681911/409700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40956377362641445251/40970000000000000000 : ℝ)*(X 0 2+X 1 2)+(740275681911/409700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (334/3125 : ℝ)) (hi := (2957/20000 : ℝ)) (c := (40956377362641445251/40970000000000000000 : ℝ)) (alpha := (740275681911/409700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431511401/2000000000 : ℝ)*X 0 0+(337565331/625000000 : ℝ)*X 0 1+(2629090733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346784823/10000000000 : ℝ)*X 1 0+(-446029131/2000000000 : ℝ)*X 1 1+(5258181661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346784827/10000000000 : ℝ)*X 2 0+(5258181719/10000000000 : ℝ)*X 2 1+(-2230145573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218085351/500000000 : ℝ)*X 0 0+(1055350637/2500000000 : ℝ)*X 0 1+(4506630079/10000000000 : ℝ)*X 0 2+(218085351/500000000 : ℝ)*X 1 0+(1055350637/2500000000 : ℝ)*X 1 1+(4506630079/10000000000 : ℝ)*X 1 2+(218085351/500000000 : ℝ)*X 2 0+(1055350637/2500000000 : ℝ)*X 2 1+(4506630079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157564109/10000000000 : ℝ)*X 0 0+(5258586209/10000000000 : ℝ)*X 0 1+(270031939/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655272033/5000000000 : ℝ)*X 1 0+(-2087688137/10000000000 : ℝ)*X 1 1+(2700319347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310543859/10000000000 : ℝ)*X 2 0+(540063871/1000000000 : ℝ)*X 2 1+(-417537679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090430141/2500000000 : ℝ)*X 0 0+(4505821839/10000000000 : ℝ)*X 0 1+(4222214399/10000000000 : ℝ)*X 0 2+(1090430141/2500000000 : ℝ)*X 1 0+(4505821839/10000000000 : ℝ)*X 1 1+(4222214399/10000000000 : ℝ)*X 1 2+(1090430141/2500000000 : ℝ)*X 2 0+(4505821839/10000000000 : ℝ)*X 2 1+(4222214399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19238960605911102265437/2560625000000000000000000000 : ℝ) := by norm_num
    linear_combination (28965729/2000000000000 : ℝ)*(base19) + (1237843841/100000000000000 : ℝ)*(base23) + (115319037/100000000000000 : ℝ)*(lower2) + (218947801/100000000000000 : ℝ)*(upper3) + (11014669/6250000000000 : ℝ)*(upper5) + (5252884248108121/100000000000000 : ℝ)*(major0) + (5252884248108121/100000000000000 : ℝ)*(major1) + (5252884248108121/100000000000000 : ℝ)*(major2) + (874964171348241/12500000000000 : ℝ)*(sp0) + (699975434212287/10000000000000 : ℝ)*(sp1) + (6999754552565479/100000000000000 : ℝ)*(sp2) + (1752995848491709/50000000000000 : ℝ)*(sp3) + (1325613231/3125000000000 : ℝ)*(sp4) + (10379188671/50000000000000 : ℝ)*(sp7) + (3506012455360761/100000000000000 : ℝ)*(f.failure) + (174993894760233/2500000000000 : ℝ)*(f.sum) + (50234389237431/20485000000000000000000000000 : ℝ)*base65 + (11439917967927083371/4097000000000000000000000000000000 : ℝ)*base67 + (23667360920137083371/4097000000000000000000000000000000 : ℝ)*base69 + (21744309734152916629/4097000000000000000000000000000000 : ℝ)*base72 + (119078343650511/20485000000000000000000000000 : ℝ)*base73 + (11358444609476916629/4097000000000000000000000000000000 : ℝ)*base76 + (5864276783083916629/4097000000000000000000000000000000 : ℝ)*base78 + (28500306197782083371/4097000000000000000000000000000000 : ℝ)*base79 + (88549907338963/10242500000000000000000000000 : ℝ)*base81 + (33008591/10000000000000000000000 : ℝ)*base89 + (33008591/10000000000000000000000 : ℝ)*base91 + (33008591/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9292157178222732090527641587/1024250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (549837821/20000000000000 : ℝ)*(base19) + (1271554977/50000000000000 : ℝ)*(base23) + (49239759/50000000000000 : ℝ)*(upper2) + (33461897/25000000000000 : ℝ)*(upper3) + (328965277/100000000000000 : ℝ)*(upper5) + (2641411107019221/50000000000000 : ℝ)*(major0) + (2641411107019221/50000000000000 : ℝ)*(major1) + (2641411107019221/50000000000000 : ℝ)*(major2) + (75114776661/100000000000000 : ℝ)*(sp1) + (28975988591/50000000000000 : ℝ)*(sp2) + (7039649718209473/100000000000000 : ℝ)*(sp4) + (1759892963560927/25000000000000 : ℝ)*(sp5) + (7039589223122337/100000000000000 : ℝ)*(sp6) + (881498601865539/25000000000000 : ℝ)*(sp7) + (881498601865539/25000000000000 : ℝ)*(f.failure) + (7039649718209473/100000000000000 : ℝ)*(f.sum) + (20659929340567/20485000000000000000000000000 : ℝ)*base65 + (9220253590270769471/2048500000000000000000000000000000 : ℝ)*base67 + (16650850478785269471/2048500000000000000000000000000000 : ℝ)*base69 + (22242883612531769471/2048500000000000000000000000000000 : ℝ)*base71 + (25588548520157/20485000000000000000000000000 : ℝ)*base73 + (33465063571365230529/2048500000000000000000000000000000 : ℝ)*base76 + (13183918282130769471/2048500000000000000000000000000000 : ℝ)*base77 + (26985843450372730529/2048500000000000000000000000000000 : ℝ)*base80 + (25798379411193/20485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11493291/2500000000000000000000 : ℝ)*base90 + (11493291/2500000000000000000000 : ℝ)*base92 + (11493291/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1160_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2957/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (334/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1160_s5_0 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215815593/1000000000 : ℝ)*x 0 + (5394450219/10000000000 : ℝ)*x 1 + (5264383251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215815593/1000000000 : ℝ)^8353 ≤ (13115309867433/100000000000000 : ℝ)^6305 := by
    have hnat : (215815593 : ℕ)^8353*100000000000000^6305 ≤ 13115309867433^6305*1000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215815593 1000000000 13115309867433 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394450219/10000000000 : ℝ)^8353 ≤ (44144627342327/100000000000000 : ℝ)^6305 := by
    have hnat : (5394450219 : ℕ)^8353*100000000000000^6305 ≤ 44144627342327^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394450219 10000000000 44144627342327 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264383251/10000000000 : ℝ)^8353 ≤ (2137003138803/5000000000000 : ℝ)^6305 := by
    have hnat : (5264383251 : ℕ)^8353*5000000000000^6305 ≤ 2137003138803^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264383251 10000000000 2137003138803 5000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215815593/1000000000 : ℝ), (5394450219/10000000000 : ℝ), (5264383251/10000000000 : ℝ)] ![(13115309867433/100000000000000 : ℝ), (44144627342327/100000000000000 : ℝ), (2137003138803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215815593/1000000000 : ℝ)|^8353 ≤ (13115309867433/100000000000000 : ℝ)^6305
        have hw : |(-215815593/1000000000 : ℝ)|=(215815593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394450219/10000000000 : ℝ)|^8353 ≤ (44144627342327/100000000000000 : ℝ)^6305
        have hw : |(5394450219/10000000000 : ℝ)|=(5394450219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264383251/10000000000 : ℝ)|^8353 ≤ (2137003138803/5000000000000 : ℝ)^6305
        have hw : |(5264383251/10000000000 : ℝ)|=(5264383251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_1 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345127867/10000000000 : ℝ)*x 0 + (-2224148699/10000000000 : ℝ)*x 1 + (1316095777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345127867/10000000000 : ℝ)^8353 ≤ (21805348184137/50000000000000 : ℝ)^6305 := by
    have hnat : (5345127867 : ℕ)^8353*50000000000000^6305 ≤ 21805348184137^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345127867 10000000000 21805348184137 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224148699/10000000000 : ℝ)^8353 ≤ (6824621191879/50000000000000 : ℝ)^6305 := by
    have hnat : (2224148699 : ℕ)^8353*50000000000000^6305 ≤ 6824621191879^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224148699 10000000000 6824621191879 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316095777/2500000000 : ℝ)^8353 ≤ (42740061237973/100000000000000 : ℝ)^6305 := by
    have hnat : (1316095777 : ℕ)^8353*100000000000000^6305 ≤ 42740061237973^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316095777 2500000000 42740061237973 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345127867/10000000000 : ℝ), (-2224148699/10000000000 : ℝ), (1316095777/2500000000 : ℝ)] ![(21805348184137/50000000000000 : ℝ), (6824621191879/50000000000000 : ℝ), (42740061237973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345127867/10000000000 : ℝ)|^8353 ≤ (21805348184137/50000000000000 : ℝ)^6305
        have hw : |(5345127867/10000000000 : ℝ)|=(5345127867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224148699/10000000000 : ℝ)|^8353 ≤ (6824621191879/50000000000000 : ℝ)^6305
        have hw : |(-2224148699/10000000000 : ℝ)|=(2224148699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316095777/2500000000 : ℝ)|^8353 ≤ (42740061237973/100000000000000 : ℝ)^6305
        have hw : |(1316095777/2500000000 : ℝ)|=(1316095777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_2 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336281921/2500000000 : ℝ)*x 0 + (5264383187/10000000000 : ℝ)*x 1 + (-2224148837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336281921/2500000000 : ℝ)^8353 ≤ (10902673597549/25000000000000 : ℝ)^6305 := by
    have hnat : (1336281921 : ℕ)^8353*25000000000000^6305 ≤ 10902673597549^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336281921 2500000000 10902673597549 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264383187/10000000000 : ℝ)^8353 ≤ (21370031043843/50000000000000 : ℝ)^6305 := by
    have hnat : (5264383187 : ℕ)^8353*50000000000000^6305 ≤ 21370031043843^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264383187 10000000000 21370031043843 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224148837/10000000000 : ℝ)^8353 ≤ (213269429777/1562500000000 : ℝ)^6305 := by
    have hnat : (2224148837 : ℕ)^8353*1562500000000^6305 ≤ 213269429777^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224148837 10000000000 213269429777 1562500000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336281921/2500000000 : ℝ), (5264383187/10000000000 : ℝ), (-2224148837/10000000000 : ℝ)] ![(10902673597549/25000000000000 : ℝ), (21370031043843/50000000000000 : ℝ), (213269429777/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336281921/2500000000 : ℝ)|^8353 ≤ (10902673597549/25000000000000 : ℝ)^6305
        have hw : |(1336281921/2500000000 : ℝ)|=(1336281921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264383187/10000000000 : ℝ)|^8353 ≤ (21370031043843/50000000000000 : ℝ)^6305
        have hw : |(5264383187/10000000000 : ℝ)|=(5264383187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2224148837/10000000000 : ℝ)|^8353 ≤ (213269429777/1562500000000 : ℝ)^6305
        have hw : |(-2224148837/10000000000 : ℝ)|=(2224148837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_3 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362056131/10000000000 : ℝ)*x 0 + (2117065909/5000000000 : ℝ)*x 1 + (1123452711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362056131/10000000000 : ℝ)^8353 ≤ (33316179691191/100000000000000 : ℝ)^6305 := by
    have hnat : (4362056131 : ℕ)^8353*100000000000000^6305 ≤ 33316179691191^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362056131 10000000000 33316179691191 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117065909/5000000000 : ℝ)^8353 ≤ (32027968486349/100000000000000 : ℝ)^6305 := by
    have hnat : (2117065909 : ℕ)^8353*100000000000000^6305 ≤ 32027968486349^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117065909 5000000000 32027968486349 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123452711/2500000000 : ℝ)^8353 ≤ (34655851807077/100000000000000 : ℝ)^6305 := by
    have hnat : (1123452711 : ℕ)^8353*100000000000000^6305 ≤ 34655851807077^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123452711 2500000000 34655851807077 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362056131/10000000000 : ℝ), (2117065909/5000000000 : ℝ), (1123452711/2500000000 : ℝ)] ![(33316179691191/100000000000000 : ℝ), (32027968486349/100000000000000 : ℝ), (34655851807077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362056131/10000000000 : ℝ)|^8353 ≤ (33316179691191/100000000000000 : ℝ)^6305
        have hw : |(4362056131/10000000000 : ℝ)|=(4362056131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117065909/5000000000 : ℝ)|^8353 ≤ (32027968486349/100000000000000 : ℝ)^6305
        have hw : |(2117065909/5000000000 : ℝ)|=(2117065909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123452711/2500000000 : ℝ)|^8353 ≤ (34655851807077/100000000000000 : ℝ)^6305
        have hw : |(1123452711/2500000000 : ℝ)|=(1123452711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_4 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079080461/5000000000 : ℝ)*x 0 + (1316179799/2500000000 : ℝ)*x 1 + (5394113213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079080461/5000000000 : ℝ)^8353 ≤ (2623070011669/20000000000000 : ℝ)^6305 := by
    have hnat : (1079080461 : ℕ)^8353*20000000000000^6305 ≤ 2623070011669^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079080461 5000000000 2623070011669 20000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316179799/2500000000 : ℝ)^8353 ≤ (21371838095061/50000000000000 : ℝ)^6305 := by
    have hnat : (1316179799 : ℕ)^8353*50000000000000^6305 ≤ 21371838095061^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316179799 2500000000 21371838095061 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394113213/10000000000 : ℝ)^8353 ≤ (44140973739941/100000000000000 : ℝ)^6305 := by
    have hnat : (5394113213 : ℕ)^8353*100000000000000^6305 ≤ 44140973739941^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394113213 10000000000 44140973739941 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079080461/5000000000 : ℝ), (1316179799/2500000000 : ℝ), (5394113213/10000000000 : ℝ)] ![(2623070011669/20000000000000 : ℝ), (21371838095061/50000000000000 : ℝ), (44140973739941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079080461/5000000000 : ℝ)|^8353 ≤ (2623070011669/20000000000000 : ℝ)^6305
        have hw : |(-1079080461/5000000000 : ℝ)|=(1079080461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316179799/2500000000 : ℝ)|^8353 ≤ (21371838095061/50000000000000 : ℝ)^6305
        have hw : |(1316179799/2500000000 : ℝ)|=(1316179799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394113213/10000000000 : ℝ)|^8353 ≤ (44140973739941/100000000000000 : ℝ)^6305
        have hw : |(5394113213/10000000000 : ℝ)|=(5394113213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_5 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328032941/2500000000 : ℝ)*x 0 + (-2094418081/10000000000 : ℝ)*x 1 + (43152907/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328032941/2500000000 : ℝ)^8353 ≤ (10813598497179/25000000000000 : ℝ)^6305 := by
    have hnat : (1328032941 : ℕ)^8353*25000000000000^6305 ≤ 10813598497179^6305*2500000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328032941 2500000000 10813598497179 25000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094418081/10000000000 : ℝ)^8353 ≤ (12604630499497/100000000000000 : ℝ)^6305 := by
    have hnat : (2094418081 : ℕ)^8353*100000000000000^6305 ≤ 12604630499497^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094418081 10000000000 12604630499497 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43152907/80000000 : ℝ)^8353 ≤ (44140975496223/100000000000000 : ℝ)^6305 := by
    have hnat : (43152907 : ℕ)^8353*100000000000000^6305 ≤ 44140975496223^6305*80000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43152907 80000000 44140975496223 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328032941/2500000000 : ℝ), (-2094418081/10000000000 : ℝ), (43152907/80000000 : ℝ)] ![(10813598497179/25000000000000 : ℝ), (12604630499497/100000000000000 : ℝ), (44140975496223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328032941/2500000000 : ℝ)|^8353 ≤ (10813598497179/25000000000000 : ℝ)^6305
        have hw : |(1328032941/2500000000 : ℝ)|=(1328032941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094418081/10000000000 : ℝ)|^8353 ≤ (12604630499497/100000000000000 : ℝ)^6305
        have hw : |(-2094418081/10000000000 : ℝ)|=(2094418081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43152907/80000000 : ℝ)|^8353 ≤ (44140975496223/100000000000000 : ℝ)^6305
        have hw : |(43152907/80000000 : ℝ)|=(43152907/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_6 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664016431/1250000000 : ℝ)*x 0 + (539411363/1000000000 : ℝ)*x 1 + (-2094418161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664016431/1250000000 : ℝ)^8353 ≤ (21627195289941/50000000000000 : ℝ)^6305 := by
    have hnat : (664016431 : ℕ)^8353*50000000000000^6305 ≤ 21627195289941^6305*1250000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664016431 1250000000 21627195289941 50000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539411363/1000000000 : ℝ)^8353 ≤ (44140978260741/100000000000000 : ℝ)^6305 := by
    have hnat : (539411363 : ℕ)^8353*100000000000000^6305 ≤ 44140978260741^6305*1000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539411363 1000000000 44140978260741 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094418161/10000000000 : ℝ)^8353 ≤ (12604631137341/100000000000000 : ℝ)^6305 := by
    have hnat : (2094418161 : ℕ)^8353*100000000000000^6305 ≤ 12604631137341^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094418161 10000000000 12604631137341 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664016431/1250000000 : ℝ), (539411363/1000000000 : ℝ), (-2094418161/10000000000 : ℝ)] ![(21627195289941/50000000000000 : ℝ), (44140978260741/100000000000000 : ℝ), (12604631137341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664016431/1250000000 : ℝ)|^8353 ≤ (21627195289941/50000000000000 : ℝ)^6305
        have hw : |(664016431/1250000000 : ℝ)|=(664016431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539411363/1000000000 : ℝ)|^8353 ≤ (44140978260741/100000000000000 : ℝ)^6305
        have hw : |(539411363/1000000000 : ℝ)|=(539411363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094418161/10000000000 : ℝ)|^8353 ≤ (12604631137341/100000000000000 : ℝ)^6305
        have hw : |(-2094418161/10000000000 : ℝ)|=(2094418161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1160_s5_7 (p : ℝ) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181033537/5000000000 : ℝ)*x 0 + (4493140383/10000000000 : ℝ)*x 1 + (846960857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181033537/5000000000 : ℝ)^8353 ≤ (33316290419307/100000000000000 : ℝ)^6305 := by
    have hnat : (2181033537 : ℕ)^8353*100000000000000^6305 ≤ 33316290419307^6305*5000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181033537 5000000000 33316290419307 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493140383/10000000000 : ℝ)^8353 ≤ (866225048487/2500000000000 : ℝ)^6305 := by
    have hnat : (4493140383 : ℕ)^8353*2500000000000^6305 ≤ 866225048487^6305*10000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493140383 10000000000 866225048487 2500000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846960857/2000000000 : ℝ)^8353 ≤ (32034707628037/100000000000000 : ℝ)^6305 := by
    have hnat : (846960857 : ℕ)^8353*100000000000000^6305 ≤ 32034707628037^6305*2000000000^8353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846960857 2000000000 32034707628037 100000000000000 8353 6305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8353/2048 : ℝ)) 8353 6305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181033537/5000000000 : ℝ), (4493140383/10000000000 : ℝ), (846960857/2000000000 : ℝ)] ![(33316290419307/100000000000000 : ℝ), (866225048487/2500000000000 : ℝ), (32034707628037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181033537/5000000000 : ℝ)|^8353 ≤ (33316290419307/100000000000000 : ℝ)^6305
        have hw : |(2181033537/5000000000 : ℝ)|=(2181033537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493140383/10000000000 : ℝ)|^8353 ≤ (866225048487/2500000000000 : ℝ)^6305
        have hw : |(4493140383/10000000000 : ℝ)|=(4493140383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846960857/2000000000 : ℝ)|^8353 ≤ (32034707628037/100000000000000 : ℝ)^6305
        have hw : |(846960857/2000000000 : ℝ)|=(846960857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1160_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11209/100000 : ℝ) ^ (261/64 : ℝ) ≤ (13305000288733707/100000000000000000000 : ℝ) := by
    have hpowers : (11209/100000 : ℝ)^261 ≤ (13305000288733707/100000000000000000000 : ℝ)^64 := by
      have hnat : (11209 : ℕ)^261*100000000000000000000^64 ≤ 13305000288733707^64*100000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11209 100000 13305000288733707 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11209/100000 : ℝ)) (X := (13305000288733707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (261/64 : ℝ) ≤ (35260294752613023/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^261 ≤ (35260294752613023/100000000000000000000 : ℝ)^64 := by
      have hnat : (2847 : ℕ)^261*100000000000000000000^64 ≤ 35260294752613023^64*20000^261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35260294752613023 100000000000000000000 261 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35260294752613023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013305000288733707/50000000000000000000 : ℝ) ≤ (500032622012189/500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50013305000288733707/50000000000000000000 : ℝ)^64 ≤ (500032622012189/500000000000000 : ℝ)^261 := by
      have hnat : (50013305000288733707 : ℕ)^64*500000000000000^261 ≤ 500032622012189^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013305000288733707 50000000000000000000 500032622012189 500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500032622012189/500000000000000 : ℝ)) (X := (50013305000288733707/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004856529504134673/10000000000000000000 : ℝ) ≤ (625074415933157/625000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (10004856529504134673/10000000000000000000 : ℝ)^64 ≤ (625074415933157/625000000000000 : ℝ)^261 := by
      have hnat : (10004856529504134673 : ℕ)^64*625000000000000^261 ≤ 625074415933157^261*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004856529504134673 10000000000000000000 625074415933157 625000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074415933157/625000000000000 : ℝ)) (X := (10004856529504134673/10000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035260294752613023/50000000000000000000 : ℝ) ≤ (2500432217404311/2500000000000000 : ℝ) ^ (261/64 : ℝ) := by
    have hpowers : (50035260294752613023/50000000000000000000 : ℝ)^64 ≤ (2500432217404311/2500000000000000 : ℝ)^261 := by
      have hnat : (50035260294752613023 : ℕ)^64*2500000000000000^261 ≤ 2500432217404311^261*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035260294752613023 50000000000000000000 2500432217404311 2500000000000000 64 261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500432217404311/2500000000000000 : ℝ)) (X := (50035260294752613023/50000000000000000000 : ℝ)) (by norm_num) 261 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13305000288733707/100000000000000000000 : ℝ) ≤ ((1890619286708157519/1891250000000000000 : ℝ)+2*(134553671683/75650000000000 : ℝ)*(11209/100000 : ℝ))^(261/64 : ℝ) := by
    rw [show (1890619286708157519/1891250000000000000 : ℝ)+2*(134553671683/75650000000000 : ℝ)*(11209/100000 : ℝ)=(500032622012189/500000000000000 : ℝ) by norm_num, show 1+2*(13305000288733707/100000000000000000000 : ℝ)=(50013305000288733707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35260294752613023/100000000000000000000 : ℝ)+(13305000288733707/100000000000000000000 : ℝ) ≤ ((1890619286708157519/1891250000000000000 : ℝ)+(134553671683/75650000000000 : ℝ)*((2847/20000 : ℝ)+(11209/100000 : ℝ)))^(261/64 : ℝ) := by
    rw [show (1890619286708157519/1891250000000000000 : ℝ)+(134553671683/75650000000000 : ℝ)*((2847/20000 : ℝ)+(11209/100000 : ℝ))=(625074415933157/625000000000000 : ℝ) by norm_num, show 1+(35260294752613023/100000000000000000000 : ℝ)+(13305000288733707/100000000000000000000 : ℝ)=(10004856529504134673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35260294752613023/100000000000000000000 : ℝ) ≤ ((1890619286708157519/1891250000000000000 : ℝ)+2*(134553671683/75650000000000 : ℝ)*(2847/20000 : ℝ))^(261/64 : ℝ) := by
    rw [show (1890619286708157519/1891250000000000000 : ℝ)+2*(134553671683/75650000000000 : ℝ)*(2847/20000 : ℝ)=(2500432217404311/2500000000000000 : ℝ) by norm_num, show 1+2*(35260294752613023/100000000000000000000 : ℝ)=(50035260294752613023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1890619286708157519/1891250000000000000 : ℝ)*(X 1 0+X 2 0)+(134553671683/75650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1890619286708157519/1891250000000000000 : ℝ)) (alpha := (134553671683/75650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1890619286708157519/1891250000000000000 : ℝ)*(X 0 1+X 2 1)+(134553671683/75650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1890619286708157519/1891250000000000000 : ℝ)) (alpha := (134553671683/75650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1890619286708157519/1891250000000000000 : ℝ)*(X 0 2+X 1 2)+(134553671683/75650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (261/64 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1890619286708157519/1891250000000000000 : ℝ)) (alpha := (134553671683/75650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215815593/1000000000 : ℝ)*X 0 0+(5394450219/10000000000 : ℝ)*X 0 1+(5264383251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345127867/10000000000 : ℝ)*X 1 0+(-2224148699/10000000000 : ℝ)*X 1 1+(1316095777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336281921/2500000000 : ℝ)*X 2 0+(5264383187/10000000000 : ℝ)*X 2 1+(-2224148837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362056131/10000000000 : ℝ)*X 0 0+(2117065909/5000000000 : ℝ)*X 0 1+(1123452711/2500000000 : ℝ)*X 0 2+(4362056131/10000000000 : ℝ)*X 1 0+(2117065909/5000000000 : ℝ)*X 1 1+(1123452711/2500000000 : ℝ)*X 1 2+(4362056131/10000000000 : ℝ)*X 2 0+(2117065909/5000000000 : ℝ)*X 2 1+(1123452711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079080461/5000000000 : ℝ)*X 0 0+(1316179799/2500000000 : ℝ)*X 0 1+(5394113213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328032941/2500000000 : ℝ)*X 1 0+(-2094418081/10000000000 : ℝ)*X 1 1+(43152907/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664016431/1250000000 : ℝ)*X 2 0+(539411363/1000000000 : ℝ)*X 2 1+(-2094418161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181033537/5000000000 : ℝ)*X 0 0+(4493140383/10000000000 : ℝ)*X 0 1+(846960857/2000000000 : ℝ)*X 0 2+(2181033537/5000000000 : ℝ)*X 1 0+(4493140383/10000000000 : ℝ)*X 1 1+(846960857/2000000000 : ℝ)*X 1 2+(2181033537/5000000000 : ℝ)*X 2 0+(4493140383/10000000000 : ℝ)*X 2 1+(846960857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1160_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1049363511380485642939681461/94562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (668180387/50000000000000 : ℝ)*(base19) + (506056641/50000000000000 : ℝ)*(base23) + (1146481/50000000000000 : ℝ)*(upper2) + (155300639/50000000000000 : ℝ)*(upper3) + (17454877/50000000000000 : ℝ)*(upper4) + (5769666638958527/100000000000000 : ℝ)*(major0) + (5769666638958527/100000000000000 : ℝ)*(major1) + (5769666638958527/100000000000000 : ℝ)*(major2) + (7688380153718531/100000000000000 : ℝ)*(sp0) + (7688395182422123/100000000000000 : ℝ)*(sp1) + (1537679101333923/20000000000000 : ℝ)*(sp2) + (962729881898719/25000000000000 : ℝ)*(sp3) + (8182532183/50000000000000 : ℝ)*(sp4) + (843081903/5000000000000 : ℝ)*(sp7) + (481367048654117/12500000000000 : ℝ)*(f.failure) + (480524782423931/6250000000000 : ℝ)*(f.sum) + (2416778451717/472812500000000000000000000 : ℝ)*base65 + (278707166754114513/189125000000000000000000000000000 : ℝ)*base67 + (584136895924635487/189125000000000000000000000000000 : ℝ)*base70 + (743651449450114513/189125000000000000000000000000000 : ℝ)*base71 + (8142949017267/7565000000000000000000000000 : ℝ)*base73 + (428456123314739513/189125000000000000000000000000000 : ℝ)*base75 + (688690524143260487/189125000000000000000000000000000 : ℝ)*base78 + (1622121619911614513/189125000000000000000000000000000 : ℝ)*base79 + (24730262159597/7565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (302627/1250000000000000000000 : ℝ)*base89 + (302627/1250000000000000000000 : ℝ)*base91 + (302627/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93755205716909484840653217/23640625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35001059/6250000000000 : ℝ)*(base19) + (138922129/20000000000000 : ℝ)*(base23) + (10565563/50000000000000 : ℝ)*(upper3) + (144428623/50000000000000 : ℝ)*(lower4) + (1449906473839003/25000000000000 : ℝ)*(major0) + (1449906473839003/25000000000000 : ℝ)*(major1) + (1449906473839003/25000000000000 : ℝ)*(major2) + (27904444107/100000000000000 : ℝ)*(sp1) + (4505413639/12500000000000 : ℝ)*(sp2) + (336851971/6250000000000 : ℝ)*(sp3) + (1545663821392441/20000000000000 : ℝ)*(sp4) + (7728290642501153/100000000000000 : ℝ)*(sp5) + (3864141184521223/50000000000000 : ℝ)*(sp6) + (1935463580961613/50000000000000 : ℝ)*(sp7) + (3870932551554761/100000000000000 : ℝ)*(f.failure) + (1545663821392441/20000000000000 : ℝ)*(f.sum) + (24359576064529/3782500000000000000000000000 : ℝ)*base66 + (372606668816923943/47281250000000000000000000000000 : ℝ)*base68 + (593007235693455193/47281250000000000000000000000000 : ℝ)*base70 + (760725514626142693/47281250000000000000000000000000 : ℝ)*base72 + (2010496857977/1891250000000000000000000000 : ℝ)*base74 + (479014565864017693/47281250000000000000000000000000 : ℝ)*base76 + (3502853676513557/47281250000000000000000000000000 : ℝ)*base77 + (49385034087923943/47281250000000000000000000000000 : ℝ)*base80 + (2061941551117/1891250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (34977409/10000000000000000000000 : ℝ)*base90 + (34977409/10000000000000000000000 : ℝ)*base92 + (34977409/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1160_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1160_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1160_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1160_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1160_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1160_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (261/64 : ℝ) ≤ p) (hpb : p ≤ (8353/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149825031/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16449/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1160_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:24.209838+00:00
-- url     : https://prove2.me/submissions/ba2426b3-68b4-4c90-9859-ebce1483db46

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
theorem support_rectangle_w1186_s0_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1877962627/10000000000 : ℝ)*x 0 + (3022108201/5000000000 : ℝ)*x 1 + (598251469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877962627/10000000000 : ℝ)^8379 ≤ (2733214313611/25000000000000 : ℝ)^6331 := by
    have hnat : (1877962627 : ℕ)^8379*25000000000000^6331 ≤ 2733214313611^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877962627 10000000000 2733214313611 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3022108201/5000000000 : ℝ)^8379 ≤ (12839443975437/25000000000000 : ℝ)^6331 := by
    have hnat : (3022108201 : ℕ)^8379*25000000000000^6331 ≤ 12839443975437^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022108201 5000000000 12839443975437 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598251469/1250000000 : ℝ)^8379 ≤ (7541873366839/20000000000000 : ℝ)^6331 := by
    have hnat : (598251469 : ℕ)^8379*20000000000000^6331 ≤ 7541873366839^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598251469 1250000000 7541873366839 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1877962627/10000000000 : ℝ), (3022108201/5000000000 : ℝ), (598251469/1250000000 : ℝ)] ![(2733214313611/25000000000000 : ℝ), (12839443975437/25000000000000 : ℝ), (7541873366839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1877962627/10000000000 : ℝ)|^8379 ≤ (2733214313611/25000000000000 : ℝ)^6331
        have hw : |(-1877962627/10000000000 : ℝ)|=(1877962627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3022108201/5000000000 : ℝ)|^8379 ≤ (12839443975437/25000000000000 : ℝ)^6331
        have hw : |(3022108201/5000000000 : ℝ)|=(3022108201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598251469/1250000000 : ℝ)|^8379 ≤ (7541873366839/20000000000000 : ℝ)^6331
        have hw : |(598251469/1250000000 : ℝ)|=(598251469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757157323/5000000000 : ℝ)*x 0 + (-2598792191/10000000000 : ℝ)*x 1 + (2393005887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757157323/5000000000 : ℝ)^8379 ≤ (5685612743357/12500000000000 : ℝ)^6331 := by
    have hnat : (2757157323 : ℕ)^8379*12500000000000^6331 ≤ 5685612743357^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757157323 5000000000 5685612743357 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598792191/10000000000 : ℝ)^8379 ≤ (840286548461/5000000000000 : ℝ)^6331 := by
    have hnat : (2598792191 : ℕ)^8379*5000000000000^6331 ≤ 840286548461^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598792191 10000000000 840286548461 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393005887/5000000000 : ℝ)^8379 ≤ (4713670882951/12500000000000 : ℝ)^6331 := by
    have hnat : (2393005887 : ℕ)^8379*12500000000000^6331 ≤ 4713670882951^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393005887 5000000000 4713670882951 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757157323/5000000000 : ℝ), (-2598792191/10000000000 : ℝ), (2393005887/5000000000 : ℝ)] ![(5685612743357/12500000000000 : ℝ), (840286548461/5000000000000 : ℝ), (4713670882951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757157323/5000000000 : ℝ)|^8379 ≤ (5685612743357/12500000000000 : ℝ)^6331
        have hw : |(2757157323/5000000000 : ℝ)|=(2757157323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2598792191/10000000000 : ℝ)|^8379 ≤ (840286548461/5000000000000 : ℝ)^6331
        have hw : |(-2598792191/10000000000 : ℝ)|=(2598792191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2393005887/5000000000 : ℝ)|^8379 ≤ (4713670882951/12500000000000 : ℝ)^6331
        have hw : |(2393005887/5000000000 : ℝ)|=(2393005887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1102862921/2000000000 : ℝ)*x 0 + (957202349/2000000000 : ℝ)*x 1 + (-2598792279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102862921/2000000000 : ℝ)^8379 ≤ (45484901499267/100000000000000 : ℝ)^6331 := by
    have hnat : (1102862921 : ℕ)^8379*100000000000000^6331 ≤ 45484901499267^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102862921 2000000000 45484901499267 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957202349/2000000000 : ℝ)^8379 ≤ (94273416903/250000000000 : ℝ)^6331 := by
    have hnat : (957202349 : ℕ)^8379*250000000000^6331 ≤ 94273416903^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957202349 2000000000 94273416903 250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598792279/10000000000 : ℝ)^8379 ≤ (8402865861191/50000000000000 : ℝ)^6331 := by
    have hnat : (2598792279 : ℕ)^8379*50000000000000^6331 ≤ 8402865861191^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598792279 10000000000 8402865861191 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102862921/2000000000 : ℝ), (957202349/2000000000 : ℝ), (-2598792279/10000000000 : ℝ)] ![(45484901499267/100000000000000 : ℝ), (94273416903/250000000000 : ℝ), (8402865861191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102862921/2000000000 : ℝ)|^8379 ≤ (45484901499267/100000000000000 : ℝ)^6331
        have hw : |(1102862921/2000000000 : ℝ)|=(1102862921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957202349/2000000000 : ℝ)|^8379 ≤ (94273416903/250000000000 : ℝ)^6331
        have hw : |(957202349/2000000000 : ℝ)|=(957202349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2598792279/10000000000 : ℝ)|^8379 ≤ (8402865861191/50000000000000 : ℝ)^6331
        have hw : |(-2598792279/10000000000 : ℝ)|=(2598792279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2098727723/5000000000 : ℝ)*x 0 + (389890907/1250000000 : ℝ)*x 1 + (2821957169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098727723/5000000000 : ℝ)^8379 ≤ (7924407131053/25000000000000 : ℝ)^6331 := by
    have hnat : (2098727723 : ℕ)^8379*25000000000000^6331 ≤ 7924407131053^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098727723 5000000000 7924407131053 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389890907/1250000000 : ℝ)^8379 ≤ (21397304801291/100000000000000 : ℝ)^6331 := by
    have hnat : (389890907 : ℕ)^8379*100000000000000^6331 ≤ 21397304801291^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389890907 1250000000 21397304801291 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821957169/5000000000 : ℝ)^8379 ≤ (46905066661107/100000000000000 : ℝ)^6331 := by
    have hnat : (2821957169 : ℕ)^8379*100000000000000^6331 ≤ 46905066661107^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821957169 5000000000 46905066661107 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098727723/5000000000 : ℝ), (389890907/1250000000 : ℝ), (2821957169/5000000000 : ℝ)] ![(7924407131053/25000000000000 : ℝ), (21397304801291/100000000000000 : ℝ), (46905066661107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098727723/5000000000 : ℝ)|^8379 ≤ (7924407131053/25000000000000 : ℝ)^6331
        have hw : |(2098727723/5000000000 : ℝ)|=(2098727723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389890907/1250000000 : ℝ)|^8379 ≤ (21397304801291/100000000000000 : ℝ)^6331
        have hw : |(389890907/1250000000 : ℝ)|=(389890907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2821957169/5000000000 : ℝ)|^8379 ≤ (46905066661107/100000000000000 : ℝ)^6331
        have hw : |(2821957169/5000000000 : ℝ)|=(2821957169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882980011/10000000000 : ℝ)*x 0 + (2409223181/5000000000 : ℝ)*x 1 + (3005319159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882980011/10000000000 : ℝ)^8379 ≤ (10971532356627/100000000000000 : ℝ)^6331 := by
    have hnat : (1882980011 : ℕ)^8379*100000000000000^6331 ≤ 10971532356627^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882980011 10000000000 10971532356627 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409223181/5000000000 : ℝ)^8379 ≤ (38047960707297/100000000000000 : ℝ)^6331 := by
    have hnat : (2409223181 : ℕ)^8379*100000000000000^6331 ≤ 38047960707297^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409223181 5000000000 38047960707297 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005319159/5000000000 : ℝ)^8379 ≤ (50980506929797/100000000000000 : ℝ)^6331 := by
    have hnat : (3005319159 : ℕ)^8379*100000000000000^6331 ≤ 50980506929797^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005319159 5000000000 50980506929797 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882980011/10000000000 : ℝ), (2409223181/5000000000 : ℝ), (3005319159/5000000000 : ℝ)] ![(10971532356627/100000000000000 : ℝ), (38047960707297/100000000000000 : ℝ), (50980506929797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882980011/10000000000 : ℝ)|^8379 ≤ (10971532356627/100000000000000 : ℝ)^6331
        have hw : |(-1882980011/10000000000 : ℝ)|=(1882980011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2409223181/5000000000 : ℝ)|^8379 ≤ (38047960707297/100000000000000 : ℝ)^6331
        have hw : |(2409223181/5000000000 : ℝ)|=(2409223181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005319159/5000000000 : ℝ)|^8379 ≤ (50980506929797/100000000000000 : ℝ)^6331
        have hw : |(3005319159/5000000000 : ℝ)|=(3005319159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586112091/5000000000 : ℝ)*x 0 + (-343541471/2500000000 : ℝ)*x 1 + (1502659497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586112091/5000000000 : ℝ)^8379 ≤ (41788377593071/100000000000000 : ℝ)^6331 := by
    have hnat : (2586112091 : ℕ)^8379*100000000000000^6331 ≤ 41788377593071^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586112091 5000000000 41788377593071 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343541471/2500000000 : ℝ)^8379 ≤ (723111917177/10000000000000 : ℝ)^6331 := by
    have hnat : (343541471 : ℕ)^8379*10000000000000^6331 ≤ 723111917177^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343541471 2500000000 723111917177 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502659497/2500000000 : ℝ)^8379 ≤ (25490251612701/50000000000000 : ℝ)^6331 := by
    have hnat : (1502659497 : ℕ)^8379*50000000000000^6331 ≤ 25490251612701^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502659497 2500000000 25490251612701 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586112091/5000000000 : ℝ), (-343541471/2500000000 : ℝ), (1502659497/2500000000 : ℝ)] ![(41788377593071/100000000000000 : ℝ), (723111917177/10000000000000 : ℝ), (25490251612701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586112091/5000000000 : ℝ)|^8379 ≤ (41788377593071/100000000000000 : ℝ)^6331
        have hw : |(2586112091/5000000000 : ℝ)|=(2586112091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343541471/2500000000 : ℝ)|^8379 ≤ (723111917177/10000000000000 : ℝ)^6331
        have hw : |(-343541471/2500000000 : ℝ)|=(343541471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502659497/2500000000 : ℝ)|^8379 ≤ (25490251612701/50000000000000 : ℝ)^6331
        have hw : |(1502659497/2500000000 : ℝ)|=(1502659497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1293056029/2500000000 : ℝ)*x 0 + (6010638171/10000000000 : ℝ)*x 1 + (-1374165689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293056029/2500000000 : ℝ)^8379 ≤ (5223547110917/12500000000000 : ℝ)^6331 := by
    have hnat : (1293056029 : ℕ)^8379*12500000000000^6331 ≤ 5223547110917^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293056029 2500000000 5223547110917 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6010638171/10000000000 : ℝ)^8379 ≤ (25490252639829/50000000000000 : ℝ)^6331 := by
    have hnat : (6010638171 : ℕ)^8379*50000000000000^6331 ≤ 25490252639829^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6010638171 10000000000 25490252639829 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374165689/10000000000 : ℝ)^8379 ≤ (903889726713/12500000000000 : ℝ)^6331 := by
    have hnat : (1374165689 : ℕ)^8379*12500000000000^6331 ≤ 903889726713^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374165689 10000000000 903889726713 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293056029/2500000000 : ℝ), (6010638171/10000000000 : ℝ), (-1374165689/10000000000 : ℝ)] ![(5223547110917/12500000000000 : ℝ), (25490252639829/50000000000000 : ℝ), (903889726713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293056029/2500000000 : ℝ)|^8379 ≤ (5223547110917/12500000000000 : ℝ)^6331
        have hw : |(1293056029/2500000000 : ℝ)|=(1293056029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6010638171/10000000000 : ℝ)|^8379 ≤ (25490252639829/50000000000000 : ℝ)^6331
        have hw : |(6010638171/10000000000 : ℝ)|=(6010638171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1374165689/10000000000 : ℝ)|^8379 ≤ (903889726713/12500000000000 : ℝ)^6331
        have hw : |(-1374165689/10000000000 : ℝ)|=(1374165689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s0_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103761857/5000000000 : ℝ)*x 0 + (2789414327/5000000000 : ℝ)*x 1 + (3186507381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103761857/5000000000 : ℝ)^8379 ≤ (31798294727557/100000000000000 : ℝ)^6331 := by
    have hnat : (2103761857 : ℕ)^8379*100000000000000^6331 ≤ 31798294727557^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103761857 5000000000 31798294727557 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2789414327/5000000000 : ℝ)^8379 ≤ (46190518086313/100000000000000 : ℝ)^6331 := by
    have hnat : (2789414327 : ℕ)^8379*100000000000000^6331 ≤ 46190518086313^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789414327 5000000000 46190518086313 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186507381/10000000000 : ℝ)^8379 ≤ (22011187170343/100000000000000 : ℝ)^6331 := by
    have hnat : (3186507381 : ℕ)^8379*100000000000000^6331 ≤ 22011187170343^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186507381 10000000000 22011187170343 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103761857/5000000000 : ℝ), (2789414327/5000000000 : ℝ), (3186507381/10000000000 : ℝ)] ![(31798294727557/100000000000000 : ℝ), (46190518086313/100000000000000 : ℝ), (22011187170343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103761857/5000000000 : ℝ)|^8379 ≤ (31798294727557/100000000000000 : ℝ)^6331
        have hw : |(2103761857/5000000000 : ℝ)|=(2103761857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2789414327/5000000000 : ℝ)|^8379 ≤ (46190518086313/100000000000000 : ℝ)^6331
        have hw : |(2789414327/5000000000 : ℝ)|=(2789414327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186507381/10000000000 : ℝ)|^8379 ≤ (22011187170343/100000000000000 : ℝ)^6331
        have hw : |(3186507381/10000000000 : ℝ)|=(3186507381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27647/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4189/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4189 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4189*1^1024 ≤ 0^1024*1^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4189/1024 : ℝ) ≤ (2355585809421978073/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4189 ≤ (2355585809421978073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4189*100000000000000000000^1024 ≤ 2355585809421978073^1024*5^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2355585809421978073 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2355585809421978073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4189 := by
      have hnat : (1 : ℕ)^1024*1^4189 ≤ 1^4189*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102355585809421978073/100000000000000000000 : ℝ) ≤ (1257134596626209/1250000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (102355585809421978073/100000000000000000000 : ℝ)^1024 ≤ (1257134596626209/1250000000000000 : ℝ)^4189 := by
      have hnat : (102355585809421978073 : ℕ)^1024*1250000000000000^4189 ≤ 1257134596626209^4189*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102355585809421978073 100000000000000000000 1257134596626209 1250000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257134596626209/1250000000000000 : ℝ)) (X := (102355585809421978073/100000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52355585809421978073/50000000000000000000 : ℝ) ≤ (632134596626209/625000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (52355585809421978073/50000000000000000000 : ℝ)^1024 ≤ (632134596626209/625000000000000 : ℝ)^4189 := by
      have hnat : (52355585809421978073 : ℕ)^1024*625000000000000^4189 ≤ 632134596626209^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52355585809421978073 50000000000000000000 632134596626209 625000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632134596626209/625000000000000 : ℝ)) (X := (52355585809421978073/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7134596626209/500000000000000 : ℝ)*(0 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7134596626209/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2355585809421978073/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7134596626209/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7134596626209/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257134596626209/1250000000000000 : ℝ) by norm_num, show 1+(2355585809421978073/100000000000000000000 : ℝ)+(0 : ℝ)=(102355585809421978073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2355585809421978073/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7134596626209/500000000000000 : ℝ)*(2/5 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7134596626209/500000000000000 : ℝ)*(2/5 : ℝ)=(632134596626209/625000000000000 : ℝ) by norm_num, show 1+2*(2355585809421978073/100000000000000000000 : ℝ)=(52355585809421978073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7134596626209/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7134596626209/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7134596626209/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7134596626209/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7134596626209/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7134596626209/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1877962627/10000000000 : ℝ)*X 0 0+(3022108201/5000000000 : ℝ)*X 0 1+(598251469/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757157323/5000000000 : ℝ)*X 1 0+(-2598792191/10000000000 : ℝ)*X 1 1+(2393005887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102862921/2000000000 : ℝ)*X 2 0+(957202349/2000000000 : ℝ)*X 2 1+(-2598792279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098727723/5000000000 : ℝ)*X 0 0+(389890907/1250000000 : ℝ)*X 0 1+(2821957169/5000000000 : ℝ)*X 0 2+(2098727723/5000000000 : ℝ)*X 1 0+(389890907/1250000000 : ℝ)*X 1 1+(2821957169/5000000000 : ℝ)*X 1 2+(2098727723/5000000000 : ℝ)*X 2 0+(389890907/1250000000 : ℝ)*X 2 1+(2821957169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1882980011/10000000000 : ℝ)*X 0 0+(2409223181/5000000000 : ℝ)*X 0 1+(3005319159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586112091/5000000000 : ℝ)*X 1 0+(-343541471/2500000000 : ℝ)*X 1 1+(1502659497/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293056029/2500000000 : ℝ)*X 2 0+(6010638171/10000000000 : ℝ)*X 2 1+(-1374165689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103761857/5000000000 : ℝ)*X 0 0+(2789414327/5000000000 : ℝ)*X 0 1+(3186507381/10000000000 : ℝ)*X 0 2+(2103761857/5000000000 : ℝ)*X 1 0+(2789414327/5000000000 : ℝ)*X 1 1+(3186507381/10000000000 : ℝ)*X 1 2+(2103761857/5000000000 : ℝ)*X 2 0+(2789414327/5000000000 : ℝ)*X 2 1+(3186507381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38760299238631457760237/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31050361/50000000000000 : ℝ)*(base1) + (1510956691/100000000000000 : ℝ)*(base19) + (1407326991/100000000000000 : ℝ)*(base23) + (97720281/100000000000000 : ℝ)*(base24) + (43615939/12500000000000 : ℝ)*(upper3) + (595434607482319/100000000000000 : ℝ)*(major0) + (595434607482319/100000000000000 : ℝ)*(major1) + (595434607482319/100000000000000 : ℝ)*(major2) + (397394199141901/50000000000000 : ℝ)*(sp0) + (397395090310719/50000000000000 : ℝ)*(sp1) + (794790186530857/100000000000000 : ℝ)*(sp2) + (198037288835779/50000000000000 : ℝ)*(sp3) + (3355395049/100000000000000 : ℝ)*(sp4) + (21415141/800000000000 : ℝ)*(sp7) + (198038658332453/50000000000000 : ℝ)*(f.failure) + (794791691578129/100000000000000 : ℝ)*(f.sum) + (101455501373671/25000000000000000000000000000 : ℝ)*base65 + (471762832498671/50000000000000000000000000000 : ℝ)*base67 + (177920398748671/50000000000000000000000000000 : ℝ)*base69 + (353795266198671/50000000000000000000000000000 : ℝ)*base71 + (108238245998671/25000000000000000000000000000 : ℝ)*base73 + (560186282448671/50000000000000000000000000000 : ℝ)*base75 + (449130989348671/50000000000000000000000000000 : ℝ)*base77 + (432726166348671/50000000000000000000000000000 : ℝ)*base79 + (6452746151329/25000000000000000000000000000 : ℝ)*base82 + (15250119/5000000000000000000000 : ℝ)*base89 + (15250119/5000000000000000000000 : ℝ)*base91 + (15250119/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (826763121170801499561/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36745189/100000000000000 : ℝ)*(base1) + (860141223/100000000000000 : ℝ)*(base19) + (853099419/100000000000000 : ℝ)*(base23) + (16821499/20000000000000 : ℝ)*(upper3) + (108057647/100000000000000 : ℝ)*(upper5) + (6283976773907/1000000000000 : ℝ)*(major0) + (6283976773907/1000000000000 : ℝ)*(major1) + (6283976773907/1000000000000 : ℝ)*(major2) + (1708828861/100000000000000 : ℝ)*(sp1) + (35283789/2000000000000 : ℝ)*(sp2) + (167758250147359/20000000000000 : ℝ)*(sp4) + (419394322510761/50000000000000 : ℝ)*(sp5) + (52424287293921/6250000000000 : ℝ)*(sp6) + (83600798761903/20000000000000 : ℝ)*(sp7) + (83600806110941/20000000000000 : ℝ)*(f.failure) + (419395606995803/50000000000000 : ℝ)*(f.sum) + (209650037313/250000000000000000000000000 : ℝ)*base65 + (2695382771437/500000000000000000000000000 : ℝ)*base68 + (209336983937/500000000000000000000000000 : ℝ)*base70 + (2041807431437/500000000000000000000000000 : ℝ)*base72 + (298317800813/250000000000000000000000000 : ℝ)*base73 + (5183475153937/500000000000000000000000000 : ℝ)*base76 + (1145364860563/500000000000000000000000000 : ℝ)*base77 + (1775150929437/500000000000000000000000000 : ℝ)*base80 + (558521388313/250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (22810543/2000000000000000000000 : ℝ)*base89 + (22810543/2000000000000000000000 : ℝ)*base91 + (22810543/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1186_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27647/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s1_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-103972263/500000000 : ℝ)*x 0 + (5689903903/10000000000 : ℝ)*x 1 + (2505673849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103972263/500000000 : ℝ)^8379 ≤ (12511574408713/100000000000000 : ℝ)^6331 := by
    have hnat : (103972263 : ℕ)^8379*100000000000000^6331 ≤ 12511574408713^6331*500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103972263 500000000 12511574408713 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5689903903/10000000000 : ℝ)^8379 ≤ (47411578367789/100000000000000 : ℝ)^6331 := by
    have hnat : (5689903903 : ℕ)^8379*100000000000000^6331 ≤ 47411578367789^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689903903 10000000000 47411578367789 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2505673849/5000000000 : ℝ)^8379 ≤ (20038423604091/50000000000000 : ℝ)^6331 := by
    have hnat : (2505673849 : ℕ)^8379*50000000000000^6331 ≤ 20038423604091^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505673849 5000000000 20038423604091 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103972263/500000000 : ℝ), (5689903903/10000000000 : ℝ), (2505673849/5000000000 : ℝ)] ![(12511574408713/100000000000000 : ℝ), (47411578367789/100000000000000 : ℝ), (20038423604091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103972263/500000000 : ℝ)|^8379 ≤ (12511574408713/100000000000000 : ℝ)^6331
        have hw : |(-103972263/500000000 : ℝ)|=(103972263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5689903903/10000000000 : ℝ)|^8379 ≤ (47411578367789/100000000000000 : ℝ)^6331
        have hw : |(5689903903/10000000000 : ℝ)|=(5689903903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2505673849/5000000000 : ℝ)|^8379 ≤ (20038423604091/50000000000000 : ℝ)^6331
        have hw : |(2505673849/5000000000 : ℝ)|=(2505673849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2708354679/5000000000 : ℝ)*x 0 + (-1222409197/5000000000 : ℝ)*x 1 + (5011347947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708354679/5000000000 : ℝ)^8379 ≤ (22211213381477/50000000000000 : ℝ)^6331 := by
    have hnat : (2708354679 : ℕ)^8379*50000000000000^6331 ≤ 22211213381477^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708354679 5000000000 22211213381477 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222409197/5000000000 : ℝ)^8379 ≤ (15500723385463/100000000000000 : ℝ)^6331 := by
    have hnat : (1222409197 : ℕ)^8379*100000000000000^6331 ≤ 15500723385463^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222409197 5000000000 15500723385463 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5011347947/10000000000 : ℝ)^8379 ≤ (40076849843653/100000000000000 : ℝ)^6331 := by
    have hnat : (5011347947 : ℕ)^8379*100000000000000^6331 ≤ 40076849843653^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011347947 10000000000 40076849843653 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708354679/5000000000 : ℝ), (-1222409197/5000000000 : ℝ), (5011347947/10000000000 : ℝ)] ![(22211213381477/50000000000000 : ℝ), (15500723385463/100000000000000 : ℝ), (40076849843653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708354679/5000000000 : ℝ)|^8379 ≤ (22211213381477/50000000000000 : ℝ)^6331
        have hw : |(2708354679/5000000000 : ℝ)|=(2708354679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1222409197/5000000000 : ℝ)|^8379 ≤ (15500723385463/100000000000000 : ℝ)^6331
        have hw : |(-1222409197/5000000000 : ℝ)|=(1222409197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5011347947/10000000000 : ℝ)|^8379 ≤ (40076849843653/100000000000000 : ℝ)^6331
        have hw : |(5011347947/10000000000 : ℝ)|=(5011347947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338544281/625000000 : ℝ)*x 0 + (5011348521/10000000000 : ℝ)*x 1 + (-2444818783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338544281/625000000 : ℝ)^8379 ≤ (71075867851/160000000000 : ℝ)^6331 := by
    have hnat : (338544281 : ℕ)^8379*160000000000^6331 ≤ 71075867851^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338544281 625000000 71075867851 160000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011348521/10000000000 : ℝ)^8379 ≤ (10019213979749/25000000000000 : ℝ)^6331 := by
    have hnat : (5011348521 : ℕ)^8379*25000000000000^6331 ≤ 10019213979749^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011348521 10000000000 10019213979749 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2444818783/10000000000 : ℝ)^8379 ≤ (15500726649649/100000000000000 : ℝ)^6331 := by
    have hnat : (2444818783 : ℕ)^8379*100000000000000^6331 ≤ 15500726649649^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444818783 10000000000 15500726649649 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338544281/625000000 : ℝ), (5011348521/10000000000 : ℝ), (-2444818783/10000000000 : ℝ)] ![(71075867851/160000000000 : ℝ), (10019213979749/25000000000000 : ℝ), (15500726649649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338544281/625000000 : ℝ)|^8379 ≤ (71075867851/160000000000 : ℝ)^6331
        have hw : |(338544281/625000000 : ℝ)|=(338544281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011348521/10000000000 : ℝ)|^8379 ≤ (10019213979749/25000000000000 : ℝ)^6331
        have hw : |(5011348521/10000000000 : ℝ)|=(5011348521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2444818783/10000000000 : ℝ)|^8379 ≤ (15500726649649/100000000000000 : ℝ)^6331
        have hw : |(-2444818783/10000000000 : ℝ)|=(2444818783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4313688637/10000000000 : ℝ)*x 0 + (1842619379/5000000000 : ℝ)*x 1 + (315429341/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313688637/10000000000 : ℝ)^8379 ≤ (16432245373599/50000000000000 : ℝ)^6331 := by
    have hnat : (4313688637 : ℕ)^8379*50000000000000^6331 ≤ 16432245373599^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313688637 10000000000 16432245373599 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842619379/5000000000 : ℝ)^8379 ≤ (26682261543341/100000000000000 : ℝ)^6331 := by
    have hnat : (1842619379 : ℕ)^8379*100000000000000^6331 ≤ 26682261543341^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842619379 5000000000 26682261543341 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315429341/625000000 : ℝ)^8379 ≤ (10113311923271/25000000000000 : ℝ)^6331 := by
    have hnat : (315429341 : ℕ)^8379*25000000000000^6331 ≤ 10113311923271^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315429341 625000000 10113311923271 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313688637/10000000000 : ℝ), (1842619379/5000000000 : ℝ), (315429341/625000000 : ℝ)] ![(16432245373599/50000000000000 : ℝ), (26682261543341/100000000000000 : ℝ), (10113311923271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313688637/10000000000 : ℝ)|^8379 ≤ (16432245373599/50000000000000 : ℝ)^6331
        have hw : |(4313688637/10000000000 : ℝ)|=(4313688637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842619379/5000000000 : ℝ)|^8379 ≤ (26682261543341/100000000000000 : ℝ)^6331
        have hw : |(1842619379/5000000000 : ℝ)|=(1842619379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315429341/625000000 : ℝ)|^8379 ≤ (10113311923271/25000000000000 : ℝ)^6331
        have hw : |(315429341/625000000 : ℝ)|=(315429341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080192327/10000000000 : ℝ)*x 0 + (2510228969/5000000000 : ℝ)*x 1 + (2840307913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080192327/10000000000 : ℝ)^8379 ≤ (2503504750687/20000000000000 : ℝ)^6331 := by
    have hnat : (2080192327 : ℕ)^8379*20000000000000^6331 ≤ 2503504750687^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080192327 10000000000 2503504750687 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510228969/5000000000 : ℝ)^8379 ≤ (1255415635639/3125000000000 : ℝ)^6331 := by
    have hnat : (2510228969 : ℕ)^8379*3125000000000^6331 ≤ 1255415635639^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510228969 5000000000 1255415635639 3125000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840307913/5000000000 : ℝ)^8379 ≤ (23654587947613/50000000000000 : ℝ)^6331 := by
    have hnat : (2840307913 : ℕ)^8379*50000000000000^6331 ≤ 23654587947613^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840307913 5000000000 23654587947613 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080192327/10000000000 : ℝ), (2510228969/5000000000 : ℝ), (2840307913/5000000000 : ℝ)] ![(2503504750687/20000000000000 : ℝ), (1255415635639/3125000000000 : ℝ), (23654587947613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080192327/10000000000 : ℝ)|^8379 ≤ (2503504750687/20000000000000 : ℝ)^6331
        have hw : |(-2080192327/10000000000 : ℝ)|=(2080192327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510228969/5000000000 : ℝ)|^8379 ≤ (1255415635639/3125000000000 : ℝ)^6331
        have hw : |(2510228969/5000000000 : ℝ)|=(2510228969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840307913/5000000000 : ℝ)|^8379 ≤ (23654587947613/50000000000000 : ℝ)^6331
        have hw : |(2840307913/5000000000 : ℝ)|=(2840307913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242360979/10000000000 : ℝ)*x 0 + (-887774759/5000000000 : ℝ)*x 1 + (5680617049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242360979/10000000000 : ℝ)^8379 ≤ (42539987639497/100000000000000 : ℝ)^6331 := by
    have hnat : (5242360979 : ℕ)^8379*100000000000000^6331 ≤ 42539987639497^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242360979 10000000000 42539987639497 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887774759/5000000000 : ℝ)^8379 ≤ (5075411484189/50000000000000 : ℝ)^6331 := by
    have hnat : (887774759 : ℕ)^8379*50000000000000^6331 ≤ 5075411484189^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887774759 5000000000 5075411484189 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680617049/10000000000 : ℝ)^8379 ≤ (1892367575017/4000000000000 : ℝ)^6331 := by
    have hnat : (5680617049 : ℕ)^8379*4000000000000^6331 ≤ 1892367575017^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680617049 10000000000 1892367575017 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242360979/10000000000 : ℝ), (-887774759/5000000000 : ℝ), (5680617049/10000000000 : ℝ)] ![(42539987639497/100000000000000 : ℝ), (5075411484189/50000000000000 : ℝ), (1892367575017/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242360979/10000000000 : ℝ)|^8379 ≤ (42539987639497/100000000000000 : ℝ)^6331
        have hw : |(5242360979/10000000000 : ℝ)|=(5242360979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887774759/5000000000 : ℝ)|^8379 ≤ (5075411484189/50000000000000 : ℝ)^6331
        have hw : |(-887774759/5000000000 : ℝ)|=(887774759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680617049/10000000000 : ℝ)|^8379 ≤ (1892367575017/4000000000000 : ℝ)^6331
        have hw : |(5680617049/10000000000 : ℝ)|=(5680617049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242360739/10000000000 : ℝ)*x 0 + (568061787/1000000000 : ℝ)*x 1 + (-887774331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242360739/10000000000 : ℝ)^8379 ≤ (2126999253099/5000000000000 : ℝ)^6331 := by
    have hnat : (5242360739 : ℕ)^8379*5000000000000^6331 ≤ 2126999253099^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242360739 10000000000 2126999253099 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568061787/1000000000 : ℝ)^8379 ≤ (11827299606171/25000000000000 : ℝ)^6331 := by
    have hnat : (568061787 : ℕ)^8379*25000000000000^6331 ≤ 11827299606171^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568061787 1000000000 11827299606171 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887774331/5000000000 : ℝ)^8379 ≤ (5075408245777/50000000000000 : ℝ)^6331 := by
    have hnat : (887774331 : ℕ)^8379*50000000000000^6331 ≤ 5075408245777^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887774331 5000000000 5075408245777 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242360739/10000000000 : ℝ), (568061787/1000000000 : ℝ), (-887774331/5000000000 : ℝ)] ![(2126999253099/5000000000000 : ℝ), (11827299606171/25000000000000 : ℝ), (5075408245777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242360739/10000000000 : ℝ)|^8379 ≤ (2126999253099/5000000000000 : ℝ)^6331
        have hw : |(5242360739/10000000000 : ℝ)|=(5242360739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568061787/1000000000 : ℝ)|^8379 ≤ (11827299606171/25000000000000 : ℝ)^6331
        have hw : |(568061787/1000000000 : ℝ)|=(568061787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-887774331/5000000000 : ℝ)|^8379 ≤ (5075408245777/50000000000000 : ℝ)^6331
        have hw : |(-887774331/5000000000 : ℝ)|=(887774331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s1_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315185601/10000000000 : ℝ)*x 0 + (2514294433/5000000000 : ℝ)*x 1 + (3703874247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315185601/10000000000 : ℝ)^8379 ≤ (1643979288407/5000000000000 : ℝ)^6331 := by
    have hnat : (4315185601 : ℕ)^8379*5000000000000^6331 ≤ 1643979288407^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315185601 10000000000 1643979288407 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514294433/5000000000 : ℝ)^8379 ≤ (10064858251107/25000000000000 : ℝ)^6331 := by
    have hnat : (2514294433 : ℕ)^8379*25000000000000^6331 ≤ 10064858251107^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514294433 5000000000 10064858251107 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3703874247/10000000000 : ℝ)^8379 ≤ (26860981207431/100000000000000 : ℝ)^6331 := by
    have hnat : (3703874247 : ℕ)^8379*100000000000000^6331 ≤ 26860981207431^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703874247 10000000000 26860981207431 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315185601/10000000000 : ℝ), (2514294433/5000000000 : ℝ), (3703874247/10000000000 : ℝ)] ![(1643979288407/5000000000000 : ℝ), (10064858251107/25000000000000 : ℝ), (26860981207431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315185601/10000000000 : ℝ)|^8379 ≤ (1643979288407/5000000000000 : ℝ)^6331
        have hw : |(4315185601/10000000000 : ℝ)|=(4315185601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2514294433/5000000000 : ℝ)|^8379 ≤ (10064858251107/25000000000000 : ℝ)^6331
        have hw : |(2514294433/5000000000 : ℝ)|=(2514294433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3703874247/10000000000 : ℝ)|^8379 ≤ (26860981207431/100000000000000 : ℝ)^6331
        have hw : |(3703874247/10000000000 : ℝ)|=(3703874247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1473/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27647/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27647/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27647/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27647/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27647/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27647/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (593/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (77618796533/100000000000000000000 : ℝ) := by
    have hpowers : (593/100000 : ℝ)^4189 ≤ (77618796533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (593 : ℕ)^4189*100000000000000000000^1024 ≤ 77618796533^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        593 100000 77618796533 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (593/100000 : ℝ)) (X := (77618796533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27647/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (519855146889656019/100000000000000000000 : ℝ) := by
    have hpowers : (27647/100000 : ℝ)^4189 ≤ (519855146889656019/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27647 : ℕ)^4189*100000000000000000000^1024 ≤ 519855146889656019^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27647 100000 519855146889656019 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27647/100000 : ℝ)) (X := (519855146889656019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000077618796533/50000000000000000000 : ℝ) ≤ (500000000189739/500000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50000000077618796533/50000000000000000000 : ℝ)^1024 ≤ (500000000189739/500000000000000 : ℝ)^4189 := by
      have hnat : (50000000077618796533 : ℕ)^1024*500000000000000^4189 ≤ 500000000189739^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000077618796533 50000000000000000000 500000000189739 500000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000189739/500000000000000 : ℝ)) (X := (50000000077618796533/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12564981903063556569/12500000000000000000 : ℝ) ≤ (312896342713971/312500000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (12564981903063556569/12500000000000000000 : ℝ)^1024 ≤ (312896342713971/312500000000000 : ℝ)^4189 := by
      have hnat : (12564981903063556569 : ℕ)^1024*312500000000000^4189 ≤ 312896342713971^4189*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12564981903063556569 12500000000000000000 312896342713971 312500000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312896342713971/312500000000000 : ℝ)) (X := (12564981903063556569/12500000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50519855146889656019/50000000000000000000 : ℝ) ≤ (2506341482474841/2500000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50519855146889656019/50000000000000000000 : ℝ)^1024 ≤ (2506341482474841/2500000000000000 : ℝ)^4189 := by
      have hnat : (50519855146889656019 : ℕ)^1024*2500000000000000^4189 ≤ 2506341482474841^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50519855146889656019 50000000000000000000 2506341482474841 2500000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506341482474841/2500000000000000 : ℝ)) (X := (50519855146889656019/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(77618796533/100000000000000000000 : ℝ) ≤ ((88061509800938789/88066406250000000 : ℝ)+2*(1056913587691/225450000000000 : ℝ)*(593/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (88061509800938789/88066406250000000 : ℝ)+2*(1056913587691/225450000000000 : ℝ)*(593/100000 : ℝ)=(500000000189739/500000000000000 : ℝ) by norm_num, show 1+2*(77618796533/100000000000000000000 : ℝ)=(50000000077618796533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(519855146889656019/100000000000000000000 : ℝ)+(77618796533/100000000000000000000 : ℝ) ≤ ((88061509800938789/88066406250000000 : ℝ)+(1056913587691/225450000000000 : ℝ)*((27647/100000 : ℝ)+(593/100000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (88061509800938789/88066406250000000 : ℝ)+(1056913587691/225450000000000 : ℝ)*((27647/100000 : ℝ)+(593/100000 : ℝ))=(312896342713971/312500000000000 : ℝ) by norm_num, show 1+(519855146889656019/100000000000000000000 : ℝ)+(77618796533/100000000000000000000 : ℝ)=(12564981903063556569/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(519855146889656019/100000000000000000000 : ℝ) ≤ ((88061509800938789/88066406250000000 : ℝ)+2*(1056913587691/225450000000000 : ℝ)*(27647/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (88061509800938789/88066406250000000 : ℝ)+2*(1056913587691/225450000000000 : ℝ)*(27647/100000 : ℝ)=(2506341482474841/2500000000000000 : ℝ) by norm_num, show 1+2*(519855146889656019/100000000000000000000 : ℝ)=(50519855146889656019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88061509800938789/88066406250000000 : ℝ)*(X 1 0+X 2 0)+(1056913587691/225450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (593/100000 : ℝ)) (hi := (27647/100000 : ℝ)) (c := (88061509800938789/88066406250000000 : ℝ)) (alpha := (1056913587691/225450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88061509800938789/88066406250000000 : ℝ)*(X 0 1+X 2 1)+(1056913587691/225450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (593/100000 : ℝ)) (hi := (27647/100000 : ℝ)) (c := (88061509800938789/88066406250000000 : ℝ)) (alpha := (1056913587691/225450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88061509800938789/88066406250000000 : ℝ)*(X 0 2+X 1 2)+(1056913587691/225450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (593/100000 : ℝ)) (hi := (27647/100000 : ℝ)) (c := (88061509800938789/88066406250000000 : ℝ)) (alpha := (1056913587691/225450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-103972263/500000000 : ℝ)*X 0 0+(5689903903/10000000000 : ℝ)*X 0 1+(2505673849/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2708354679/5000000000 : ℝ)*X 1 0+(-1222409197/5000000000 : ℝ)*X 1 1+(5011347947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338544281/625000000 : ℝ)*X 2 0+(5011348521/10000000000 : ℝ)*X 2 1+(-2444818783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313688637/10000000000 : ℝ)*X 0 0+(1842619379/5000000000 : ℝ)*X 0 1+(315429341/625000000 : ℝ)*X 0 2+(4313688637/10000000000 : ℝ)*X 1 0+(1842619379/5000000000 : ℝ)*X 1 1+(315429341/625000000 : ℝ)*X 1 2+(4313688637/10000000000 : ℝ)*X 2 0+(1842619379/5000000000 : ℝ)*X 2 1+(315429341/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2080192327/10000000000 : ℝ)*X 0 0+(2510228969/5000000000 : ℝ)*X 0 1+(2840307913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242360979/10000000000 : ℝ)*X 1 0+(-887774759/5000000000 : ℝ)*X 1 1+(5680617049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242360739/10000000000 : ℝ)*X 2 0+(568061787/1000000000 : ℝ)*X 2 1+(-887774331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315185601/10000000000 : ℝ)*X 0 0+(2514294433/5000000000 : ℝ)*X 0 1+(3703874247/10000000000 : ℝ)*X 0 2+(4315185601/10000000000 : ℝ)*X 1 0+(2514294433/5000000000 : ℝ)*X 1 1+(3703874247/10000000000 : ℝ)*X 1 2+(4315185601/10000000000 : ℝ)*X 2 0+(2514294433/5000000000 : ℝ)*X 2 1+(3703874247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19658107060664147729516199/2609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3541779/12500000000000 : ℝ)*(base1) + (72545351/4000000000000 : ℝ)*(base19) + (315821487/20000000000000 : ℝ)*(base23) + (299768501/100000000000000 : ℝ)*(upper3) + (48250363/50000000000000 : ℝ)*(upper5) + (1104081349761333/100000000000000 : ℝ)*(major0) + (1104081349761333/100000000000000 : ℝ)*(major1) + (1104081349761333/100000000000000 : ℝ)*(major2) + (1473728912534539/100000000000000 : ℝ)*(sp0) + (1473736446287143/100000000000000 : ℝ)*(sp1) + (736868340406741/50000000000000 : ℝ)*(sp2) + (367209219713339/50000000000000 : ℝ)*(sp3) + (9375720611/100000000000000 : ℝ)*(sp4) + (5720719303/100000000000000 : ℝ)*(sp7) + (183606047120053/25000000000000 : ℝ)*(f.failure) + (736869129960459/50000000000000 : ℝ)*(f.sum) + (1659702900937/1252500000000000000000000000 : ℝ)*base65 + (877399839573201/1304687500000000000000000000000 : ℝ)*base68 + (2686437879801799/1304687500000000000000000000000 : ℝ)*base69 + (686081629282481/326171875000000000000000000000 : ℝ)*base71 + (550074413617/1252500000000000000000000000 : ℝ)*base73 + (1507309764744223/2609375000000000000000000000000 : ℝ)*base75 + (7574855168489299/1304687500000000000000000000000 : ℝ)*base77 + (5932433978212973/2609375000000000000000000000000 : ℝ)*base79 + (839011036619/2505000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (25595081/2500000000000000000000 : ℝ)*base90 + (25595081/2500000000000000000000 : ℝ)*base92 + (25595081/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4005445004574939018751863/521875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77174211/3125000000000 : ℝ)*(base19) + (2810382199/100000000000000 : ℝ)*(base23) + (143866291/100000000000000 : ℝ)*(upper2) + (421536857/100000000000000 : ℝ)*(upper3) + (124872023/50000000000000 : ℝ)*(upper5) + (226966705719429/20000000000000 : ℝ)*(major0) + (226966705719429/20000000000000 : ℝ)*(major1) + (226966705719429/20000000000000 : ℝ)*(major2) + (12407945411/100000000000000 : ℝ)*(sp1) + (16489033583/100000000000000 : ℝ)*(sp2) + (757393281125837/50000000000000 : ℝ)*(sp4) + (1514771684731511/100000000000000 : ℝ)*(sp5) + (378691815708973/25000000000000 : ℝ)*(sp6) + (150976047821161/20000000000000 : ℝ)*(sp7) + (150976047821161/20000000000000 : ℝ)*(f.failure) + (757393281125837/50000000000000 : ℝ)*(f.sum) + (1657043614019/300600000000000000000000000 : ℝ)*base66 + (9620122779805003/1565625000000000000000000000000 : ℝ)*base68 + (2232984640042657/391406250000000000000000000000 : ℝ)*base70 + (6639210151273753/1565625000000000000000000000000 : ℝ)*base72 + (1015073931967/375750000000000000000000000 : ℝ)*base74 + (150428170940117/97851562500000000000000000000 : ℝ)*base75 + (2702200816963439/782812500000000000000000000000 : ℝ)*base78 + (1656800715013439/782812500000000000000000000000 : ℝ)*base80 + (69197868109/15030000000000000000000000 : ℝ)*base82 + (14383603/2000000000000000000000 : ℝ)*base89 + (14383603/2000000000000000000000 : ℝ)*base91 + (14383603/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1186_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1473/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s2_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065171769/5000000000 : ℝ)*x 0 + (687830351/1250000000 : ℝ)*x 1 + (5166201857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065171769/5000000000 : ℝ)^8379 ≤ (12918480366119/100000000000000 : ℝ)^6331 := by
    have hnat : (1065171769 : ℕ)^8379*100000000000000^6331 ≤ 12918480366119^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065171769 5000000000 12918480366119 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687830351/1250000000 : ℝ)^8379 ≤ (1814301055917/4000000000000 : ℝ)^6331 := by
    have hnat : (687830351 : ℕ)^8379*4000000000000^6331 ≤ 1814301055917^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687830351 1250000000 1814301055917 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5166201857/10000000000 : ℝ)^8379 ≤ (41723993228081/100000000000000 : ℝ)^6331 := by
    have hnat : (5166201857 : ℕ)^8379*100000000000000^6331 ≤ 41723993228081^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166201857 10000000000 41723993228081 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065171769/5000000000 : ℝ), (687830351/1250000000 : ℝ), (5166201857/10000000000 : ℝ)] ![(12918480366119/100000000000000 : ℝ), (1814301055917/4000000000000 : ℝ), (41723993228081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065171769/5000000000 : ℝ)|^8379 ≤ (12918480366119/100000000000000 : ℝ)^6331
        have hw : |(-1065171769/5000000000 : ℝ)|=(1065171769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687830351/1250000000 : ℝ)|^8379 ≤ (1814301055917/4000000000000 : ℝ)^6331
        have hw : |(687830351/1250000000 : ℝ)|=(687830351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5166201857/10000000000 : ℝ)|^8379 ≤ (41723993228081/100000000000000 : ℝ)^6331
        have hw : |(5166201857/10000000000 : ℝ)|=(5166201857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342999371/2500000000 : ℝ)*x 0 + (-28812071/125000000 : ℝ)*x 1 + (80721963/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342999371/2500000000 : ℝ)^8379 ≤ (2746111049143/6250000000000 : ℝ)^6331 := by
    have hnat : (1342999371 : ℕ)^8379*6250000000000^6331 ≤ 2746111049143^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342999371 2500000000 2746111049143 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28812071/125000000 : ℝ)^8379 ≤ (14338189624887/100000000000000 : ℝ)^6331 := by
    have hnat : (28812071 : ℕ)^8379*100000000000000^6331 ≤ 14338189624887^6331*125000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28812071 125000000 14338189624887 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80721963/156250000 : ℝ)^8379 ≤ (4172403357881/10000000000000 : ℝ)^6331 := by
    have hnat : (80721963 : ℕ)^8379*10000000000000^6331 ≤ 4172403357881^6331*156250000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80721963 156250000 4172403357881 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342999371/2500000000 : ℝ), (-28812071/125000000 : ℝ), (80721963/156250000 : ℝ)] ![(2746111049143/6250000000000 : ℝ), (14338189624887/100000000000000 : ℝ), (4172403357881/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342999371/2500000000 : ℝ)|^8379 ≤ (2746111049143/6250000000000 : ℝ)^6331
        have hw : |(1342999371/2500000000 : ℝ)|=(1342999371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28812071/125000000 : ℝ)|^8379 ≤ (14338189624887/100000000000000 : ℝ)^6331
        have hw : |(-28812071/125000000 : ℝ)|=(28812071/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80721963/156250000 : ℝ)|^8379 ≤ (4172403357881/10000000000000 : ℝ)^6331
        have hw : |(80721963/156250000 : ℝ)|=(80721963/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342999721/2500000000 : ℝ)*x 0 + (5166203639/10000000000 : ℝ)*x 1 + (-1152483213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342999721/2500000000 : ℝ)^8379 ≤ (1373055998159/3125000000000 : ℝ)^6331 := by
    have hnat : (1342999721 : ℕ)^8379*3125000000000^6331 ≤ 1373055998159^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342999721 2500000000 1373055998159 3125000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5166203639/10000000000 : ℝ)^8379 ≤ (20862006137881/50000000000000 : ℝ)^6331 := by
    have hnat : (5166203639 : ℕ)^8379*50000000000000^6331 ≤ 20862006137881^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166203639 10000000000 20862006137881 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152483213/5000000000 : ℝ)^8379 ≤ (14338195766587/100000000000000 : ℝ)^6331 := by
    have hnat : (1152483213 : ℕ)^8379*100000000000000^6331 ≤ 14338195766587^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152483213 5000000000 14338195766587 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342999721/2500000000 : ℝ), (5166203639/10000000000 : ℝ), (-1152483213/5000000000 : ℝ)] ![(1373055998159/3125000000000 : ℝ), (20862006137881/50000000000000 : ℝ), (14338195766587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342999721/2500000000 : ℝ)|^8379 ≤ (1373055998159/3125000000000 : ℝ)^6331
        have hw : |(1342999721/2500000000 : ℝ)|=(1342999721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5166203639/10000000000 : ℝ)|^8379 ≤ (20862006137881/50000000000000 : ℝ)^6331
        have hw : |(5166203639/10000000000 : ℝ)|=(5166203639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1152483213/5000000000 : ℝ)|^8379 ≤ (14338195766587/100000000000000 : ℝ)^6331
        have hw : |(-1152483213/5000000000 : ℝ)|=(1152483213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348716373/10000000000 : ℝ)*x 0 + (503001287/1250000000 : ℝ)*x 1 + (4699127999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348716373/10000000000 : ℝ)^8379 ≤ (3321814512453/10000000000000 : ℝ)^6331 := by
    have hnat : (4348716373 : ℕ)^8379*10000000000000^6331 ≤ 3321814512453^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348716373 10000000000 3321814512453 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503001287/1250000000 : ℝ)^8379 ≤ (14987914362649/50000000000000 : ℝ)^6331 := by
    have hnat : (503001287 : ℕ)^8379*50000000000000^6331 ≤ 14987914362649^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503001287 1250000000 14987914362649 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4699127999/10000000000 : ℝ)^8379 ≤ (29444820901/80000000000 : ℝ)^6331 := by
    have hnat : (4699127999 : ℕ)^8379*80000000000^6331 ≤ 29444820901^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699127999 10000000000 29444820901 80000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348716373/10000000000 : ℝ), (503001287/1250000000 : ℝ), (4699127999/10000000000 : ℝ)] ![(3321814512453/10000000000000 : ℝ), (14987914362649/50000000000000 : ℝ), (29444820901/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348716373/10000000000 : ℝ)|^8379 ≤ (3321814512453/10000000000000 : ℝ)^6331
        have hw : |(4348716373/10000000000 : ℝ)|=(4348716373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503001287/1250000000 : ℝ)|^8379 ≤ (14987914362649/50000000000000 : ℝ)^6331
        have hw : |(503001287/1250000000 : ℝ)|=(503001287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4699127999/10000000000 : ℝ)|^8379 ≤ (29444820901/80000000000 : ℝ)^6331
        have hw : |(4699127999/10000000000 : ℝ)|=(4699127999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53260843/250000000 : ℝ)*x 0 + (2584226221/5000000000 : ℝ)*x 1 + (2750185519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53260843/250000000 : ℝ)^8379 ≤ (2583840828531/20000000000000 : ℝ)^6331 := by
    have hnat : (53260843 : ℕ)^8379*20000000000000^6331 ≤ 2583840828531^6331*250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53260843 250000000 2583840828531 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584226221/5000000000 : ℝ)^8379 ≤ (5218506409523/12500000000000 : ℝ)^6331 := by
    have hnat : (2584226221 : ℕ)^8379*12500000000000^6331 ≤ 5218506409523^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584226221 5000000000 5218506409523 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750185519/5000000000 : ℝ)^8379 ≤ (5666593071711/12500000000000 : ℝ)^6331 := by
    have hnat : (2750185519 : ℕ)^8379*12500000000000^6331 ≤ 5666593071711^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750185519 5000000000 5666593071711 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53260843/250000000 : ℝ), (2584226221/5000000000 : ℝ), (2750185519/5000000000 : ℝ)] ![(2583840828531/20000000000000 : ℝ), (5218506409523/12500000000000 : ℝ), (5666593071711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53260843/250000000 : ℝ)|^8379 ≤ (2583840828531/20000000000000 : ℝ)^6331
        have hw : |(-53260843/250000000 : ℝ)|=(53260843/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584226221/5000000000 : ℝ)|^8379 ≤ (5218506409523/12500000000000 : ℝ)^6331
        have hw : |(2584226221/5000000000 : ℝ)|=(2584226221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750185519/5000000000 : ℝ)|^8379 ≤ (5666593071711/12500000000000 : ℝ)^6331
        have hw : |(2750185519/5000000000 : ℝ)|=(2750185519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321596653/2500000000 : ℝ)*x 0 + (-985399381/5000000000 : ℝ)*x 1 + (5500371047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321596653/2500000000 : ℝ)^8379 ≤ (43013448766451/100000000000000 : ℝ)^6331 := by
    have hnat : (1321596653 : ℕ)^8379*100000000000000^6331 ≤ 43013448766451^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321596653 2500000000 43013448766451 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985399381/5000000000 : ℝ)^8379 ≤ (2913451637021/25000000000000 : ℝ)^6331 := by
    have hnat : (985399381 : ℕ)^8379*25000000000000^6331 ≤ 2913451637021^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985399381 5000000000 2913451637021 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500371047/10000000000 : ℝ)^8379 ≤ (22666372335929/50000000000000 : ℝ)^6331 := by
    have hnat : (5500371047 : ℕ)^8379*50000000000000^6331 ≤ 22666372335929^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500371047 10000000000 22666372335929 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321596653/2500000000 : ℝ), (-985399381/5000000000 : ℝ), (5500371047/10000000000 : ℝ)] ![(43013448766451/100000000000000 : ℝ), (2913451637021/25000000000000 : ℝ), (22666372335929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321596653/2500000000 : ℝ)|^8379 ≤ (43013448766451/100000000000000 : ℝ)^6331
        have hw : |(1321596653/2500000000 : ℝ)|=(1321596653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985399381/5000000000 : ℝ)|^8379 ≤ (2913451637021/25000000000000 : ℝ)^6331
        have hw : |(-985399381/5000000000 : ℝ)|=(985399381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500371047/10000000000 : ℝ)|^8379 ≤ (22666372335929/50000000000000 : ℝ)^6331
        have hw : |(5500371047/10000000000 : ℝ)|=(5500371047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330399173/625000000 : ℝ)*x 0 + (5500371053/10000000000 : ℝ)*x 1 + (-985399269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330399173/625000000 : ℝ)^8379 ≤ (344107603571/800000000000 : ℝ)^6331 := by
    have hnat : (330399173 : ℕ)^8379*800000000000^6331 ≤ 344107603571^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330399173 625000000 344107603571 800000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500371053/10000000000 : ℝ)^8379 ≤ (22666372368653/50000000000000 : ℝ)^6331 := by
    have hnat : (5500371053 : ℕ)^8379*50000000000000^6331 ≤ 22666372368653^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500371053 10000000000 22666372368653 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985399269/5000000000 : ℝ)^8379 ≤ (5826902397519/50000000000000 : ℝ)^6331 := by
    have hnat : (985399269 : ℕ)^8379*50000000000000^6331 ≤ 5826902397519^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985399269 5000000000 5826902397519 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330399173/625000000 : ℝ), (5500371053/10000000000 : ℝ), (-985399269/5000000000 : ℝ)] ![(344107603571/800000000000 : ℝ), (22666372368653/50000000000000 : ℝ), (5826902397519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330399173/625000000 : ℝ)|^8379 ≤ (344107603571/800000000000 : ℝ)^6331
        have hw : |(330399173/625000000 : ℝ)|=(330399173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500371053/10000000000 : ℝ)|^8379 ≤ (22666372368653/50000000000000 : ℝ)^6331
        have hw : |(5500371053/10000000000 : ℝ)|=(5500371053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985399269/5000000000 : ℝ)|^8379 ≤ (5826902397519/50000000000000 : ℝ)^6331
        have hw : |(-985399269/5000000000 : ℝ)|=(985399269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s2_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174449701/5000000000 : ℝ)*x 0 + (938922899/2000000000 : ℝ)*x 1 + (503570847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174449701/5000000000 : ℝ)^8379 ≤ (2076249717997/6250000000000 : ℝ)^6331 := by
    have hnat : (2174449701 : ℕ)^8379*6250000000000^6331 ≤ 2076249717997^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174449701 5000000000 2076249717997 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938922899/2000000000 : ℝ)^8379 ≤ (7351849060299/20000000000000 : ℝ)^6331 := by
    have hnat : (938922899 : ℕ)^8379*20000000000000^6331 ≤ 7351849060299^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938922899 2000000000 7351849060299 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503570847/1250000000 : ℝ)^8379 ≤ (30020759196421/100000000000000 : ℝ)^6331 := by
    have hnat : (503570847 : ℕ)^8379*100000000000000^6331 ≤ 30020759196421^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503570847 1250000000 30020759196421 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174449701/5000000000 : ℝ), (938922899/2000000000 : ℝ), (503570847/1250000000 : ℝ)] ![(2076249717997/6250000000000 : ℝ), (7351849060299/20000000000000 : ℝ), (30020759196421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174449701/5000000000 : ℝ)|^8379 ≤ (2076249717997/6250000000000 : ℝ)^6331
        have hw : |(2174449701/5000000000 : ℝ)|=(2174449701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(938922899/2000000000 : ℝ)|^8379 ≤ (7351849060299/20000000000000 : ℝ)^6331
        have hw : |(938922899/2000000000 : ℝ)|=(938922899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503570847/1250000000 : ℝ)|^8379 ≤ (30020759196421/100000000000000 : ℝ)^6331
        have hw : |(503570847/1250000000 : ℝ)|=(503570847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1473/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1853/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (131/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1473/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1473/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1473/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1473/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1473/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1473/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1473/25000 : ℝ) ^ (4189/1024 : ℝ) ≤ (931892529578733/100000000000000000000 : ℝ) := by
    have hpowers : (1473/25000 : ℝ)^4189 ≤ (931892529578733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1473 : ℕ)^4189*100000000000000000000^1024 ≤ 931892529578733^1024*25000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 25000 931892529578733 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/25000 : ℝ)) (X := (931892529578733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20241/100000 : ℝ) ^ (4189/1024 : ℝ) ≤ (145184291562532219/100000000000000000000 : ℝ) := by
    have hpowers : (20241/100000 : ℝ)^4189 ≤ (145184291562532219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20241 : ℕ)^4189*100000000000000000000^1024 ≤ 145184291562532219^1024*100000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20241 100000 145184291562532219 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20241/100000 : ℝ)) (X := (145184291562532219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000931892529578733/50000000000000000000 : ℝ) ≤ (10000045559858273/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50000931892529578733/50000000000000000000 : ℝ)^1024 ≤ (10000045559858273/10000000000000000 : ℝ)^4189 := by
      have hnat : (50000931892529578733 : ℕ)^1024*10000000000000000^4189 ≤ 10000045559858273^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000931892529578733 50000000000000000000 10000045559858273 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000045559858273/10000000000000000 : ℝ)) (X := (50000931892529578733/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12518264523011513869/12500000000000000000 : ℝ) ≤ (5001784918269087/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (12518264523011513869/12500000000000000000 : ℝ)^1024 ≤ (5001784918269087/5000000000000000 : ℝ)^4189 := by
      have hnat : (12518264523011513869 : ℕ)^1024*5000000000000000^4189 ≤ 5001784918269087^4189*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518264523011513869 12500000000000000000 5001784918269087 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001784918269087/5000000000000000 : ℝ)) (X := (12518264523011513869/12500000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50145184291562532219/50000000000000000000 : ℝ) ≤ (400283764528723/400000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50145184291562532219/50000000000000000000 : ℝ)^1024 ≤ (400283764528723/400000000000000 : ℝ)^4189 := by
      have hnat : (50145184291562532219 : ℕ)^1024*400000000000000^4189 ≤ 400283764528723^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50145184291562532219 50000000000000000000 400283764528723 400000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400283764528723/400000000000000 : ℝ)) (X := (50145184291562532219/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(931892529578733/100000000000000000000 : ℝ) ≤ ((47816374554003468631/47830000000000000000 : ℝ)+2*(3524276679901/1434900000000000 : ℝ)*(1473/25000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (47816374554003468631/47830000000000000000 : ℝ)+2*(3524276679901/1434900000000000 : ℝ)*(1473/25000 : ℝ)=(10000045559858273/10000000000000000 : ℝ) by norm_num, show 1+2*(931892529578733/100000000000000000000 : ℝ)=(50000931892529578733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(145184291562532219/100000000000000000000 : ℝ)+(931892529578733/100000000000000000000 : ℝ) ≤ ((47816374554003468631/47830000000000000000 : ℝ)+(3524276679901/1434900000000000 : ℝ)*((20241/100000 : ℝ)+(1473/25000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (47816374554003468631/47830000000000000000 : ℝ)+(3524276679901/1434900000000000 : ℝ)*((20241/100000 : ℝ)+(1473/25000 : ℝ))=(5001784918269087/5000000000000000 : ℝ) by norm_num, show 1+(145184291562532219/100000000000000000000 : ℝ)+(931892529578733/100000000000000000000 : ℝ)=(12518264523011513869/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(145184291562532219/100000000000000000000 : ℝ) ≤ ((47816374554003468631/47830000000000000000 : ℝ)+2*(3524276679901/1434900000000000 : ℝ)*(20241/100000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (47816374554003468631/47830000000000000000 : ℝ)+2*(3524276679901/1434900000000000 : ℝ)*(20241/100000 : ℝ)=(400283764528723/400000000000000 : ℝ) by norm_num, show 1+2*(145184291562532219/100000000000000000000 : ℝ)=(50145184291562532219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47816374554003468631/47830000000000000000 : ℝ)*(X 1 0+X 2 0)+(3524276679901/1434900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1473/25000 : ℝ)) (hi := (20241/100000 : ℝ)) (c := (47816374554003468631/47830000000000000000 : ℝ)) (alpha := (3524276679901/1434900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47816374554003468631/47830000000000000000 : ℝ)*(X 0 1+X 2 1)+(3524276679901/1434900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1473/25000 : ℝ)) (hi := (20241/100000 : ℝ)) (c := (47816374554003468631/47830000000000000000 : ℝ)) (alpha := (3524276679901/1434900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47816374554003468631/47830000000000000000 : ℝ)*(X 0 2+X 1 2)+(3524276679901/1434900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1473/25000 : ℝ)) (hi := (20241/100000 : ℝ)) (c := (47816374554003468631/47830000000000000000 : ℝ)) (alpha := (3524276679901/1434900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1065171769/5000000000 : ℝ)*X 0 0+(687830351/1250000000 : ℝ)*X 0 1+(5166201857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342999371/2500000000 : ℝ)*X 1 0+(-28812071/125000000 : ℝ)*X 1 1+(80721963/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342999721/2500000000 : ℝ)*X 2 0+(5166203639/10000000000 : ℝ)*X 2 1+(-1152483213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348716373/10000000000 : ℝ)*X 0 0+(503001287/1250000000 : ℝ)*X 0 1+(4699127999/10000000000 : ℝ)*X 0 2+(4348716373/10000000000 : ℝ)*X 1 0+(503001287/1250000000 : ℝ)*X 1 1+(4699127999/10000000000 : ℝ)*X 1 2+(4348716373/10000000000 : ℝ)*X 2 0+(503001287/1250000000 : ℝ)*X 2 1+(4699127999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53260843/250000000 : ℝ)*X 0 0+(2584226221/5000000000 : ℝ)*X 0 1+(2750185519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321596653/2500000000 : ℝ)*X 1 0+(-985399381/5000000000 : ℝ)*X 1 1+(5500371047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330399173/625000000 : ℝ)*X 2 0+(5500371053/10000000000 : ℝ)*X 2 1+(-985399269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174449701/5000000000 : ℝ)*X 0 0+(938922899/2000000000 : ℝ)*X 0 1+(503570847/1250000000 : ℝ)*X 0 2+(2174449701/5000000000 : ℝ)*X 1 0+(938922899/2000000000 : ℝ)*X 1 1+(503570847/1250000000 : ℝ)*X 1 2+(2174449701/5000000000 : ℝ)*X 2 0+(938922899/2000000000 : ℝ)*X 2 1+(503570847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5041517283825938626264056507/2391500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29044593/10000000000000 : ℝ)*(base23) + (63522047/100000000000000 : ℝ)*(upper2) + (310572473/100000000000000 : ℝ)*(upper3) + (35415603/12500000000000 : ℝ)*(upper4) + (2226788230863201/100000000000000 : ℝ)*(major0) + (2226788230863201/100000000000000 : ℝ)*(major1) + (2226788230863201/100000000000000 : ℝ)*(major2) + (1486157104157737/50000000000000 : ℝ)*(sp0) + (74308462299559/2500000000000 : ℝ)*(sp1) + (743083373649637/25000000000000 : ℝ)*(sp2) + (46288380075041/3125000000000 : ℝ)*(sp3) + (24283666887/100000000000000 : ℝ)*(sp4) + (4706937883/100000000000000 : ℝ)*(sp6) + (4868536389/50000000000000 : ℝ)*(sp7) + (148123789947409/10000000000000 : ℝ)*(f.failure) + (74308462299559/2500000000000 : ℝ)*(f.sum) + (78253774550167/23915000000000000000000000000 : ℝ)*base65 + (5410750453071552169/4783000000000000000000000000000000 : ℝ)*base68 + (34979351246472447831/4783000000000000000000000000000000 : ℝ)*base69 + (2631300303416447831/4783000000000000000000000000000000 : ℝ)*base71 + (25130703057363/23915000000000000000000000000 : ℝ)*base74 + (50468629944804447831/4783000000000000000000000000000000 : ℝ)*base75 + (1288375786328447831/4783000000000000000000000000000000 : ℝ)*base77 + (33214893488346552169/4783000000000000000000000000000000 : ℝ)*base80 + (156585672621057/23915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1246507/1000000000000000000000 : ℝ)*base89 + (1246507/1000000000000000000000 : ℝ)*base91 + (1246507/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1289465499912267336495973543/298937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1137516979/100000000000000 : ℝ)*(base19) + (266596279/20000000000000 : ℝ)*(base23) + (3262509/12500000000000 : ℝ)*(upper2) + (29877561/20000000000000 : ℝ)*(upper3) + (92336133/100000000000000 : ℝ)*(upper5) + (282136299061051/12500000000000 : ℝ)*(major0) + (282136299061051/12500000000000 : ℝ)*(major1) + (282136299061051/12500000000000 : ℝ)*(major2) + (10927645977/100000000000000 : ℝ)*(sp1) + (14458591721/100000000000000 : ℝ)*(sp2) + (1506393019085423/50000000000000 : ℝ)*(sp4) + (301277397300789/10000000000000 : ℝ)*(sp5) + (301277024659773/10000000000000 : ℝ)*(sp6) + (1501394603022791/100000000000000 : ℝ)*(sp7) + (1501394603022791/100000000000000 : ℝ)*(f.failure) + (1506393019085423/50000000000000 : ℝ)*(f.sum) + (53062905854209/35872500000000000000000000000 : ℝ)*base65 + (9134596808291851457/1793625000000000000000000000000000 : ℝ)*base68 + (1282259754212773543/1793625000000000000000000000000000 : ℝ)*base69 + (7153000003353976457/1793625000000000000000000000000000 : ℝ)*base72 + (213190147498883/71745000000000000000000000000 : ℝ)*base73 + (7154495133281476457/1793625000000000000000000000000000 : ℝ)*base76 + (5830360008128023543/1793625000000000000000000000000000 : ℝ)*base77 + (975533854350976457/1793625000000000000000000000000000 : ℝ)*base80 + (76173044089879/35872500000000000000000000000 : ℝ)*base81 + (6648093/10000000000000000000000 : ℝ)*base89 + (6648093/10000000000000000000000 : ℝ)*base91 + (6648093/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1186_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1473/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (131/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1186_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (131/800 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1186_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1186_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1186_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (131/800 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

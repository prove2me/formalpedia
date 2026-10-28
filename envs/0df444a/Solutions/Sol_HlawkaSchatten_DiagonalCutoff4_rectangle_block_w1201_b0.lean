-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:09.359747+00:00
-- url     : https://prove2.me/submissions/76c2a9dc-e1c6-4d9a-9055-5a5f8bb505f3

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
theorem support_rectangle_w1201_s0_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873277073/10000000000 : ℝ)*x 0 + (1208158761/2000000000 : ℝ)*x 1 + (957577733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873277073/10000000000 : ℝ)^4197 ≤ (10910734225911/100000000000000 : ℝ)^3173 := by
    have hnat : (1873277073 : ℕ)^4197*100000000000000^3173 ≤ 10910734225911^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873277073 10000000000 10910734225911 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208158761/2000000000 : ℝ)^4197 ≤ (6417384088409/12500000000000 : ℝ)^3173 := by
    have hnat : (1208158761 : ℕ)^4197*12500000000000^3173 ≤ 6417384088409^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208158761 2000000000 6417384088409 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957577733/2000000000 : ℝ)^4197 ≤ (943754826363/2500000000000 : ℝ)^3173 := by
    have hnat : (957577733 : ℕ)^4197*2500000000000^3173 ≤ 943754826363^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957577733 2000000000 943754826363 2500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873277073/10000000000 : ℝ), (1208158761/2000000000 : ℝ), (957577733/2000000000 : ℝ)] ![(10910734225911/100000000000000 : ℝ), (6417384088409/12500000000000 : ℝ), (943754826363/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873277073/10000000000 : ℝ)|^4197 ≤ (10910734225911/100000000000000 : ℝ)^3173
        have hw : |(-1873277073/10000000000 : ℝ)|=(1873277073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208158761/2000000000 : ℝ)|^4197 ≤ (6417384088409/12500000000000 : ℝ)^3173
        have hw : |(1208158761/2000000000 : ℝ)|=(1208158761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957577733/2000000000 : ℝ)|^4197 ≤ (943754826363/2500000000000 : ℝ)^3173
        have hw : |(957577733/2000000000 : ℝ)|=(957577733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2756734601/5000000000 : ℝ)*x 0 + (-647664071/2500000000 : ℝ)*x 1 + (4787888627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756734601/5000000000 : ℝ)^4197 ≤ (45496380196797/100000000000000 : ℝ)^3173 := by
    have hnat : (2756734601 : ℕ)^4197*100000000000000^3173 ≤ 45496380196797^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756734601 5000000000 45496380196797 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647664071/2500000000 : ℝ)^4197 ≤ (523544597911/3125000000000 : ℝ)^3173 := by
    have hnat : (647664071 : ℕ)^4197*3125000000000^3173 ≤ 523544597911^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647664071 2500000000 523544597911 3125000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787888627/10000000000 : ℝ)^4197 ≤ (37750192658217/100000000000000 : ℝ)^3173 := by
    have hnat : (4787888627 : ℕ)^4197*100000000000000^3173 ≤ 37750192658217^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787888627 10000000000 37750192658217 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756734601/5000000000 : ℝ), (-647664071/2500000000 : ℝ), (4787888627/10000000000 : ℝ)] ![(45496380196797/100000000000000 : ℝ), (523544597911/3125000000000 : ℝ), (37750192658217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756734601/5000000000 : ℝ)|^4197 ≤ (45496380196797/100000000000000 : ℝ)^3173
        have hw : |(2756734601/5000000000 : ℝ)|=(2756734601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-647664071/2500000000 : ℝ)|^4197 ≤ (523544597911/3125000000000 : ℝ)^3173
        have hw : |(-647664071/2500000000 : ℝ)|=(647664071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787888627/10000000000 : ℝ)|^4197 ≤ (37750192658217/100000000000000 : ℝ)^3173
        have hw : |(4787888627/10000000000 : ℝ)|=(4787888627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (110269391/200000000 : ℝ)*x 0 + (4787888297/10000000000 : ℝ)*x 1 + (-1295328121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110269391/200000000 : ℝ)^4197 ≤ (5687047999399/12500000000000 : ℝ)^3173 := by
    have hnat : (110269391 : ℕ)^4197*12500000000000^3173 ≤ 5687047999399^3173*200000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110269391 200000000 5687047999399 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787888297/10000000000 : ℝ)^4197 ≤ (9437547304159/25000000000000 : ℝ)^3173 := by
    have hnat : (4787888297 : ℕ)^4197*25000000000000^3173 ≤ 9437547304159^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787888297 10000000000 9437547304159 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295328121/5000000000 : ℝ)^4197 ≤ (16753426773889/100000000000000 : ℝ)^3173 := by
    have hnat : (1295328121 : ℕ)^4197*100000000000000^3173 ≤ 16753426773889^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295328121 5000000000 16753426773889 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110269391/200000000 : ℝ), (4787888297/10000000000 : ℝ), (-1295328121/5000000000 : ℝ)] ![(5687047999399/12500000000000 : ℝ), (9437547304159/25000000000000 : ℝ), (16753426773889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110269391/200000000 : ℝ)|^4197 ≤ (5687047999399/12500000000000 : ℝ)^3173
        have hw : |(110269391/200000000 : ℝ)|=(110269391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787888297/10000000000 : ℝ)|^4197 ≤ (9437547304159/25000000000000 : ℝ)^3173
        have hw : |(4787888297/10000000000 : ℝ)|=(4787888297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1295328121/5000000000 : ℝ)|^4197 ≤ (16753426773889/100000000000000 : ℝ)^3173
        have hw : |(-1295328121/5000000000 : ℝ)|=(1295328121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839252159/2000000000 : ℝ)*x 0 + (779625371/2500000000 : ℝ)*x 1 + (5640002817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839252159/2000000000 : ℝ)^4197 ≤ (31706735248239/100000000000000 : ℝ)^3173 := by
    have hnat : (839252159 : ℕ)^4197*100000000000000^3173 ≤ 31706735248239^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839252159 2000000000 31706735248239 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779625371/2500000000 : ℝ)^4197 ≤ (21410691214057/100000000000000 : ℝ)^3173 := by
    have hnat : (779625371 : ℕ)^4197*100000000000000^3173 ≤ 21410691214057^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779625371 2500000000 21410691214057 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5640002817/10000000000 : ℝ)^4197 ≤ (146508042259/312500000000 : ℝ)^3173 := by
    have hnat : (5640002817 : ℕ)^4197*312500000000^3173 ≤ 146508042259^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640002817 10000000000 146508042259 312500000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839252159/2000000000 : ℝ), (779625371/2500000000 : ℝ), (5640002817/10000000000 : ℝ)] ![(31706735248239/100000000000000 : ℝ), (21410691214057/100000000000000 : ℝ), (146508042259/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839252159/2000000000 : ℝ)|^4197 ≤ (31706735248239/100000000000000 : ℝ)^3173
        have hw : |(839252159/2000000000 : ℝ)|=(839252159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779625371/2500000000 : ℝ)|^4197 ≤ (21410691214057/100000000000000 : ℝ)^3173
        have hw : |(779625371/2500000000 : ℝ)|=(779625371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5640002817/10000000000 : ℝ)|^4197 ≤ (146508042259/312500000000 : ℝ)^3173
        have hw : |(5640002817/10000000000 : ℝ)|=(5640002817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939125723/5000000000 : ℝ)*x 0 + (4820179017/10000000000 : ℝ)*x 1 + (750920517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939125723/5000000000 : ℝ)^4197 ≤ (2737268402711/25000000000000 : ℝ)^3173 := by
    have hnat : (939125723 : ℕ)^4197*25000000000000^3173 ≤ 2737268402711^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939125723 5000000000 2737268402711 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820179017/10000000000 : ℝ)^4197 ≤ (9521829028097/25000000000000 : ℝ)^3173 := by
    have hnat : (4820179017 : ℕ)^4197*25000000000000^3173 ≤ 9521829028097^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820179017 10000000000 9521829028097 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750920517/1250000000 : ℝ)^4197 ≤ (50963610257367/100000000000000 : ℝ)^3173 := by
    have hnat : (750920517 : ℕ)^4197*100000000000000^3173 ≤ 50963610257367^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750920517 1250000000 50963610257367 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939125723/5000000000 : ℝ), (4820179017/10000000000 : ℝ), (750920517/1250000000 : ℝ)] ![(2737268402711/25000000000000 : ℝ), (9521829028097/25000000000000 : ℝ), (50963610257367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939125723/5000000000 : ℝ)|^4197 ≤ (2737268402711/25000000000000 : ℝ)^3173
        have hw : |(-939125723/5000000000 : ℝ)|=(939125723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820179017/10000000000 : ℝ)|^4197 ≤ (9521829028097/25000000000000 : ℝ)^3173
        have hw : |(4820179017/10000000000 : ℝ)|=(4820179017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750920517/1250000000 : ℝ)|^4197 ≤ (50963610257367/100000000000000 : ℝ)^3173
        have hw : |(750920517/1250000000 : ℝ)|=(750920517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293187587/2500000000 : ℝ)*x 0 + (-685590083/5000000000 : ℝ)*x 1 + (1501841479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293187587/2500000000 : ℝ)^4197 ≤ (10453768636751/25000000000000 : ℝ)^3173 := by
    have hnat : (1293187587 : ℕ)^4197*25000000000000^3173 ≤ 10453768636751^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293187587 2500000000 10453768636751 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685590083/5000000000 : ℝ)^4197 ≤ (3610647606403/50000000000000 : ℝ)^3173 := by
    have hnat : (685590083 : ℕ)^4197*50000000000000^3173 ≤ 3610647606403^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685590083 5000000000 3610647606403 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1501841479/2500000000 : ℝ)^4197 ≤ (50963630231371/100000000000000 : ℝ)^3173 := by
    have hnat : (1501841479 : ℕ)^4197*100000000000000^3173 ≤ 50963630231371^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501841479 2500000000 50963630231371 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293187587/2500000000 : ℝ), (-685590083/5000000000 : ℝ), (1501841479/2500000000 : ℝ)] ![(10453768636751/25000000000000 : ℝ), (3610647606403/50000000000000 : ℝ), (50963630231371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293187587/2500000000 : ℝ)|^4197 ≤ (10453768636751/25000000000000 : ℝ)^3173
        have hw : |(1293187587/2500000000 : ℝ)|=(1293187587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685590083/5000000000 : ℝ)|^4197 ≤ (3610647606403/50000000000000 : ℝ)^3173
        have hw : |(-685590083/5000000000 : ℝ)|=(685590083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1501841479/2500000000 : ℝ)|^4197 ≤ (50963630231371/100000000000000 : ℝ)^3173
        have hw : |(1501841479/2500000000 : ℝ)|=(1501841479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034550421/2000000000 : ℝ)*x 0 + (600736473/1000000000 : ℝ)*x 1 + (-68558969/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034550421/2000000000 : ℝ)^4197 ≤ (41815093333771/100000000000000 : ℝ)^3173 := by
    have hnat : (1034550421 : ℕ)^4197*100000000000000^3173 ≤ 41815093333771^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034550421 2000000000 41815093333771 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600736473/1000000000 : ℝ)^4197 ≤ (50963616922849/100000000000000 : ℝ)^3173 := by
    have hnat : (600736473 : ℕ)^4197*100000000000000^3173 ≤ 50963616922849^3173*1000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600736473 1000000000 50963616922849 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68558969/500000000 : ℝ)^4197 ≤ (1444257947491/20000000000000 : ℝ)^3173 := by
    have hnat : (68558969 : ℕ)^4197*20000000000000^3173 ≤ 1444257947491^3173*500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68558969 500000000 1444257947491 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034550421/2000000000 : ℝ), (600736473/1000000000 : ℝ), (-68558969/500000000 : ℝ)] ![(41815093333771/100000000000000 : ℝ), (50963616922849/100000000000000 : ℝ), (1444257947491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034550421/2000000000 : ℝ)|^4197 ≤ (41815093333771/100000000000000 : ℝ)^3173
        have hw : |(1034550421/2000000000 : ℝ)|=(1034550421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600736473/1000000000 : ℝ)|^4197 ≤ (50963616922849/100000000000000 : ℝ)^3173
        have hw : |(600736473/1000000000 : ℝ)|=(600736473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68558969/500000000 : ℝ)|^4197 ≤ (1444257947491/20000000000000 : ℝ)^3173
        have hw : |(-68558969/500000000 : ℝ)|=(68558969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s0_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105156791/250000000 : ℝ)*x 0 + (2787510477/5000000000 : ℝ)*x 1 + (398221969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105156791/250000000 : ℝ)^4197 ≤ (7951706603649/25000000000000 : ℝ)^3173 := by
    have hnat : (105156791 : ℕ)^4197*25000000000000^3173 ≤ 7951706603649^3173*250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105156791 250000000 7951706603649 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787510477/5000000000 : ℝ)^4197 ≤ (2308471011111/5000000000000 : ℝ)^3173 := by
    have hnat : (2787510477 : ℕ)^4197*5000000000000^3173 ≤ 2308471011111^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787510477 5000000000 2308471011111 5000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398221969/1250000000 : ℝ)^4197 ≤ (11011876671943/50000000000000 : ℝ)^3173 := by
    have hnat : (398221969 : ℕ)^4197*50000000000000^3173 ≤ 11011876671943^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398221969 1250000000 11011876671943 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105156791/250000000 : ℝ), (2787510477/5000000000 : ℝ), (398221969/1250000000 : ℝ)] ![(7951706603649/25000000000000 : ℝ), (2308471011111/5000000000000 : ℝ), (11011876671943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105156791/250000000 : ℝ)|^4197 ≤ (7951706603649/25000000000000 : ℝ)^3173
        have hw : |(105156791/250000000 : ℝ)|=(105156791/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787510477/5000000000 : ℝ)|^4197 ≤ (2308471011111/5000000000000 : ℝ)^3173
        have hw : |(2787510477/5000000000 : ℝ)|=(2787510477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398221969/1250000000 : ℝ)|^4197 ≤ (11011876671943/50000000000000 : ℝ)^3173
        have hw : |(398221969/1250000000 : ℝ)|=(398221969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (327/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2759/10000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (8393/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8393 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8393*1^2048 ≤ 0^2048*1^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8393/2048 : ℝ) ≤ (1169915066644338869/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8393 ≤ (1169915066644338869/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8393*50000000000000000000^2048 ≤ 1169915066644338869^2048*5^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1169915066644338869 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1169915066644338869/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8393 := by
      have hnat : (1 : ℕ)^2048*1^8393 ≤ 1^8393*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51169915066644338869/50000000000000000000 : ℝ) ≤ (5028298351106999/5000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (51169915066644338869/50000000000000000000 : ℝ)^2048 ≤ (5028298351106999/5000000000000000 : ℝ)^8393 := by
      have hnat : (51169915066644338869 : ℕ)^2048*5000000000000000^8393 ≤ 5028298351106999^8393*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51169915066644338869 50000000000000000000 5028298351106999 5000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028298351106999/5000000000000000 : ℝ)) (X := (51169915066644338869/50000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26169915066644338869/25000000000000000000 : ℝ) ≤ (2528298351106999/2500000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (26169915066644338869/25000000000000000000 : ℝ)^2048 ≤ (2528298351106999/2500000000000000 : ℝ)^8393 := by
      have hnat : (26169915066644338869 : ℕ)^2048*2500000000000000^8393 ≤ 2528298351106999^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26169915066644338869 25000000000000000000 2528298351106999 2500000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528298351106999/2500000000000000 : ℝ)) (X := (26169915066644338869/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28298351106999/2000000000000000 : ℝ)*(0 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28298351106999/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1169915066644338869/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28298351106999/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28298351106999/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028298351106999/5000000000000000 : ℝ) by norm_num, show 1+(1169915066644338869/50000000000000000000 : ℝ)+(0 : ℝ)=(51169915066644338869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1169915066644338869/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28298351106999/2000000000000000 : ℝ)*(2/5 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28298351106999/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528298351106999/2500000000000000 : ℝ) by norm_num, show 1+2*(1169915066644338869/50000000000000000000 : ℝ)=(26169915066644338869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28298351106999/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28298351106999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28298351106999/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28298351106999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28298351106999/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28298351106999/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1873277073/10000000000 : ℝ)*X 0 0+(1208158761/2000000000 : ℝ)*X 0 1+(957577733/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2756734601/5000000000 : ℝ)*X 1 0+(-647664071/2500000000 : ℝ)*X 1 1+(4787888627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((110269391/200000000 : ℝ)*X 2 0+(4787888297/10000000000 : ℝ)*X 2 1+(-1295328121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839252159/2000000000 : ℝ)*X 0 0+(779625371/2500000000 : ℝ)*X 0 1+(5640002817/10000000000 : ℝ)*X 0 2+(839252159/2000000000 : ℝ)*X 1 0+(779625371/2500000000 : ℝ)*X 1 1+(5640002817/10000000000 : ℝ)*X 1 2+(839252159/2000000000 : ℝ)*X 2 0+(779625371/2500000000 : ℝ)*X 2 1+(5640002817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-939125723/5000000000 : ℝ)*X 0 0+(4820179017/10000000000 : ℝ)*X 0 1+(750920517/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293187587/2500000000 : ℝ)*X 1 0+(-685590083/5000000000 : ℝ)*X 1 1+(1501841479/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034550421/2000000000 : ℝ)*X 2 0+(600736473/1000000000 : ℝ)*X 2 1+(-68558969/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105156791/250000000 : ℝ)*X 0 0+(2787510477/5000000000 : ℝ)*X 0 1+(398221969/1250000000 : ℝ)*X 0 2+(105156791/250000000 : ℝ)*X 1 0+(2787510477/5000000000 : ℝ)*X 1 1+(398221969/1250000000 : ℝ)*X 1 2+(105156791/250000000 : ℝ)*X 2 0+(2787510477/5000000000 : ℝ)*X 2 1+(398221969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4005658306936493037/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33810003/100000000000000 : ℝ)*(base1) + (952002447/100000000000000 : ℝ)*(base19) + (922656681/100000000000000 : ℝ)*(base23) + (39861731/50000000000000 : ℝ)*(base24) + (47708357/20000000000000 : ℝ)*(upper3) + (597370989572631/100000000000000 : ℝ)*(major0) + (597370989572631/100000000000000 : ℝ)*(major1) + (597370989572631/100000000000000 : ℝ)*(major2) + (199537035292003/25000000000000 : ℝ)*(sp0) + (399074555277063/50000000000000 : ℝ)*(sp1) + (79814906017643/10000000000000 : ℝ)*(sp2) + (79318008696519/20000000000000 : ℝ)*(sp3) + (391039713/20000000000000 : ℝ)*(sp4) + (1705774141/100000000000000 : ℝ)*(sp7) + (19829589153337/5000000000000 : ℝ)*(f.failure) + (798150062556573/100000000000000 : ℝ)*(f.sum) + (155738723044369/100000000000000000000000000000 : ℝ)*base65 + (1316914788855631/200000000000000000000000000000 : ℝ)*base68 + (204155169544369/200000000000000000000000000000 : ℝ)*base69 + (59865580455631/200000000000000000000000000000 : ℝ)*base72 + (115254608055631/100000000000000000000000000000 : ℝ)*base74 + (373500066855631/200000000000000000000000000000 : ℝ)*base76 + (424598609944369/200000000000000000000000000000 : ℝ)*base77 + (1020307477855631/200000000000000000000000000000 : ℝ)*base80 + (442932454244369/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1277317/125000000000000000000 : ℝ)*base89 + (1277317/125000000000000000000 : ℝ)*base91 + (1277317/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183106292357582190218379/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (243997487/100000000000000 : ℝ)*(base19) + (9520297/1562500000000 : ℝ)*(base23) + (12192599/100000000000000 : ℝ)*(base39) + (156314483/100000000000000 : ℝ)*(upper3) + (78804449888987/12500000000000 : ℝ)*(major0) + (630435599111897/100000000000000 : ℝ)*(major1) + (630435586919297/100000000000000 : ℝ)*(major2) + (46658901/6250000000000 : ℝ)*(sp1) + (1768801257/100000000000000 : ℝ)*(sp2) + (9393397/5000000000000 : ℝ)*(sp3) + (842327903572489/100000000000000 : ℝ)*(sp4) + (168465382606517/20000000000000 : ℝ)*(sp5) + (842325537664823/100000000000000 : ℝ)*(sp6) + (418543033555329/100000000000000 : ℝ)*(sp7) + (418543221423269/100000000000000 : ℝ)*(f.failure) + (26322747367659/3125000000000 : ℝ)*(f.sum) + (93106346263403/100000000000000000000000000000 : ℝ)*base65 + (693413997059703/200000000000000000000000000000 : ℝ)*base67 + (328766442467103/200000000000000000000000000000 : ℝ)*base69 + (427404669540297/200000000000000000000000000000 : ℝ)*base72 + (94050219780193/200000000000000000000000000000 : ℝ)*base74 + (193282981720013/25000000000000000000000000000 : ℝ)*base75 + (358130504132897/200000000000000000000000000000 : ℝ)*base78 + (103982385095013/25000000000000000000000000000 : ℝ)*base79 + (558379399827207/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7452529/2500000000000000000000 : ℝ)*base89 + (17547471/2500000000000000000000 : ℝ)*base92 + (7452529/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1201_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (327/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2759/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1201_s1_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073672461/10000000000 : ℝ)*x 0 + (355375997/625000000 : ℝ)*x 1 + (5014388533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073672461/10000000000 : ℝ)^4197 ≤ (6240315050989/50000000000000 : ℝ)^3173 := by
    have hnat : (2073672461 : ℕ)^4197*50000000000000^3173 ≤ 6240315050989^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073672461 10000000000 6240315050989 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355375997/625000000 : ℝ)^4197 ≤ (5923644934583/12500000000000 : ℝ)^3173 := by
    have hnat : (355375997 : ℕ)^4197*12500000000000^3173 ≤ 5923644934583^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355375997 625000000 5923644934583 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014388533/10000000000 : ℝ)^4197 ≤ (20065105203309/50000000000000 : ℝ)^3173 := by
    have hnat : (5014388533 : ℕ)^4197*50000000000000^3173 ≤ 20065105203309^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014388533 10000000000 20065105203309 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073672461/10000000000 : ℝ), (355375997/625000000 : ℝ), (5014388533/10000000000 : ℝ)] ![(6240315050989/50000000000000 : ℝ), (5923644934583/12500000000000 : ℝ), (20065105203309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073672461/10000000000 : ℝ)|^4197 ≤ (6240315050989/50000000000000 : ℝ)^3173
        have hw : |(-2073672461/10000000000 : ℝ)|=(2073672461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355375997/625000000 : ℝ)|^4197 ≤ (5923644934583/12500000000000 : ℝ)^3173
        have hw : |(355375997/625000000 : ℝ)|=(355375997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5014388533/10000000000 : ℝ)|^4197 ≤ (20065105203309/50000000000000 : ℝ)^3173
        have hw : |(5014388533/10000000000 : ℝ)|=(5014388533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415888483/10000000000 : ℝ)*x 0 + (-2435046011/10000000000 : ℝ)*x 1 + (2507194469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415888483/10000000000 : ℝ)^4197 ≤ (5554293485437/12500000000000 : ℝ)^3173 := by
    have hnat : (5415888483 : ℕ)^4197*12500000000000^3173 ≤ 5554293485437^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415888483 10000000000 5554293485437 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435046011/10000000000 : ℝ)^4197 ≤ (15435437409601/100000000000000 : ℝ)^3173 := by
    have hnat : (2435046011 : ℕ)^4197*100000000000000^3173 ≤ 15435437409601^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435046011 10000000000 15435437409601 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507194469/5000000000 : ℝ)^4197 ≤ (20065107346927/50000000000000 : ℝ)^3173 := by
    have hnat : (2507194469 : ℕ)^4197*50000000000000^3173 ≤ 20065107346927^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507194469 5000000000 20065107346927 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415888483/10000000000 : ℝ), (-2435046011/10000000000 : ℝ), (2507194469/5000000000 : ℝ)] ![(5554293485437/12500000000000 : ℝ), (15435437409601/100000000000000 : ℝ), (20065107346927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415888483/10000000000 : ℝ)|^4197 ≤ (5554293485437/12500000000000 : ℝ)^3173
        have hw : |(5415888483/10000000000 : ℝ)|=(5415888483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2435046011/10000000000 : ℝ)|^4197 ≤ (15435437409601/100000000000000 : ℝ)^3173
        have hw : |(-2435046011/10000000000 : ℝ)|=(2435046011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2507194469/5000000000 : ℝ)|^4197 ≤ (20065107346927/50000000000000 : ℝ)^3173
        have hw : |(2507194469/5000000000 : ℝ)|=(2507194469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707943677/5000000000 : ℝ)*x 0 + (2507194831/5000000000 : ℝ)*x 1 + (-1217523279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707943677/5000000000 : ℝ)^4197 ≤ (11108583907839/25000000000000 : ℝ)^3173 := by
    have hnat : (2707943677 : ℕ)^4197*25000000000000^3173 ≤ 11108583907839^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707943677 5000000000 11108583907839 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507194831/5000000000 : ℝ)^4197 ≤ (802604447159/2000000000000 : ℝ)^3173 := by
    have hnat : (2507194831 : ℕ)^4197*2000000000000^3173 ≤ 802604447159^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507194831 5000000000 802604447159 2000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217523279/5000000000 : ℝ)^4197 ≤ (385886049899/2500000000000 : ℝ)^3173 := by
    have hnat : (1217523279 : ℕ)^4197*2500000000000^3173 ≤ 385886049899^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217523279 5000000000 385886049899 2500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707943677/5000000000 : ℝ), (2507194831/5000000000 : ℝ), (-1217523279/5000000000 : ℝ)] ![(11108583907839/25000000000000 : ℝ), (802604447159/2000000000000 : ℝ), (385886049899/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707943677/5000000000 : ℝ)|^4197 ≤ (11108583907839/25000000000000 : ℝ)^3173
        have hw : |(2707943677/5000000000 : ℝ)|=(2707943677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2507194831/5000000000 : ℝ)|^4197 ≤ (802604447159/2000000000000 : ℝ)^3173
        have hw : |(2507194831/5000000000 : ℝ)|=(2507194831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217523279/5000000000 : ℝ)|^4197 ≤ (385886049899/2500000000000 : ℝ)^3173
        have hw : |(-1217523279/5000000000 : ℝ)|=(1217523279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312402189/10000000000 : ℝ)*x 0 + (1844005689/5000000000 : ℝ)*x 1 + (2519838869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312402189/10000000000 : ℝ)^4197 ≤ (4109081762721/12500000000000 : ℝ)^3173 := by
    have hnat : (4312402189 : ℕ)^4197*12500000000000^3173 ≤ 4109081762721^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312402189 10000000000 4109081762721 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1844005689/5000000000 : ℝ)^4197 ≤ (26729212213657/100000000000000 : ℝ)^3173 := by
    have hnat : (1844005689 : ℕ)^4197*100000000000000^3173 ≤ 26729212213657^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844005689 5000000000 26729212213657 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2519838869/5000000000 : ℝ)^4197 ≤ (20199066831359/50000000000000 : ℝ)^3173 := by
    have hnat : (2519838869 : ℕ)^4197*50000000000000^3173 ≤ 20199066831359^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519838869 5000000000 20199066831359 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312402189/10000000000 : ℝ), (1844005689/5000000000 : ℝ), (2519838869/5000000000 : ℝ)] ![(4109081762721/12500000000000 : ℝ), (26729212213657/100000000000000 : ℝ), (20199066831359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312402189/10000000000 : ℝ)|^4197 ≤ (4109081762721/12500000000000 : ℝ)^3173
        have hw : |(4312402189/10000000000 : ℝ)|=(4312402189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1844005689/5000000000 : ℝ)|^4197 ≤ (26729212213657/100000000000000 : ℝ)^3173
        have hw : |(1844005689/5000000000 : ℝ)|=(1844005689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2519838869/5000000000 : ℝ)|^4197 ≤ (20199066831359/50000000000000 : ℝ)^3173
        have hw : |(2519838869/5000000000 : ℝ)|=(2519838869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037199073/5000000000 : ℝ)*x 0 + (1004670531/2000000000 : ℝ)*x 1 + (5676879257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037199073/5000000000 : ℝ)^4197 ≤ (12486407574871/100000000000000 : ℝ)^3173 := by
    have hnat : (1037199073 : ℕ)^4197*100000000000000^3173 ≤ 12486407574871^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037199073 5000000000 12486407574871 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004670531/2000000000 : ℝ)^4197 ≤ (4022512987999/10000000000000 : ℝ)^3173 := by
    have hnat : (1004670531 : ℕ)^4197*10000000000000^3173 ≤ 4022512987999^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004670531 2000000000 4022512987999 10000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5676879257/10000000000 : ℝ)^4197 ≤ (4728846253179/10000000000000 : ℝ)^3173 := by
    have hnat : (5676879257 : ℕ)^4197*10000000000000^3173 ≤ 4728846253179^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676879257 10000000000 4728846253179 10000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037199073/5000000000 : ℝ), (1004670531/2000000000 : ℝ), (5676879257/10000000000 : ℝ)] ![(12486407574871/100000000000000 : ℝ), (4022512987999/10000000000000 : ℝ), (4728846253179/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037199073/5000000000 : ℝ)|^4197 ≤ (12486407574871/100000000000000 : ℝ)^3173
        have hw : |(-1037199073/5000000000 : ℝ)|=(1037199073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004670531/2000000000 : ℝ)|^4197 ≤ (4022512987999/10000000000000 : ℝ)^3173
        have hw : |(1004670531/2000000000 : ℝ)|=(1004670531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5676879257/10000000000 : ℝ)|^4197 ≤ (4728846253179/10000000000000 : ℝ)^3173
        have hw : |(5676879257/10000000000 : ℝ)|=(5676879257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (327699693/625000000 : ℝ)*x 0 + (-354511417/2000000000 : ℝ)*x 1 + (2838438979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327699693/625000000 : ℝ)^4197 ≤ (21284978407571/50000000000000 : ℝ)^3173 := by
    have hnat : (327699693 : ℕ)^4197*50000000000000^3173 ≤ 21284978407571^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327699693 625000000 21284978407571 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354511417/2000000000 : ℝ)^4197 ≤ (5070797478643/50000000000000 : ℝ)^3173 := by
    have hnat : (354511417 : ℕ)^4197*50000000000000^3173 ≤ 5070797478643^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354511417 2000000000 5070797478643 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838438979/5000000000 : ℝ)^4197 ≤ (2955528013689/6250000000000 : ℝ)^3173 := by
    have hnat : (2838438979 : ℕ)^4197*6250000000000^3173 ≤ 2955528013689^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838438979 5000000000 2955528013689 6250000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327699693/625000000 : ℝ), (-354511417/2000000000 : ℝ), (2838438979/5000000000 : ℝ)] ![(21284978407571/50000000000000 : ℝ), (5070797478643/50000000000000 : ℝ), (2955528013689/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327699693/625000000 : ℝ)|^4197 ≤ (21284978407571/50000000000000 : ℝ)^3173
        have hw : |(327699693/625000000 : ℝ)|=(327699693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354511417/2000000000 : ℝ)|^4197 ≤ (5070797478643/50000000000000 : ℝ)^3173
        have hw : |(-354511417/2000000000 : ℝ)|=(354511417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838438979/5000000000 : ℝ)|^4197 ≤ (2955528013689/6250000000000 : ℝ)^3173
        have hw : |(2838438979/5000000000 : ℝ)|=(2838438979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2621597579/5000000000 : ℝ)*x 0 + (2838439243/5000000000 : ℝ)*x 1 + (-221569527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621597579/5000000000 : ℝ)^4197 ≤ (42569957566893/100000000000000 : ℝ)^3173 := by
    have hnat : (2621597579 : ℕ)^4197*100000000000000^3173 ≤ 42569957566893^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621597579 5000000000 42569957566893 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2838439243/5000000000 : ℝ)^4197 ≤ (11822113509171/25000000000000 : ℝ)^3173 := by
    have hnat : (2838439243 : ℕ)^4197*25000000000000^3173 ≤ 11822113509171^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838439243 5000000000 11822113509171 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221569527/1250000000 : ℝ)^4197 ≤ (10141588380789/100000000000000 : ℝ)^3173 := by
    have hnat : (221569527 : ℕ)^4197*100000000000000^3173 ≤ 10141588380789^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221569527 1250000000 10141588380789 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621597579/5000000000 : ℝ), (2838439243/5000000000 : ℝ), (-221569527/1250000000 : ℝ)] ![(42569957566893/100000000000000 : ℝ), (11822113509171/25000000000000 : ℝ), (10141588380789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621597579/5000000000 : ℝ)|^4197 ≤ (42569957566893/100000000000000 : ℝ)^3173
        have hw : |(2621597579/5000000000 : ℝ)|=(2621597579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2838439243/5000000000 : ℝ)|^4197 ≤ (11822113509171/25000000000000 : ℝ)^3173
        have hw : |(2838439243/5000000000 : ℝ)|=(2838439243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221569527/1250000000 : ℝ)|^4197 ≤ (10141588380789/100000000000000 : ℝ)^3173
        have hw : |(-221569527/1250000000 : ℝ)|=(221569527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s1_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156932079/5000000000 : ℝ)*x 0 + (1004327253/2000000000 : ℝ)*x 1 + (29651213/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156932079/5000000000 : ℝ)^4197 ≤ (4110924469957/12500000000000 : ℝ)^3173 := by
    have hnat : (2156932079 : ℕ)^4197*12500000000000^3173 ≤ 4110924469957^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156932079 5000000000 4110924469957 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004327253/2000000000 : ℝ)^4197 ≤ (40206951100877/100000000000000 : ℝ)^3173 := by
    have hnat : (1004327253 : ℕ)^4197*100000000000000^3173 ≤ 40206951100877^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004327253 2000000000 40206951100877 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29651213/80000000 : ℝ)^4197 ≤ (13452826559797/50000000000000 : ℝ)^3173 := by
    have hnat : (29651213 : ℕ)^4197*50000000000000^3173 ≤ 13452826559797^3173*80000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29651213 80000000 13452826559797 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156932079/5000000000 : ℝ), (1004327253/2000000000 : ℝ), (29651213/80000000 : ℝ)] ![(4110924469957/12500000000000 : ℝ), (40206951100877/100000000000000 : ℝ), (13452826559797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156932079/5000000000 : ℝ)|^4197 ≤ (4110924469957/12500000000000 : ℝ)^3173
        have hw : |(2156932079/5000000000 : ℝ)|=(2156932079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004327253/2000000000 : ℝ)|^4197 ≤ (40206951100877/100000000000000 : ℝ)^3173
        have hw : |(1004327253/2000000000 : ℝ)|=(1004327253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29651213/80000000 : ℝ)|^4197 ≤ (13452826559797/50000000000000 : ℝ)^3173
        have hw : |(29651213/80000000 : ℝ)|=(29651213/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2759/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2987/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (807/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2759/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (327/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2759/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (327/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2759/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (327/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2759/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (327/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2759/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (327/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2759/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (327/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (327/50000 : ℝ) ^ (8393/2048 : ℝ) ≤ (55833120313/50000000000000000000 : ℝ) := by
    have hpowers : (327/50000 : ℝ)^8393 ≤ (55833120313/50000000000000000000 : ℝ)^2048 := by
      have hnat : (327 : ℕ)^8393*50000000000000000000^2048 ≤ 55833120313^2048*50000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 50000 55833120313 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/50000 : ℝ)) (X := (55833120313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2759/10000 : ℝ) ^ (8393/2048 : ℝ) ≤ (255322826787975223/50000000000000000000 : ℝ) := by
    have hpowers : (2759/10000 : ℝ)^8393 ≤ (255322826787975223/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2759 : ℕ)^8393*50000000000000000000^2048 ≤ 255322826787975223^2048*10000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 10000 255322826787975223 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/10000 : ℝ)) (X := (255322826787975223/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000055833120313/25000000000000000000 : ℝ) ≤ (3125000001703/3125000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (25000000055833120313/25000000000000000000 : ℝ)^2048 ≤ (3125000001703/3125000000000 : ℝ)^8393 := by
      have hnat : (25000000055833120313 : ℕ)^2048*3125000000000^8393 ≤ 3125000001703^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000055833120313 25000000000000000000 3125000001703 3125000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3125000001703/3125000000000 : ℝ)) (X := (25000000055833120313/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3140957680163818471/3125000000000000000 : ℝ) ≤ (5006218217104017/5000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (3140957680163818471/3125000000000000000 : ℝ)^2048 ≤ (5006218217104017/5000000000000000 : ℝ)^8393 := by
      have hnat : (3140957680163818471 : ℕ)^2048*5000000000000000^8393 ≤ 5006218217104017^8393*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3140957680163818471 3125000000000000000 5006218217104017 5000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006218217104017/5000000000000000 : ℝ)) (X := (3140957680163818471/3125000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25255322826787975223/25000000000000000000 : ℝ) ≤ (2506218215741617/2500000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (25255322826787975223/25000000000000000000 : ℝ)^2048 ≤ (2506218215741617/2500000000000000 : ℝ)^8393 := by
      have hnat : (25255322826787975223 : ℕ)^2048*2500000000000000^8393 ≤ 2506218215741617^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25255322826787975223 25000000000000000000 2506218215741617 2500000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506218215741617/2500000000000000 : ℝ)) (X := (25255322826787975223/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(55833120313/50000000000000000000 : ℝ) ≤ ((33667966662246799241/33670000000000000000 : ℝ)+2*(6218214379217/1346800000000000 : ℝ)*(327/50000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (33667966662246799241/33670000000000000000 : ℝ)+2*(6218214379217/1346800000000000 : ℝ)*(327/50000 : ℝ)=(3125000001703/3125000000000 : ℝ) by norm_num, show 1+2*(55833120313/50000000000000000000 : ℝ)=(25000000055833120313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(255322826787975223/50000000000000000000 : ℝ)+(55833120313/50000000000000000000 : ℝ) ≤ ((33667966662246799241/33670000000000000000 : ℝ)+(6218214379217/1346800000000000 : ℝ)*((2759/10000 : ℝ)+(327/50000 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (33667966662246799241/33670000000000000000 : ℝ)+(6218214379217/1346800000000000 : ℝ)*((2759/10000 : ℝ)+(327/50000 : ℝ))=(5006218217104017/5000000000000000 : ℝ) by norm_num, show 1+(255322826787975223/50000000000000000000 : ℝ)+(55833120313/50000000000000000000 : ℝ)=(3140957680163818471/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(255322826787975223/50000000000000000000 : ℝ) ≤ ((33667966662246799241/33670000000000000000 : ℝ)+2*(6218214379217/1346800000000000 : ℝ)*(2759/10000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (33667966662246799241/33670000000000000000 : ℝ)+2*(6218214379217/1346800000000000 : ℝ)*(2759/10000 : ℝ)=(2506218215741617/2500000000000000 : ℝ) by norm_num, show 1+2*(255322826787975223/50000000000000000000 : ℝ)=(25255322826787975223/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33667966662246799241/33670000000000000000 : ℝ)*(X 1 0+X 2 0)+(6218214379217/1346800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (327/50000 : ℝ)) (hi := (2759/10000 : ℝ)) (c := (33667966662246799241/33670000000000000000 : ℝ)) (alpha := (6218214379217/1346800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33667966662246799241/33670000000000000000 : ℝ)*(X 0 1+X 2 1)+(6218214379217/1346800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (327/50000 : ℝ)) (hi := (2759/10000 : ℝ)) (c := (33667966662246799241/33670000000000000000 : ℝ)) (alpha := (6218214379217/1346800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33667966662246799241/33670000000000000000 : ℝ)*(X 0 2+X 1 2)+(6218214379217/1346800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (327/50000 : ℝ)) (hi := (2759/10000 : ℝ)) (c := (33667966662246799241/33670000000000000000 : ℝ)) (alpha := (6218214379217/1346800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2073672461/10000000000 : ℝ)*X 0 0+(355375997/625000000 : ℝ)*X 0 1+(5014388533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415888483/10000000000 : ℝ)*X 1 0+(-2435046011/10000000000 : ℝ)*X 1 1+(2507194469/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707943677/5000000000 : ℝ)*X 2 0+(2507194831/5000000000 : ℝ)*X 2 1+(-1217523279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312402189/10000000000 : ℝ)*X 0 0+(1844005689/5000000000 : ℝ)*X 0 1+(2519838869/5000000000 : ℝ)*X 0 2+(4312402189/10000000000 : ℝ)*X 1 0+(1844005689/5000000000 : ℝ)*X 1 1+(2519838869/5000000000 : ℝ)*X 1 2+(4312402189/10000000000 : ℝ)*X 2 0+(1844005689/5000000000 : ℝ)*X 2 1+(2519838869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1037199073/5000000000 : ℝ)*X 0 0+(1004670531/2000000000 : ℝ)*X 0 1+(5676879257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327699693/625000000 : ℝ)*X 1 0+(-354511417/2000000000 : ℝ)*X 1 1+(2838438979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621597579/5000000000 : ℝ)*X 2 0+(2838439243/5000000000 : ℝ)*X 2 1+(-221569527/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2156932079/5000000000 : ℝ)*X 0 0+(1004327253/2000000000 : ℝ)*X 0 1+(29651213/80000000 : ℝ)*X 0 2+(2156932079/5000000000 : ℝ)*X 1 0+(1004327253/2000000000 : ℝ)*X 1 1+(29651213/80000000 : ℝ)*X 1 2+(2156932079/5000000000 : ℝ)*X 2 0+(1004327253/2000000000 : ℝ)*X 2 1+(29651213/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106534483531150192625524329/64750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17821723/100000000000000 : ℝ)*(base16) + (536413183/100000000000000 : ℝ)*(base19) + (356633261/100000000000000 : ℝ)*(base23) + (61081147/100000000000000 : ℝ)*(upper2) + (70078869/50000000000000 : ℝ)*(upper3) + (1114380181205499/100000000000000 : ℝ)*(major0) + (1114380181205499/100000000000000 : ℝ)*(major1) + (2228760362411/200000000000 : ℝ)*(major2) + (372231465904037/25000000000000 : ℝ)*(sp0) + (1488928005903723/100000000000000 : ℝ)*(sp1) + (186116025438171/12500000000000 : ℝ)*(sp2) + (739829509159777/100000000000000 : ℝ)*(sp3) + (2696522481/100000000000000 : ℝ)*(sp4) + (1119134289/50000000000000 : ℝ)*(sp7) + (147966349485671/20000000000000 : ℝ)*(f.failure) + (372232140034657/25000000000000 : ℝ)*(f.sum) + (358901740994143/134680000000000000000000000000 : ℝ)*base65 + (5868148397936181963/481000000000000000000000000000000 : ℝ)*base68 + (28787147919526201/6734000000000000000000000000000 : ℝ)*base69 + (2305308073815181963/481000000000000000000000000000000 : ℝ)*base72 + (295822181178143/134680000000000000000000000000 : ℝ)*base73 + (1086954684455799/6734000000000000000000000000000 : ℝ)*base76 + (1672804498946746057/259000000000000000000000000000000 : ℝ)*base78 + (3516038616083746057/259000000000000000000000000000000 : ℝ)*base80 + (9661612689031/5180000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3924011/500000000000000000000 : ℝ)*base89 + (3924011/500000000000000000000 : ℝ)*base91 + (1075989/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (725632725861853633561535853/84175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156380567/100000000000000 : ℝ)*(base1) + (1813893771/100000000000000 : ℝ)*(base19) + (232804469/12500000000000 : ℝ)*(base23) + (2656613/6250000000000 : ℝ)*(upper3) + (111192341/50000000000000 : ℝ)*(upper5) + (114524091384189/10000000000000 : ℝ)*(major0) + (114524091384189/10000000000000 : ℝ)*(major1) + (114524091384189/10000000000000 : ℝ)*(major2) + (6854744073/100000000000000 : ℝ)*(sp1) + (7708356037/100000000000000 : ℝ)*(sp2) + (1530161654412017/100000000000000 : ℝ)*(sp4) + (765076414696803/50000000000000 : ℝ)*(sp5) + (1530151927239661/100000000000000 : ℝ)*(sp6) + (760319885920909/100000000000000 : ℝ)*(sp7) + (30412801692059/4000000000000 : ℝ)*(f.failure) + (30603229960629/2000000000000 : ℝ)*(f.sum) + (6048622848747/6734000000000000000000000000 : ℝ)*base66 + (1389990809750925549/336700000000000000000000000000000 : ℝ)*base67 + (516291860555125549/336700000000000000000000000000000 : ℝ)*base69 + (1159729023514625549/336700000000000000000000000000000 : ℝ)*base71 + (1174563373233/1346800000000000000000000000 : ℝ)*base73 + (1512597378390025549/336700000000000000000000000000000 : ℝ)*base75 + (155959542613674451/336700000000000000000000000000000 : ℝ)*base78 + (3482895247147425549/336700000000000000000000000000000 : ℝ)*base79 + (8742846784011/6734000000000000000000000000 : ℝ)*base81 + (892081/100000000000000000000 : ℝ)*base90 + (892081/100000000000000000000 : ℝ)*base92 + (892081/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1201_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2759/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2987/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1201_s2_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-530948091/2500000000 : ℝ)*x 0 + (2749967483/5000000000 : ℝ)*x 1 + (1292136053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530948091/2500000000 : ℝ)^4197 ≤ (2576236037993/20000000000000 : ℝ)^3173 := by
    have hnat : (530948091 : ℕ)^4197*20000000000000^3173 ≤ 2576236037993^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530948091 2500000000 2576236037993 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749967483/5000000000 : ℝ)^4197 ≤ (22674356780851/50000000000000 : ℝ)^3173 := by
    have hnat : (2749967483 : ℕ)^4197*50000000000000^3173 ≤ 22674356780851^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749967483 5000000000 22674356780851 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292136053/2500000000 : ℝ)^4197 ≤ (41770106236869/100000000000000 : ℝ)^3173 := by
    have hnat : (1292136053 : ℕ)^4197*100000000000000^3173 ≤ 41770106236869^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292136053 2500000000 41770106236869 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530948091/2500000000 : ℝ), (2749967483/5000000000 : ℝ), (1292136053/2500000000 : ℝ)] ![(2576236037993/20000000000000 : ℝ), (22674356780851/50000000000000 : ℝ), (41770106236869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530948091/2500000000 : ℝ)|^4197 ≤ (2576236037993/20000000000000 : ℝ)^3173
        have hw : |(-530948091/2500000000 : ℝ)|=(530948091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749967483/5000000000 : ℝ)|^4197 ≤ (22674356780851/50000000000000 : ℝ)^3173
        have hw : |(2749967483/5000000000 : ℝ)|=(2749967483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292136053/2500000000 : ℝ)|^4197 ≤ (41770106236869/100000000000000 : ℝ)^3173
        have hw : |(1292136053/2500000000 : ℝ)|=(1292136053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074273797/2000000000 : ℝ)*x 0 + (-2295697289/10000000000 : ℝ)*x 1 + (2584274357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074273797/2000000000 : ℝ)^4197 ≤ (43951855190507/100000000000000 : ℝ)^3173 := by
    have hnat : (1074273797 : ℕ)^4197*100000000000000^3173 ≤ 43951855190507^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074273797 2000000000 43951855190507 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2295697289/10000000000 : ℝ)^4197 ≤ (7138995216547/50000000000000 : ℝ)^3173 := by
    have hnat : (2295697289 : ℕ)^4197*50000000000000^3173 ≤ 7138995216547^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295697289 10000000000 7138995216547 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584274357/5000000000 : ℝ)^4197 ≤ (8354030872397/20000000000000 : ℝ)^3173 := by
    have hnat : (2584274357 : ℕ)^4197*20000000000000^3173 ≤ 8354030872397^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584274357 5000000000 8354030872397 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074273797/2000000000 : ℝ), (-2295697289/10000000000 : ℝ), (2584274357/5000000000 : ℝ)] ![(43951855190507/100000000000000 : ℝ), (7138995216547/50000000000000 : ℝ), (8354030872397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074273797/2000000000 : ℝ)|^4197 ≤ (43951855190507/100000000000000 : ℝ)^3173
        have hw : |(1074273797/2000000000 : ℝ)|=(1074273797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2295697289/10000000000 : ℝ)|^4197 ≤ (7138995216547/50000000000000 : ℝ)^3173
        have hw : |(-2295697289/10000000000 : ℝ)|=(2295697289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584274357/5000000000 : ℝ)|^4197 ≤ (8354030872397/20000000000000 : ℝ)^3173
        have hw : |(2584274357/5000000000 : ℝ)|=(2584274357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685685473/5000000000 : ℝ)*x 0 + (2584272991/5000000000 : ℝ)*x 1 + (-2295698259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685685473/5000000000 : ℝ)^4197 ≤ (43951876415069/100000000000000 : ℝ)^3173 := by
    have hnat : (2685685473 : ℕ)^4197*100000000000000^3173 ≤ 43951876415069^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685685473 5000000000 43951876415069 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584272991/5000000000 : ℝ)^4197 ≤ (4177012515767/10000000000000 : ℝ)^3173 := by
    have hnat : (2584272991 : ℕ)^4197*10000000000000^3173 ≤ 4177012515767^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584272991 5000000000 4177012515767 10000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2295698259/10000000000 : ℝ)^4197 ≤ (2855599682583/20000000000000 : ℝ)^3173 := by
    have hnat : (2295698259 : ℕ)^4197*20000000000000^3173 ≤ 2855599682583^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295698259 10000000000 2855599682583 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685685473/5000000000 : ℝ), (2584272991/5000000000 : ℝ), (-2295698259/10000000000 : ℝ)] ![(43951876415069/100000000000000 : ℝ), (4177012515767/10000000000000 : ℝ), (2855599682583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685685473/5000000000 : ℝ)|^4197 ≤ (43951876415069/100000000000000 : ℝ)^3173
        have hw : |(2685685473/5000000000 : ℝ)|=(2685685473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2584272991/5000000000 : ℝ)|^4197 ≤ (4177012515767/10000000000000 : ℝ)^3173
        have hw : |(2584272991/5000000000 : ℝ)|=(2584272991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2295698259/10000000000 : ℝ)|^4197 ≤ (2855599682583/20000000000000 : ℝ)^3173
        have hw : |(-2295698259/10000000000 : ℝ)|=(2295698259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4346929869/10000000000 : ℝ)*x 0 + (2012985433/5000000000 : ℝ)*x 1 + (2346449339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346929869/10000000000 : ℝ)^4197 ≤ (33221241373557/100000000000000 : ℝ)^3173 := by
    have hnat : (4346929869 : ℕ)^4197*100000000000000^3173 ≤ 33221241373557^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346929869 10000000000 33221241373557 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012985433/5000000000 : ℝ)^4197 ≤ (30016033488353/100000000000000 : ℝ)^3173 := by
    have hnat : (2012985433 : ℕ)^4197*100000000000000^3173 ≤ 30016033488353^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012985433 5000000000 30016033488353 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2346449339/5000000000 : ℝ)^4197 ≤ (36762725126793/100000000000000 : ℝ)^3173 := by
    have hnat : (2346449339 : ℕ)^4197*100000000000000^3173 ≤ 36762725126793^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346449339 5000000000 36762725126793 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346929869/10000000000 : ℝ), (2012985433/5000000000 : ℝ), (2346449339/5000000000 : ℝ)] ![(33221241373557/100000000000000 : ℝ), (30016033488353/100000000000000 : ℝ), (36762725126793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346929869/10000000000 : ℝ)|^4197 ≤ (33221241373557/100000000000000 : ℝ)^3173
        have hw : |(4346929869/10000000000 : ℝ)|=(4346929869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012985433/5000000000 : ℝ)|^4197 ≤ (30016033488353/100000000000000 : ℝ)^3173
        have hw : |(2012985433/5000000000 : ℝ)|=(2012985433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2346449339/5000000000 : ℝ)|^4197 ≤ (36762725126793/100000000000000 : ℝ)^3173
        have hw : |(2346449339/5000000000 : ℝ)|=(2346449339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123878671/10000000000 : ℝ)*x 0 + (1034147597/2000000000 : ℝ)*x 1 + (2748860487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123878671/10000000000 : ℝ)^4197 ≤ (402558518651/3125000000000 : ℝ)^3173 := by
    have hnat : (2123878671 : ℕ)^4197*3125000000000^3173 ≤ 402558518651^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123878671 10000000000 402558518651 3125000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034147597/2000000000 : ℝ)^4197 ≤ (41793558657189/100000000000000 : ℝ)^3173 := by
    have hnat : (1034147597 : ℕ)^4197*100000000000000^3173 ≤ 41793558657189^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034147597 2000000000 41793558657189 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748860487/5000000000 : ℝ)^4197 ≤ (45324568731901/100000000000000 : ℝ)^3173 := by
    have hnat : (2748860487 : ℕ)^4197*100000000000000^3173 ≤ 45324568731901^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748860487 5000000000 45324568731901 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123878671/10000000000 : ℝ), (1034147597/2000000000 : ℝ), (2748860487/5000000000 : ℝ)] ![(402558518651/3125000000000 : ℝ), (41793558657189/100000000000000 : ℝ), (45324568731901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123878671/10000000000 : ℝ)|^4197 ≤ (402558518651/3125000000000 : ℝ)^3173
        have hw : |(-2123878671/10000000000 : ℝ)|=(2123878671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034147597/2000000000 : ℝ)|^4197 ≤ (41793558657189/100000000000000 : ℝ)^3173
        have hw : |(1034147597/2000000000 : ℝ)|=(1034147597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748860487/5000000000 : ℝ)|^4197 ≤ (45324568731901/100000000000000 : ℝ)^3173
        have hw : |(2748860487/5000000000 : ℝ)|=(2748860487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286961859/10000000000 : ℝ)*x 0 + (-245815419/1250000000 : ℝ)*x 1 + (1099544199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286961859/10000000000 : ℝ)^4197 ≤ (43040613329713/100000000000000 : ℝ)^3173 := by
    have hnat : (5286961859 : ℕ)^4197*100000000000000^3173 ≤ 43040613329713^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286961859 10000000000 43040613329713 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245815419/1250000000 : ℝ)^4197 ≤ (11634817693923/100000000000000 : ℝ)^3173 := by
    have hnat : (245815419 : ℕ)^4197*100000000000000^3173 ≤ 11634817693923^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245815419 1250000000 11634817693923 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099544199/2000000000 : ℝ)^4197 ≤ (45324568960903/100000000000000 : ℝ)^3173 := by
    have hnat : (1099544199 : ℕ)^4197*100000000000000^3173 ≤ 45324568960903^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099544199 2000000000 45324568960903 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286961859/10000000000 : ℝ), (-245815419/1250000000 : ℝ), (1099544199/2000000000 : ℝ)] ![(43040613329713/100000000000000 : ℝ), (11634817693923/100000000000000 : ℝ), (45324568960903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286961859/10000000000 : ℝ)|^4197 ≤ (43040613329713/100000000000000 : ℝ)^3173
        have hw : |(5286961859/10000000000 : ℝ)|=(5286961859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245815419/1250000000 : ℝ)|^4197 ≤ (11634817693923/100000000000000 : ℝ)^3173
        have hw : |(-245815419/1250000000 : ℝ)|=(245815419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099544199/2000000000 : ℝ)|^4197 ≤ (45324568960903/100000000000000 : ℝ)^3173
        have hw : |(1099544199/2000000000 : ℝ)|=(1099544199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330435127/625000000 : ℝ)*x 0 + (1099544203/2000000000 : ℝ)*x 1 + (-983261543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330435127/625000000 : ℝ)^4197 ≤ (10760153798151/25000000000000 : ℝ)^3173 := by
    have hnat : (330435127 : ℕ)^4197*25000000000000^3173 ≤ 10760153798151^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330435127 625000000 10760153798151 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099544203/2000000000 : ℝ)^4197 ≤ (45324569179/100000000000 : ℝ)^3173 := by
    have hnat : (1099544203 : ℕ)^4197*100000000000^3173 ≤ 45324569179^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099544203 2000000000 45324569179 100000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983261543/5000000000 : ℝ)^4197 ≤ (11634815612257/100000000000000 : ℝ)^3173 := by
    have hnat : (983261543 : ℕ)^4197*100000000000000^3173 ≤ 11634815612257^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983261543 5000000000 11634815612257 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330435127/625000000 : ℝ), (1099544203/2000000000 : ℝ), (-983261543/5000000000 : ℝ)] ![(10760153798151/25000000000000 : ℝ), (45324569179/100000000000 : ℝ), (11634815612257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330435127/625000000 : ℝ)|^4197 ≤ (10760153798151/25000000000000 : ℝ)^3173
        have hw : |(330435127/625000000 : ℝ)|=(330435127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099544203/2000000000 : ℝ)|^4197 ≤ (45324569179/100000000000 : ℝ)^3173
        have hw : |(1099544203/2000000000 : ℝ)|=(1099544203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983261543/5000000000 : ℝ)|^4197 ≤ (11634815612257/100000000000000 : ℝ)^3173
        have hw : |(-983261543/5000000000 : ℝ)|=(983261543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s2_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086776483/2500000000 : ℝ)*x 0 + (2344243197/5000000000 : ℝ)*x 1 + (4030424931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086776483/2500000000 : ℝ)^4197 ≤ (16611510590577/50000000000000 : ℝ)^3173 := by
    have hnat : (1086776483 : ℕ)^4197*50000000000000^3173 ≤ 16611510590577^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086776483 2500000000 16611510590577 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2344243197/5000000000 : ℝ)^4197 ≤ (71712915699/195312500000 : ℝ)^3173 := by
    have hnat : (2344243197 : ℕ)^4197*195312500000^3173 ≤ 71712915699^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2344243197 5000000000 71712915699 195312500000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030424931/10000000000 : ℝ)^4197 ≤ (30059965958737/100000000000000 : ℝ)^3173 := by
    have hnat : (4030424931 : ℕ)^4197*100000000000000^3173 ≤ 30059965958737^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030424931 10000000000 30059965958737 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086776483/2500000000 : ℝ), (2344243197/5000000000 : ℝ), (4030424931/10000000000 : ℝ)] ![(16611510590577/50000000000000 : ℝ), (71712915699/195312500000 : ℝ), (30059965958737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086776483/2500000000 : ℝ)|^4197 ≤ (16611510590577/50000000000000 : ℝ)^3173
        have hw : |(1086776483/2500000000 : ℝ)|=(1086776483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2344243197/5000000000 : ℝ)|^4197 ≤ (71712915699/195312500000 : ℝ)^3173
        have hw : |(2344243197/5000000000 : ℝ)|=(2344243197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030424931/10000000000 : ℝ)|^4197 ≤ (30059965958737/100000000000000 : ℝ)^3173
        have hw : |(4030424931/10000000000 : ℝ)|=(4030424931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2987/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9329/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16333/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (807/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2987/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (807/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2987/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (807/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2987/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (807/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2987/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (807/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2987/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (807/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2987/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2987/50000 : ℝ) ^ (8393/2048 : ℝ) ≤ (965957450419841/100000000000000000000 : ℝ) := by
    have hpowers : (2987/50000 : ℝ)^8393 ≤ (965957450419841/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2987 : ℕ)^8393*100000000000000000000^2048 ≤ 965957450419841^2048*50000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2987 50000 965957450419841 100000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2987/50000 : ℝ)) (X := (965957450419841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (807/4000 : ℝ) ^ (8393/2048 : ℝ) ≤ (70793833320747493/50000000000000000000 : ℝ) := by
    have hpowers : (807/4000 : ℝ)^8393 ≤ (70793833320747493/50000000000000000000 : ℝ)^2048 := by
      have hnat : (807 : ℕ)^8393*50000000000000000000^2048 ≤ 70793833320747493^2048*4000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        807 4000 70793833320747493 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (807/4000 : ℝ)) (X := (70793833320747493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000965957450419841/50000000000000000000 : ℝ) ≤ (5000023570432649/5000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (50000965957450419841/50000000000000000000 : ℝ)^2048 ≤ (5000023570432649/5000000000000000 : ℝ)^8393 := by
      have hnat : (50000965957450419841 : ℕ)^2048*5000000000000000^8393 ≤ 5000023570432649^8393*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000965957450419841 50000000000000000000 5000023570432649 5000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023570432649/5000000000000000 : ℝ)) (X := (50000965957450419841/50000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100142553624091914827/100000000000000000000 : ℝ) ≤ (10003476619063561/10000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (100142553624091914827/100000000000000000000 : ℝ)^2048 ≤ (10003476619063561/10000000000000000 : ℝ)^8393 := by
      have hnat : (100142553624091914827 : ℕ)^2048*10000000000000000^8393 ≤ 10003476619063561^8393*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100142553624091914827 100000000000000000000 10003476619063561 10000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003476619063561/10000000000000000 : ℝ)) (X := (100142553624091914827/100000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25070793833320747493/25000000000000000000 : ℝ) ≤ (39089476942429/39062500000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (25070793833320747493/25000000000000000000 : ℝ)^2048 ≤ (39089476942429/39062500000000 : ℝ)^8393 := by
      have hnat : (25070793833320747493 : ℕ)^2048*39062500000000^8393 ≤ 39089476942429^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25070793833320747493 25000000000000000000 39089476942429 39062500000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39089476942429/39062500000000 : ℝ)) (X := (25070793833320747493/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(965957450419841/100000000000000000000 : ℝ) ≤ ((70984847020957625287/71005000000000000000 : ℝ)+2*(3429478198263/1420100000000000 : ℝ)*(2987/50000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (70984847020957625287/71005000000000000000 : ℝ)+2*(3429478198263/1420100000000000 : ℝ)*(2987/50000 : ℝ)=(5000023570432649/5000000000000000 : ℝ) by norm_num, show 1+2*(965957450419841/100000000000000000000 : ℝ)=(50000965957450419841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70793833320747493/50000000000000000000 : ℝ)+(965957450419841/100000000000000000000 : ℝ) ≤ ((70984847020957625287/71005000000000000000 : ℝ)+(3429478198263/1420100000000000 : ℝ)*((807/4000 : ℝ)+(2987/50000 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (70984847020957625287/71005000000000000000 : ℝ)+(3429478198263/1420100000000000 : ℝ)*((807/4000 : ℝ)+(2987/50000 : ℝ))=(10003476619063561/10000000000000000 : ℝ) by norm_num, show 1+(70793833320747493/50000000000000000000 : ℝ)+(965957450419841/100000000000000000000 : ℝ)=(100142553624091914827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70793833320747493/50000000000000000000 : ℝ) ≤ ((70984847020957625287/71005000000000000000 : ℝ)+2*(3429478198263/1420100000000000 : ℝ)*(807/4000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (70984847020957625287/71005000000000000000 : ℝ)+2*(3429478198263/1420100000000000 : ℝ)*(807/4000 : ℝ)=(39089476942429/39062500000000 : ℝ) by norm_num, show 1+2*(70793833320747493/50000000000000000000 : ℝ)=(25070793833320747493/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70984847020957625287/71005000000000000000 : ℝ)*(X 1 0+X 2 0)+(3429478198263/1420100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2987/50000 : ℝ)) (hi := (807/4000 : ℝ)) (c := (70984847020957625287/71005000000000000000 : ℝ)) (alpha := (3429478198263/1420100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70984847020957625287/71005000000000000000 : ℝ)*(X 0 1+X 2 1)+(3429478198263/1420100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2987/50000 : ℝ)) (hi := (807/4000 : ℝ)) (c := (70984847020957625287/71005000000000000000 : ℝ)) (alpha := (3429478198263/1420100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70984847020957625287/71005000000000000000 : ℝ)*(X 0 2+X 1 2)+(3429478198263/1420100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2987/50000 : ℝ)) (hi := (807/4000 : ℝ)) (c := (70984847020957625287/71005000000000000000 : ℝ)) (alpha := (3429478198263/1420100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-530948091/2500000000 : ℝ)*X 0 0+(2749967483/5000000000 : ℝ)*X 0 1+(1292136053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074273797/2000000000 : ℝ)*X 1 0+(-2295697289/10000000000 : ℝ)*X 1 1+(2584274357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685685473/5000000000 : ℝ)*X 2 0+(2584272991/5000000000 : ℝ)*X 2 1+(-2295698259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346929869/10000000000 : ℝ)*X 0 0+(2012985433/5000000000 : ℝ)*X 0 1+(2346449339/5000000000 : ℝ)*X 0 2+(4346929869/10000000000 : ℝ)*X 1 0+(2012985433/5000000000 : ℝ)*X 1 1+(2346449339/5000000000 : ℝ)*X 1 2+(4346929869/10000000000 : ℝ)*X 2 0+(2012985433/5000000000 : ℝ)*X 2 1+(2346449339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2123878671/10000000000 : ℝ)*X 0 0+(1034147597/2000000000 : ℝ)*X 0 1+(2748860487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286961859/10000000000 : ℝ)*X 1 0+(-245815419/1250000000 : ℝ)*X 1 1+(1099544199/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330435127/625000000 : ℝ)*X 2 0+(1099544203/2000000000 : ℝ)*X 2 1+(-983261543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086776483/2500000000 : ℝ)*X 0 0+(2344243197/5000000000 : ℝ)*X 0 1+(4030424931/10000000000 : ℝ)*X 0 2+(1086776483/2500000000 : ℝ)*X 1 0+(2344243197/5000000000 : ℝ)*X 1 1+(4030424931/10000000000 : ℝ)*X 1 2+(1086776483/2500000000 : ℝ)*X 2 0+(2344243197/5000000000 : ℝ)*X 2 1+(4030424931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164000190799019269338965733/32275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384229201/50000000000000 : ℝ)*(base19) + (414046949/25000000000000 : ℝ)*(base23) + (16805751/12500000000000 : ℝ)*(upper2) + (36114327/6250000000000 : ℝ)*(upper3) + (249376739/100000000000000 : ℝ)*(upper4) + (225855119114317/10000000000000 : ℝ)*(major0) + (225855119114317/10000000000000 : ℝ)*(major1) + (225855119114317/10000000000000 : ℝ)*(major2) + (377203216373013/12500000000000 : ℝ)*(sp0) + (1508829979438513/50000000000000 : ℝ)*(sp1) + (188603691946727/6250000000000 : ℝ)*(sp2) + (1499423282922841/100000000000000 : ℝ)*(sp3) + (8749087831/25000000000000 : ℝ)*(sp4) + (4550662531/25000000000000 : ℝ)*(sp7) + (374860371393241/25000000000000 : ℝ)*(f.failure) + (754415181833857/25000000000000 : ℝ)*(f.sum) + (1439116652069/258200000000000000000000000 : ℝ)*base66 + (48225263143346911/64550000000000000000000000000000 : ℝ)*base68 + (40018750331653089/64550000000000000000000000000000 : ℝ)*base69 + (178075736999896911/64550000000000000000000000000000 : ℝ)*base72 + (406697514523/645500000000000000000000000 : ℝ)*base74 + (143571865254653089/64550000000000000000000000000000 : ℝ)*base75 + (175912508538003089/64550000000000000000000000000000 : ℝ)*base77 + (280283111965653089/64550000000000000000000000000000 : ℝ)*base79 + (330703424023/322750000000000000000000000 : ℝ)*base82 + (5660619/625000000000000000000 : ℝ)*base90 + (5660619/625000000000000000000 : ℝ)*base92 + (5660619/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (791534020260026286074157987/177512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302048601/25000000000000 : ℝ)*(base19) + (18037749/1250000000000 : ℝ)*(base23) + (34025483/100000000000000 : ℝ)*(upper2) + (165015573/100000000000000 : ℝ)*(upper3) + (23162583/25000000000000 : ℝ)*(upper5) + (228893887502633/10000000000000 : ℝ)*(major0) + (228893887502633/10000000000000 : ℝ)*(major1) + (228893887502633/10000000000000 : ℝ)*(major2) + (11707231429/100000000000000 : ℝ)*(sp1) + (16116229473/100000000000000 : ℝ)*(sp2) + (2446609500647/80000000000 : ℝ)*(sp4) + (1529124480191459/50000000000000 : ℝ)*(sp5) + (1529122158279679/50000000000000 : ℝ)*(sp6) + (1519615725609483/100000000000000 : ℝ)*(sp7) + (1519615725609483/100000000000000 : ℝ)*(f.failure) + (2446609500647/80000000000 : ℝ)*(f.sum) + (22763227648537/3550250000000000000000000000 : ℝ)*base66 + (8359681611891230671/710050000000000000000000000000000 : ℝ)*base67 + (5102185140975180671/710050000000000000000000000000000 : ℝ)*base69 + (428093484669680671/710050000000000000000000000000000 : ℝ)*base71 + (34221277948773/14201000000000000000000000000 : ℝ)*base73 + (4890183228954380671/710050000000000000000000000000000 : ℝ)*base75 + (4906109415739669329/710050000000000000000000000000000 : ℝ)*base78 + (3804521203275930671/710050000000000000000000000000000 : ℝ)*base79 + (2418829529549/710050000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3421697/2500000000000000000000 : ℝ)*base90 + (3421697/2500000000000000000000 : ℝ)*base92 + (3421697/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1201_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (807/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2987/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1201_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1201_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1201_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1201_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

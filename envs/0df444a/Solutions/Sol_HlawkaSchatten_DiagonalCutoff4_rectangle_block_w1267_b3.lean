-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:56.599734+00:00
-- url     : https://prove2.me/submissions/15a17587-b54d-4f5a-a53e-a401d12d3290

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
theorem support_rectangle_w1267_box_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-992792849/5000000000 : ℝ)*x 0 + (2687231169/5000000000 : ℝ)*x 1 + (5374462363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992792849/5000000000 : ℝ)^2115 ≤ (11847684428259/100000000000000 : ℝ)^1603 := by
    have hnat : (992792849 : ℕ)^2115*100000000000000^1603 ≤ 11847684428259^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992792849 5000000000 11847684428259 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687231169/5000000000 : ℝ)^2115 ≤ (44076157643269/100000000000000 : ℝ)^1603 := by
    have hnat : (2687231169 : ℕ)^2115*100000000000000^1603 ≤ 44076157643269^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687231169 5000000000 44076157643269 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374462363/10000000000 : ℝ)^2115 ≤ (2203807895689/5000000000000 : ℝ)^1603 := by
    have hnat : (5374462363 : ℕ)^2115*5000000000000^1603 ≤ 2203807895689^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374462363 10000000000 2203807895689 5000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-992792849/5000000000 : ℝ), (2687231169/5000000000 : ℝ), (5374462363/10000000000 : ℝ)] ![(11847684428259/100000000000000 : ℝ), (44076157643269/100000000000000 : ℝ), (2203807895689/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-992792849/5000000000 : ℝ)|^2115 ≤ (11847684428259/100000000000000 : ℝ)^1603
        have hw : |(-992792849/5000000000 : ℝ)|=(992792849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687231169/5000000000 : ℝ)|^2115 ≤ (44076157643269/100000000000000 : ℝ)^1603
        have hw : |(2687231169/5000000000 : ℝ)|=(2687231169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374462363/10000000000 : ℝ)|^2115 ≤ (2203807895689/5000000000000 : ℝ)^1603
        have hw : |(5374462363/10000000000 : ℝ)|=(5374462363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2648481217/5000000000 : ℝ)*x 0 + (-2090975301/10000000000 : ℝ)*x 1 + (2687231173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648481217/5000000000 : ℝ)^2115 ≤ (21619755441287/50000000000000 : ℝ)^1603 := by
    have hnat : (2648481217 : ℕ)^2115*50000000000000^1603 ≤ 21619755441287^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648481217 5000000000 21619755441287 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090975301/10000000000 : ℝ)^2115 ≤ (12684331373333/100000000000000 : ℝ)^1603 := by
    have hnat : (2090975301 : ℕ)^2115*100000000000000^1603 ≤ 12684331373333^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090975301 10000000000 12684331373333 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687231173/5000000000 : ℝ)^2115 ≤ (5509519716229/12500000000000 : ℝ)^1603 := by
    have hnat : (2687231173 : ℕ)^2115*12500000000000^1603 ≤ 5509519716229^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687231173 5000000000 5509519716229 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648481217/5000000000 : ℝ), (-2090975301/10000000000 : ℝ), (2687231173/5000000000 : ℝ)] ![(21619755441287/50000000000000 : ℝ), (12684331373333/100000000000000 : ℝ), (5509519716229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648481217/5000000000 : ℝ)|^2115 ≤ (21619755441287/50000000000000 : ℝ)^1603
        have hw : |(2648481217/5000000000 : ℝ)|=(2648481217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090975301/10000000000 : ℝ)|^2115 ≤ (12684331373333/100000000000000 : ℝ)^1603
        have hw : |(-2090975301/10000000000 : ℝ)|=(2090975301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687231173/5000000000 : ℝ)|^2115 ≤ (5509519716229/12500000000000 : ℝ)^1603
        have hw : |(2687231173/5000000000 : ℝ)|=(2687231173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (529696257/1000000000 : ℝ)*x 0 + (5374462353/10000000000 : ℝ)*x 1 + (-522743777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529696257/1000000000 : ℝ)^2115 ≤ (8647902469469/20000000000000 : ℝ)^1603 := by
    have hnat : (529696257 : ℕ)^2115*20000000000000^1603 ≤ 8647902469469^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529696257 1000000000 8647902469469 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374462353/10000000000 : ℝ)^2115 ≤ (5509519725697/12500000000000 : ℝ)^1603 := by
    have hnat : (5374462353 : ℕ)^2115*12500000000000^1603 ≤ 5509519725697^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374462353 10000000000 5509519725697 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522743777/2500000000 : ℝ)^2115 ≤ (6342164914301/50000000000000 : ℝ)^1603 := by
    have hnat : (522743777 : ℕ)^2115*50000000000000^1603 ≤ 6342164914301^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522743777 2500000000 6342164914301 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529696257/1000000000 : ℝ), (5374462353/10000000000 : ℝ), (-522743777/2500000000 : ℝ)] ![(8647902469469/20000000000000 : ℝ), (5509519725697/12500000000000 : ℝ), (6342164914301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529696257/1000000000 : ℝ)|^2115 ≤ (8647902469469/20000000000000 : ℝ)^1603
        have hw : |(529696257/1000000000 : ℝ)|=(529696257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374462353/10000000000 : ℝ)|^2115 ≤ (5509519725697/12500000000000 : ℝ)^1603
        have hw : |(5374462353/10000000000 : ℝ)|=(5374462353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522743777/2500000000 : ℝ)|^2115 ≤ (6342164914301/50000000000000 : ℝ)^1603
        have hw : |(-522743777/2500000000 : ℝ)|=(522743777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2226822011/5000000000 : ℝ)*x 0 + (859248169/2000000000 : ℝ)*x 1 + (429624077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2226822011/5000000000 : ℝ)^2115 ≤ (34396546277923/100000000000000 : ℝ)^1603 := by
    have hnat : (2226822011 : ℕ)^2115*100000000000000^1603 ≤ 34396546277923^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226822011 5000000000 34396546277923 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859248169/2000000000 : ℝ)^2115 ≤ (32801727230211/100000000000000 : ℝ)^1603 := by
    have hnat : (859248169 : ℕ)^2115*100000000000000^1603 ≤ 32801727230211^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859248169 2000000000 32801727230211 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429624077/1000000000 : ℝ)^2115 ≤ (32801726474691/100000000000000 : ℝ)^1603 := by
    have hnat : (429624077 : ℕ)^2115*100000000000000^1603 ≤ 32801726474691^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429624077 1000000000 32801726474691 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2226822011/5000000000 : ℝ), (859248169/2000000000 : ℝ), (429624077/1000000000 : ℝ)] ![(34396546277923/100000000000000 : ℝ), (32801727230211/100000000000000 : ℝ), (32801726474691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2226822011/5000000000 : ℝ)|^2115 ≤ (34396546277923/100000000000000 : ℝ)^1603
        have hw : |(2226822011/5000000000 : ℝ)|=(2226822011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859248169/2000000000 : ℝ)|^2115 ≤ (32801727230211/100000000000000 : ℝ)^1603
        have hw : |(859248169/2000000000 : ℝ)|=(859248169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429624077/1000000000 : ℝ)|^2115 ≤ (32801726474691/100000000000000 : ℝ)^1603
        have hw : |(429624077/1000000000 : ℝ)|=(429624077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-558202423/2500000000 : ℝ)*x 0 + (1056506659/2000000000 : ℝ)*x 1 + (5282533319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558202423/2500000000 : ℝ)^2115 ≤ (6915828540099/50000000000000 : ℝ)^1603 := by
    have hnat : (558202423 : ℕ)^2115*50000000000000^1603 ≤ 6915828540099^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558202423 2500000000 6915828540099 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056506659/2000000000 : ℝ)^2115 ≤ (43084171327583/100000000000000 : ℝ)^1603 := by
    have hnat : (1056506659 : ℕ)^2115*100000000000000^1603 ≤ 43084171327583^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056506659 2000000000 43084171327583 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282533319/10000000000 : ℝ)^2115 ≤ (43084171585847/100000000000000 : ℝ)^1603 := by
    have hnat : (5282533319 : ℕ)^2115*100000000000000^1603 ≤ 43084171585847^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282533319 10000000000 43084171585847 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-558202423/2500000000 : ℝ), (1056506659/2000000000 : ℝ), (5282533319/10000000000 : ℝ)] ![(6915828540099/50000000000000 : ℝ), (43084171327583/100000000000000 : ℝ), (43084171585847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-558202423/2500000000 : ℝ)|^2115 ≤ (6915828540099/50000000000000 : ℝ)^1603
        have hw : |(-558202423/2500000000 : ℝ)|=(558202423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056506659/2000000000 : ℝ)|^2115 ≤ (43084171327583/100000000000000 : ℝ)^1603
        have hw : |(1056506659/2000000000 : ℝ)|=(1056506659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282533319/10000000000 : ℝ)|^2115 ≤ (43084171585847/100000000000000 : ℝ)^1603
        have hw : |(5282533319/10000000000 : ℝ)|=(5282533319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361730543/10000000000 : ℝ)*x 0 + (-531871981/2500000000 : ℝ)*x 1 + (5282533323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361730543/10000000000 : ℝ)^2115 ≤ (21969222982981/50000000000000 : ℝ)^1603 := by
    have hnat : (5361730543 : ℕ)^2115*50000000000000^1603 ≤ 21969222982981^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361730543 10000000000 21969222982981 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531871981/2500000000 : ℝ)^2115 ≤ (6488691196553/50000000000000 : ℝ)^1603 := by
    have hnat : (531871981 : ℕ)^2115*50000000000000^1603 ≤ 6488691196553^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531871981 2500000000 6488691196553 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282533323/10000000000 : ℝ)^2115 ≤ (4308417162889/10000000000000 : ℝ)^1603 := by
    have hnat : (5282533323 : ℕ)^2115*10000000000000^1603 ≤ 4308417162889^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282533323 10000000000 4308417162889 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361730543/10000000000 : ℝ), (-531871981/2500000000 : ℝ), (5282533323/10000000000 : ℝ)] ![(21969222982981/50000000000000 : ℝ), (6488691196553/50000000000000 : ℝ), (4308417162889/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361730543/10000000000 : ℝ)|^2115 ≤ (21969222982981/50000000000000 : ℝ)^1603
        have hw : |(5361730543/10000000000 : ℝ)|=(5361730543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531871981/2500000000 : ℝ)|^2115 ≤ (6488691196553/50000000000000 : ℝ)^1603
        have hw : |(-531871981/2500000000 : ℝ)|=(531871981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282533323/10000000000 : ℝ)|^2115 ≤ (4308417162889/10000000000000 : ℝ)^1603
        have hw : |(5282533323/10000000000 : ℝ)|=(5282533323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1340432641/2500000000 : ℝ)*x 0 + (660316661/1250000000 : ℝ)*x 1 + (-2127487943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340432641/2500000000 : ℝ)^2115 ≤ (43938446193019/100000000000000 : ℝ)^1603 := by
    have hnat : (1340432641 : ℕ)^2115*100000000000000^1603 ≤ 43938446193019^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340432641 2500000000 43938446193019 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660316661/1250000000 : ℝ)^2115 ≤ (1346380351633/3125000000000 : ℝ)^1603 := by
    have hnat : (660316661 : ℕ)^2115*3125000000000^1603 ≤ 1346380351633^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660316661 1250000000 1346380351633 3125000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127487943/10000000000 : ℝ)^2115 ≤ (12977382546021/100000000000000 : ℝ)^1603 := by
    have hnat : (2127487943 : ℕ)^2115*100000000000000^1603 ≤ 12977382546021^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127487943 10000000000 12977382546021 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340432641/2500000000 : ℝ), (660316661/1250000000 : ℝ), (-2127487943/10000000000 : ℝ)] ![(43938446193019/100000000000000 : ℝ), (1346380351633/3125000000000 : ℝ), (12977382546021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340432641/2500000000 : ℝ)|^2115 ≤ (43938446193019/100000000000000 : ℝ)^1603
        have hw : |(1340432641/2500000000 : ℝ)|=(1340432641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660316661/1250000000 : ℝ)|^2115 ≤ (1346380351633/3125000000000 : ℝ)^1603
        have hw : |(660316661/1250000000 : ℝ)|=(660316661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127487943/10000000000 : ℝ)|^2115 ≤ (12977382546021/100000000000000 : ℝ)^1603
        have hw : |(-2127487943/10000000000 : ℝ)|=(2127487943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2120329721/5000000000 : ℝ)*x 0 + (4402713153/10000000000 : ℝ)*x 1 + (4402713193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120329721/5000000000 : ℝ)^2115 ≤ (32242982322073/100000000000000 : ℝ)^1603 := by
    have hnat : (2120329721 : ℕ)^2115*100000000000000^1603 ≤ 32242982322073^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120329721 5000000000 32242982322073 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402713153/10000000000 : ℝ)^2115 ≤ (16939254314439/50000000000000 : ℝ)^1603 := by
    have hnat : (4402713153 : ℕ)^2115*50000000000000^1603 ≤ 16939254314439^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402713153 10000000000 16939254314439 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402713193/10000000000 : ℝ)^2115 ≤ (16939254517493/50000000000000 : ℝ)^1603 := by
    have hnat : (4402713193 : ℕ)^2115*50000000000000^1603 ≤ 16939254517493^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402713193 10000000000 16939254517493 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120329721/5000000000 : ℝ), (4402713153/10000000000 : ℝ), (4402713193/10000000000 : ℝ)] ![(32242982322073/100000000000000 : ℝ), (16939254314439/50000000000000 : ℝ), (16939254517493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120329721/5000000000 : ℝ)|^2115 ≤ (32242982322073/100000000000000 : ℝ)^1603
        have hw : |(2120329721/5000000000 : ℝ)|=(2120329721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402713153/10000000000 : ℝ)|^2115 ≤ (16939254314439/50000000000000 : ℝ)^1603
        have hw : |(4402713153/10000000000 : ℝ)|=(4402713153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402713193/10000000000 : ℝ)|^2115 ≤ (16939254517493/50000000000000 : ℝ)^1603
        have hw : |(4402713193/10000000000 : ℝ)|=(4402713193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_8 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180978953/10000000000 : ℝ)*x 0 + (2609891161/5000000000 : ℝ)*x 1 + (1076815007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180978953/10000000000 : ℝ)^2115 ≤ (6704802926827/50000000000000 : ℝ)^1603 := by
    have hnat : (2180978953 : ℕ)^2115*50000000000000^1603 ≤ 6704802926827^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180978953 10000000000 6704802926827 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609891161/5000000000 : ℝ)^2115 ≤ (2650637064877/6250000000000 : ℝ)^1603 := by
    have hnat : (2609891161 : ℕ)^2115*6250000000000^1603 ≤ 2650637064877^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609891161 5000000000 2650637064877 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076815007/2000000000 : ℝ)^2115 ≤ (22090100552021/50000000000000 : ℝ)^1603 := by
    have hnat : (1076815007 : ℕ)^2115*50000000000000^1603 ≤ 22090100552021^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076815007 2000000000 22090100552021 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180978953/10000000000 : ℝ), (2609891161/5000000000 : ℝ), (1076815007/2000000000 : ℝ)] ![(6704802926827/50000000000000 : ℝ), (2650637064877/6250000000000 : ℝ), (22090100552021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180978953/10000000000 : ℝ)|^2115 ≤ (6704802926827/50000000000000 : ℝ)^1603
        have hw : |(-2180978953/10000000000 : ℝ)|=(2180978953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609891161/5000000000 : ℝ)|^2115 ≤ (2650637064877/6250000000000 : ℝ)^1603
        have hw : |(2609891161/5000000000 : ℝ)|=(2609891161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076815007/2000000000 : ℝ)|^2115 ≤ (22090100552021/50000000000000 : ℝ)^1603
        have hw : |(1076815007/2000000000 : ℝ)|=(1076815007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_9 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645093457/5000000000 : ℝ)*x 0 + (-2087090191/10000000000 : ℝ)*x 1 + (5384075307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645093457/5000000000 : ℝ)^2115 ≤ (21583275459467/50000000000000 : ℝ)^1603 := by
    have hnat : (2645093457 : ℕ)^2115*50000000000000^1603 ≤ 21583275459467^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645093457 5000000000 21583275459467 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087090191/10000000000 : ℝ)^2115 ≤ (12653245011063/100000000000000 : ℝ)^1603 := by
    have hnat : (2087090191 : ℕ)^2115*100000000000000^1603 ≤ 12653245011063^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087090191 10000000000 12653245011063 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384075307/10000000000 : ℝ)^2115 ≤ (22090102024443/50000000000000 : ℝ)^1603 := by
    have hnat : (5384075307 : ℕ)^2115*50000000000000^1603 ≤ 22090102024443^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384075307 10000000000 22090102024443 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645093457/5000000000 : ℝ), (-2087090191/10000000000 : ℝ), (5384075307/10000000000 : ℝ)] ![(21583275459467/50000000000000 : ℝ), (12653245011063/100000000000000 : ℝ), (22090102024443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645093457/5000000000 : ℝ)|^2115 ≤ (21583275459467/50000000000000 : ℝ)^1603
        have hw : |(2645093457/5000000000 : ℝ)|=(2645093457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087090191/10000000000 : ℝ)|^2115 ≤ (12653245011063/100000000000000 : ℝ)^1603
        have hw : |(-2087090191/10000000000 : ℝ)|=(2087090191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384075307/10000000000 : ℝ)|^2115 ≤ (22090102024443/50000000000000 : ℝ)^1603
        have hw : |(5384075307/10000000000 : ℝ)|=(5384075307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_10 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290186341/10000000000 : ℝ)*x 0 + (1076815227/2000000000 : ℝ)*x 1 + (-2087089843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290186341/10000000000 : ℝ)^2115 ≤ (43166544750033/100000000000000 : ℝ)^1603 := by
    have hnat : (5290186341 : ℕ)^2115*100000000000000^1603 ≤ 43166544750033^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290186341 10000000000 43166544750033 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076815227/2000000000 : ℝ)^2115 ≤ (44180213013339/100000000000000 : ℝ)^1603 := by
    have hnat : (1076815227 : ℕ)^2115*100000000000000^1603 ≤ 44180213013339^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076815227 2000000000 44180213013339 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087089843/10000000000 : ℝ)^2115 ≤ (12653242227399/100000000000000 : ℝ)^1603 := by
    have hnat : (2087089843 : ℕ)^2115*100000000000000^1603 ≤ 12653242227399^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087089843 10000000000 12653242227399 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290186341/10000000000 : ℝ), (1076815227/2000000000 : ℝ), (-2087089843/10000000000 : ℝ)] ![(43166544750033/100000000000000 : ℝ), (44180213013339/100000000000000 : ℝ), (12653242227399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290186341/10000000000 : ℝ)|^2115 ≤ (43166544750033/100000000000000 : ℝ)^1603
        have hw : |(5290186341/10000000000 : ℝ)|=(5290186341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076815227/2000000000 : ℝ)|^2115 ≤ (44180213013339/100000000000000 : ℝ)^1603
        have hw : |(1076815227/2000000000 : ℝ)|=(1076815227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087089843/10000000000 : ℝ)|^2115 ≤ (12653242227399/100000000000000 : ℝ)^1603
        have hw : |(-2087089843/10000000000 : ℝ)|=(2087089843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_11 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (895128699/2000000000 : ℝ)*x 0 + (4285100843/10000000000 : ℝ)*x 1 + (4285100239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895128699/2000000000 : ℝ)^2115 ≤ (4327612323493/12500000000000 : ℝ)^1603 := by
    have hnat : (895128699 : ℕ)^2115*12500000000000^1603 ≤ 4327612323493^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895128699 2000000000 4327612323493 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4285100843/10000000000 : ℝ)^2115 ≤ (32689553741359/100000000000000 : ℝ)^1603 := by
    have hnat : (4285100843 : ℕ)^2115*100000000000000^1603 ≤ 32689553741359^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285100843 10000000000 32689553741359 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4285100239/10000000000 : ℝ)^2115 ≤ (6537909532389/20000000000000 : ℝ)^1603 := by
    have hnat : (4285100239 : ℕ)^2115*20000000000000^1603 ≤ 6537909532389^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285100239 10000000000 6537909532389 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895128699/2000000000 : ℝ), (4285100843/10000000000 : ℝ), (4285100239/10000000000 : ℝ)] ![(4327612323493/12500000000000 : ℝ), (32689553741359/100000000000000 : ℝ), (6537909532389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895128699/2000000000 : ℝ)|^2115 ≤ (4327612323493/12500000000000 : ℝ)^1603
        have hw : |(895128699/2000000000 : ℝ)|=(895128699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4285100843/10000000000 : ℝ)|^2115 ≤ (32689553741359/100000000000000 : ℝ)^1603
        have hw : |(4285100843/10000000000 : ℝ)|=(4285100843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4285100239/10000000000 : ℝ)|^2115 ≤ (6537909532389/20000000000000 : ℝ)^1603
        have hw : |(4285100239/10000000000 : ℝ)|=(4285100239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_12 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037661927/10000000000 : ℝ)*x 0 + (5436021309/10000000000 : ℝ)*x 1 + (5274445583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037661927/10000000000 : ℝ)^2115 ≤ (12259370142281/100000000000000 : ℝ)^1603 := by
    have hnat : (2037661927 : ℕ)^2115*100000000000000^1603 ≤ 12259370142281^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037661927 10000000000 12259370142281 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436021309/10000000000 : ℝ)^2115 ≤ (11185867260309/25000000000000 : ℝ)^1603 := by
    have hnat : (5436021309 : ℕ)^2115*25000000000000^1603 ≤ 11185867260309^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436021309 10000000000 11185867260309 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274445583/10000000000 : ℝ)^2115 ≤ (10749290200561/25000000000000 : ℝ)^1603 := by
    have hnat : (5274445583 : ℕ)^2115*25000000000000^1603 ≤ 10749290200561^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274445583 10000000000 10749290200561 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037661927/10000000000 : ℝ), (5436021309/10000000000 : ℝ), (5274445583/10000000000 : ℝ)] ![(12259370142281/100000000000000 : ℝ), (11185867260309/25000000000000 : ℝ), (10749290200561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037661927/10000000000 : ℝ)|^2115 ≤ (12259370142281/100000000000000 : ℝ)^1603
        have hw : |(-2037661927/10000000000 : ℝ)|=(2037661927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436021309/10000000000 : ℝ)|^2115 ≤ (11185867260309/25000000000000 : ℝ)^1603
        have hw : |(5436021309/10000000000 : ℝ)|=(5436021309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274445583/10000000000 : ℝ)|^2115 ≤ (10749290200561/25000000000000 : ℝ)^1603
        have hw : |(5274445583/10000000000 : ℝ)|=(5274445583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_13 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20966513/39062500 : ℝ)*x 0 + (-2130644757/10000000000 : ℝ)*x 1 + (5274444887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20966513/39062500 : ℝ)^2115 ≤ (44000051546411/100000000000000 : ℝ)^1603 := by
    have hnat : (20966513 : ℕ)^2115*100000000000000^1603 ≤ 44000051546411^1603*39062500^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20966513 39062500 44000051546411 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130644757/10000000000 : ℝ)^2115 ≤ (13002795123133/100000000000000 : ℝ)^1603 := by
    have hnat : (2130644757 : ℕ)^2115*100000000000000^1603 ≤ 13002795123133^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130644757 10000000000 13002795123133 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274444887/10000000000 : ℝ)^2115 ≤ (42997153316257/100000000000000 : ℝ)^1603 := by
    have hnat : (5274444887 : ℕ)^2115*100000000000000^1603 ≤ 42997153316257^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274444887 10000000000 42997153316257 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20966513/39062500 : ℝ), (-2130644757/10000000000 : ℝ), (5274444887/10000000000 : ℝ)] ![(44000051546411/100000000000000 : ℝ), (13002795123133/100000000000000 : ℝ), (42997153316257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20966513/39062500 : ℝ)|^2115 ≤ (44000051546411/100000000000000 : ℝ)^1603
        have hw : |(20966513/39062500 : ℝ)|=(20966513/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130644757/10000000000 : ℝ)|^2115 ≤ (13002795123133/100000000000000 : ℝ)^1603
        have hw : |(-2130644757/10000000000 : ℝ)|=(2130644757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274444887/10000000000 : ℝ)|^2115 ≤ (42997153316257/100000000000000 : ℝ)^1603
        have hw : |(5274444887/10000000000 : ℝ)|=(5274444887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_14 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073485421/2000000000 : ℝ)*x 0 + (2637222567/5000000000 : ℝ)*x 1 + (-2130644727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073485421/2000000000 : ℝ)^2115 ≤ (44000049134459/100000000000000 : ℝ)^1603 := by
    have hnat : (1073485421 : ℕ)^2115*100000000000000^1603 ≤ 44000049134459^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073485421 2000000000 44000049134459 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2637222567/5000000000 : ℝ)^2115 ≤ (21498577986461/50000000000000 : ℝ)^1603 := by
    have hnat : (2637222567 : ℕ)^2115*50000000000000^1603 ≤ 21498577986461^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637222567 5000000000 21498577986461 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130644727/10000000000 : ℝ)^2115 ≤ (6501397440787/50000000000000 : ℝ)^1603 := by
    have hnat : (2130644727 : ℕ)^2115*50000000000000^1603 ≤ 6501397440787^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130644727 10000000000 6501397440787 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073485421/2000000000 : ℝ), (2637222567/5000000000 : ℝ), (-2130644727/10000000000 : ℝ)] ![(44000049134459/100000000000000 : ℝ), (21498577986461/50000000000000 : ℝ), (6501397440787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073485421/2000000000 : ℝ)|^2115 ≤ (44000049134459/100000000000000 : ℝ)^1603
        have hw : |(1073485421/2000000000 : ℝ)|=(1073485421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2637222567/5000000000 : ℝ)|^2115 ≤ (21498577986461/50000000000000 : ℝ)^1603
        have hw : |(2637222567/5000000000 : ℝ)|=(2637222567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130644727/10000000000 : ℝ)|^2115 ≤ (6501397440787/50000000000000 : ℝ)^1603
        have hw : |(-2130644727/10000000000 : ℝ)|=(2130644727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_box_15 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (844337697/2000000000 : ℝ)*x 0 + (4412075661/10000000000 : ℝ)*x 1 + (4412075997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844337697/2000000000 : ℝ)^2115 ≤ (2003300354419/6250000000000 : ℝ)^1603 := by
    have hnat : (844337697 : ℕ)^2115*6250000000000^1603 ≤ 2003300354419^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844337697 2000000000 2003300354419 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412075661/10000000000 : ℝ)^2115 ≤ (6794719090407/20000000000000 : ℝ)^1603 := by
    have hnat : (4412075661 : ℕ)^2115*20000000000000^1603 ≤ 6794719090407^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412075661 10000000000 6794719090407 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412075997/10000000000 : ℝ)^2115 ≤ (33973598865651/100000000000000 : ℝ)^1603 := by
    have hnat : (4412075997 : ℕ)^2115*100000000000000^1603 ≤ 33973598865651^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412075997 10000000000 33973598865651 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844337697/2000000000 : ℝ), (4412075661/10000000000 : ℝ), (4412075997/10000000000 : ℝ)] ![(2003300354419/6250000000000 : ℝ), (6794719090407/20000000000000 : ℝ), (33973598865651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844337697/2000000000 : ℝ)|^2115 ≤ (2003300354419/6250000000000 : ℝ)^1603
        have hw : |(844337697/2000000000 : ℝ)|=(844337697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412075661/10000000000 : ℝ)|^2115 ≤ (6794719090407/20000000000000 : ℝ)^1603
        have hw : |(4412075661/10000000000 : ℝ)|=(4412075661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412075997/10000000000 : ℝ)|^2115 ≤ (33973598865651/100000000000000 : ℝ)^1603
        have hw : |(4412075997/10000000000 : ℝ)|=(4412075997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15563/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29699/50000 : ℝ) ∧ (40091/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (417/500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11509/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (1654423982133383/12500000000000000000 : ℝ) := by
    have hpowers : (11509/100000 : ℝ)^8459 ≤ (1654423982133383/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11509 : ℕ)^8459*12500000000000000000^2048 ≤ 1654423982133383^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11509 100000 1654423982133383 12500000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11509/100000 : ℝ)) (X := (1654423982133383/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (6153902953135893/20000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^8459 ≤ (6153902953135893/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14117 : ℕ)^8459*20000000000000000000^2048 ≤ 6153902953135893^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 6153902953135893 20000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (6153902953135893/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251654423982133383/6250000000000000000 : ℝ) ≤ (2500160204302743/2500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (6251654423982133383/6250000000000000000 : ℝ)^2048 ≤ (2500160204302743/2500000000000000 : ℝ)^8459 := by
      have hnat : (6251654423982133383 : ℕ)^2048*2500000000000000^8459 ≤ 2500160204302743^8459*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251654423982133383 6250000000000000000 2500160204302743 2500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500160204302743/2500000000000000 : ℝ)) (X := (6251654423982133383/6250000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044004906622746529/100000000000000000000 : ℝ) ≤ (10001065220763327/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100044004906622746529/100000000000000000000 : ℝ)^2048 ≤ (10001065220763327/10000000000000000 : ℝ)^8459 := by
      have hnat : (100044004906622746529 : ℕ)^2048*10000000000000000^8459 ≤ 10001065220763327^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044004906622746529 100000000000000000000 10001065220763327 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001065220763327/10000000000000000 : ℝ)) (X := (100044004906622746529/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006153902953135893/10000000000000000000 : ℝ) ≤ (5000744812157841/5000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (10006153902953135893/10000000000000000000 : ℝ)^2048 ≤ (5000744812157841/5000000000000000 : ℝ)^8459 := by
      have hnat : (10006153902953135893 : ℕ)^2048*5000000000000000^8459 ≤ 5000744812157841^8459*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006153902953135893 10000000000000000000 5000744812157841 5000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000744812157841/5000000000000000 : ℝ)) (X := (10006153902953135893/10000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1654423982133383/12500000000000000000 : ℝ) ≤ ((13035951165159053793/13040000000000000000 : ℝ)+2*(84880710471/52160000000000 : ℝ)*(11509/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (13035951165159053793/13040000000000000000 : ℝ)+2*(84880710471/52160000000000 : ℝ)*(11509/100000 : ℝ)=(2500160204302743/2500000000000000 : ℝ) by norm_num, show 1+2*(1654423982133383/12500000000000000000 : ℝ)=(6251654423982133383/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6153902953135893/20000000000000000000 : ℝ)+(1654423982133383/12500000000000000000 : ℝ) ≤ ((13035951165159053793/13040000000000000000 : ℝ)+(84880710471/52160000000000 : ℝ)*((14117/100000 : ℝ)+(11509/100000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (13035951165159053793/13040000000000000000 : ℝ)+(84880710471/52160000000000 : ℝ)*((14117/100000 : ℝ)+(11509/100000 : ℝ))=(10001065220763327/10000000000000000 : ℝ) by norm_num, show 1+(6153902953135893/20000000000000000000 : ℝ)+(1654423982133383/12500000000000000000 : ℝ)=(100044004906622746529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6153902953135893/20000000000000000000 : ℝ) ≤ ((13035951165159053793/13040000000000000000 : ℝ)+2*(84880710471/52160000000000 : ℝ)*(14117/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (13035951165159053793/13040000000000000000 : ℝ)+2*(84880710471/52160000000000 : ℝ)*(14117/100000 : ℝ)=(5000744812157841/5000000000000000 : ℝ) by norm_num, show 1+2*(6153902953135893/20000000000000000000 : ℝ)=(10006153902953135893/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13035951165159053793/13040000000000000000 : ℝ)*(X 1 0+X 2 0)+(84880710471/52160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13035951165159053793/13040000000000000000 : ℝ)) (alpha := (84880710471/52160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13035951165159053793/13040000000000000000 : ℝ)*(X 0 1+X 2 1)+(84880710471/52160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13035951165159053793/13040000000000000000 : ℝ)) (alpha := (84880710471/52160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13035951165159053793/13040000000000000000 : ℝ)*(X 0 2+X 1 2)+(84880710471/52160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13035951165159053793/13040000000000000000 : ℝ)) (alpha := (84880710471/52160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-992792849/5000000000 : ℝ)*X 0 0+(2687231169/5000000000 : ℝ)*X 0 1+(5374462363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648481217/5000000000 : ℝ)*X 1 0+(-2090975301/10000000000 : ℝ)*X 1 1+(2687231173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529696257/1000000000 : ℝ)*X 2 0+(5374462353/10000000000 : ℝ)*X 2 1+(-522743777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2226822011/5000000000 : ℝ)*X 0 0+(859248169/2000000000 : ℝ)*X 0 1+(429624077/1000000000 : ℝ)*X 0 2+(2226822011/5000000000 : ℝ)*X 1 0+(859248169/2000000000 : ℝ)*X 1 1+(429624077/1000000000 : ℝ)*X 1 2+(2226822011/5000000000 : ℝ)*X 2 0+(859248169/2000000000 : ℝ)*X 2 1+(429624077/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-558202423/2500000000 : ℝ)*X 0 0+(1056506659/2000000000 : ℝ)*X 0 1+(5282533319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361730543/10000000000 : ℝ)*X 1 0+(-531871981/2500000000 : ℝ)*X 1 1+(5282533323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340432641/2500000000 : ℝ)*X 2 0+(660316661/1250000000 : ℝ)*X 2 1+(-2127487943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120329721/5000000000 : ℝ)*X 0 0+(4402713153/10000000000 : ℝ)*X 0 1+(4402713193/10000000000 : ℝ)*X 0 2+(2120329721/5000000000 : ℝ)*X 1 0+(4402713153/10000000000 : ℝ)*X 1 1+(4402713193/10000000000 : ℝ)*X 1 2+(2120329721/5000000000 : ℝ)*X 2 0+(4402713153/10000000000 : ℝ)*X 2 1+(4402713193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2180978953/10000000000 : ℝ)*X 0 0+(2609891161/5000000000 : ℝ)*X 0 1+(1076815007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2645093457/5000000000 : ℝ)*X 1 0+(-2087090191/10000000000 : ℝ)*X 1 1+(5384075307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290186341/10000000000 : ℝ)*X 2 0+(1076815227/2000000000 : ℝ)*X 2 1+(-2087089843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((895128699/2000000000 : ℝ)*X 0 0+(4285100843/10000000000 : ℝ)*X 0 1+(4285100239/10000000000 : ℝ)*X 0 2+(895128699/2000000000 : ℝ)*X 1 0+(4285100843/10000000000 : ℝ)*X 1 1+(4285100239/10000000000 : ℝ)*X 1 2+(895128699/2000000000 : ℝ)*X 2 0+(4285100843/10000000000 : ℝ)*X 2 1+(4285100239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2037661927/10000000000 : ℝ)*X 0 0+(5436021309/10000000000 : ℝ)*X 0 1+(5274445583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((20966513/39062500 : ℝ)*X 1 0+(-2130644757/10000000000 : ℝ)*X 1 1+(5274444887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073485421/2000000000 : ℝ)*X 2 0+(2637222567/5000000000 : ℝ)*X 2 1+(-2130644727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((844337697/2000000000 : ℝ)*X 0 0+(4412075661/10000000000 : ℝ)*X 0 1+(4412075997/10000000000 : ℝ)*X 0 2+(844337697/2000000000 : ℝ)*X 1 0+(4412075661/10000000000 : ℝ)*X 1 1+(4412075997/10000000000 : ℝ)*X 1 2+(844337697/2000000000 : ℝ)*X 2 0+(4412075661/10000000000 : ℝ)*X 2 1+(4412075997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15563/25000 : ℝ) ≤ (-25366541911531140170649529075383/40750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1945451/25000000000000 : ℝ)*(upper1) + (2820219/20000000000000 : ℝ)*(upper2) + (3598417/50000000000000 : ℝ)*(upper3) + (29622651/100000000000000 : ℝ)*(upper5) + (251478455074877/6250000000000 : ℝ)*(major0) + (251478455074877/6250000000000 : ℝ)*(major1) + (251478455074877/6250000000000 : ℝ)*(major2) + (90875227/2500000000000 : ℝ)*(sp2) + (220152339/10000000000000 : ℝ)*(sp3) + (2709748119635301/50000000000000 : ℝ)*(sp4) + (5419492835924931/100000000000000 : ℝ)*(sp5) + (2709746302130761/50000000000000 : ℝ)*(sp6) + (2648561849137049/100000000000000 : ℝ)*(sp7) + (3403345671/100000000000000 : ℝ)*(sp13) + (1324282025330219/50000000000000 : ℝ)*(f.failure) + (2709748119635301/50000000000000 : ℝ)*(f.sum) + (15873494493/32600000000000000000000000 : ℝ)*base65 + (602857042137108461/81500000000000000000000000000000 : ℝ)*base67 + (2538668213739891539/81500000000000000000000000000000 : ℝ)*base70 + (75576848955891539/81500000000000000000000000000000 : ℝ)*base72 + (250002259461/163000000000000000000000000 : ℝ)*base74 + (2244459055322108461/81500000000000000000000000000000 : ℝ)*base75 + (236329406003608461/81500000000000000000000000000000 : ℝ)*base77 + (414101739278108461/81500000000000000000000000000000 : ℝ)*base79 + (2650787842953/81500000000000000000000000 : ℝ)*base82 + (2138669/156250000000000000000 : ℝ)*base90 + (2138669/156250000000000000000 : ℝ)*base92 + (2138669/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29699/50000 : ℝ) ≤ (387288523398321930788933644251621/652000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12137989/25000000000000 : ℝ)*(lower1) + (23188833/100000000000000 : ℝ)*(lower2) + (115707847/100000000000000 : ℝ)*(upper4) + (4089866627946999/100000000000000 : ℝ)*(major0) + (4089866627946999/100000000000000 : ℝ)*(major1) + (4089866627946999/100000000000000 : ℝ)*(major2) + (683473015208889/12500000000000 : ℝ)*(sp0) + (1366930986367511/25000000000000 : ℝ)*(sp1) + (5467782168990201/100000000000000 : ℝ)*(sp2) + (538429059169731/20000000000000 : ℝ)*(sp3) + (350630429/10000000000000 : ℝ)*(sp6) + (2257992233/100000000000000 : ℝ)*(sp7) + (1553623379/100000000000000 : ℝ)*(sp8) + (61729824447/100000000000000 : ℝ)*(sp9) + (336518444230111/12500000000000 : ℝ)*(f.failure) + (1366946418823623/25000000000000 : ℝ)*(f.sum) + (7103448278493/521600000000000000000000000 : ℝ)*base65 + (6406942576845832793/1304000000000000000000000000000000 : ℝ)*base68 + (7162421786333832793/1304000000000000000000000000000000 : ℝ)*base70 + (17766116469426167207/1304000000000000000000000000000000 : ℝ)*base71 + (1069441009341/521600000000000000000000000 : ℝ)*base73 + (15654060048061832793/1304000000000000000000000000000000 : ℝ)*base76 + (8385032920722167207/1304000000000000000000000000000000 : ℝ)*base77 + (5449705619861832793/1304000000000000000000000000000000 : ℝ)*base80 + (4812485142801/2608000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15471/2441406250000000000 : ℝ)*base90 + (15471/2441406250000000000 : ℝ)*base92 + (15471/2441406250000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40091/50000 : ℝ) ≤ (522805192859578460259785158493139/652000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7457163/20000000000000 : ℝ)*(lower3) + (7946339/6250000000000 : ℝ)*(upper4) + (6986797/2500000000000 : ℝ)*(lower5) + (4556313596225147/100000000000000 : ℝ)*(major0) + (4556313596225147/100000000000000 : ℝ)*(major1) + (4556313596225147/100000000000000 : ℝ)*(major2) + (20552531983/100000000000000 : ℝ)*(sp0) + (231563299753/100000000000000 : ℝ)*(sp1) + (933862008287/100000000000000 : ℝ)*(sp2) + (23358821963/10000000000000 : ℝ)*(sp3) + (304334645163751/5000000000000 : ℝ)*(sp8) + (24345927570029/400000000000 : ℝ)*(sp9) + (1521444898449679/25000000000000 : ℝ)*(sp10) + (2998951866580113/100000000000000 : ℝ)*(sp11) + (1499592727399871/50000000000000 : ℝ)*(f.failure) + (6086713455807003/100000000000000 : ℝ)*(f.sum) + (10384614382829/2608000000000000000000000000 : ℝ)*base65 + (8823076556440417429/1304000000000000000000000000000000 : ℝ)*base68 + (22972869662672417429/1304000000000000000000000000000000 : ℝ)*base70 + (2045141175816417429/1304000000000000000000000000000000 : ℝ)*base72 + (3520348980989/2608000000000000000000000000 : ℝ)*base73 + (8817551628408417429/1304000000000000000000000000000000 : ℝ)*base76 + (6782247754792417429/1304000000000000000000000000000000 : ℝ)*base78 + (5942031053648417429/1304000000000000000000000000000000 : ℝ)*base80 + (1607404949747/2608000000000000000000000000 : ℝ)*base82 + (2008421/156250000000000000000 : ℝ)*base90 + (2008421/156250000000000000000 : ℝ)*base92 + (2008421/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-417/500 : ℝ) ≤ (-135938233845352638366157109990739/163000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5227703/5000000000000 : ℝ)*(upper3) + (50064373/50000000000000 : ℝ)*(lower4) + (25460237/12500000000000 : ℝ)*(upper5) + (2295988785724841/50000000000000 : ℝ)*(major0) + (2295988785724841/50000000000000 : ℝ)*(major1) + (2295988785724841/50000000000000 : ℝ)*(major2) + (8940049023/20000000000000 : ℝ)*(sp4) + (176630971353/25000000000000 : ℝ)*(sp5) + (64004355517/10000000000000 : ℝ)*(sp6) + (371445583487/100000000000000 : ℝ)*(sp7) + (6189048468371691/100000000000000 : ℝ)*(sp12) + (6188386644731393/100000000000000 : ℝ)*(sp13) + (1547113281265409/25000000000000 : ℝ)*(sp14) + (23611638738471/781250000000 : ℝ)*(sp15) + (5903635164273/195312500000 : ℝ)*(f.failure) + (3094546584308403/50000000000000 : ℝ)*(f.sum) + (7801489094823/1304000000000000000000000000 : ℝ)*base65 + (1345997219852878087/652000000000000000000000000000000 : ℝ)*base68 + (3105591237163121913/652000000000000000000000000000000 : ℝ)*base69 + (7875318173535121913/652000000000000000000000000000000 : ℝ)*base71 + (5203098037649/1304000000000000000000000000 : ℝ)*base74 + (4820909265055121913/652000000000000000000000000000000 : ℝ)*base75 + (2978137671455121913/652000000000000000000000000000000 : ℝ)*base77 + (1664410177667121913/652000000000000000000000000000000 : ℝ)*base79 + (11589406129831/1304000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (50839/19531250000000000000 : ℝ)*base89 + (50839/19531250000000000000 : ℝ)*base91 + (50839/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1267_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15563/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29699/50000 : ℝ) else (40091/50000 : ℝ) ≤ X j i ∧ X j i ≤ (417/500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1267_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1267_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15563/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29699/50000 : ℝ) else (40091/50000 : ℝ) ≤ X j i ∧ X j i ≤ (417/500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1267_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15563/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29699/50000 : ℝ) else (40091/50000 : ℝ) ≤ X j i ∧ X j i ≤ (417/500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

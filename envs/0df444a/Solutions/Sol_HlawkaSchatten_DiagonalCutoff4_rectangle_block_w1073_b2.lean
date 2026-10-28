-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:24.723054+00:00
-- url     : https://prove2.me/submissions/537e1e63-4bbb-4e1a-a9bd-53001c32bbed

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
theorem support_rectangle_w1073_s6_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200278017/10000000000 : ℝ)*x 0 + (674346617/1250000000 : ℝ)*x 1 + (5264074267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200278017/10000000000 : ℝ)^4133 ≤ (835202541329/6250000000000 : ℝ)^3109 := by
    have hnat : (2200278017 : ℕ)^4133*6250000000000^3109 ≤ 835202541329^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200278017 10000000000 835202541329 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674346617/1250000000 : ℝ)^4133 ≤ (22012235689481/50000000000000 : ℝ)^3109 := by
    have hnat : (674346617 : ℕ)^4133*50000000000000^3109 ≤ 22012235689481^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674346617 1250000000 22012235689481 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264074267/10000000000 : ℝ)^4133 ≤ (2130614397491/5000000000000 : ℝ)^3109 := by
    have hnat : (5264074267 : ℕ)^4133*5000000000000^3109 ≤ 2130614397491^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264074267 10000000000 2130614397491 5000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200278017/10000000000 : ℝ), (674346617/1250000000 : ℝ), (5264074267/10000000000 : ℝ)] ![(835202541329/6250000000000 : ℝ), (22012235689481/50000000000000 : ℝ), (2130614397491/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200278017/10000000000 : ℝ)|^4133 ≤ (835202541329/6250000000000 : ℝ)^3109
        have hw : |(-2200278017/10000000000 : ℝ)|=(2200278017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674346617/1250000000 : ℝ)|^4133 ≤ (22012235689481/50000000000000 : ℝ)^3109
        have hw : |(674346617/1250000000 : ℝ)|=(674346617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264074267/10000000000 : ℝ)|^4133 ≤ (2130614397491/5000000000000 : ℝ)^3109
        have hw : |(5264074267/10000000000 : ℝ)|=(5264074267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345097141/10000000000 : ℝ)*x 0 + (-2266596799/10000000000 : ℝ)*x 1 + (1316018523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345097141/10000000000 : ℝ)^4133 ≤ (21743193706171/50000000000000 : ℝ)^3109 := by
    have hnat : (5345097141 : ℕ)^4133*50000000000000^3109 ≤ 21743193706171^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345097141 10000000000 21743193706171 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266596799/10000000000 : ℝ)^4133 ≤ (13901326507597/100000000000000 : ℝ)^3109 := by
    have hnat : (2266596799 : ℕ)^4133*100000000000000^3109 ≤ 13901326507597^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266596799 10000000000 13901326507597 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316018523/2500000000 : ℝ)^4133 ≤ (665816969791/1562500000000 : ℝ)^3109 := by
    have hnat : (1316018523 : ℕ)^4133*1562500000000^3109 ≤ 665816969791^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316018523 2500000000 665816969791 1562500000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345097141/10000000000 : ℝ), (-2266596799/10000000000 : ℝ), (1316018523/2500000000 : ℝ)] ![(21743193706171/50000000000000 : ℝ), (13901326507597/100000000000000 : ℝ), (665816969791/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345097141/10000000000 : ℝ)|^4133 ≤ (21743193706171/50000000000000 : ℝ)^3109
        have hw : |(5345097141/10000000000 : ℝ)|=(5345097141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2266596799/10000000000 : ℝ)|^4133 ≤ (13901326507597/100000000000000 : ℝ)^3109
        have hw : |(-2266596799/10000000000 : ℝ)|=(2266596799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316018523/2500000000 : ℝ)|^4133 ≤ (665816969791/1562500000000 : ℝ)^3109
        have hw : |(1316018523/2500000000 : ℝ)|=(1316018523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672548907/5000000000 : ℝ)*x 0 + (5264073733/10000000000 : ℝ)*x 1 + (-2266596381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672548907/5000000000 : ℝ)^4133 ≤ (1358949834097/3125000000000 : ℝ)^3109 := by
    have hnat : (2672548907 : ℕ)^4133*3125000000000^3109 ≤ 1358949834097^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672548907 5000000000 1358949834097 3125000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264073733/10000000000 : ℝ)^4133 ≤ (21306141101691/50000000000000 : ℝ)^3109 := by
    have hnat : (5264073733 : ℕ)^4133*50000000000000^3109 ≤ 21306141101691^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264073733 10000000000 21306141101691 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266596381/10000000000 : ℝ)^4133 ≤ (1390132309957/10000000000000 : ℝ)^3109 := by
    have hnat : (2266596381 : ℕ)^4133*10000000000000^3109 ≤ 1390132309957^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266596381 10000000000 1390132309957 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672548907/5000000000 : ℝ), (5264073733/10000000000 : ℝ), (-2266596381/10000000000 : ℝ)] ![(1358949834097/3125000000000 : ℝ), (21306141101691/50000000000000 : ℝ), (1390132309957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672548907/5000000000 : ℝ)|^4133 ≤ (1358949834097/3125000000000 : ℝ)^3109
        have hw : |(2672548907/5000000000 : ℝ)|=(2672548907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264073733/10000000000 : ℝ)|^4133 ≤ (21306141101691/50000000000000 : ℝ)^3109
        have hw : |(5264073733/10000000000 : ℝ)|=(5264073733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266596381/10000000000 : ℝ)|^4133 ≤ (1390132309957/10000000000000 : ℝ)^3109
        have hw : |(-2266596381/10000000000 : ℝ)|=(2266596381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4374459741/10000000000 : ℝ)*x 0 + (4248107769/10000000000 : ℝ)*x 1 + (4504614737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374459741/10000000000 : ℝ)^4133 ≤ (16658159435911/50000000000000 : ℝ)^3109 := by
    have hnat : (4374459741 : ℕ)^4133*50000000000000^3109 ≤ 16658159435911^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374459741 10000000000 16658159435911 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248107769/10000000000 : ℝ)^4133 ≤ (6408636465529/20000000000000 : ℝ)^3109 := by
    have hnat : (4248107769 : ℕ)^4133*20000000000000^3109 ≤ 6408636465529^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248107769 10000000000 6408636465529 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504614737/10000000000 : ℝ)^4133 ≤ (1385619951351/4000000000000 : ℝ)^3109 := by
    have hnat : (4504614737 : ℕ)^4133*4000000000000^3109 ≤ 1385619951351^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504614737 10000000000 1385619951351 4000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374459741/10000000000 : ℝ), (4248107769/10000000000 : ℝ), (4504614737/10000000000 : ℝ)] ![(16658159435911/50000000000000 : ℝ), (6408636465529/20000000000000 : ℝ), (1385619951351/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374459741/10000000000 : ℝ)|^4133 ≤ (16658159435911/50000000000000 : ℝ)^3109
        have hw : |(4374459741/10000000000 : ℝ)|=(4374459741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248107769/10000000000 : ℝ)|^4133 ≤ (6408636465529/20000000000000 : ℝ)^3109
        have hw : |(4248107769/10000000000 : ℝ)|=(4248107769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504614737/10000000000 : ℝ)|^4133 ≤ (1385619951351/4000000000000 : ℝ)^3109
        have hw : |(4504614737/10000000000 : ℝ)|=(4504614737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220028343/1000000000 : ℝ)*x 0 + (1052880843/2000000000 : ℝ)*x 1 + (5394441607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220028343/1000000000 : ℝ)^4133 ≤ (6681642182427/50000000000000 : ℝ)^3109 := by
    have hnat : (220028343 : ℕ)^4133*50000000000000^3109 ≤ 6681642182427^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220028343 1000000000 6681642182427 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052880843/2000000000 : ℝ)^4133 ≤ (8523167719387/20000000000000 : ℝ)^3109 := by
    have hnat : (1052880843 : ℕ)^4133*20000000000000^3109 ≤ 8523167719387^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052880843 2000000000 8523167719387 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394441607/10000000000 : ℝ)^4133 ≤ (44020877026017/100000000000000 : ℝ)^3109 := by
    have hnat : (5394441607 : ℕ)^4133*100000000000000^3109 ≤ 44020877026017^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394441607 10000000000 44020877026017 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220028343/1000000000 : ℝ), (1052880843/2000000000 : ℝ), (5394441607/10000000000 : ℝ)] ![(6681642182427/50000000000000 : ℝ), (8523167719387/20000000000000 : ℝ), (44020877026017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220028343/1000000000 : ℝ)|^4133 ≤ (6681642182427/50000000000000 : ℝ)^3109
        have hw : |(-220028343/1000000000 : ℝ)|=(220028343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052880843/2000000000 : ℝ)|^4133 ≤ (8523167719387/20000000000000 : ℝ)^3109
        have hw : |(1052880843/2000000000 : ℝ)|=(1052880843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394441607/10000000000 : ℝ)|^4133 ≤ (44020877026017/100000000000000 : ℝ)^3109
        have hw : |(5394441607/10000000000 : ℝ)|=(5394441607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312158713/10000000000 : ℝ)*x 0 + (-267028621/1250000000 : ℝ)*x 1 + (1078888321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312158713/10000000000 : ℝ)^4133 ≤ (43130507308673/100000000000000 : ℝ)^3109 := by
    have hnat : (5312158713 : ℕ)^4133*100000000000000^3109 ≤ 43130507308673^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312158713 10000000000 43130507308673 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267028621/1250000000 : ℝ)^4133 ≤ (6424307837081/50000000000000 : ℝ)^3109 := by
    have hnat : (267028621 : ℕ)^4133*50000000000000^3109 ≤ 6424307837081^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267028621 1250000000 6424307837081 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078888321/2000000000 : ℝ)^4133 ≤ (44020877004321/100000000000000 : ℝ)^3109 := by
    have hnat : (1078888321 : ℕ)^4133*100000000000000^3109 ≤ 44020877004321^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078888321 2000000000 44020877004321 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312158713/10000000000 : ℝ), (-267028621/1250000000 : ℝ), (1078888321/2000000000 : ℝ)] ![(43130507308673/100000000000000 : ℝ), (6424307837081/50000000000000 : ℝ), (44020877004321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312158713/10000000000 : ℝ)|^4133 ≤ (43130507308673/100000000000000 : ℝ)^3109
        have hw : |(5312158713/10000000000 : ℝ)|=(5312158713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267028621/1250000000 : ℝ)|^4133 ≤ (6424307837081/50000000000000 : ℝ)^3109
        have hw : |(-267028621/1250000000 : ℝ)|=(267028621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078888321/2000000000 : ℝ)|^4133 ≤ (44020877004321/100000000000000 : ℝ)^3109
        have hw : |(1078888321/2000000000 : ℝ)|=(1078888321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132803963/250000000 : ℝ)*x 0 + (5394441871/10000000000 : ℝ)*x 1 + (-534057217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132803963/250000000 : ℝ)^4133 ≤ (10782626306387/25000000000000 : ℝ)^3109 := by
    have hnat : (132803963 : ℕ)^4133*25000000000000^3109 ≤ 10782626306387^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132803963 250000000 10782626306387 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394441871/10000000000 : ℝ)^4133 ≤ (44020879889937/100000000000000 : ℝ)^3109 := by
    have hnat : (5394441871 : ℕ)^4133*100000000000000^3109 ≤ 44020879889937^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394441871 10000000000 44020879889937 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534057217/2500000000 : ℝ)^4133 ≤ (6424307437299/50000000000000 : ℝ)^3109 := by
    have hnat : (534057217 : ℕ)^4133*50000000000000^3109 ≤ 6424307437299^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534057217 2500000000 6424307437299 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132803963/250000000 : ℝ), (5394441871/10000000000 : ℝ), (-534057217/2500000000 : ℝ)] ![(10782626306387/25000000000000 : ℝ), (44020879889937/100000000000000 : ℝ), (6424307437299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132803963/250000000 : ℝ)|^4133 ≤ (10782626306387/25000000000000 : ℝ)^3109
        have hw : |(132803963/250000000 : ℝ)|=(132803963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394441871/10000000000 : ℝ)|^4133 ≤ (44020879889937/100000000000000 : ℝ)^3109
        have hw : |(5394441871/10000000000 : ℝ)|=(5394441871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534057217/2500000000 : ℝ)|^4133 ≤ (6424307437299/50000000000000 : ℝ)^3109
        have hw : |(-534057217/2500000000 : ℝ)|=(534057217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s6_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273404367/625000000 : ℝ)*x 0 + (900793437/2000000000 : ℝ)*x 1 + (2124378843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273404367/625000000 : ℝ)^4133 ≤ (33316421444041/100000000000000 : ℝ)^3109 := by
    have hnat : (273404367 : ℕ)^4133*100000000000000^3109 ≤ 33316421444041^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273404367 625000000 33316421444041 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900793437/2000000000 : ℝ)^4133 ≤ (17316939563029/50000000000000 : ℝ)^3109 := by
    have hnat : (900793437 : ℕ)^4133*50000000000000^3109 ≤ 17316939563029^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900793437 2000000000 17316939563029 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124378843/5000000000 : ℝ)^4133 ≤ (32049699416421/100000000000000 : ℝ)^3109 := by
    have hnat : (2124378843 : ℕ)^4133*100000000000000^3109 ≤ 32049699416421^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124378843 5000000000 32049699416421 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273404367/625000000 : ℝ), (900793437/2000000000 : ℝ), (2124378843/5000000000 : ℝ)] ![(33316421444041/100000000000000 : ℝ), (17316939563029/50000000000000 : ℝ), (32049699416421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273404367/625000000 : ℝ)|^4133 ≤ (33316421444041/100000000000000 : ℝ)^3109
        have hw : |(273404367/625000000 : ℝ)|=(273404367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900793437/2000000000 : ℝ)|^4133 ≤ (17316939563029/50000000000000 : ℝ)^3109
        have hw : |(900793437/2000000000 : ℝ)|=(900793437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124378843/5000000000 : ℝ)|^4133 ≤ (32049699416421/100000000000000 : ℝ)^3109
        have hw : |(2124378843/5000000000 : ℝ)|=(2124378843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9/80 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14019/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1121/10000 : ℝ) ^ (8265/2048 : ℝ) ≤ (7303248737062717/50000000000000000000 : ℝ) := by
    have hpowers : (1121/10000 : ℝ)^8265 ≤ (7303248737062717/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1121 : ℕ)^8265*50000000000000000000^2048 ≤ 7303248737062717^2048*10000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 10000 7303248737062717 50000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/10000 : ℝ)) (X := (7303248737062717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (36449894032422583/100000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^8265 ≤ (36449894032422583/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14061 : ℕ)^8265*100000000000000000000^2048 ≤ 36449894032422583^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 36449894032422583 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (36449894032422583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007303248737062717/25000000000000000000 : ℝ) ≤ (5000361897406983/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (25007303248737062717/25000000000000000000 : ℝ)^2048 ≤ (5000361897406983/5000000000000000 : ℝ)^8265 := by
      have hnat : (25007303248737062717 : ℕ)^2048*5000000000000000^8265 ≤ 5000361897406983^8265*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007303248737062717 25000000000000000000 5000361897406983 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361897406983/5000000000000000 : ℝ)) (X := (25007303248737062717/25000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051056391506548017/100000000000000000000 : ℝ) ≤ (10001264893127287/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (100051056391506548017/100000000000000000000 : ℝ)^2048 ≤ (10001264893127287/10000000000000000 : ℝ)^8265 := by
      have hnat : (100051056391506548017 : ℕ)^2048*10000000000000000^8265 ≤ 10001264893127287^8265*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051056391506548017 100000000000000000000 10001264893127287 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264893127287/10000000000000000 : ℝ)) (X := (100051056391506548017/100000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036449894032422583/50000000000000000000 : ℝ) ≤ (312556437232519/312500000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50036449894032422583/50000000000000000000 : ℝ)^2048 ≤ (312556437232519/312500000000000 : ℝ)^8265 := by
      have hnat : (50036449894032422583 : ℕ)^2048*312500000000000^8265 ≤ 312556437232519^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036449894032422583 50000000000000000000 312556437232519 312500000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312556437232519/312500000000000 : ℝ)) (X := (50036449894032422583/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7303248737062717/50000000000000000000 : ℝ) ≤ ((14249966057414980123/14255000000000000000 : ℝ)+2*(541098313321/285100000000000 : ℝ)*(1121/10000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (14249966057414980123/14255000000000000000 : ℝ)+2*(541098313321/285100000000000 : ℝ)*(1121/10000 : ℝ)=(5000361897406983/5000000000000000 : ℝ) by norm_num, show 1+2*(7303248737062717/50000000000000000000 : ℝ)=(25007303248737062717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36449894032422583/100000000000000000000 : ℝ)+(7303248737062717/50000000000000000000 : ℝ) ≤ ((14249966057414980123/14255000000000000000 : ℝ)+(541098313321/285100000000000 : ℝ)*((14061/100000 : ℝ)+(1121/10000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (14249966057414980123/14255000000000000000 : ℝ)+(541098313321/285100000000000 : ℝ)*((14061/100000 : ℝ)+(1121/10000 : ℝ))=(10001264893127287/10000000000000000 : ℝ) by norm_num, show 1+(36449894032422583/100000000000000000000 : ℝ)+(7303248737062717/50000000000000000000 : ℝ)=(100051056391506548017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36449894032422583/100000000000000000000 : ℝ) ≤ ((14249966057414980123/14255000000000000000 : ℝ)+2*(541098313321/285100000000000 : ℝ)*(14061/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (14249966057414980123/14255000000000000000 : ℝ)+2*(541098313321/285100000000000 : ℝ)*(14061/100000 : ℝ)=(312556437232519/312500000000000 : ℝ) by norm_num, show 1+2*(36449894032422583/100000000000000000000 : ℝ)=(50036449894032422583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14249966057414980123/14255000000000000000 : ℝ)*(X 1 0+X 2 0)+(541098313321/285100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (14249966057414980123/14255000000000000000 : ℝ)) (alpha := (541098313321/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14249966057414980123/14255000000000000000 : ℝ)*(X 0 1+X 2 1)+(541098313321/285100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (14249966057414980123/14255000000000000000 : ℝ)) (alpha := (541098313321/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14249966057414980123/14255000000000000000 : ℝ)*(X 0 2+X 1 2)+(541098313321/285100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (14249966057414980123/14255000000000000000 : ℝ)) (alpha := (541098313321/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200278017/10000000000 : ℝ)*X 0 0+(674346617/1250000000 : ℝ)*X 0 1+(5264074267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345097141/10000000000 : ℝ)*X 1 0+(-2266596799/10000000000 : ℝ)*X 1 1+(1316018523/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672548907/5000000000 : ℝ)*X 2 0+(5264073733/10000000000 : ℝ)*X 2 1+(-2266596381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374459741/10000000000 : ℝ)*X 0 0+(4248107769/10000000000 : ℝ)*X 0 1+(4504614737/10000000000 : ℝ)*X 0 2+(4374459741/10000000000 : ℝ)*X 1 0+(4248107769/10000000000 : ℝ)*X 1 1+(4504614737/10000000000 : ℝ)*X 1 2+(4374459741/10000000000 : ℝ)*X 2 0+(4248107769/10000000000 : ℝ)*X 2 1+(4504614737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220028343/1000000000 : ℝ)*X 0 0+(1052880843/2000000000 : ℝ)*X 0 1+(5394441607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312158713/10000000000 : ℝ)*X 1 0+(-267028621/1250000000 : ℝ)*X 1 1+(1078888321/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132803963/250000000 : ℝ)*X 2 0+(5394441871/10000000000 : ℝ)*X 2 1+(-534057217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273404367/625000000 : ℝ)*X 0 0+(900793437/2000000000 : ℝ)*X 0 1+(2124378843/5000000000 : ℝ)*X 0 2+(273404367/625000000 : ℝ)*X 1 0+(900793437/2000000000 : ℝ)*X 1 1+(2124378843/5000000000 : ℝ)*X 1 2+(273404367/625000000 : ℝ)*X 2 0+(900793437/2000000000 : ℝ)*X 2 1+(2124378843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3158207206274694654833760273/356375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1436848711/100000000000000 : ℝ)*(base19) + (2122113027/100000000000000 : ℝ)*(base23) + (47609653/25000000000000 : ℝ)*(lower2) + (250822999/100000000000000 : ℝ)*(upper5) + (2887459001278983/50000000000000 : ℝ)*(major0) + (2887459001278983/50000000000000 : ℝ)*(major1) + (2887459001278983/50000000000000 : ℝ)*(major2) + (3825606816791789/50000000000000 : ℝ)*(sp0) + (382562706159071/5000000000000 : ℝ)*(sp1) + (765126612487191/10000000000000 : ℝ)*(sp2) + (487318414685349/12500000000000 : ℝ)*(sp3) + (54613401359/100000000000000 : ℝ)*(sp4) + (2537390961/20000000000000 : ℝ)*(sp5) + (20145247077/100000000000000 : ℝ)*(sp7) + (3898567462729869/100000000000000 : ℝ)*(f.failure) + (7651268246984937/100000000000000 : ℝ)*(f.sum) + (11069934497007/7127500000000000000000000000 : ℝ)*base66 + (11828634832246695091/712750000000000000000000000000000 : ℝ)*base68 + (5626689373103945091/712750000000000000000000000000000 : ℝ)*base70 + (865318139637054909/712750000000000000000000000000000 : ℝ)*base71 + (82148874907471/14255000000000000000000000000 : ℝ)*base73 + (15926228135514554909/712750000000000000000000000000000 : ℝ)*base75 + (1943909489560804909/712750000000000000000000000000000 : ℝ)*base77 + (768674854681554909/712750000000000000000000000000000 : ℝ)*base79 + (14437413714003/7127500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (55700739/10000000000000000000000 : ℝ)*base89 + (55700739/10000000000000000000000 : ℝ)*base91 + (55700739/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3401057330706513999761061897/356375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2016969667/100000000000000 : ℝ)*(base19) + (1781130619/100000000000000 : ℝ)*(base23) + (62838443/25000000000000 : ℝ)*(upper3) + (3115233/100000000000000 : ℝ)*(lower4) + (52266113/25000000000000 : ℝ)*(upper5) + (2902110151729087/50000000000000 : ℝ)*(major0) + (2902110151729087/50000000000000 : ℝ)*(major1) + (2902110151729087/50000000000000 : ℝ)*(major2) + (3241007627/6250000000000 : ℝ)*(sp1) + (14483306973/25000000000000 : ℝ)*(sp2) + (7690091247038201/100000000000000 : ℝ)*(sp4) + (3845018686973251/50000000000000 : ℝ)*(sp5) + (7690031532679689/100000000000000 : ℝ)*(sp6) + (979587260440543/25000000000000 : ℝ)*(sp7) + (979587260440543/25000000000000 : ℝ)*(f.failure) + (7690091247038201/100000000000000 : ℝ)*(f.sum) + (8298133527677/1781875000000000000000000000 : ℝ)*base66 + (11857905509386037701/712750000000000000000000000000000 : ℝ)*base67 + (4420972250045037701/712750000000000000000000000000000 : ℝ)*base69 + (633196034198212299/712750000000000000000000000000000 : ℝ)*base72 + (9878180315637/7127500000000000000000000000 : ℝ)*base73 + (7468967618854212299/712750000000000000000000000000000 : ℝ)*base76 + (2602798779194287701/712750000000000000000000000000000 : ℝ)*base77 + (17743366119201037701/712750000000000000000000000000000 : ℝ)*base79 + (1892549316793/7127500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5812433/2500000000000000000000 : ℝ)*base89 + (5812433/2500000000000000000000 : ℝ)*base91 + (5812433/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s7_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200317309/10000000000 : ℝ)*x 0 + (2697164963/5000000000 : ℝ)*x 1 + (2632245689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200317309/10000000000 : ℝ)^4133 ≤ (13363557898623/100000000000000 : ℝ)^3109 := by
    have hnat : (2200317309 : ℕ)^4133*100000000000000^3109 ≤ 13363557898623^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200317309 10000000000 13363557898623 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697164963/5000000000 : ℝ)^4133 ≤ (11004916373643/25000000000000 : ℝ)^3109 := by
    have hnat : (2697164963 : ℕ)^4133*25000000000000^3109 ≤ 11004916373643^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697164963 5000000000 11004916373643 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632245689/5000000000 : ℝ)^4133 ≤ (1704671063619/4000000000000 : ℝ)^3109 := by
    have hnat : (2632245689 : ℕ)^4133*4000000000000^3109 ≤ 1704671063619^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632245689 5000000000 1704671063619 4000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200317309/10000000000 : ℝ), (2697164963/5000000000 : ℝ), (2632245689/5000000000 : ℝ)] ![(13363557898623/100000000000000 : ℝ), (11004916373643/25000000000000 : ℝ), (1704671063619/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200317309/10000000000 : ℝ)|^4133 ≤ (13363557898623/100000000000000 : ℝ)^3109
        have hw : |(-2200317309/10000000000 : ℝ)|=(2200317309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697164963/5000000000 : ℝ)|^4133 ≤ (11004916373643/25000000000000 : ℝ)^3109
        have hw : |(2697164963/5000000000 : ℝ)|=(2697164963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632245689/5000000000 : ℝ)|^4133 ≤ (1704671063619/4000000000000 : ℝ)^3109
        have hw : |(2632245689/5000000000 : ℝ)|=(2632245689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336246619/2500000000 : ℝ)*x 0 + (-226619269/1000000000 : ℝ)*x 1 + (2632245737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336246619/2500000000 : ℝ)^4133 ≤ (5435648816333/12500000000000 : ℝ)^3109 := by
    have hnat : (1336246619 : ℕ)^4133*12500000000000^3109 ≤ 5435648816333^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336246619 2500000000 5435648816333 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226619269/1000000000 : ℝ)^4133 ≤ (6949015916881/50000000000000 : ℝ)^3109 := by
    have hnat : (226619269 : ℕ)^4133*50000000000000^3109 ≤ 6949015916881^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226619269 1000000000 6949015916881 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632245737/5000000000 : ℝ)^4133 ≤ (4261677762357/10000000000000 : ℝ)^3109 := by
    have hnat : (2632245737 : ℕ)^4133*10000000000000^3109 ≤ 4261677762357^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632245737 5000000000 4261677762357 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336246619/2500000000 : ℝ), (-226619269/1000000000 : ℝ), (2632245737/5000000000 : ℝ)] ![(5435648816333/12500000000000 : ℝ), (6949015916881/50000000000000 : ℝ), (4261677762357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336246619/2500000000 : ℝ)|^4133 ≤ (5435648816333/12500000000000 : ℝ)^3109
        have hw : |(1336246619/2500000000 : ℝ)|=(1336246619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226619269/1000000000 : ℝ)|^4133 ≤ (6949015916881/50000000000000 : ℝ)^3109
        have hw : |(-226619269/1000000000 : ℝ)|=(226619269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632245737/5000000000 : ℝ)|^4133 ≤ (4261677762357/10000000000000 : ℝ)^3109
        have hw : |(2632245737/5000000000 : ℝ)|=(2632245737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344986527/10000000000 : ℝ)*x 0 + (5264491407/10000000000 : ℝ)*x 1 + (-2266192709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344986527/10000000000 : ℝ)^4133 ≤ (8697038216449/20000000000000 : ℝ)^3109 := by
    have hnat : (5344986527 : ℕ)^4133*20000000000000^3109 ≤ 8697038216449^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344986527 10000000000 8697038216449 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264491407/10000000000 : ℝ)^4133 ≤ (10654194225639/25000000000000 : ℝ)^3109 := by
    have hnat : (5264491407 : ℕ)^4133*25000000000000^3109 ≤ 10654194225639^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264491407 10000000000 10654194225639 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266192709/10000000000 : ℝ)^4133 ≤ (1737253998583/12500000000000 : ℝ)^3109 := by
    have hnat : (2266192709 : ℕ)^4133*12500000000000^3109 ≤ 1737253998583^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266192709 10000000000 1737253998583 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344986527/10000000000 : ℝ), (5264491407/10000000000 : ℝ), (-2266192709/10000000000 : ℝ)] ![(8697038216449/20000000000000 : ℝ), (10654194225639/25000000000000 : ℝ), (1737253998583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344986527/10000000000 : ℝ)|^4133 ≤ (8697038216449/20000000000000 : ℝ)^3109
        have hw : |(5344986527/10000000000 : ℝ)|=(5344986527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264491407/10000000000 : ℝ)|^4133 ≤ (10654194225639/25000000000000 : ℝ)^3109
        have hw : |(5264491407/10000000000 : ℝ)|=(5264491407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266192709/10000000000 : ℝ)|^4133 ≤ (1737253998583/12500000000000 : ℝ)^3109
        have hw : |(-2266192709/10000000000 : ℝ)|=(2266192709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546810227/1250000000 : ℝ)*x 0 + (4248948807/10000000000 : ℝ)*x 1 + (1125941967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546810227/1250000000 : ℝ)^4133 ≤ (16658271186121/50000000000000 : ℝ)^3109 := by
    have hnat : (546810227 : ℕ)^4133*50000000000000^3109 ≤ 16658271186121^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546810227 1250000000 16658271186121 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248948807/10000000000 : ℝ)^4133 ≤ (32051615958271/100000000000000 : ℝ)^3109 := by
    have hnat : (4248948807 : ℕ)^4133*100000000000000^3109 ≤ 32051615958271^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248948807 10000000000 32051615958271 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125941967/2500000000 : ℝ)^4133 ≤ (4328980206681/12500000000000 : ℝ)^3109 := by
    have hnat : (1125941967 : ℕ)^4133*12500000000000^3109 ≤ 4328980206681^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125941967 2500000000 4328980206681 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546810227/1250000000 : ℝ), (4248948807/10000000000 : ℝ), (1125941967/2500000000 : ℝ)] ![(16658271186121/50000000000000 : ℝ), (32051615958271/100000000000000 : ℝ), (4328980206681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546810227/1250000000 : ℝ)|^4133 ≤ (16658271186121/50000000000000 : ℝ)^3109
        have hw : |(546810227/1250000000 : ℝ)|=(546810227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248948807/10000000000 : ℝ)|^4133 ≤ (32051615958271/100000000000000 : ℝ)^3109
        have hw : |(4248948807/10000000000 : ℝ)|=(4248948807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125941967/2500000000 : ℝ)|^4133 ≤ (4328980206681/12500000000000 : ℝ)^3109
        have hw : |(1125941967/2500000000 : ℝ)|=(1125941967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200322319/10000000000 : ℝ)*x 0 + (5264817107/10000000000 : ℝ)*x 1 + (1078800613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200322319/10000000000 : ℝ)^4133 ≤ (133635983487/1000000000000 : ℝ)^3109 := by
    have hnat : (2200322319 : ℕ)^4133*1000000000000^3109 ≤ 133635983487^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200322319 10000000000 133635983487 1000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264817107/10000000000 : ℝ)^4133 ≤ (21310140963481/50000000000000 : ℝ)^3109 := by
    have hnat : (5264817107 : ℕ)^4133*50000000000000^3109 ≤ 21310140963481^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264817107 10000000000 21310140963481 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078800613/2000000000 : ℝ)^4133 ≤ (11004029926803/25000000000000 : ℝ)^3109 := by
    have hnat : (1078800613 : ℕ)^4133*25000000000000^3109 ≤ 11004029926803^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078800613 2000000000 11004029926803 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200322319/10000000000 : ℝ), (5264817107/10000000000 : ℝ), (1078800613/2000000000 : ℝ)] ![(133635983487/1000000000000 : ℝ), (21310140963481/50000000000000 : ℝ), (11004029926803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200322319/10000000000 : ℝ)|^4133 ≤ (133635983487/1000000000000 : ℝ)^3109
        have hw : |(-2200322319/10000000000 : ℝ)|=(2200322319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264817107/10000000000 : ℝ)|^4133 ≤ (21310140963481/50000000000000 : ℝ)^3109
        have hw : |(5264817107/10000000000 : ℝ)|=(5264817107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078800613/2000000000 : ℝ)|^4133 ≤ (11004029926803/25000000000000 : ℝ)^3109
        have hw : |(1078800613/2000000000 : ℝ)|=(1078800613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312264553/10000000000 : ℝ)*x 0 + (-2136681057/10000000000 : ℝ)*x 1 + (539400307/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312264553/10000000000 : ℝ)^4133 ≤ (10782912421427/25000000000000 : ℝ)^3109 := by
    have hnat : (5312264553 : ℕ)^4133*25000000000000^3109 ≤ 10782912421427^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312264553 10000000000 10782912421427 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136681057/10000000000 : ℝ)^4133 ≤ (6426115270473/50000000000000 : ℝ)^3109 := by
    have hnat : (2136681057 : ℕ)^4133*50000000000000^3109 ≤ 6426115270473^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136681057 10000000000 6426115270473 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539400307/1000000000 : ℝ)^4133 ≤ (11004029940363/25000000000000 : ℝ)^3109 := by
    have hnat : (539400307 : ℕ)^4133*25000000000000^3109 ≤ 11004029940363^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539400307 1000000000 11004029940363 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312264553/10000000000 : ℝ), (-2136681057/10000000000 : ℝ), (539400307/1000000000 : ℝ)] ![(10782912421427/25000000000000 : ℝ), (6426115270473/50000000000000 : ℝ), (11004029940363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312264553/10000000000 : ℝ)|^4133 ≤ (10782912421427/25000000000000 : ℝ)^3109
        have hw : |(5312264553/10000000000 : ℝ)|=(5312264553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136681057/10000000000 : ℝ)|^4133 ≤ (6426115270473/50000000000000 : ℝ)^3109
        have hw : |(-2136681057/10000000000 : ℝ)|=(2136681057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539400307/1000000000 : ℝ)|^4133 ≤ (11004029940363/25000000000000 : ℝ)^3109
        have hw : |(539400307/1000000000 : ℝ)|=(539400307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656132277/5000000000 : ℝ)*x 0 + (2697001533/5000000000 : ℝ)*x 1 + (-2136681061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656132277/5000000000 : ℝ)^4133 ≤ (43131649696501/100000000000000 : ℝ)^3109 := by
    have hnat : (2656132277 : ℕ)^4133*100000000000000^3109 ≤ 43131649696501^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656132277 5000000000 43131649696501 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697001533/5000000000 : ℝ)^4133 ≤ (2200805985903/5000000000000 : ℝ)^3109 := by
    have hnat : (2697001533 : ℕ)^4133*5000000000000^3109 ≤ 2200805985903^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697001533 5000000000 2200805985903 5000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136681061/10000000000 : ℝ)^4133 ≤ (1285223057293/10000000000000 : ℝ)^3109 := by
    have hnat : (2136681061 : ℕ)^4133*10000000000000^3109 ≤ 1285223057293^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136681061 10000000000 1285223057293 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656132277/5000000000 : ℝ), (2697001533/5000000000 : ℝ), (-2136681061/10000000000 : ℝ)] ![(43131649696501/100000000000000 : ℝ), (2200805985903/5000000000000 : ℝ), (1285223057293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656132277/5000000000 : ℝ)|^4133 ≤ (43131649696501/100000000000000 : ℝ)^3109
        have hw : |(2656132277/5000000000 : ℝ)|=(2656132277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697001533/5000000000 : ℝ)|^4133 ≤ (2200805985903/5000000000000 : ℝ)^3109
        have hw : |(2697001533/5000000000 : ℝ)|=(2697001533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136681061/10000000000 : ℝ)|^4133 ≤ (1285223057293/10000000000000 : ℝ)^3109
        have hw : |(-2136681061/10000000000 : ℝ)|=(2136681061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s7_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (109362293/250000000 : ℝ)*x 0 + (281445541/625000000 : ℝ)*x 1 + (4249590369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109362293/250000000 : ℝ)^4133 ≤ (6663328529269/20000000000000 : ℝ)^3109 := by
    have hnat : (109362293 : ℕ)^4133*20000000000000^3109 ≤ 6663328529269^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109362293 250000000 6663328529269 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281445541/625000000 : ℝ)^4133 ≤ (34625307654799/100000000000000 : ℝ)^3109 := by
    have hnat : (281445541 : ℕ)^4133*100000000000000^3109 ≤ 34625307654799^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281445541 625000000 34625307654799 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249590369/10000000000 : ℝ)^4133 ≤ (32058049684051/100000000000000 : ℝ)^3109 := by
    have hnat : (4249590369 : ℕ)^4133*100000000000000^3109 ≤ 32058049684051^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249590369 10000000000 32058049684051 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109362293/250000000 : ℝ), (281445541/625000000 : ℝ), (4249590369/10000000000 : ℝ)] ![(6663328529269/20000000000000 : ℝ), (34625307654799/100000000000000 : ℝ), (32058049684051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109362293/250000000 : ℝ)|^4133 ≤ (6663328529269/20000000000000 : ℝ)^3109
        have hw : |(109362293/250000000 : ℝ)|=(109362293/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281445541/625000000 : ℝ)|^4133 ≤ (34625307654799/100000000000000 : ℝ)^3109
        have hw : |(281445541/625000000 : ℝ)|=(281445541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249590369/10000000000 : ℝ)|^4133 ≤ (32058049684051/100000000000000 : ℝ)^3109
        have hw : |(4249590369/10000000000 : ℝ)|=(4249590369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    (11259/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/80 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/80 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/80 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/80 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/80 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/80 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9/80 : ℝ) ^ (8265/2048 : ℝ) ≤ (592719011591193/4000000000000000000 : ℝ) := by
    have hpowers : (9/80 : ℝ)^8265 ≤ (592719011591193/4000000000000000000 : ℝ)^2048 := by
      have hnat : (9 : ℕ)^8265*4000000000000000000^2048 ≤ 592719011591193^2048*80^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 80 592719011591193 4000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/80 : ℝ)) (X := (592719011591193/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14019/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (36012500033410633/100000000000000000000 : ℝ) := by
    have hpowers : (14019/100000 : ℝ)^8265 ≤ (36012500033410633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14019 : ℕ)^8265*100000000000000000000^2048 ≤ 36012500033410633^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14019 100000 36012500033410633 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14019/100000 : ℝ)) (X := (36012500033410633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000592719011591193/2000000000000000000 : ℝ) ≤ (10000734272992557/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (2000592719011591193/2000000000000000000 : ℝ)^2048 ≤ (10000734272992557/10000000000000000 : ℝ)^8265 := by
      have hnat : (2000592719011591193 : ℕ)^2048*10000000000000000^8265 ≤ 10000734272992557^8265*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000592719011591193 2000000000000000000 10000734272992557 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734272992557/10000000000000000 : ℝ)) (X := (2000592719011591193/2000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025415237661595229/50000000000000000000 : ℝ) ≤ (1000125929725161/1000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50025415237661595229/50000000000000000000 : ℝ)^2048 ≤ (1000125929725161/1000000000000000 : ℝ)^8265 := by
      have hnat : (50025415237661595229 : ℕ)^2048*1000000000000000^8265 ≤ 1000125929725161^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025415237661595229 50000000000000000000 1000125929725161 1000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000125929725161/1000000000000000 : ℝ)) (X := (50025415237661595229/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036012500033410633/50000000000000000000 : ℝ) ≤ (10001784321510663/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50036012500033410633/50000000000000000000 : ℝ)^2048 ≤ (10001784321510663/10000000000000000 : ℝ)^8265 := by
      have hnat : (50036012500033410633 : ℕ)^2048*10000000000000000^8265 ≤ 10001784321510663^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036012500033410633 50000000000000000000 10001784321510663 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001784321510663/10000000000000000 : ℝ)) (X := (50036012500033410633/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(592719011591193/4000000000000000000 : ℝ) ≤ ((9226740052029232611/9230000000000000000 : ℝ)+2*(175008086351/92300000000000 : ℝ)*(9/80 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (9226740052029232611/9230000000000000000 : ℝ)+2*(175008086351/92300000000000 : ℝ)*(9/80 : ℝ)=(10000734272992557/10000000000000000 : ℝ) by norm_num, show 1+2*(592719011591193/4000000000000000000 : ℝ)=(2000592719011591193/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36012500033410633/100000000000000000000 : ℝ)+(592719011591193/4000000000000000000 : ℝ) ≤ ((9226740052029232611/9230000000000000000 : ℝ)+(175008086351/92300000000000 : ℝ)*((14019/100000 : ℝ)+(9/80 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (9226740052029232611/9230000000000000000 : ℝ)+(175008086351/92300000000000 : ℝ)*((14019/100000 : ℝ)+(9/80 : ℝ))=(1000125929725161/1000000000000000 : ℝ) by norm_num, show 1+(36012500033410633/100000000000000000000 : ℝ)+(592719011591193/4000000000000000000 : ℝ)=(50025415237661595229/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36012500033410633/100000000000000000000 : ℝ) ≤ ((9226740052029232611/9230000000000000000 : ℝ)+2*(175008086351/92300000000000 : ℝ)*(14019/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (9226740052029232611/9230000000000000000 : ℝ)+2*(175008086351/92300000000000 : ℝ)*(14019/100000 : ℝ)=(10001784321510663/10000000000000000 : ℝ) by norm_num, show 1+2*(36012500033410633/100000000000000000000 : ℝ)=(50036012500033410633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9226740052029232611/9230000000000000000 : ℝ)*(X 1 0+X 2 0)+(175008086351/92300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (9226740052029232611/9230000000000000000 : ℝ)) (alpha := (175008086351/92300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9226740052029232611/9230000000000000000 : ℝ)*(X 0 1+X 2 1)+(175008086351/92300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (9226740052029232611/9230000000000000000 : ℝ)) (alpha := (175008086351/92300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9226740052029232611/9230000000000000000 : ℝ)*(X 0 2+X 1 2)+(175008086351/92300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (9/80 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (9226740052029232611/9230000000000000000 : ℝ)) (alpha := (175008086351/92300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200317309/10000000000 : ℝ)*X 0 0+(2697164963/5000000000 : ℝ)*X 0 1+(2632245689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336246619/2500000000 : ℝ)*X 1 0+(-226619269/1000000000 : ℝ)*X 1 1+(2632245737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344986527/10000000000 : ℝ)*X 2 0+(5264491407/10000000000 : ℝ)*X 2 1+(-2266192709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546810227/1250000000 : ℝ)*X 0 0+(4248948807/10000000000 : ℝ)*X 0 1+(1125941967/2500000000 : ℝ)*X 0 2+(546810227/1250000000 : ℝ)*X 1 0+(4248948807/10000000000 : ℝ)*X 1 1+(1125941967/2500000000 : ℝ)*X 1 2+(546810227/1250000000 : ℝ)*X 2 0+(4248948807/10000000000 : ℝ)*X 2 1+(1125941967/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2200322319/10000000000 : ℝ)*X 0 0+(5264817107/10000000000 : ℝ)*X 0 1+(1078800613/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312264553/10000000000 : ℝ)*X 1 0+(-2136681057/10000000000 : ℝ)*X 1 1+(539400307/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656132277/5000000000 : ℝ)*X 2 0+(2697001533/5000000000 : ℝ)*X 2 1+(-2136681061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((109362293/250000000 : ℝ)*X 0 0+(281445541/625000000 : ℝ)*X 0 1+(4249590369/10000000000 : ℝ)*X 0 2+(109362293/250000000 : ℝ)*X 1 0+(281445541/625000000 : ℝ)*X 1 1+(4249590369/10000000000 : ℝ)*X 1 2+(109362293/250000000 : ℝ)*X 2 0+(281445541/625000000 : ℝ)*X 2 1+(4249590369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3570797725822945181993390679/461500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1614782963/100000000000000 : ℝ)*(base19) + (1609178391/100000000000000 : ℝ)*(base23) + (10568917/25000000000000 : ℝ)*(lower2) + (14238739/6250000000000 : ℝ)*(upper3) + (75875313/50000000000000 : ℝ)*(upper5) + (5813184965072821/100000000000000 : ℝ)*(major0) + (5813184965072821/100000000000000 : ℝ)*(major1) + (5813184965072821/100000000000000 : ℝ)*(major2) + (1540384309853743/20000000000000 : ℝ)*(sp0) + (3850983548162023/50000000000000 : ℝ)*(sp1) + (3850983550964309/50000000000000 : ℝ)*(sp2) + (981093960469081/25000000000000 : ℝ)*(sp3) + (23580919147/50000000000000 : ℝ)*(sp4) + (12559624929/50000000000000 : ℝ)*(sp7) + (1962200480563091/50000000000000 : ℝ)*(f.failure) + (120343261111047/1562500000000 : ℝ)*(f.sum) + (381725247013/2307500000000000000000000000 : ℝ)*base65 + (17330658394491934369/923000000000000000000000000000000 : ℝ)*base68 + (10359930121541934369/923000000000000000000000000000000 : ℝ)*base70 + (4589811151939934369/923000000000000000000000000000000 : ℝ)*base72 + (34039760472069/4615000000000000000000000000 : ℝ)*base74 + (15635035191893934369/923000000000000000000000000000000 : ℝ)*base76 + (8043795102109934369/923000000000000000000000000000000 : ℝ)*base78 + (9973817649185934369/923000000000000000000000000000000 : ℝ)*base80 + (9136648655109/4615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (66813021/5000000000000000000000 : ℝ)*base89 + (66813021/5000000000000000000000 : ℝ)*base91 + (66813021/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68820749566605689126840097/23075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21947257/4000000000000 : ℝ)*(base19) + (619207583/100000000000000 : ℝ)*(base23) + (23212471/50000000000000 : ℝ)*(upper3) + (7101769/20000000000000 : ℝ)*(lower4) + (9874747/12500000000000 : ℝ)*(upper5) + (292123914115403/5000000000000 : ℝ)*(major0) + (292123914115403/5000000000000 : ℝ)*(major1) + (292123914115403/5000000000000 : ℝ)*(major2) + (3245546351/20000000000000 : ℝ)*(sp1) + (829453303/5000000000000 : ℝ)*(sp2) + (967597498723733/12500000000000 : ℝ)*(sp4) + (1935190803344171/25000000000000 : ℝ)*(sp5) + (7740762781516221/100000000000000 : ℝ)*(sp6) + (1972088237705109/50000000000000 : ℝ)*(sp7) + (1972088237705109/50000000000000 : ℝ)*(f.failure) + (967597498723733/12500000000000 : ℝ)*(f.sum) + (7409142803/9230000000000000000000000 : ℝ)*base65 + (3034217114092767/46150000000000000000000000000000 : ℝ)*base68 + (176831108801992767/46150000000000000000000000000000 : ℝ)*base70 + (259693387190492767/46150000000000000000000000000000 : ℝ)*base72 + (319781054899/461500000000000000000000000 : ℝ)*base74 + (176694670480492767/46150000000000000000000000000000 : ℝ)*base76 + (394759504065792767/46150000000000000000000000000000 : ℝ)*base78 + (737081190265792767/46150000000000000000000000000000 : ℝ)*base80 + (2491219771/923000000000000000000000000 : ℝ)*base82 + (941179/5000000000000000000000 : ℝ)*base89 + (941179/5000000000000000000000 : ℝ)*base91 + (941179/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s8_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200328013/10000000000 : ℝ)*x 0 + (107884557/200000000 : ℝ)*x 1 + (1052917249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200328013/10000000000 : ℝ)^4133 ≤ (668182216067/5000000000000 : ℝ)^3109 := by
    have hnat : (2200328013 : ℕ)^4133*5000000000000^3109 ≤ 668182216067^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200328013 10000000000 668182216067 5000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107884557/200000000 : ℝ)^4133 ≤ (11004639541691/25000000000000 : ℝ)^3109 := by
    have hnat : (107884557 : ℕ)^4133*25000000000000^3109 ≤ 11004639541691^3109*200000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107884557 200000000 11004639541691 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052917249/2000000000 : ℝ)^4133 ≤ (8523559499089/20000000000000 : ℝ)^3109 := by
    have hnat : (1052917249 : ℕ)^4133*20000000000000^3109 ≤ 8523559499089^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052917249 2000000000 8523559499089 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200328013/10000000000 : ℝ), (107884557/200000000 : ℝ), (1052917249/2000000000 : ℝ)] ![(668182216067/5000000000000 : ℝ), (11004639541691/25000000000000 : ℝ), (8523559499089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200328013/10000000000 : ℝ)|^4133 ≤ (668182216067/5000000000000 : ℝ)^3109
        have hw : |(-2200328013/10000000000 : ℝ)|=(2200328013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107884557/200000000 : ℝ)|^4133 ≤ (11004639541691/25000000000000 : ℝ)^3109
        have hw : |(107884557/200000000 : ℝ)|=(107884557/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052917249/2000000000 : ℝ)|^4133 ≤ (8523559499089/20000000000000 : ℝ)^3109
        have hw : |(1052917249/2000000000 : ℝ)|=(1052917249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344960451/10000000000 : ℝ)*x 0 + (-1133051059/5000000000 : ℝ)*x 1 + (1052917249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344960451/10000000000 : ℝ)^4133 ≤ (43484909062137/100000000000000 : ℝ)^3109 := by
    have hnat : (5344960451 : ℕ)^4133*100000000000000^3109 ≤ 43484909062137^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344960451 10000000000 43484909062137 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133051059/5000000000 : ℝ)^4133 ≤ (6948646716403/50000000000000 : ℝ)^3109 := by
    have hnat : (1133051059 : ℕ)^4133*50000000000000^3109 ≤ 6948646716403^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133051059 5000000000 6948646716403 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052917249/2000000000 : ℝ)^4133 ≤ (8523559499089/20000000000000 : ℝ)^3109 := by
    have hnat : (1052917249 : ℕ)^4133*20000000000000^3109 ≤ 8523559499089^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052917249 2000000000 8523559499089 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344960451/10000000000 : ℝ), (-1133051059/5000000000 : ℝ), (1052917249/2000000000 : ℝ)] ![(43484909062137/100000000000000 : ℝ), (6948646716403/50000000000000 : ℝ), (8523559499089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344960451/10000000000 : ℝ)|^4133 ≤ (43484909062137/100000000000000 : ℝ)^3109
        have hw : |(5344960451/10000000000 : ℝ)|=(5344960451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133051059/5000000000 : ℝ)|^4133 ≤ (6948646716403/50000000000000 : ℝ)^3109
        have hw : |(-1133051059/5000000000 : ℝ)|=(1133051059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052917249/2000000000 : ℝ)|^4133 ≤ (8523559499089/20000000000000 : ℝ)^3109
        have hw : |(1052917249/2000000000 : ℝ)|=(1052917249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344960451/10000000000 : ℝ)*x 0 + (1316146561/2500000000 : ℝ)*x 1 + (-1133051059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344960451/10000000000 : ℝ)^4133 ≤ (43484909062137/100000000000000 : ℝ)^3109 := by
    have hnat : (5344960451 : ℕ)^4133*100000000000000^3109 ≤ 43484909062137^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344960451 10000000000 43484909062137 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316146561/2500000000 : ℝ)^4133 ≤ (10654449371171/25000000000000 : ℝ)^3109 := by
    have hnat : (1316146561 : ℕ)^4133*25000000000000^3109 ≤ 10654449371171^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316146561 2500000000 10654449371171 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133051059/5000000000 : ℝ)^4133 ≤ (6948646716403/50000000000000 : ℝ)^3109 := by
    have hnat : (1133051059 : ℕ)^4133*50000000000000^3109 ≤ 6948646716403^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133051059 5000000000 6948646716403 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344960451/10000000000 : ℝ), (1316146561/2500000000 : ℝ), (-1133051059/5000000000 : ℝ)] ![(43484909062137/100000000000000 : ℝ), (10654449371171/25000000000000 : ℝ), (6948646716403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344960451/10000000000 : ℝ)|^4133 ≤ (43484909062137/100000000000000 : ℝ)^3109
        have hw : |(5344960451/10000000000 : ℝ)|=(5344960451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316146561/2500000000 : ℝ)|^4133 ≤ (10654449371171/25000000000000 : ℝ)^3109
        have hw : |(1316146561/2500000000 : ℝ)|=(1316146561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133051059/5000000000 : ℝ)|^4133 ≤ (6948646716403/50000000000000 : ℝ)^3109
        have hw : |(-1133051059/5000000000 : ℝ)|=(1133051059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174979471/400000000 : ℝ)*x 0 + (4249141399/10000000000 : ℝ)*x 1 + (4503574021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174979471/400000000 : ℝ)^4133 ≤ (8329148145039/25000000000000 : ℝ)^3109 := by
    have hnat : (174979471 : ℕ)^4133*25000000000000^3109 ≤ 8329148145039^3109*400000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174979471 400000000 8329148145039 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249141399/10000000000 : ℝ)^4133 ≤ (32053547279881/100000000000000 : ℝ)^3109 := by
    have hnat : (4249141399 : ℕ)^4133*100000000000000^3109 ≤ 32053547279881^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249141399 10000000000 32053547279881 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503574021/10000000000 : ℝ)^4133 ≤ (17314930062577/50000000000000 : ℝ)^3109 := by
    have hnat : (4503574021 : ℕ)^4133*50000000000000^3109 ≤ 17314930062577^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503574021 10000000000 17314930062577 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174979471/400000000 : ℝ), (4249141399/10000000000 : ℝ), (4503574021/10000000000 : ℝ)] ![(8329148145039/25000000000000 : ℝ), (32053547279881/100000000000000 : ℝ), (17314930062577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174979471/400000000 : ℝ)|^4133 ≤ (8329148145039/25000000000000 : ℝ)^3109
        have hw : |(174979471/400000000 : ℝ)|=(174979471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249141399/10000000000 : ℝ)|^4133 ≤ (32053547279881/100000000000000 : ℝ)^3109
        have hw : |(4249141399/10000000000 : ℝ)|=(4249141399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503574021/10000000000 : ℝ)|^4133 ≤ (17314930062577/50000000000000 : ℝ)^3109
        have hw : |(4503574021/10000000000 : ℝ)|=(4503574021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22003331/100000000 : ℝ)*x 0 + (5264910841/10000000000 : ℝ)*x 1 + (1348475513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22003331/100000000 : ℝ)^4133 ≤ (13363685393171/100000000000000 : ℝ)^3109 := by
    have hnat : (22003331 : ℕ)^4133*100000000000000^3109 ≤ 13363685393171^3109*100000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22003331 100000000 13363685393171 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264910841/10000000000 : ℝ)^4133 ≤ (10655322664937/25000000000000 : ℝ)^3109 := by
    have hnat : (5264910841 : ℕ)^4133*25000000000000^3109 ≤ 10655322664937^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264910841 10000000000 10655322664937 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348475513/2500000000 : ℝ)^4133 ≤ (2200751196637/5000000000000 : ℝ)^3109 := by
    have hnat : (1348475513 : ℕ)^4133*5000000000000^3109 ≤ 2200751196637^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348475513 2500000000 2200751196637 5000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22003331/100000000 : ℝ), (5264910841/10000000000 : ℝ), (1348475513/2500000000 : ℝ)] ![(13363685393171/100000000000000 : ℝ), (10655322664937/25000000000000 : ℝ), (2200751196637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22003331/100000000 : ℝ)|^4133 ≤ (13363685393171/100000000000000 : ℝ)^3109
        have hw : |(-22003331/100000000 : ℝ)|=(22003331/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264910841/10000000000 : ℝ)|^4133 ≤ (10655322664937/25000000000000 : ℝ)^3109
        have hw : |(5264910841/10000000000 : ℝ)|=(5264910841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348475513/2500000000 : ℝ)|^4133 ≤ (2200751196637/5000000000000 : ℝ)^3109
        have hw : |(1348475513/2500000000 : ℝ)|=(1348475513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312288541/10000000000 : ℝ)*x 0 + (-1068392703/5000000000 : ℝ)*x 1 + (5393902283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312288541/10000000000 : ℝ)^4133 ≤ (1078297714991/2500000000000 : ℝ)^3109 := by
    have hnat : (5312288541 : ℕ)^4133*2500000000000^3109 ≤ 1078297714991^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312288541 10000000000 1078297714991 2500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068392703/5000000000 : ℝ)^4133 ≤ (3213266235707/25000000000000 : ℝ)^3109 := by
    have hnat : (1068392703 : ℕ)^4133*25000000000000^3109 ≤ 3213266235707^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068392703 5000000000 3213266235707 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393902283/10000000000 : ℝ)^4133 ≤ (44015026438587/100000000000000 : ℝ)^3109 := by
    have hnat : (5393902283 : ℕ)^4133*100000000000000^3109 ≤ 44015026438587^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393902283 10000000000 44015026438587 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312288541/10000000000 : ℝ), (-1068392703/5000000000 : ℝ), (5393902283/10000000000 : ℝ)] ![(1078297714991/2500000000000 : ℝ), (3213266235707/25000000000000 : ℝ), (44015026438587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312288541/10000000000 : ℝ)|^4133 ≤ (1078297714991/2500000000000 : ℝ)^3109
        have hw : |(5312288541/10000000000 : ℝ)|=(5312288541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068392703/5000000000 : ℝ)|^4133 ≤ (3213266235707/25000000000000 : ℝ)^3109
        have hw : |(-1068392703/5000000000 : ℝ)|=(1068392703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393902283/10000000000 : ℝ)|^4133 ≤ (44015026438587/100000000000000 : ℝ)^3109
        have hw : |(5393902283/10000000000 : ℝ)|=(5393902283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656143593/5000000000 : ℝ)*x 0 + (5393902199/10000000000 : ℝ)*x 1 + (-2136787349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656143593/5000000000 : ℝ)^4133 ≤ (10782973493617/25000000000000 : ℝ)^3109 := by
    have hnat : (2656143593 : ℕ)^4133*25000000000000^3109 ≤ 10782973493617^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656143593 5000000000 10782973493617 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393902199/10000000000 : ℝ)^4133 ≤ (4401502552737/10000000000000 : ℝ)^3109 := by
    have hnat : (5393902199 : ℕ)^4133*10000000000000^3109 ≤ 4401502552737^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393902199 10000000000 4401502552737 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136787349/10000000000 : ℝ)^4133 ≤ (12853080479691/100000000000000 : ℝ)^3109 := by
    have hnat : (2136787349 : ℕ)^4133*100000000000000^3109 ≤ 12853080479691^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136787349 10000000000 12853080479691 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656143593/5000000000 : ℝ), (5393902199/10000000000 : ℝ), (-2136787349/10000000000 : ℝ)] ![(10782973493617/25000000000000 : ℝ), (4401502552737/10000000000000 : ℝ), (12853080479691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656143593/5000000000 : ℝ)|^4133 ≤ (10782973493617/25000000000000 : ℝ)^3109
        have hw : |(2656143593/5000000000 : ℝ)|=(2656143593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393902199/10000000000 : ℝ)|^4133 ≤ (4401502552737/10000000000000 : ℝ)^3109
        have hw : |(5393902199/10000000000 : ℝ)|=(5393902199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136787349/10000000000 : ℝ)|^4133 ≤ (12853080479691/100000000000000 : ℝ)^3109
        have hw : |(-2136787349/10000000000 : ℝ)|=(2136787349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s8_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273405977/625000000 : ℝ)*x 0 + (900587349/2000000000 : ℝ)*x 1 + (169991281/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273405977/625000000 : ℝ)^4133 ≤ (16658341126913/50000000000000 : ℝ)^3109 := by
    have hnat : (273405977 : ℕ)^4133*50000000000000^3109 ≤ 16658341126913^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273405977 625000000 16658341126913 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900587349/2000000000 : ℝ)^4133 ≤ (34623346008111/100000000000000 : ℝ)^3109 := by
    have hnat : (900587349 : ℕ)^4133*100000000000000^3109 ≤ 34623346008111^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900587349 2000000000 34623346008111 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169991281/400000000 : ℝ)^4133 ≤ (16029985857457/50000000000000 : ℝ)^3109 := by
    have hnat : (169991281 : ℕ)^4133*50000000000000^3109 ≤ 16029985857457^3109*400000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169991281 400000000 16029985857457 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273405977/625000000 : ℝ), (900587349/2000000000 : ℝ), (169991281/400000000 : ℝ)] ![(16658341126913/50000000000000 : ℝ), (34623346008111/100000000000000 : ℝ), (16029985857457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273405977/625000000 : ℝ)|^4133 ≤ (16658341126913/50000000000000 : ℝ)^3109
        have hw : |(273405977/625000000 : ℝ)|=(273405977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900587349/2000000000 : ℝ)|^4133 ≤ (34623346008111/100000000000000 : ℝ)^3109
        have hw : |(900587349/2000000000 : ℝ)|=(900587349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169991281/400000000 : ℝ)|^4133 ≤ (16029985857457/50000000000000 : ℝ)^3109
        have hw : |(169991281/400000000 : ℝ)|=(169991281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11261/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (11259/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (14865873476246237/100000000000000000000 : ℝ) := by
    have hpowers : (11259/100000 : ℝ)^8265 ≤ (14865873476246237/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11259 : ℕ)^8265*100000000000000000000^2048 ≤ 14865873476246237^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11259 100000 14865873476246237 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11259/100000 : ℝ)) (X := (14865873476246237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (35908943165044131/100000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^8265 ≤ (35908943165044131/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14009 : ℕ)^8265*100000000000000000000^2048 ≤ 35908943165044131^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 35908943165044131 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (35908943165044131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014865873476246237/50000000000000000000 : ℝ) ≤ (10000736646219137/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50014865873476246237/50000000000000000000 : ℝ)^2048 ≤ (10000736646219137/10000000000000000 : ℝ)^8265 := by
      have hnat : (50014865873476246237 : ℕ)^2048*10000000000000000^8265 ≤ 10000736646219137^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014865873476246237 50000000000000000000 10000736646219137 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000736646219137/10000000000000000 : ℝ)) (X := (50014865873476246237/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (781646678255010081/781250000000000000 : ℝ) ≤ (10001257918601399/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (781646678255010081/781250000000000000 : ℝ)^2048 ≤ (10001257918601399/10000000000000000 : ℝ)^8265 := by
      have hnat : (781646678255010081 : ℕ)^2048*10000000000000000^8265 ≤ 10001257918601399^8265*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781646678255010081 781250000000000000 10001257918601399 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001257918601399/10000000000000000 : ℝ)) (X := (781646678255010081/781250000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035908943165044131/50000000000000000000 : ℝ) ≤ (10001779190983661/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50035908943165044131/50000000000000000000 : ℝ)^2048 ≤ (10001779190983661/10000000000000000 : ℝ)^8265 := by
      have hnat : (50035908943165044131 : ℕ)^2048*10000000000000000^8265 ≤ 10001779190983661^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035908943165044131 50000000000000000000 10001779190983661 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001779190983661/10000000000000000 : ℝ)) (X := (50035908943165044131/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14865873476246237/100000000000000000000 : ℝ) ≤ ((13745143882799425517/13750000000000000000 : ℝ)+2*(260636191131/137500000000000 : ℝ)*(11259/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (13745143882799425517/13750000000000000000 : ℝ)+2*(260636191131/137500000000000 : ℝ)*(11259/100000 : ℝ)=(10000736646219137/10000000000000000 : ℝ) by norm_num, show 1+2*(14865873476246237/100000000000000000000 : ℝ)=(50014865873476246237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35908943165044131/100000000000000000000 : ℝ)+(14865873476246237/100000000000000000000 : ℝ) ≤ ((13745143882799425517/13750000000000000000 : ℝ)+(260636191131/137500000000000 : ℝ)*((14009/100000 : ℝ)+(11259/100000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (13745143882799425517/13750000000000000000 : ℝ)+(260636191131/137500000000000 : ℝ)*((14009/100000 : ℝ)+(11259/100000 : ℝ))=(10001257918601399/10000000000000000 : ℝ) by norm_num, show 1+(35908943165044131/100000000000000000000 : ℝ)+(14865873476246237/100000000000000000000 : ℝ)=(781646678255010081/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35908943165044131/100000000000000000000 : ℝ) ≤ ((13745143882799425517/13750000000000000000 : ℝ)+2*(260636191131/137500000000000 : ℝ)*(14009/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (13745143882799425517/13750000000000000000 : ℝ)+2*(260636191131/137500000000000 : ℝ)*(14009/100000 : ℝ)=(10001779190983661/10000000000000000 : ℝ) by norm_num, show 1+2*(35908943165044131/100000000000000000000 : ℝ)=(50035908943165044131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13745143882799425517/13750000000000000000 : ℝ)*(X 1 0+X 2 0)+(260636191131/137500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13745143882799425517/13750000000000000000 : ℝ)) (alpha := (260636191131/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13745143882799425517/13750000000000000000 : ℝ)*(X 0 1+X 2 1)+(260636191131/137500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13745143882799425517/13750000000000000000 : ℝ)) (alpha := (260636191131/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13745143882799425517/13750000000000000000 : ℝ)*(X 0 2+X 1 2)+(260636191131/137500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (13745143882799425517/13750000000000000000 : ℝ)) (alpha := (260636191131/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200328013/10000000000 : ℝ)*X 0 0+(107884557/200000000 : ℝ)*X 0 1+(1052917249/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344960451/10000000000 : ℝ)*X 1 0+(-1133051059/5000000000 : ℝ)*X 1 1+(1052917249/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344960451/10000000000 : ℝ)*X 2 0+(1316146561/2500000000 : ℝ)*X 2 1+(-1133051059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174979471/400000000 : ℝ)*X 0 0+(4249141399/10000000000 : ℝ)*X 0 1+(4503574021/10000000000 : ℝ)*X 0 2+(174979471/400000000 : ℝ)*X 1 0+(4249141399/10000000000 : ℝ)*X 1 1+(4503574021/10000000000 : ℝ)*X 1 2+(174979471/400000000 : ℝ)*X 2 0+(4249141399/10000000000 : ℝ)*X 2 1+(4503574021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22003331/100000000 : ℝ)*X 0 0+(5264910841/10000000000 : ℝ)*X 0 1+(1348475513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312288541/10000000000 : ℝ)*X 1 0+(-1068392703/5000000000 : ℝ)*X 1 1+(5393902283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656143593/5000000000 : ℝ)*X 2 0+(5393902199/10000000000 : ℝ)*X 2 1+(-2136787349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273405977/625000000 : ℝ)*X 0 0+(900587349/2000000000 : ℝ)*X 0 1+(169991281/400000000 : ℝ)*X 0 2+(273405977/625000000 : ℝ)*X 1 0+(900587349/2000000000 : ℝ)*X 1 1+(169991281/400000000 : ℝ)*X 1 2+(273405977/625000000 : ℝ)*X 2 0+(900587349/2000000000 : ℝ)*X 2 1+(169991281/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7064111933413062314031/859375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1648790649/100000000000000 : ℝ)*(base19) + (767395021/50000000000000 : ℝ)*(base23) + (15233219/25000000000000 : ℝ)*(lower2) + (20908639/10000000000000 : ℝ)*(upper3) + (123346441/100000000000000 : ℝ)*(upper5) + (727751495563989/12500000000000 : ℝ)*(major0) + (727751495563989/12500000000000 : ℝ)*(major1) + (727751495563989/12500000000000 : ℝ)*(major2) + (1542723899997903/20000000000000 : ℝ)*(sp0) + (7713662059576353/100000000000000 : ℝ)*(sp1) + (7713662173576961/100000000000000 : ℝ)*(sp2) + (982583886386673/25000000000000 : ℝ)*(sp3) + (44208377487/100000000000000 : ℝ)*(sp4) + (24401108207/100000000000000 : ℝ)*(sp7) + (3930359946654899/100000000000000 : ℝ)*(f.failure) + (3856831854183501/50000000000000 : ℝ)*(f.sum) + (19864600509403/6875000000000000000000000000 : ℝ)*base66 + (696048634393807313/171875000000000000000000000000000 : ℝ)*base67 + (852902693362557313/171875000000000000000000000000000 : ℝ)*base69 + (869486436809317687/171875000000000000000000000000000 : ℝ)*base72 + (23933953846903/6875000000000000000000000000 : ℝ)*base74 + (435805741731192687/171875000000000000000000000000000 : ℝ)*base76 + (2370365183690682313/171875000000000000000000000000000 : ℝ)*base77 + (731939597434317687/171875000000000000000000000000000 : ℝ)*base80 + (25268471371903/6875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11252669/10000000000000000000000 : ℝ)*base89 + (11252669/10000000000000000000000 : ℝ)*base91 + (11252669/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47325551913333016385739/6875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13136689/25000000000000 : ℝ)*(base8) + (68567223/25000000000000 : ℝ)*(upper1) + (425648359/50000000000000 : ℝ)*(upper2) + (416413121/100000000000000 : ℝ)*(lower4) + (20080219/100000000000000 : ℝ)*(lower5) + (5851311382452141/100000000000000 : ℝ)*(major0) + (5851311382452141/100000000000000 : ℝ)*(major1) + (5851311382452141/100000000000000 : ℝ)*(major2) + (29244592969/100000000000000 : ℝ)*(sp0) + (66493938543/100000000000000 : ℝ)*(sp1) + (969056707358329/12500000000000 : ℝ)*(sp4) + (3876208231033907/50000000000000 : ℝ)*(sp5) + (7752482956006357/100000000000000 : ℝ)*(sp6) + (3950139579440699/100000000000000 : ℝ)*(sp7) + (3950139579440699/100000000000000 : ℝ)*(f.failure) + (7752482956006357/100000000000000 : ℝ)*(f.sum) + (54509599632077/3437500000000000000000000000 : ℝ)*base66 + (998717495181218103/1375000000000000000000000000000000 : ℝ)*base68 + (5833969382306218103/1375000000000000000000000000000000 : ℝ)*base70 + (2715047342568781897/1375000000000000000000000000000000 : ℝ)*base71 + (3876983774113/859375000000000000000000000 : ℝ)*base74 + (1552090441693781897/1375000000000000000000000000000000 : ℝ)*base75 + (9644771468056218103/1375000000000000000000000000000000 : ℝ)*base78 + (2581322043443781897/1375000000000000000000000000000000 : ℝ)*base79 + (23305761777279/6875000000000000000000000000 : ℝ)*base82 + (52972469/10000000000000000000000 : ℝ)*base89 + (52972469/10000000000000000000000 : ℝ)*base91 + (52972469/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1073_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1073_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1073_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1073_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:29.570985+00:00
-- url     : https://prove2.me/submissions/3846fc69-d3b8-4eb8-a3e0-fadc369c649b

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
theorem support_rectangle_w1072_s3_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137260001/625000000 : ℝ)*x 0 + (5436835877/10000000000 : ℝ)*x 1 + (5225024479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137260001/625000000 : ℝ)^8265 ≤ (13328932455859/100000000000000 : ℝ)^6217 := by
    have hnat : (137260001 : ℕ)^8265*100000000000000^6217 ≤ 13328932455859^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137260001 625000000 13328932455859 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436835877/10000000000 : ℝ)^8265 ≤ (4447993583607/10000000000000 : ℝ)^6217 := by
    have hnat : (5436835877 : ℕ)^8265*10000000000000^6217 ≤ 4447993583607^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436835877 10000000000 4447993583607 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225024479/10000000000 : ℝ)^8265 ≤ (42191131695777/100000000000000 : ℝ)^6217 := by
    have hnat : (5225024479 : ℕ)^8265*100000000000000^6217 ≤ 42191131695777^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225024479 10000000000 42191131695777 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137260001/625000000 : ℝ), (5436835877/10000000000 : ℝ), (5225024479/10000000000 : ℝ)] ![(13328932455859/100000000000000 : ℝ), (4447993583607/10000000000000 : ℝ), (42191131695777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137260001/625000000 : ℝ)|^8265 ≤ (13328932455859/100000000000000 : ℝ)^6217
        have hw : |(-137260001/625000000 : ℝ)|=(137260001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436835877/10000000000 : ℝ)|^8265 ≤ (4447993583607/10000000000000 : ℝ)^6217
        have hw : |(5436835877/10000000000 : ℝ)|=(5436835877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225024479/10000000000 : ℝ)|^8265 ≤ (42191131695777/100000000000000 : ℝ)^6217
        have hw : |(5225024479/10000000000 : ℝ)|=(5225024479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355535939/10000000000 : ℝ)*x 0 + (-2304608029/10000000000 : ℝ)*x 1 + (65312807/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355535939/10000000000 : ℝ)^8265 ≤ (21798940542367/50000000000000 : ℝ)^6217 := by
    have hnat : (5355535939 : ℕ)^8265*50000000000000^6217 ≤ 21798940542367^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355535939 10000000000 21798940542367 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2304608029/10000000000 : ℝ)^8265 ≤ (14210986341403/100000000000000 : ℝ)^6217 := by
    have hnat : (2304608029 : ℕ)^8265*100000000000000^6217 ≤ 14210986341403^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304608029 10000000000 14210986341403 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65312807/125000000 : ℝ)^8265 ≤ (21095566282649/50000000000000 : ℝ)^6217 := by
    have hnat : (65312807 : ℕ)^8265*50000000000000^6217 ≤ 21095566282649^6217*125000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65312807 125000000 21095566282649 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355535939/10000000000 : ℝ), (-2304608029/10000000000 : ℝ), (65312807/125000000 : ℝ)] ![(21798940542367/50000000000000 : ℝ), (14210986341403/100000000000000 : ℝ), (21095566282649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355535939/10000000000 : ℝ)|^8265 ≤ (21798940542367/50000000000000 : ℝ)^6217
        have hw : |(5355535939/10000000000 : ℝ)|=(5355535939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2304608029/10000000000 : ℝ)|^8265 ≤ (14210986341403/100000000000000 : ℝ)^6217
        have hw : |(-2304608029/10000000000 : ℝ)|=(2304608029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65312807/125000000 : ℝ)|^8265 ≤ (21095566282649/50000000000000 : ℝ)^6217
        have hw : |(65312807/125000000 : ℝ)|=(65312807/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355535917/10000000000 : ℝ)*x 0 + (5225024947/10000000000 : ℝ)*x 1 + (-46092151/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355535917/10000000000 : ℝ)^8265 ≤ (43597880846641/100000000000000 : ℝ)^6217 := by
    have hnat : (5355535917 : ℕ)^8265*100000000000000^6217 ≤ 43597880846641^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355535917 10000000000 43597880846641 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225024947/10000000000 : ℝ)^8265 ≤ (21095568359837/50000000000000 : ℝ)^6217 := by
    have hnat : (5225024947 : ℕ)^8265*50000000000000^6217 ≤ 21095568359837^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225024947 10000000000 21095568359837 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46092151/200000000 : ℝ)^8265 ≤ (14210982414731/100000000000000 : ℝ)^6217 := by
    have hnat : (46092151 : ℕ)^8265*100000000000000^6217 ≤ 14210982414731^6217*200000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46092151 200000000 14210982414731 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355535917/10000000000 : ℝ), (5225024947/10000000000 : ℝ), (-46092151/200000000 : ℝ)] ![(43597880846641/100000000000000 : ℝ), (21095568359837/50000000000000 : ℝ), (14210982414731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355535917/10000000000 : ℝ)|^8265 ≤ (43597880846641/100000000000000 : ℝ)^6217
        have hw : |(5355535917/10000000000 : ℝ)|=(5355535917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225024947/10000000000 : ℝ)|^8265 ≤ (21095568359837/50000000000000 : ℝ)^6217
        have hw : |(5225024947/10000000000 : ℝ)|=(5225024947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46092151/200000000 : ℝ)|^8265 ≤ (14210982414731/100000000000000 : ℝ)^6217
        have hw : |(-46092151/200000000 : ℝ)|=(46092151/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371874859/10000000000 : ℝ)*x 0 + (2084528057/5000000000 : ℝ)*x 1 + (4584670073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371874859/10000000000 : ℝ)^8265 ≤ (16644345676657/50000000000000 : ℝ)^6217 := by
    have hnat : (4371874859 : ℕ)^8265*50000000000000^6217 ≤ 16644345676657^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371874859 10000000000 16644345676657 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084528057/5000000000 : ℝ)^8265 ≤ (31251497037767/100000000000000 : ℝ)^6217 := by
    have hnat : (2084528057 : ℕ)^8265*100000000000000^6217 ≤ 31251497037767^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084528057 5000000000 31251497037767 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4584670073/10000000000 : ℝ)^8265 ≤ (35459811599713/100000000000000 : ℝ)^6217 := by
    have hnat : (4584670073 : ℕ)^8265*100000000000000^6217 ≤ 35459811599713^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584670073 10000000000 35459811599713 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371874859/10000000000 : ℝ), (2084528057/5000000000 : ℝ), (4584670073/10000000000 : ℝ)] ![(16644345676657/50000000000000 : ℝ), (31251497037767/100000000000000 : ℝ), (35459811599713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371874859/10000000000 : ℝ)|^8265 ≤ (16644345676657/50000000000000 : ℝ)^6217
        have hw : |(4371874859/10000000000 : ℝ)|=(4371874859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084528057/5000000000 : ℝ)|^8265 ≤ (31251497037767/100000000000000 : ℝ)^6217
        have hw : |(2084528057/5000000000 : ℝ)|=(2084528057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4584670073/10000000000 : ℝ)|^8265 ≤ (35459811599713/100000000000000 : ℝ)^6217
        have hw : |(4584670073/10000000000 : ℝ)|=(4584670073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196182111/10000000000 : ℝ)*x 0 + (5225889099/10000000000 : ℝ)*x 1 + (339747879/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196182111/10000000000 : ℝ)^8265 ≤ (6664555364949/50000000000000 : ℝ)^6217 := by
    have hnat : (2196182111 : ℕ)^8265*50000000000000^6217 ≤ 6664555364949^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196182111 10000000000 6664555364949 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225889099/10000000000 : ℝ)^8265 ≤ (2637525843143/6250000000000 : ℝ)^6217 := by
    have hnat : (5225889099 : ℕ)^8265*6250000000000^6217 ≤ 2637525843143^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225889099 10000000000 2637525843143 6250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339747879/625000000 : ℝ)^8265 ≤ (22235237882827/50000000000000 : ℝ)^6217 := by
    have hnat : (339747879 : ℕ)^8265*50000000000000^6217 ≤ 22235237882827^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339747879 625000000 22235237882827 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196182111/10000000000 : ℝ), (5225889099/10000000000 : ℝ), (339747879/625000000 : ℝ)] ![(6664555364949/50000000000000 : ℝ), (2637525843143/6250000000000 : ℝ), (22235237882827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196182111/10000000000 : ℝ)|^8265 ≤ (6664555364949/50000000000000 : ℝ)^6217
        have hw : |(-2196182111/10000000000 : ℝ)|=(2196182111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225889099/10000000000 : ℝ)|^8265 ≤ (2637525843143/6250000000000 : ℝ)^6217
        have hw : |(5225889099/10000000000 : ℝ)|=(5225889099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339747879/625000000 : ℝ)|^8265 ≤ (22235237882827/50000000000000 : ℝ)^6217
        have hw : |(339747879/625000000 : ℝ)|=(339747879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302156333/10000000000 : ℝ)*x 0 + (-130854147/625000000 : ℝ)*x 1 + (5435966383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302156333/10000000000 : ℝ)^8265 ≤ (43021135022877/100000000000000 : ℝ)^6217 := by
    have hnat : (5302156333 : ℕ)^8265*100000000000000^6217 ≤ 43021135022877^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302156333 10000000000 43021135022877 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130854147/625000000 : ℝ)^8265 ≤ (12508385732787/100000000000000 : ℝ)^6217 := by
    have hnat : (130854147 : ℕ)^8265*100000000000000^6217 ≤ 12508385732787^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130854147 625000000 12508385732787 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435966383/10000000000 : ℝ)^8265 ≤ (8894095847/20000000000 : ℝ)^6217 := by
    have hnat : (5435966383 : ℕ)^8265*20000000000^6217 ≤ 8894095847^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435966383 10000000000 8894095847 20000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302156333/10000000000 : ℝ), (-130854147/625000000 : ℝ), (5435966383/10000000000 : ℝ)] ![(43021135022877/100000000000000 : ℝ), (12508385732787/100000000000000 : ℝ), (8894095847/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302156333/10000000000 : ℝ)|^8265 ≤ (43021135022877/100000000000000 : ℝ)^6217
        have hw : |(5302156333/10000000000 : ℝ)|=(5302156333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130854147/625000000 : ℝ)|^8265 ≤ (12508385732787/100000000000000 : ℝ)^6217
        have hw : |(-130854147/625000000 : ℝ)|=(130854147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435966383/10000000000 : ℝ)|^8265 ≤ (8894095847/20000000000 : ℝ)^6217
        have hw : |(5435966383/10000000000 : ℝ)|=(5435966383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662769567/1250000000 : ℝ)*x 0 + (2717983051/5000000000 : ℝ)*x 1 + (-2093666461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662769567/1250000000 : ℝ)^8265 ≤ (43021137212591/100000000000000 : ℝ)^6217 := by
    have hnat : (662769567 : ℕ)^8265*100000000000000^6217 ≤ 43021137212591^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662769567 1250000000 43021137212591 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717983051/5000000000 : ℝ)^8265 ≤ (4447047617893/10000000000000 : ℝ)^6217 := by
    have hnat : (2717983051 : ℕ)^8265*10000000000000^6217 ≤ 4447047617893^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717983051 5000000000 4447047617893 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093666461/10000000000 : ℝ)^8265 ≤ (3127096649629/25000000000000 : ℝ)^6217 := by
    have hnat : (2093666461 : ℕ)^8265*25000000000000^6217 ≤ 3127096649629^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093666461 10000000000 3127096649629 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662769567/1250000000 : ℝ), (2717983051/5000000000 : ℝ), (-2093666461/10000000000 : ℝ)] ![(43021137212591/100000000000000 : ℝ), (4447047617893/10000000000000 : ℝ), (3127096649629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662769567/1250000000 : ℝ)|^8265 ≤ (43021137212591/100000000000000 : ℝ)^6217
        have hw : |(662769567/1250000000 : ℝ)|=(662769567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717983051/5000000000 : ℝ)|^8265 ≤ (4447047617893/10000000000000 : ℝ)^6217
        have hw : |(2717983051/5000000000 : ℝ)|=(2717983051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093666461/10000000000 : ℝ)|^8265 ≤ (3127096649629/25000000000000 : ℝ)^6217
        have hw : |(-2093666461/10000000000 : ℝ)|=(2093666461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s3_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185958833/5000000000 : ℝ)*x 0 + (4582974699/10000000000 : ℝ)*x 1 + (130336303/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185958833/5000000000 : ℝ)^8265 ≤ (33289124671069/100000000000000 : ℝ)^6217 := by
    have hnat : (2185958833 : ℕ)^8265*100000000000000^6217 ≤ 33289124671069^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185958833 5000000000 33289124671069 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582974699/10000000000 : ℝ)^8265 ≤ (7088476063053/20000000000000 : ℝ)^6217 := by
    have hnat : (4582974699 : ℕ)^8265*20000000000000^6217 ≤ 7088476063053^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582974699 10000000000 7088476063053 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130336303/312500000 : ℝ)^8265 ≤ (31268495003161/100000000000000 : ℝ)^6217 := by
    have hnat : (130336303 : ℕ)^8265*100000000000000^6217 ≤ 31268495003161^6217*312500000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130336303 312500000 31268495003161 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185958833/5000000000 : ℝ), (4582974699/10000000000 : ℝ), (130336303/312500000 : ℝ)] ![(33289124671069/100000000000000 : ℝ), (7088476063053/20000000000000 : ℝ), (31268495003161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185958833/5000000000 : ℝ)|^8265 ≤ (33289124671069/100000000000000 : ℝ)^6217
        have hw : |(2185958833/5000000000 : ℝ)|=(2185958833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582974699/10000000000 : ℝ)|^8265 ≤ (7088476063053/20000000000000 : ℝ)^6217
        have hw : |(4582974699/10000000000 : ℝ)|=(4582974699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130336303/312500000 : ℝ)|^8265 ≤ (31268495003161/100000000000000 : ℝ)^6217
        have hw : |(130336303/312500000 : ℝ)|=(130336303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (651/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14897/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8741/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (2679191418085903/50000000000000000000 : ℝ) := by
    have hpowers : (8741/100000 : ℝ)^1033 ≤ (2679191418085903/50000000000000000000 : ℝ)^256 := by
      have hnat : (8741 : ℕ)^1033*50000000000000000000^256 ≤ 2679191418085903^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8741 100000 2679191418085903 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8741/100000 : ℝ)) (X := (2679191418085903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16721/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (73407731074672401/100000000000000000000 : ℝ) := by
    have hpowers : (16721/100000 : ℝ)^1033 ≤ (73407731074672401/100000000000000000000 : ℝ)^256 := by
      have hnat : (16721 : ℕ)^1033*100000000000000000000^256 ≤ 73407731074672401^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16721 100000 73407731074672401 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16721/100000 : ℝ)) (X := (73407731074672401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002679191418085903/25000000000000000000 : ℝ) ≤ (10000265574195909/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25002679191418085903/25000000000000000000 : ℝ)^256 ≤ (10000265574195909/10000000000000000 : ℝ)^1033 := by
      have hnat : (25002679191418085903 : ℕ)^256*10000000000000000^1033 ≤ 10000265574195909^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002679191418085903 25000000000000000000 10000265574195909 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000265574195909/10000000000000000 : ℝ)) (X := (25002679191418085903/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078766113910844207/100000000000000000000 : ℝ) ≤ (5000975709325941/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (100078766113910844207/100000000000000000000 : ℝ)^256 ≤ (5000975709325941/5000000000000000 : ℝ)^1033 := by
      have hnat : (100078766113910844207 : ℕ)^256*5000000000000000^1033 ≤ 5000975709325941^1033*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078766113910844207 100000000000000000000 5000975709325941 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000975709325941/5000000000000000 : ℝ)) (X := (100078766113910844207/100000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073407731074672401/50000000000000000000 : ℝ) ≤ (2000727452621571/2000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50073407731074672401/50000000000000000000 : ℝ)^256 ≤ (2000727452621571/2000000000000000 : ℝ)^1033 := by
      have hnat : (50073407731074672401 : ℕ)^256*2000000000000000^1033 ≤ 2000727452621571^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073407731074672401 50000000000000000000 2000727452621571 2000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000727452621571/2000000000000000 : ℝ)) (X := (50073407731074672401/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2679191418085903/50000000000000000000 : ℝ) ≤ ((13295441224884005639/13300000000000000000 : ℝ)+2*(561948151991/266000000000000 : ℝ)*(8741/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (13295441224884005639/13300000000000000000 : ℝ)+2*(561948151991/266000000000000 : ℝ)*(8741/100000 : ℝ)=(10000265574195909/10000000000000000 : ℝ) by norm_num, show 1+2*(2679191418085903/50000000000000000000 : ℝ)=(25002679191418085903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73407731074672401/100000000000000000000 : ℝ)+(2679191418085903/50000000000000000000 : ℝ) ≤ ((13295441224884005639/13300000000000000000 : ℝ)+(561948151991/266000000000000 : ℝ)*((16721/100000 : ℝ)+(8741/100000 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (13295441224884005639/13300000000000000000 : ℝ)+(561948151991/266000000000000 : ℝ)*((16721/100000 : ℝ)+(8741/100000 : ℝ))=(5000975709325941/5000000000000000 : ℝ) by norm_num, show 1+(73407731074672401/100000000000000000000 : ℝ)+(2679191418085903/50000000000000000000 : ℝ)=(100078766113910844207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73407731074672401/100000000000000000000 : ℝ) ≤ ((13295441224884005639/13300000000000000000 : ℝ)+2*(561948151991/266000000000000 : ℝ)*(16721/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (13295441224884005639/13300000000000000000 : ℝ)+2*(561948151991/266000000000000 : ℝ)*(16721/100000 : ℝ)=(2000727452621571/2000000000000000 : ℝ) by norm_num, show 1+2*(73407731074672401/100000000000000000000 : ℝ)=(50073407731074672401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13295441224884005639/13300000000000000000 : ℝ)*(X 1 0+X 2 0)+(561948151991/266000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (16721/100000 : ℝ)) (c := (13295441224884005639/13300000000000000000 : ℝ)) (alpha := (561948151991/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13295441224884005639/13300000000000000000 : ℝ)*(X 0 1+X 2 1)+(561948151991/266000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (16721/100000 : ℝ)) (c := (13295441224884005639/13300000000000000000 : ℝ)) (alpha := (561948151991/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13295441224884005639/13300000000000000000 : ℝ)*(X 0 2+X 1 2)+(561948151991/266000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (16721/100000 : ℝ)) (c := (13295441224884005639/13300000000000000000 : ℝ)) (alpha := (561948151991/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-137260001/625000000 : ℝ)*X 0 0+(5436835877/10000000000 : ℝ)*X 0 1+(5225024479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355535939/10000000000 : ℝ)*X 1 0+(-2304608029/10000000000 : ℝ)*X 1 1+(65312807/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355535917/10000000000 : ℝ)*X 2 0+(5225024947/10000000000 : ℝ)*X 2 1+(-46092151/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371874859/10000000000 : ℝ)*X 0 0+(2084528057/5000000000 : ℝ)*X 0 1+(4584670073/10000000000 : ℝ)*X 0 2+(4371874859/10000000000 : ℝ)*X 1 0+(2084528057/5000000000 : ℝ)*X 1 1+(4584670073/10000000000 : ℝ)*X 1 2+(4371874859/10000000000 : ℝ)*X 2 0+(2084528057/5000000000 : ℝ)*X 2 1+(4584670073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2196182111/10000000000 : ℝ)*X 0 0+(5225889099/10000000000 : ℝ)*X 0 1+(339747879/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302156333/10000000000 : ℝ)*X 1 0+(-130854147/625000000 : ℝ)*X 1 1+(5435966383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662769567/1250000000 : ℝ)*X 2 0+(2717983051/5000000000 : ℝ)*X 2 1+(-2093666461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185958833/5000000000 : ℝ)*X 0 0+(4582974699/10000000000 : ℝ)*X 0 1+(130336303/312500000 : ℝ)*X 0 2+(2185958833/5000000000 : ℝ)*X 1 0+(4582974699/10000000000 : ℝ)*X 1 1+(130336303/312500000 : ℝ)*X 1 2+(2185958833/5000000000 : ℝ)*X 2 0+(4582974699/10000000000 : ℝ)*X 2 1+(130336303/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1296828532819476693592302861/332500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1982357/160000000000 : ℝ)*(base19) + (13522351/1562500000000 : ℝ)*(base23) + (7770769/4000000000000 : ℝ)*(lower2) + (75049609/50000000000000 : ℝ)*(upper5) + (1781833239383833/50000000000000 : ℝ)*(major0) + (1781833239383833/50000000000000 : ℝ)*(major1) + (3563666478767667/100000000000000 : ℝ)*(major2) + (944240795192921/20000000000000 : ℝ)*(sp0) + (944246519180921/20000000000000 : ℝ)*(sp1) + (472123383191643/10000000000000 : ℝ)*(sp2) + (1203044422027229/50000000000000 : ℝ)*(sp3) + (30721382289/100000000000000 : ℝ)*(sp4) + (862469163/100000000000000 : ℝ)*(sp5) + (4643063049/50000000000000 : ℝ)*(sp7) + (2406098130180557/100000000000000 : ℝ)*(f.failure) + (2360617348673447/50000000000000 : ℝ)*(f.sum) + (9007931166597/26600000000000000000000000000 : ℝ)*base66 + (374853140579875827/35000000000000000000000000000000 : ℝ)*base68 + (198811302191546541/190000000000000000000000000000000 : ℝ)*base70 + (168667979030124173/35000000000000000000000000000000 : ℝ)*base71 + (154874113904203/26600000000000000000000000000 : ℝ)*base73 + (1312251109588453459/190000000000000000000000000000000 : ℝ)*base75 + (10705634629667415713/665000000000000000000000000000000 : ℝ)*base78 + (1235233254127415713/665000000000000000000000000000000 : ℝ)*base80 + (54056200067203/6650000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (146283561/10000000000000000000000 : ℝ)*base89 + (146283561/10000000000000000000000 : ℝ)*base91 + (46283561/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2830193834000033670277579083/665000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (789922053/100000000000000 : ℝ)*(base19) + (227986089/20000000000000 : ℝ)*(base23) + (86747263/50000000000000 : ℝ)*(upper3) + (65396293/100000000000000 : ℝ)*(lower4) + (898261063197/25000000000 : ℝ)*(major0) + (898261063197/25000000000 : ℝ)*(major1) + (3593044252788001/100000000000000 : ℝ)*(major2) + (1004060913/6250000000000 : ℝ)*(sp1) + (20477327037/100000000000000 : ℝ)*(sp2) + (263740743/100000000000000 : ℝ)*(sp3) + (952031019625521/20000000000000 : ℝ)*(sp4) + (148754320100967/3125000000000 : ℝ)*(sp5) + (4760133480870123/100000000000000 : ℝ)*(sp6) + (606483250460823/25000000000000 : ℝ)*(sp7) + (485186653116807/20000000000000 : ℝ)*(f.failure) + (952031019625521/20000000000000 : ℝ)*(f.sum) + (6624486004513/3800000000000000000000000000 : ℝ)*base65 + (10084554010589459/665000000000000000000000000000 : ℝ)*base68 + (9731050229725537639/1330000000000000000000000000000000 : ℝ)*base69 + (6614505718809459/665000000000000000000000000000 : ℝ)*base72 + (1151743727713/3800000000000000000000000000 : ℝ)*base73 + (22041355584765537639/1330000000000000000000000000000000 : ℝ)*base75 + (140532133077743/17500000000000000000000000000 : ℝ)*base78 + (161009685085243/17500000000000000000000000000 : ℝ)*base80 + (7981081697/3500000000000000000000000 : ℝ)*base81 + (27254811/2000000000000000000000 : ℝ)*base89 + (27254811/2000000000000000000000 : ℝ)*base91 + (7254811/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14897/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s4_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137486199/625000000 : ℝ)*x 0 + (5405480283/10000000000 : ℝ)*x 1 + (5254015571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137486199/625000000 : ℝ)^8265 ≤ (13358141674763/100000000000000 : ℝ)^6217 := by
    have hnat : (137486199 : ℕ)^8265*100000000000000^6217 ≤ 13358141674763^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137486199 625000000 13358141674763 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405480283/10000000000 : ℝ)^8265 ≤ (44139228349639/100000000000000 : ℝ)^6217 := by
    have hnat : (5405480283 : ℕ)^8265*100000000000000^6217 ≤ 44139228349639^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405480283 10000000000 44139228349639 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254015571/10000000000 : ℝ)^8265 ≤ (21251314982033/50000000000000 : ℝ)^6217 := by
    have hnat : (5254015571 : ℕ)^8265*50000000000000^6217 ≤ 21251314982033^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254015571 10000000000 21251314982033 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137486199/625000000 : ℝ), (5405480283/10000000000 : ℝ), (5254015571/10000000000 : ℝ)] ![(13358141674763/100000000000000 : ℝ), (44139228349639/100000000000000 : ℝ), (21251314982033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137486199/625000000 : ℝ)|^8265 ≤ (13358141674763/100000000000000 : ℝ)^6217
        have hw : |(-137486199/625000000 : ℝ)|=(137486199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405480283/10000000000 : ℝ)|^8265 ≤ (44139228349639/100000000000000 : ℝ)^6217
        have hw : |(5405480283/10000000000 : ℝ)|=(5405480283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254015571/10000000000 : ℝ)|^8265 ≤ (21251314982033/50000000000000 : ℝ)^6217
        have hw : |(5254015571/10000000000 : ℝ)|=(5254015571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106955273/200000000 : ℝ)*x 0 + (-1138406383/5000000000 : ℝ)*x 1 + (1313503877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106955273/200000000 : ℝ)^8265 ≤ (4351378621209/10000000000000 : ℝ)^6217 := by
    have hnat : (106955273 : ℕ)^8265*10000000000000^6217 ≤ 4351378621209^6217*200000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106955273 200000000 4351378621209 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138406383/5000000000 : ℝ)^8265 ≤ (13983584490657/100000000000000 : ℝ)^6217 := by
    have hnat : (1138406383 : ℕ)^8265*100000000000000^6217 ≤ 13983584490657^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138406383 5000000000 13983584490657 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313503877/2500000000 : ℝ)^8265 ≤ (21251314643269/50000000000000 : ℝ)^6217 := by
    have hnat : (1313503877 : ℕ)^8265*50000000000000^6217 ≤ 21251314643269^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313503877 2500000000 21251314643269 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106955273/200000000 : ℝ), (-1138406383/5000000000 : ℝ), (1313503877/2500000000 : ℝ)] ![(4351378621209/10000000000000 : ℝ), (13983584490657/100000000000000 : ℝ), (21251314643269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106955273/200000000 : ℝ)|^8265 ≤ (4351378621209/10000000000000 : ℝ)^6217
        have hw : |(106955273/200000000 : ℝ)|=(106955273/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138406383/5000000000 : ℝ)|^8265 ≤ (13983584490657/100000000000000 : ℝ)^6217
        have hw : |(-1138406383/5000000000 : ℝ)|=(1138406383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313503877/2500000000 : ℝ)|^8265 ≤ (21251314643269/50000000000000 : ℝ)^6217
        have hw : |(1313503877/2500000000 : ℝ)|=(1313503877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347763771/10000000000 : ℝ)*x 0 + (5254015479/10000000000 : ℝ)*x 1 + (-2276812643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347763771/10000000000 : ℝ)^8265 ≤ (43513787520977/100000000000000 : ℝ)^6217 := by
    have hnat : (5347763771 : ℕ)^8265*100000000000000^6217 ≤ 43513787520977^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347763771 10000000000 43513787520977 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254015479/10000000000 : ℝ)^8265 ≤ (42502628974661/100000000000000 : ℝ)^6217 := by
    have hnat : (5254015479 : ℕ)^8265*100000000000000^6217 ≤ 42502628974661^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254015479 10000000000 42502628974661 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276812643/10000000000 : ℝ)^8265 ≤ (13983583486369/100000000000000 : ℝ)^6217 := by
    have hnat : (2276812643 : ℕ)^8265*100000000000000^6217 ≤ 13983583486369^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276812643 10000000000 13983583486369 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347763771/10000000000 : ℝ), (5254015479/10000000000 : ℝ), (-2276812643/10000000000 : ℝ)] ![(43513787520977/100000000000000 : ℝ), (42502628974661/100000000000000 : ℝ), (13983583486369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347763771/10000000000 : ℝ)|^8265 ≤ (43513787520977/100000000000000 : ℝ)^6217
        have hw : |(5347763771/10000000000 : ℝ)|=(5347763771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254015479/10000000000 : ℝ)|^8265 ≤ (42502628974661/100000000000000 : ℝ)^6217
        have hw : |(5254015479/10000000000 : ℝ)|=(5254015479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276812643/10000000000 : ℝ)|^8265 ≤ (13983583486369/100000000000000 : ℝ)^6217
        have hw : |(-2276812643/10000000000 : ℝ)|=(2276812643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187014233/5000000000 : ℝ)*x 0 + (4227979207/10000000000 : ℝ)*x 1 + (1131295649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187014233/5000000000 : ℝ)^8265 ≤ (33310493169663/100000000000000 : ℝ)^6217 := by
    have hnat : (2187014233 : ℕ)^8265*100000000000000^6217 ≤ 33310493169663^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187014233 5000000000 33310493169663 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227979207/10000000000 : ℝ)^8265 ≤ (1273602093199/4000000000000 : ℝ)^6217 := by
    have hnat : (4227979207 : ℕ)^8265*4000000000000^6217 ≤ 1273602093199^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227979207 10000000000 1273602093199 4000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131295649/2500000000 : ℝ)^8265 ≤ (34849454480047/100000000000000 : ℝ)^6217 := by
    have hnat : (1131295649 : ℕ)^8265*100000000000000^6217 ≤ 34849454480047^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131295649 2500000000 34849454480047 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187014233/5000000000 : ℝ), (4227979207/10000000000 : ℝ), (1131295649/2500000000 : ℝ)] ![(33310493169663/100000000000000 : ℝ), (1273602093199/4000000000000 : ℝ), (34849454480047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187014233/5000000000 : ℝ)|^8265 ≤ (33310493169663/100000000000000 : ℝ)^6217
        have hw : |(2187014233/5000000000 : ℝ)|=(2187014233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227979207/10000000000 : ℝ)|^8265 ≤ (1273602093199/4000000000000 : ℝ)^6217
        have hw : |(4227979207/10000000000 : ℝ)|=(4227979207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131295649/2500000000 : ℝ)|^8265 ≤ (34849454480047/100000000000000 : ℝ)^6217
        have hw : |(1131295649/2500000000 : ℝ)|=(1131295649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219978743/1000000000 : ℝ)*x 0 + (131361457/250000000 : ℝ)*x 1 + (1081007111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219978743/1000000000 : ℝ)^8265 ≤ (13358208243841/100000000000000 : ℝ)^6217 := by
    have hnat : (219978743 : ℕ)^8265*100000000000000^6217 ≤ 13358208243841^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219978743 1000000000 13358208243841 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131361457/250000000 : ℝ)^8265 ≤ (42507391102589/100000000000000 : ℝ)^6217 := by
    have hnat : (131361457 : ℕ)^8265*100000000000000^6217 ≤ 42507391102589^6217*250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131361457 250000000 42507391102589 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081007111/2000000000 : ℝ)^8265 ≤ (4413440064127/10000000000000 : ℝ)^6217 := by
    have hnat : (1081007111 : ℕ)^8265*10000000000000^6217 ≤ 4413440064127^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081007111 2000000000 4413440064127 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219978743/1000000000 : ℝ), (131361457/250000000 : ℝ), (1081007111/2000000000 : ℝ)] ![(13358208243841/100000000000000 : ℝ), (42507391102589/100000000000000 : ℝ), (4413440064127/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219978743/1000000000 : ℝ)|^8265 ≤ (13358208243841/100000000000000 : ℝ)^6217
        have hw : |(-219978743/1000000000 : ℝ)|=(219978743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131361457/250000000 : ℝ)|^8265 ≤ (42507391102589/100000000000000 : ℝ)^6217
        have hw : |(131361457/250000000 : ℝ)|=(131361457/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081007111/2000000000 : ℝ)|^8265 ≤ (4413440064127/10000000000000 : ℝ)^6217
        have hw : |(1081007111/2000000000 : ℝ)|=(1081007111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309596919/10000000000 : ℝ)*x 0 + (-425158451/2000000000 : ℝ)*x 1 + (5405035403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309596919/10000000000 : ℝ)^8265 ≤ (21550706720501/50000000000000 : ℝ)^6217 := by
    have hnat : (5309596919 : ℕ)^8265*50000000000000^6217 ≤ 21550706720501^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309596919 10000000000 21550706720501 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425158451/2000000000 : ℝ)^8265 ≤ (2552837510363/20000000000000 : ℝ)^6217 := by
    have hnat : (425158451 : ℕ)^8265*20000000000000^6217 ≤ 2552837510363^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425158451 2000000000 2552837510363 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405035403/10000000000 : ℝ)^8265 ≤ (44134398991269/100000000000000 : ℝ)^6217 := by
    have hnat : (5405035403 : ℕ)^8265*100000000000000^6217 ≤ 44134398991269^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405035403 10000000000 44134398991269 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309596919/10000000000 : ℝ), (-425158451/2000000000 : ℝ), (5405035403/10000000000 : ℝ)] ![(21550706720501/50000000000000 : ℝ), (2552837510363/20000000000000 : ℝ), (44134398991269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309596919/10000000000 : ℝ)|^8265 ≤ (21550706720501/50000000000000 : ℝ)^6217
        have hw : |(5309596919/10000000000 : ℝ)|=(5309596919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425158451/2000000000 : ℝ)|^8265 ≤ (2552837510363/20000000000000 : ℝ)^6217
        have hw : |(-425158451/2000000000 : ℝ)|=(425158451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405035403/10000000000 : ℝ)|^8265 ≤ (44134398991269/100000000000000 : ℝ)^6217
        have hw : |(5405035403/10000000000 : ℝ)|=(5405035403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654798393/5000000000 : ℝ)*x 0 + (1081007071/2000000000 : ℝ)*x 1 + (-850317/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654798393/5000000000 : ℝ)^8265 ≤ (43101412005699/100000000000000 : ℝ)^6217 := by
    have hnat : (2654798393 : ℕ)^8265*100000000000000^6217 ≤ 43101412005699^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654798393 5000000000 43101412005699 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081007071/2000000000 : ℝ)^8265 ≤ (5516799808777/12500000000000 : ℝ)^6217 := by
    have hnat : (1081007071 : ℕ)^8265*12500000000000^6217 ≤ 5516799808777^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081007071 2000000000 5516799808777 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850317/4000000 : ℝ)^8265 ≤ (12764189507507/100000000000000 : ℝ)^6217 := by
    have hnat : (850317 : ℕ)^8265*100000000000000^6217 ≤ 12764189507507^6217*4000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850317 4000000 12764189507507 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654798393/5000000000 : ℝ), (1081007071/2000000000 : ℝ), (-850317/4000000 : ℝ)] ![(43101412005699/100000000000000 : ℝ), (5516799808777/12500000000000 : ℝ), (12764189507507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654798393/5000000000 : ℝ)|^8265 ≤ (43101412005699/100000000000000 : ℝ)^6217
        have hw : |(2654798393/5000000000 : ℝ)|=(2654798393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081007071/2000000000 : ℝ)|^8265 ≤ (5516799808777/12500000000000 : ℝ)^6217
        have hw : |(1081007071/2000000000 : ℝ)|=(1081007071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-850317/4000000 : ℝ)|^8265 ≤ (12764189507507/100000000000000 : ℝ)^6217
        have hw : |(-850317/4000000 : ℝ)|=(850317/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s4_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187022107/5000000000 : ℝ)*x 0 + (1131078413/2500000000 : ℝ)*x 1 + (2114425917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187022107/5000000000 : ℝ)^8265 ≤ (4163831575741/12500000000000 : ℝ)^6217 := by
    have hnat : (2187022107 : ℕ)^8265*12500000000000^6217 ≤ 4163831575741^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187022107 5000000000 4163831575741 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131078413/2500000000 : ℝ)^8265 ≤ (3484055837467/10000000000000 : ℝ)^6217 := by
    have hnat : (1131078413 : ℕ)^8265*10000000000000^6217 ≤ 3484055837467^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131078413 2500000000 3484055837467 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114425917/5000000000 : ℝ)^8265 ≤ (31848789007981/100000000000000 : ℝ)^6217 := by
    have hnat : (2114425917 : ℕ)^8265*100000000000000^6217 ≤ 31848789007981^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114425917 5000000000 31848789007981 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187022107/5000000000 : ℝ), (1131078413/2500000000 : ℝ), (2114425917/5000000000 : ℝ)] ![(4163831575741/12500000000000 : ℝ), (3484055837467/10000000000000 : ℝ), (31848789007981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187022107/5000000000 : ℝ)|^8265 ≤ (4163831575741/12500000000000 : ℝ)^6217
        have hw : |(2187022107/5000000000 : ℝ)|=(2187022107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131078413/2500000000 : ℝ)|^8265 ≤ (3484055837467/10000000000000 : ℝ)^6217
        have hw : |(1131078413/2500000000 : ℝ)|=(1131078413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114425917/5000000000 : ℝ)|^8265 ≤ (31848789007981/100000000000000 : ℝ)^6217
        have hw : |(2114425917/5000000000 : ℝ)|=(2114425917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2207/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (651/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (651/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (651/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (651/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (651/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (651/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (651/6250 : ℝ) ^ (1033/256 : ℝ) ≤ (2174202197374019/20000000000000000000 : ℝ) := by
    have hpowers : (651/6250 : ℝ)^1033 ≤ (2174202197374019/20000000000000000000 : ℝ)^256 := by
      have hnat : (651 : ℕ)^1033*20000000000000000000^256 ≤ 2174202197374019^256*6250^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 6250 2174202197374019 20000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/6250 : ℝ)) (X := (2174202197374019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14897/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (46060062865242973/100000000000000000000 : ℝ) := by
    have hpowers : (14897/100000 : ℝ)^1033 ≤ (46060062865242973/100000000000000000000 : ℝ)^256 := by
      have hnat : (14897 : ℕ)^1033*100000000000000000000^256 ≤ 46060062865242973^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14897 100000 46060062865242973 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14897/100000 : ℝ)) (X := (46060062865242973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002174202197374019/10000000000000000000 : ℝ) ≤ (2500134692704701/2500000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (10002174202197374019/10000000000000000000 : ℝ)^256 ≤ (2500134692704701/2500000000000000 : ℝ)^1033 := by
      have hnat : (10002174202197374019 : ℕ)^256*2500000000000000^1033 ≤ 2500134692704701^1033*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002174202197374019 10000000000000000000 2500134692704701 2500000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134692704701/2500000000000000 : ℝ)) (X := (10002174202197374019/10000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014232768463028267/25000000000000000000 : ℝ) ≤ (5000705287289727/5000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25014232768463028267/25000000000000000000 : ℝ)^256 ≤ (5000705287289727/5000000000000000 : ℝ)^1033 := by
      have hnat : (25014232768463028267 : ℕ)^256*5000000000000000^1033 ≤ 5000705287289727^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014232768463028267 25000000000000000000 5000705287289727 5000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000705287289727/5000000000000000 : ℝ)) (X := (25014232768463028267/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046060062865242973/50000000000000000000 : ℝ) ≤ (1250285297292513/1250000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50046060062865242973/50000000000000000000 : ℝ)^256 ≤ (1250285297292513/1250000000000000 : ℝ)^1033 := by
      have hnat : (50046060062865242973 : ℕ)^256*1250000000000000^1033 ≤ 1250285297292513^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046060062865242973 50000000000000000000 1250285297292513 1250000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250285297292513/1250000000000000 : ℝ)) (X := (50046060062865242973/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2174202197374019/20000000000000000000 : ℝ) ≤ ((11198563204024299981/11202500000000000000 : ℝ)+2*(17436075213/8962000000000 : ℝ)*(651/6250 : ℝ))^(1033/256 : ℝ) := by
    rw [show (11198563204024299981/11202500000000000000 : ℝ)+2*(17436075213/8962000000000 : ℝ)*(651/6250 : ℝ)=(2500134692704701/2500000000000000 : ℝ) by norm_num, show 1+2*(2174202197374019/20000000000000000000 : ℝ)=(10002174202197374019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46060062865242973/100000000000000000000 : ℝ)+(2174202197374019/20000000000000000000 : ℝ) ≤ ((11198563204024299981/11202500000000000000 : ℝ)+(17436075213/8962000000000 : ℝ)*((14897/100000 : ℝ)+(651/6250 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (11198563204024299981/11202500000000000000 : ℝ)+(17436075213/8962000000000 : ℝ)*((14897/100000 : ℝ)+(651/6250 : ℝ))=(5000705287289727/5000000000000000 : ℝ) by norm_num, show 1+(46060062865242973/100000000000000000000 : ℝ)+(2174202197374019/20000000000000000000 : ℝ)=(25014232768463028267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46060062865242973/100000000000000000000 : ℝ) ≤ ((11198563204024299981/11202500000000000000 : ℝ)+2*(17436075213/8962000000000 : ℝ)*(14897/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (11198563204024299981/11202500000000000000 : ℝ)+2*(17436075213/8962000000000 : ℝ)*(14897/100000 : ℝ)=(1250285297292513/1250000000000000 : ℝ) by norm_num, show 1+2*(46060062865242973/100000000000000000000 : ℝ)=(50046060062865242973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11198563204024299981/11202500000000000000 : ℝ)*(X 1 0+X 2 0)+(17436075213/8962000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (14897/100000 : ℝ)) (c := (11198563204024299981/11202500000000000000 : ℝ)) (alpha := (17436075213/8962000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11198563204024299981/11202500000000000000 : ℝ)*(X 0 1+X 2 1)+(17436075213/8962000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (14897/100000 : ℝ)) (c := (11198563204024299981/11202500000000000000 : ℝ)) (alpha := (17436075213/8962000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11198563204024299981/11202500000000000000 : ℝ)*(X 0 2+X 1 2)+(17436075213/8962000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (651/6250 : ℝ)) (hi := (14897/100000 : ℝ)) (c := (11198563204024299981/11202500000000000000 : ℝ)) (alpha := (17436075213/8962000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-137486199/625000000 : ℝ)*X 0 0+(5405480283/10000000000 : ℝ)*X 0 1+(5254015571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106955273/200000000 : ℝ)*X 1 0+(-1138406383/5000000000 : ℝ)*X 1 1+(1313503877/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347763771/10000000000 : ℝ)*X 2 0+(5254015479/10000000000 : ℝ)*X 2 1+(-2276812643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187014233/5000000000 : ℝ)*X 0 0+(4227979207/10000000000 : ℝ)*X 0 1+(1131295649/2500000000 : ℝ)*X 0 2+(2187014233/5000000000 : ℝ)*X 1 0+(4227979207/10000000000 : ℝ)*X 1 1+(1131295649/2500000000 : ℝ)*X 1 2+(2187014233/5000000000 : ℝ)*X 2 0+(4227979207/10000000000 : ℝ)*X 2 1+(1131295649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219978743/1000000000 : ℝ)*X 0 0+(131361457/250000000 : ℝ)*X 0 1+(1081007111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309596919/10000000000 : ℝ)*X 1 0+(-425158451/2000000000 : ℝ)*X 1 1+(5405035403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654798393/5000000000 : ℝ)*X 2 0+(1081007071/2000000000 : ℝ)*X 2 1+(-850317/4000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187022107/5000000000 : ℝ)*X 0 0+(1131078413/2500000000 : ℝ)*X 0 1+(2114425917/5000000000 : ℝ)*X 0 2+(2187022107/5000000000 : ℝ)*X 1 0+(1131078413/2500000000 : ℝ)*X 1 1+(2114425917/5000000000 : ℝ)*X 1 2+(2187022107/5000000000 : ℝ)*X 2 0+(1131078413/2500000000 : ℝ)*X 2 1+(2114425917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6486253096969689461532879/1093994140625000000000000000000 : ℝ) := by norm_num
    linear_combination (466077679/50000000000000 : ℝ)*(base19) + (324290563/50000000000000 : ℝ)*(base23) + (11576789/5000000000000 : ℝ)*(lower2) + (28190843/20000000000000 : ℝ)*(upper3) + (4104183/50000000000000 : ℝ)*(upper5) + (155733551207273/3125000000000 : ℝ)*(major0) + (155733551207273/3125000000000 : ℝ)*(major1) + (155733551207273/3125000000000 : ℝ)*(major2) + (660221359711593/10000000000000 : ℝ)*(sp0) + (264089194854929/4000000000000 : ℝ)*(sp1) + (3301115077473729/50000000000000 : ℝ)*(sp2) + (134588207342141/4000000000000 : ℝ)*(sp3) + (17206412653/100000000000000 : ℝ)*(sp4) + (11092551183/100000000000000 : ℝ)*(sp7) + (841179069026177/25000000000000 : ℝ)*(f.failure) + (6602230803528583/100000000000000 : ℝ)*(f.sum) + (2281315464091/2240500000000000000000000000 : ℝ)*base66 + (961821226892845501/70015625000000000000000000000000 : ℝ)*base67 + (1149791486263810749/70015625000000000000000000000000 : ℝ)*base70 + (345471934486019969/17503906250000000000000000000000 : ℝ)*base71 + (185230478641/4481000000000000000000000000 : ℝ)*base74 + (620493818051323781/17503906250000000000000000000000 : ℝ)*base76 + (1183106804997979/273498535156250000000000000000 : ℝ)*base78 + (6556295205779499/70015625000000000000000000000000 : ℝ)*base80 + (1347079619197/1120250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6527821/2500000000000000000000 : ℝ)*base89 + (6527821/2500000000000000000000 : ℝ)*base91 + (6527821/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1046438662354041061000199667/280062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241952509/12500000000000 : ℝ)*(base19) + (1820631297/100000000000000 : ℝ)*(base23) + (29014609/50000000000000 : ℝ)*(upper3) + (70262181/100000000000000 : ℝ)*(lower4) + (16218413/12500000000000 : ℝ)*(upper5) + (5012818324257231/100000000000000 : ℝ)*(major0) + (5012818324257231/100000000000000 : ℝ)*(major1) + (5012818324257231/100000000000000 : ℝ)*(major2) + (48366907011/100000000000000 : ℝ)*(sp1) + (37102954707/100000000000000 : ℝ)*(sp2) + (53128859623297/800000000000 : ℝ)*(sp4) + (3320528575192521/50000000000000 : ℝ)*(sp5) + (6641068529326121/100000000000000 : ℝ)*(sp6) + (211533066940881/6250000000000 : ℝ)*(sp7) + (211533066940881/6250000000000 : ℝ)*(f.failure) + (53128859623297/800000000000 : ℝ)*(f.sum) + (4483454474221/1120250000000000000000000000 : ℝ)*base66 + (4822553856618162611/1120250000000000000000000000000000 : ℝ)*base67 + (5683070704766412611/1120250000000000000000000000000000 : ℝ)*base69 + (426122885556837389/1120250000000000000000000000000000 : ℝ)*base72 + (5793606631347/2240500000000000000000000000 : ℝ)*base73 + (35970189878051662611/1120250000000000000000000000000000 : ℝ)*base75 + (7490536601979412611/1120250000000000000000000000000000 : ℝ)*base77 + (15772692217506162611/1120250000000000000000000000000000 : ℝ)*base79 + (11359057961173/4481000000000000000000000000 : ℝ)*base82 + (4419987/625000000000000000000 : ℝ)*base90 + (4419987/625000000000000000000 : ℝ)*base92 + (4419987/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1072_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s5_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-8596059/39062500 : ℝ)*x 0 + (2698412413/5000000000 : ℝ)*x 1 + (2631069279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8596059/39062500 : ℝ)^8265 ≤ (3341174153183/25000000000000 : ℝ)^6217 := by
    have hnat : (8596059 : ℕ)^8265*25000000000000^6217 ≤ 3341174153183^6217*39062500^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8596059 39062500 3341174153183 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698412413/5000000000 : ℝ)^8265 ≤ (44045293261769/100000000000000 : ℝ)^6217 := by
    have hnat : (2698412413 : ℕ)^8265*100000000000000^6217 ≤ 44045293261769^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698412413 5000000000 44045293261769 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631069279/5000000000 : ℝ)^8265 ≤ (1703600404177/4000000000000 : ℝ)^6217 := by
    have hnat : (2631069279 : ℕ)^8265*4000000000000^6217 ≤ 1703600404177^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631069279 5000000000 1703600404177 4000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8596059/39062500 : ℝ), (2698412413/5000000000 : ℝ), (2631069279/5000000000 : ℝ)] ![(3341174153183/25000000000000 : ℝ), (44045293261769/100000000000000 : ℝ), (1703600404177/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8596059/39062500 : ℝ)|^8265 ≤ (3341174153183/25000000000000 : ℝ)^6217
        have hw : |(-8596059/39062500 : ℝ)|=(8596059/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698412413/5000000000 : ℝ)|^8265 ≤ (44045293261769/100000000000000 : ℝ)^6217
        have hw : |(2698412413/5000000000 : ℝ)|=(2698412413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631069279/5000000000 : ℝ)|^8265 ≤ (1703600404177/4000000000000 : ℝ)^6217
        have hw : |(2631069279/5000000000 : ℝ)|=(2631069279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334100447/625000000 : ℝ)*x 0 + (-1134481493/5000000000 : ℝ)*x 1 + (328883669/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334100447/625000000 : ℝ)^8265 ≤ (1359076887337/3125000000000 : ℝ)^6217 := by
    have hnat : (334100447 : ℕ)^8265*3125000000000^6217 ≤ 1359076887337^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334100447 625000000 1359076887337 3125000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134481493/5000000000 : ℝ)^8265 ≤ (13919527905129/100000000000000 : ℝ)^6217 := by
    have hnat : (1134481493 : ℕ)^8265*100000000000000^6217 ≤ 13919527905129^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134481493 5000000000 13919527905129 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328883669/625000000 : ℝ)^8265 ≤ (42590011675367/100000000000000 : ℝ)^6217 := by
    have hnat : (328883669 : ℕ)^8265*100000000000000^6217 ≤ 42590011675367^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328883669 625000000 42590011675367 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334100447/625000000 : ℝ), (-1134481493/5000000000 : ℝ), (328883669/625000000 : ℝ)] ![(1359076887337/3125000000000 : ℝ), (13919527905129/100000000000000 : ℝ), (42590011675367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334100447/625000000 : ℝ)|^8265 ≤ (1359076887337/3125000000000 : ℝ)^6217
        have hw : |(334100447/625000000 : ℝ)|=(334100447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134481493/5000000000 : ℝ)|^8265 ≤ (13919527905129/100000000000000 : ℝ)^6217
        have hw : |(-1134481493/5000000000 : ℝ)|=(1134481493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328883669/625000000 : ℝ)|^8265 ≤ (42590011675367/100000000000000 : ℝ)^6217
        have hw : |(328883669/625000000 : ℝ)|=(328883669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345607637/10000000000 : ℝ)*x 0 + (5262138619/10000000000 : ℝ)*x 1 + (-453792491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345607637/10000000000 : ℝ)^8265 ≤ (43490465640451/100000000000000 : ℝ)^6217 := by
    have hnat : (5345607637 : ℕ)^8265*100000000000000^6217 ≤ 43490465640451^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345607637 10000000000 43490465640451 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262138619/10000000000 : ℝ)^8265 ≤ (42590010760777/100000000000000 : ℝ)^6217 := by
    have hnat : (5262138619 : ℕ)^8265*100000000000000^6217 ≤ 42590010760777^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262138619 10000000000 42590010760777 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453792491/2000000000 : ℝ)^8265 ≤ (6959761787237/50000000000000 : ℝ)^6217 := by
    have hnat : (453792491 : ℕ)^8265*50000000000000^6217 ≤ 6959761787237^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453792491 2000000000 6959761787237 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345607637/10000000000 : ℝ), (5262138619/10000000000 : ℝ), (-453792491/2000000000 : ℝ)] ![(43490465640451/100000000000000 : ℝ), (42590010760777/100000000000000 : ℝ), (6959761787237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345607637/10000000000 : ℝ)|^8265 ≤ (43490465640451/100000000000000 : ℝ)^6217
        have hw : |(5345607637/10000000000 : ℝ)|=(5345607637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262138619/10000000000 : ℝ)|^8265 ≤ (42590010760777/100000000000000 : ℝ)^6217
        have hw : |(5262138619/10000000000 : ℝ)|=(5262138619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453792491/2000000000 : ℝ)|^8265 ≤ (6959761787237/50000000000000 : ℝ)^6217
        have hw : |(-453792491/2000000000 : ℝ)|=(453792491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546812523/1250000000 : ℝ)*x 0 + (66318433/156250000 : ℝ)*x 1 + (563582297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546812523/1250000000 : ℝ)^8265 ≤ (208220431437/625000000000 : ℝ)^6217 := by
    have hnat : (546812523 : ℕ)^8265*625000000000^6217 ≤ 208220431437^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546812523 1250000000 208220431437 625000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66318433/156250000 : ℝ)^8265 ≤ (8001088056667/25000000000000 : ℝ)^6217 := by
    have hnat : (66318433 : ℕ)^8265*25000000000000^6217 ≤ 8001088056667^6217*156250000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66318433 156250000 8001088056667 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563582297/1250000000 : ℝ)^8265 ≤ (34680378725707/100000000000000 : ℝ)^6217 := by
    have hnat : (563582297 : ℕ)^8265*100000000000000^6217 ≤ 34680378725707^6217*1250000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563582297 1250000000 34680378725707 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546812523/1250000000 : ℝ), (66318433/156250000 : ℝ), (563582297/1250000000 : ℝ)] ![(208220431437/625000000000 : ℝ), (8001088056667/25000000000000 : ℝ), (34680378725707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546812523/1250000000 : ℝ)|^8265 ≤ (208220431437/625000000000 : ℝ)^6217
        have hw : |(546812523/1250000000 : ℝ)|=(546812523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66318433/156250000 : ℝ)|^8265 ≤ (8001088056667/25000000000000 : ℝ)^6217
        have hw : |(66318433/156250000 : ℝ)|=(66318433/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563582297/1250000000 : ℝ)|^8265 ≤ (34680378725707/100000000000000 : ℝ)^6217
        have hw : |(563582297/1250000000 : ℝ)|=(563582297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100298373/5000000000 : ℝ)*x 0 + (5262489269/10000000000 : ℝ)*x 1 + (2698236409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100298373/5000000000 : ℝ)^8265 ≤ (534589686621/4000000000000 : ℝ)^6217 := by
    have hnat : (1100298373 : ℕ)^8265*4000000000000^6217 ≤ 534589686621^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100298373 5000000000 534589686621 4000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262489269/10000000000 : ℝ)^8265 ≤ (42593783754353/100000000000000 : ℝ)^6217 := by
    have hnat : (5262489269 : ℕ)^8265*100000000000000^6217 ≤ 42593783754353^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262489269 10000000000 42593783754353 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698236409/5000000000 : ℝ)^8265 ≤ (1101036851843/2500000000000 : ℝ)^6217 := by
    have hnat : (2698236409 : ℕ)^8265*2500000000000^6217 ≤ 1101036851843^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698236409 5000000000 1101036851843 2500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100298373/5000000000 : ℝ), (5262489269/10000000000 : ℝ), (2698236409/5000000000 : ℝ)] ![(534589686621/4000000000000 : ℝ), (42593783754353/100000000000000 : ℝ), (1101036851843/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100298373/5000000000 : ℝ)|^8265 ≤ (534589686621/4000000000000 : ℝ)^6217
        have hw : |(-1100298373/5000000000 : ℝ)|=(1100298373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262489269/10000000000 : ℝ)|^8265 ≤ (42593783754353/100000000000000 : ℝ)^6217
        have hw : |(5262489269/10000000000 : ℝ)|=(5262489269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698236409/5000000000 : ℝ)|^8265 ≤ (1101036851843/2500000000000 : ℝ)^6217
        have hw : |(2698236409/5000000000 : ℝ)|=(2698236409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311666871/10000000000 : ℝ)*x 0 + (-2134628853/10000000000 : ℝ)*x 1 + (2698236383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311666871/10000000000 : ℝ)^8265 ≤ (8624750656719/20000000000000 : ℝ)^6217 := by
    have hnat : (5311666871 : ℕ)^8265*20000000000000^6217 ≤ 8624750656719^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311666871 10000000000 8624750656719 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134628853/10000000000 : ℝ)^8265 ≤ (6417386600857/50000000000000 : ℝ)^6217 := by
    have hnat : (2134628853 : ℕ)^8265*50000000000000^6217 ≤ 6417386600857^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134628853 10000000000 6417386600857 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698236383/5000000000 : ℝ)^8265 ≤ (2202073675477/5000000000000 : ℝ)^6217 := by
    have hnat : (2698236383 : ℕ)^8265*5000000000000^6217 ≤ 2202073675477^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698236383 5000000000 2202073675477 5000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311666871/10000000000 : ℝ), (-2134628853/10000000000 : ℝ), (2698236383/5000000000 : ℝ)] ![(8624750656719/20000000000000 : ℝ), (6417386600857/50000000000000 : ℝ), (2202073675477/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311666871/10000000000 : ℝ)|^8265 ≤ (8624750656719/20000000000000 : ℝ)^6217
        have hw : |(5311666871/10000000000 : ℝ)|=(5311666871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134628853/10000000000 : ℝ)|^8265 ≤ (6417386600857/50000000000000 : ℝ)^6217
        have hw : |(-2134628853/10000000000 : ℝ)|=(2134628853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698236383/5000000000 : ℝ)|^8265 ≤ (2202073675477/5000000000000 : ℝ)^6217
        have hw : |(2698236383/5000000000 : ℝ)|=(2698236383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062333367/2000000000 : ℝ)*x 0 + (2698236409/5000000000 : ℝ)*x 1 + (-213462883/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062333367/2000000000 : ℝ)^8265 ≤ (21561876447521/50000000000000 : ℝ)^6217 := by
    have hnat : (1062333367 : ℕ)^8265*50000000000000^6217 ≤ 21561876447521^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062333367 2000000000 21561876447521 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698236409/5000000000 : ℝ)^8265 ≤ (1101036851843/2500000000000 : ℝ)^6217 := by
    have hnat : (2698236409 : ℕ)^8265*2500000000000^6217 ≤ 1101036851843^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698236409 5000000000 1101036851843 2500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213462883/1000000000 : ℝ)^8265 ≤ (12834773017867/100000000000000 : ℝ)^6217 := by
    have hnat : (213462883 : ℕ)^8265*100000000000000^6217 ≤ 12834773017867^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213462883 1000000000 12834773017867 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062333367/2000000000 : ℝ), (2698236409/5000000000 : ℝ), (-213462883/1000000000 : ℝ)] ![(21561876447521/50000000000000 : ℝ), (1101036851843/2500000000000 : ℝ), (12834773017867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062333367/2000000000 : ℝ)|^8265 ≤ (21561876447521/50000000000000 : ℝ)^6217
        have hw : |(1062333367/2000000000 : ℝ)|=(1062333367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698236409/5000000000 : ℝ)|^8265 ≤ (1101036851843/2500000000000 : ℝ)^6217
        have hw : |(2698236409/5000000000 : ℝ)|=(2698236409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213462883/1000000000 : ℝ)|^8265 ≤ (12834773017867/100000000000000 : ℝ)^6217
        have hw : |(-213462883/1000000000 : ℝ)|=(213462883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s5_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374511281/10000000000 : ℝ)*x 0 + (2253985659/5000000000 : ℝ)*x 1 + (2122534667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374511281/10000000000 : ℝ)^8265 ≤ (6663076276479/20000000000000 : ℝ)^6217 := by
    have hnat : (4374511281 : ℕ)^8265*20000000000000^6217 ≤ 6663076276479^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374511281 10000000000 6663076276479 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253985659/5000000000 : ℝ)^8265 ≤ (1733667658249/5000000000000 : ℝ)^6217 := by
    have hnat : (2253985659 : ℕ)^8265*5000000000000^6217 ≤ 1733667658249^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253985659 5000000000 1733667658249 5000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122534667/5000000000 : ℝ)^8265 ≤ (80028163583/250000000000 : ℝ)^6217 := by
    have hnat : (2122534667 : ℕ)^8265*250000000000^6217 ≤ 80028163583^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122534667 5000000000 80028163583 250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374511281/10000000000 : ℝ), (2253985659/5000000000 : ℝ), (2122534667/5000000000 : ℝ)] ![(6663076276479/20000000000000 : ℝ), (1733667658249/5000000000000 : ℝ), (80028163583/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374511281/10000000000 : ℝ)|^8265 ≤ (6663076276479/20000000000000 : ℝ)^6217
        have hw : |(4374511281/10000000000 : ℝ)|=(4374511281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253985659/5000000000 : ℝ)|^8265 ≤ (1733667658249/5000000000000 : ℝ)^6217
        have hw : |(2253985659/5000000000 : ℝ)|=(2253985659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122534667/5000000000 : ℝ)|^8265 ≤ (80028163583/250000000000 : ℝ)^6217
        have hw : |(2122534667/5000000000 : ℝ)|=(2122534667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1401/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2207/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2207/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2207/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2207/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2207/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2207/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2207/20000 : ℝ) ^ (1033/256 : ℝ) ≤ (85766331107491/625000000000000000 : ℝ) := by
    have hpowers : (2207/20000 : ℝ)^1033 ≤ (85766331107491/625000000000000000 : ℝ)^256 := by
      have hnat : (2207 : ℕ)^1033*625000000000000000^256 ≤ 85766331107491^256*20000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 20000 85766331107491 625000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/20000 : ℝ)) (X := (85766331107491/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (9604320942661621/25000000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^1033 ≤ (9604320942661621/25000000000000000000 : ℝ)^256 := by
      have hnat : (7121 : ℕ)^1033*25000000000000000000^256 ≤ 9604320942661621^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 9604320942661621 25000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (9604320942661621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (312585766331107491/312500000000000000 : ℝ) ≤ (2000136016510159/2000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (312585766331107491/312500000000000000 : ℝ)^256 ≤ (2000136016510159/2000000000000000 : ℝ)^1033 := by
      have hnat : (312585766331107491 : ℕ)^256*2000000000000000^1033 ≤ 2000136016510159^1033*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312585766331107491 312500000000000000 2000136016510159 2000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136016510159/2000000000000000 : ℝ)) (X := (312585766331107491/312500000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013034974186961261/25000000000000000000 : ℝ) ≤ (10001291887411307/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25013034974186961261/25000000000000000000 : ℝ)^256 ≤ (10001291887411307/10000000000000000 : ℝ)^1033 := by
      have hnat : (25013034974186961261 : ℕ)^256*10000000000000000^1033 ≤ 10001291887411307^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013034974186961261 25000000000000000000 10001291887411307 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001291887411307/10000000000000000 : ℝ)) (X := (25013034974186961261/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509604320942661621/12500000000000000000 : ℝ) ≤ (10001903692271819/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (12509604320942661621/12500000000000000000 : ℝ)^256 ≤ (10001903692271819/10000000000000000 : ℝ)^1033 := by
      have hnat : (12509604320942661621 : ℕ)^256*10000000000000000^1033 ≤ 10001903692271819^1033*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509604320942661621 12500000000000000000 10001903692271819 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001903692271819/10000000000000000 : ℝ)) (X := (12509604320942661621/12500000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(85766331107491/625000000000000000 : ℝ) ≤ ((427449046552918663/427600000000000000 : ℝ)+2*(6372967297/3340625000000 : ℝ)*(2207/20000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (427449046552918663/427600000000000000 : ℝ)+2*(6372967297/3340625000000 : ℝ)*(2207/20000 : ℝ)=(2000136016510159/2000000000000000 : ℝ) by norm_num, show 1+2*(85766331107491/625000000000000000 : ℝ)=(312585766331107491/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9604320942661621/25000000000000000000 : ℝ)+(85766331107491/625000000000000000 : ℝ) ≤ ((427449046552918663/427600000000000000 : ℝ)+(6372967297/3340625000000 : ℝ)*((7121/50000 : ℝ)+(2207/20000 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (427449046552918663/427600000000000000 : ℝ)+(6372967297/3340625000000 : ℝ)*((7121/50000 : ℝ)+(2207/20000 : ℝ))=(10001291887411307/10000000000000000 : ℝ) by norm_num, show 1+(9604320942661621/25000000000000000000 : ℝ)+(85766331107491/625000000000000000 : ℝ)=(25013034974186961261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9604320942661621/25000000000000000000 : ℝ) ≤ ((427449046552918663/427600000000000000 : ℝ)+2*(6372967297/3340625000000 : ℝ)*(7121/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (427449046552918663/427600000000000000 : ℝ)+2*(6372967297/3340625000000 : ℝ)*(7121/50000 : ℝ)=(10001903692271819/10000000000000000 : ℝ) by norm_num, show 1+2*(9604320942661621/25000000000000000000 : ℝ)=(12509604320942661621/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (427449046552918663/427600000000000000 : ℝ)*(X 1 0+X 2 0)+(6372967297/3340625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (427449046552918663/427600000000000000 : ℝ)) (alpha := (6372967297/3340625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (427449046552918663/427600000000000000 : ℝ)*(X 0 1+X 2 1)+(6372967297/3340625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (427449046552918663/427600000000000000 : ℝ)) (alpha := (6372967297/3340625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (427449046552918663/427600000000000000 : ℝ)*(X 0 2+X 1 2)+(6372967297/3340625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (2207/20000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (427449046552918663/427600000000000000 : ℝ)) (alpha := (6372967297/3340625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8596059/39062500 : ℝ)*X 0 0+(2698412413/5000000000 : ℝ)*X 0 1+(2631069279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334100447/625000000 : ℝ)*X 1 0+(-1134481493/5000000000 : ℝ)*X 1 1+(328883669/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345607637/10000000000 : ℝ)*X 2 0+(5262138619/10000000000 : ℝ)*X 2 1+(-453792491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546812523/1250000000 : ℝ)*X 0 0+(66318433/156250000 : ℝ)*X 0 1+(563582297/1250000000 : ℝ)*X 0 2+(546812523/1250000000 : ℝ)*X 1 0+(66318433/156250000 : ℝ)*X 1 1+(563582297/1250000000 : ℝ)*X 1 2+(546812523/1250000000 : ℝ)*X 2 0+(66318433/156250000 : ℝ)*X 2 1+(563582297/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1100298373/5000000000 : ℝ)*X 0 0+(5262489269/10000000000 : ℝ)*X 0 1+(2698236409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311666871/10000000000 : ℝ)*X 1 0+(-2134628853/10000000000 : ℝ)*X 1 1+(2698236383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062333367/2000000000 : ℝ)*X 2 0+(2698236409/5000000000 : ℝ)*X 2 1+(-213462883/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374511281/10000000000 : ℝ)*X 0 0+(2253985659/5000000000 : ℝ)*X 0 1+(2122534667/5000000000 : ℝ)*X 0 2+(4374511281/10000000000 : ℝ)*X 1 0+(2253985659/5000000000 : ℝ)*X 1 1+(2122534667/5000000000 : ℝ)*X 1 2+(4374511281/10000000000 : ℝ)*X 2 0+(2253985659/5000000000 : ℝ)*X 2 1+(2122534667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13336875423519389565320439/2672500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706239493/50000000000000 : ℝ)*(base19) + (1092350403/50000000000000 : ℝ)*(base23) + (7493449/20000000000000 : ℝ)*(lower2) + (94823763/50000000000000 : ℝ)*(upper5) + (700546469191551/12500000000000 : ℝ)*(major0) + (700546469191551/12500000000000 : ℝ)*(major1) + (700546469191551/12500000000000 : ℝ)*(major2) + (1484945559007791/20000000000000 : ℝ)*(sp0) + (148495685382197/2000000000000 : ℝ)*(sp1) + (742481006219749/10000000000000 : ℝ)*(sp2) + (472988426699283/12500000000000 : ℝ)*(sp3) + (84451859341/100000000000000 : ℝ)*(sp4) + (1328265473/5000000000000 : ℝ)*(sp5) + (5920056297/25000000000000 : ℝ)*(sp7) + (3783931093819453/100000000000000 : ℝ)*(f.failure) + (928101530862287/12500000000000 : ℝ)*(f.sum) + (8001518960911/2672500000000000000000000000 : ℝ)*base65 + (7664883123662687/5345000000000000000000000000000 : ℝ)*base68 + (13232884931347687/5345000000000000000000000000000 : ℝ)*base70 + (139218929472552313/5345000000000000000000000000000 : ℝ)*base71 + (1313026515237/334062500000000000000000000 : ℝ)*base73 + (40392866012887687/5345000000000000000000000000000 : ℝ)*base76 + (63492657049402313/5345000000000000000000000000000 : ℝ)*base77 + (23928957802757687/5345000000000000000000000000000 : ℝ)*base80 + (12004463200531/2672500000000000000000000000 : ℝ)*base81 + (86814169/10000000000000000000000 : ℝ)*base89 + (86814169/10000000000000000000000 : ℝ)*base91 + (86814169/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19917541778156956388105511/2138000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357592377/20000000000000 : ℝ)*(base19) + (384721099/20000000000000 : ℝ)*(base23) + (187539997/100000000000000 : ℝ)*(upper3) + (79223821/100000000000000 : ℝ)*(lower4) + (167432401/100000000000000 : ℝ)*(upper5) + (1126729843612501/20000000000000 : ℝ)*(major0) + (1126729843612501/20000000000000 : ℝ)*(major1) + (1126729843612501/20000000000000 : ℝ)*(major2) + (11105567697/25000000000000 : ℝ)*(sp1) + (25112095639/50000000000000 : ℝ)*(sp2) + (3731799811409509/50000000000000 : ℝ)*(sp4) + (932944176573293/12500000000000 : ℝ)*(sp5) + (1865886868755561/25000000000000 : ℝ)*(sp6) + (1901849251386843/50000000000000 : ℝ)*(sp7) + (1901849251386843/50000000000000 : ℝ)*(f.failure) + (3731799811409509/50000000000000 : ℝ)*(f.sum) + (842157745909/534500000000000000000000000 : ℝ)*base66 + (56899093330542163/8552000000000000000000000000000 : ℝ)*base67 + (792484160926163/8552000000000000000000000000000 : ℝ)*base69 + (26946729513390163/8552000000000000000000000000000 : ℝ)*base71 + (1435737703777/267250000000000000000000000 : ℝ)*base74 + (26855272595262163/8552000000000000000000000000000 : ℝ)*base75 + (10677555006238163/8552000000000000000000000000000 : ℝ)*base77 + (79454087304721837/8552000000000000000000000000000 : ℝ)*base80 + (180155402319/534500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1916639/5000000000000000000000 : ℝ)*base89 + (1916639/5000000000000000000000 : ℝ)*base91 + (1916639/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1072_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1072_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1072_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1072_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:58.744164+00:00
-- url     : https://prove2.me/submissions/70f0e1c8-8391-4fe1-8509-fe6048bfb1cd

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
theorem support_rectangle_w1086_s3_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547370847/2500000000 : ℝ)*x 0 + (1358808949/2500000000 : ℝ)*x 1 + (5226512093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547370847/2500000000 : ℝ)^8279 ≤ (13290021614527/100000000000000 : ℝ)^6231 := by
    have hnat : (547370847 : ℕ)^8279*100000000000000^6231 ≤ 13290021614527^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547370847 2500000000 13290021614527 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358808949/2500000000 : ℝ)^8279 ≤ (44482602276801/100000000000000 : ℝ)^6231 := by
    have hnat : (1358808949 : ℕ)^8279*100000000000000^6231 ≤ 44482602276801^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358808949 2500000000 44482602276801 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226512093/10000000000 : ℝ)^8279 ≤ (8445475217737/20000000000000 : ℝ)^6231 := by
    have hnat : (5226512093 : ℕ)^8279*20000000000000^6231 ≤ 8445475217737^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226512093 10000000000 8445475217737 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547370847/2500000000 : ℝ), (1358808949/2500000000 : ℝ), (5226512093/10000000000 : ℝ)] ![(13290021614527/100000000000000 : ℝ), (44482602276801/100000000000000 : ℝ), (8445475217737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547370847/2500000000 : ℝ)|^8279 ≤ (13290021614527/100000000000000 : ℝ)^6231
        have hw : |(-547370847/2500000000 : ℝ)|=(547370847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358808949/2500000000 : ℝ)|^8279 ≤ (44482602276801/100000000000000 : ℝ)^6231
        have hw : |(1358808949/2500000000 : ℝ)|=(1358808949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226512093/10000000000 : ℝ)|^8279 ≤ (8445475217737/20000000000000 : ℝ)^6231
        have hw : |(5226512093/10000000000 : ℝ)|=(5226512093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355179607/10000000000 : ℝ)*x 0 + (-574078479/2500000000 : ℝ)*x 1 + (1306628011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355179607/10000000000 : ℝ)^8279 ≤ (5451772531957/12500000000000 : ℝ)^6231 := by
    have hnat : (5355179607 : ℕ)^8279*12500000000000^6231 ≤ 5451772531957^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355179607 10000000000 5451772531957 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574078479/2500000000 : ℝ)^8279 ≤ (1415844416367/10000000000000 : ℝ)^6231 := by
    have hnat : (574078479 : ℕ)^8279*10000000000000^6231 ≤ 1415844416367^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574078479 2500000000 1415844416367 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306628011/2500000000 : ℝ)^8279 ≤ (42227375562669/100000000000000 : ℝ)^6231 := by
    have hnat : (1306628011 : ℕ)^8279*100000000000000^6231 ≤ 42227375562669^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306628011 2500000000 42227375562669 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355179607/10000000000 : ℝ), (-574078479/2500000000 : ℝ), (1306628011/2500000000 : ℝ)] ![(5451772531957/12500000000000 : ℝ), (1415844416367/10000000000000 : ℝ), (42227375562669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355179607/10000000000 : ℝ)|^8279 ≤ (5451772531957/12500000000000 : ℝ)^6231
        have hw : |(5355179607/10000000000 : ℝ)|=(5355179607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-574078479/2500000000 : ℝ)|^8279 ≤ (1415844416367/10000000000000 : ℝ)^6231
        have hw : |(-574078479/2500000000 : ℝ)|=(574078479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306628011/2500000000 : ℝ)|^8279 ≤ (42227375562669/100000000000000 : ℝ)^6231
        have hw : |(1306628011/2500000000 : ℝ)|=(1306628011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355179517/10000000000 : ℝ)*x 0 + (5226512471/10000000000 : ℝ)*x 1 + (-574078369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355179517/10000000000 : ℝ)^8279 ≤ (5451772410219/12500000000000 : ℝ)^6231 := by
    have hnat : (5355179517 : ℕ)^8279*12500000000000^6231 ≤ 5451772410219^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355179517 10000000000 5451772410219 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226512471/10000000000 : ℝ)^8279 ≤ (42227380146517/100000000000000 : ℝ)^6231 := by
    have hnat : (5226512471 : ℕ)^8279*100000000000000^6231 ≤ 42227380146517^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226512471 10000000000 42227380146517 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574078369/2500000000 : ℝ)^8279 ≤ (1415844055907/10000000000000 : ℝ)^6231 := by
    have hnat : (574078369 : ℕ)^8279*10000000000000^6231 ≤ 1415844055907^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574078369 2500000000 1415844055907 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355179517/10000000000 : ℝ), (5226512471/10000000000 : ℝ), (-574078369/2500000000 : ℝ)] ![(5451772410219/12500000000000 : ℝ), (42227380146517/100000000000000 : ℝ), (1415844055907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355179517/10000000000 : ℝ)|^8279 ≤ (5451772410219/12500000000000 : ℝ)^6231
        have hw : |(5355179517/10000000000 : ℝ)|=(5355179517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226512471/10000000000 : ℝ)|^8279 ≤ (42227380146517/100000000000000 : ℝ)^6231
        have hw : |(5226512471/10000000000 : ℝ)|=(5226512471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574078369/2500000000 : ℝ)|^8279 ≤ (1415844055907/10000000000000 : ℝ)^6231
        have hw : |(-574078369/2500000000 : ℝ)|=(574078369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184987819/5000000000 : ℝ)*x 0 + (4169486043/10000000000 : ℝ)*x 1 + (183207169/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184987819/5000000000 : ℝ)^8279 ≤ (1664492935393/5000000000000 : ℝ)^6231 := by
    have hnat : (2184987819 : ℕ)^8279*5000000000000^6231 ≤ 1664492935393^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184987819 5000000000 1664492935393 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169486043/10000000000 : ℝ)^8279 ≤ (31276025480263/100000000000000 : ℝ)^6231 := by
    have hnat : (4169486043 : ℕ)^8279*100000000000000^6231 ≤ 31276025480263^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169486043 10000000000 31276025480263 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183207169/400000000 : ℝ)^8279 ≤ (17717057897559/50000000000000 : ℝ)^6231 := by
    have hnat : (183207169 : ℕ)^8279*50000000000000^6231 ≤ 17717057897559^6231*400000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183207169 400000000 17717057897559 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184987819/5000000000 : ℝ), (4169486043/10000000000 : ℝ), (183207169/400000000 : ℝ)] ![(1664492935393/5000000000000 : ℝ), (31276025480263/100000000000000 : ℝ), (17717057897559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184987819/5000000000 : ℝ)|^8279 ≤ (1664492935393/5000000000000 : ℝ)^6231
        have hw : |(2184987819/5000000000 : ℝ)|=(2184987819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169486043/10000000000 : ℝ)|^8279 ≤ (31276025480263/100000000000000 : ℝ)^6231
        have hw : |(4169486043/10000000000 : ℝ)|=(4169486043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183207169/400000000 : ℝ)|^8279 ≤ (17717057897559/50000000000000 : ℝ)^6231
        have hw : |(183207169/400000000 : ℝ)|=(183207169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-68422019/312500000 : ℝ)*x 0 + (5227355307/10000000000 : ℝ)*x 1 + (5434387583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68422019/312500000 : ℝ)^8279 ≤ (6645096377009/50000000000000 : ℝ)^6231 := by
    have hnat : (68422019 : ℕ)^8279*50000000000000^6231 ≤ 6645096377009^6231*312500000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68422019 312500000 6645096377009 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227355307/10000000000 : ℝ)^8279 ≤ (42236428235533/100000000000000 : ℝ)^6231 := by
    have hnat : (5227355307 : ℕ)^8279*100000000000000^6231 ≤ 42236428235533^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227355307 10000000000 42236428235533 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434387583/10000000000 : ℝ)^8279 ≤ (11118344747501/25000000000000 : ℝ)^6231 := by
    have hnat : (5434387583 : ℕ)^8279*25000000000000^6231 ≤ 11118344747501^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434387583 10000000000 11118344747501 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68422019/312500000 : ℝ), (5227355307/10000000000 : ℝ), (5434387583/10000000000 : ℝ)] ![(6645096377009/50000000000000 : ℝ), (42236428235533/100000000000000 : ℝ), (11118344747501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68422019/312500000 : ℝ)|^8279 ≤ (6645096377009/50000000000000 : ℝ)^6231
        have hw : |(-68422019/312500000 : ℝ)|=(68422019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227355307/10000000000 : ℝ)|^8279 ≤ (42236428235533/100000000000000 : ℝ)^6231
        have hw : |(5227355307/10000000000 : ℝ)|=(5227355307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434387583/10000000000 : ℝ)|^8279 ≤ (11118344747501/25000000000000 : ℝ)^6231
        have hw : |(5434387583/10000000000 : ℝ)|=(5434387583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060504261/2000000000 : ℝ)*x 0 + (-2088438229/10000000000 : ℝ)*x 1 + (5434387879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060504261/2000000000 : ℝ)^8279 ≤ (21522639609749/50000000000000 : ℝ)^6231 := by
    have hnat : (1060504261 : ℕ)^8279*50000000000000^6231 ≤ 21522639609749^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060504261 2000000000 21522639609749 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088438229/10000000000 : ℝ)^8279 ≤ (624066928021/5000000000000 : ℝ)^6231 := by
    have hnat : (2088438229 : ℕ)^8279*5000000000000^6231 ≤ 624066928021^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088438229 10000000000 624066928021 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434387879/10000000000 : ℝ)^8279 ≤ (22236691104281/50000000000000 : ℝ)^6231 := by
    have hnat : (5434387879 : ℕ)^8279*50000000000000^6231 ≤ 22236691104281^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434387879 10000000000 22236691104281 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060504261/2000000000 : ℝ), (-2088438229/10000000000 : ℝ), (5434387879/10000000000 : ℝ)] ![(21522639609749/50000000000000 : ℝ), (624066928021/5000000000000 : ℝ), (22236691104281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060504261/2000000000 : ℝ)|^8279 ≤ (21522639609749/50000000000000 : ℝ)^6231
        have hw : |(1060504261/2000000000 : ℝ)|=(1060504261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088438229/10000000000 : ℝ)|^8279 ≤ (624066928021/5000000000000 : ℝ)^6231
        have hw : |(-2088438229/10000000000 : ℝ)|=(2088438229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434387879/10000000000 : ℝ)|^8279 ≤ (22236691104281/50000000000000 : ℝ)^6231
        have hw : |(5434387879/10000000000 : ℝ)|=(5434387879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325630367/2500000000 : ℝ)*x 0 + (1358596903/2500000000 : ℝ)*x 1 + (-2088438373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325630367/2500000000 : ℝ)^8279 ≤ (43045280977627/100000000000000 : ℝ)^6231 := by
    have hnat : (1325630367 : ℕ)^8279*100000000000000^6231 ≤ 43045280977627^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325630367 2500000000 43045280977627 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358596903/2500000000 : ℝ)^8279 ≤ (8894675861067/20000000000000 : ℝ)^6231 := by
    have hnat : (1358596903 : ℕ)^8279*20000000000000^6231 ≤ 8894675861067^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358596903 2500000000 8894675861067 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088438373/10000000000 : ℝ)^8279 ≤ (12481339703883/100000000000000 : ℝ)^6231 := by
    have hnat : (2088438373 : ℕ)^8279*100000000000000^6231 ≤ 12481339703883^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088438373 10000000000 12481339703883 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325630367/2500000000 : ℝ), (1358596903/2500000000 : ℝ), (-2088438373/10000000000 : ℝ)] ![(43045280977627/100000000000000 : ℝ), (8894675861067/20000000000000 : ℝ), (12481339703883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325630367/2500000000 : ℝ)|^8279 ≤ (43045280977627/100000000000000 : ℝ)^6231
        have hw : |(1325630367/2500000000 : ℝ)|=(1325630367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358596903/2500000000 : ℝ)|^8279 ≤ (8894675861067/20000000000000 : ℝ)^6231
        have hw : |(1358596903/2500000000 : ℝ)|=(1358596903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088438373/10000000000 : ℝ)|^8279 ≤ (12481339703883/100000000000000 : ℝ)^6231
        have hw : |(-2088438373/10000000000 : ℝ)|=(2088438373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s3_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370016919/10000000000 : ℝ)*x 0 + (4578521027/10000000000 : ℝ)*x 1 + (4171154107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370016919/10000000000 : ℝ)^8279 ≤ (8322569135507/25000000000000 : ℝ)^6231 := by
    have hnat : (4370016919 : ℕ)^8279*25000000000000^6231 ≤ 8322569135507^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370016919 10000000000 8322569135507 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4578521027/10000000000 : ℝ)^8279 ≤ (3541707186269/10000000000000 : ℝ)^6231 := by
    have hnat : (4578521027 : ℕ)^8279*10000000000000^6231 ≤ 3541707186269^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578521027 10000000000 3541707186269 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171154107/10000000000 : ℝ)^8279 ≤ (31292651581653/100000000000000 : ℝ)^6231 := by
    have hnat : (4171154107 : ℕ)^8279*100000000000000^6231 ≤ 31292651581653^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171154107 10000000000 31292651581653 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370016919/10000000000 : ℝ), (4578521027/10000000000 : ℝ), (4171154107/10000000000 : ℝ)] ![(8322569135507/25000000000000 : ℝ), (3541707186269/10000000000000 : ℝ), (31292651581653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370016919/10000000000 : ℝ)|^8279 ≤ (8322569135507/25000000000000 : ℝ)^6231
        have hw : |(4370016919/10000000000 : ℝ)|=(4370016919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4578521027/10000000000 : ℝ)|^8279 ≤ (3541707186269/10000000000000 : ℝ)^6231
        have hw : |(4578521027/10000000000 : ℝ)|=(4578521027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171154107/10000000000 : ℝ)|^8279 ≤ (31292651581653/100000000000000 : ℝ)^6231
        have hw : |(4171154107/10000000000 : ℝ)|=(4171154107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10461/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7439/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4169/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4169/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4169/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4169/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4169/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4169/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8809/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (5437529176930269/100000000000000000000 : ℝ) := by
    have hpowers : (8809/100000 : ℝ)^4139 ≤ (5437529176930269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8809 : ℕ)^4139*100000000000000000000^1024 ≤ 5437529176930269^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8809 100000 5437529176930269 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8809/100000 : ℝ)) (X := (5437529176930269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4169/25000 : ℝ) ^ (4139/1024 : ℝ) ≤ (717301076244957/1000000000000000000 : ℝ) := by
    have hpowers : (4169/25000 : ℝ)^4139 ≤ (717301076244957/1000000000000000000 : ℝ)^1024 := by
      have hnat : (4169 : ℕ)^4139*1000000000000000000^1024 ≤ 717301076244957^1024*25000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4169 25000 717301076244957 1000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4169/25000 : ℝ)) (X := (717301076244957/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005437529176930269/50000000000000000000 : ℝ) ≤ (10000269040929349/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50005437529176930269/50000000000000000000 : ℝ)^1024 ≤ (10000269040929349/10000000000000000 : ℝ)^4139 := by
      have hnat : (50005437529176930269 : ℕ)^1024*10000000000000000^4139 ≤ 10000269040929349^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005437529176930269 50000000000000000000 10000269040929349 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000269040929349/10000000000000000 : ℝ)) (X := (50005437529176930269/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077167636801425969/100000000000000000000 : ℝ) ≤ (5000954297229221/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (100077167636801425969/100000000000000000000 : ℝ)^1024 ≤ (5000954297229221/5000000000000000 : ℝ)^4139 := by
      have hnat : (100077167636801425969 : ℕ)^1024*5000000000000000^4139 ≤ 5000954297229221^4139*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077167636801425969 100000000000000000000 5000954297229221 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000954297229221/5000000000000000 : ℝ)) (X := (100077167636801425969/100000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500717301076244957/500000000000000000 : ℝ) ≤ (2000709629597507/2000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (500717301076244957/500000000000000000 : ℝ)^1024 ≤ (2000709629597507/2000000000000000 : ℝ)^4139 := by
      have hnat : (500717301076244957 : ℕ)^1024*2000000000000000^4139 ≤ 2000709629597507^4139*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500717301076244957 500000000000000000 2000709629597507 2000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000709629597507/2000000000000000 : ℝ)) (X := (500717301076244957/500000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5437529176930269/100000000000000000000 : ℝ) ≤ ((78643230890915628109/78670000000000000000 : ℝ)+2*(1639553529093/786700000000000 : ℝ)*(8809/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (78643230890915628109/78670000000000000000 : ℝ)+2*(1639553529093/786700000000000 : ℝ)*(8809/100000 : ℝ)=(10000269040929349/10000000000000000 : ℝ) by norm_num, show 1+2*(5437529176930269/100000000000000000000 : ℝ)=(50005437529176930269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(717301076244957/1000000000000000000 : ℝ)+(5437529176930269/100000000000000000000 : ℝ) ≤ ((78643230890915628109/78670000000000000000 : ℝ)+(1639553529093/786700000000000 : ℝ)*((4169/25000 : ℝ)+(8809/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (78643230890915628109/78670000000000000000 : ℝ)+(1639553529093/786700000000000 : ℝ)*((4169/25000 : ℝ)+(8809/100000 : ℝ))=(5000954297229221/5000000000000000 : ℝ) by norm_num, show 1+(717301076244957/1000000000000000000 : ℝ)+(5437529176930269/100000000000000000000 : ℝ)=(100077167636801425969/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(717301076244957/1000000000000000000 : ℝ) ≤ ((78643230890915628109/78670000000000000000 : ℝ)+2*(1639553529093/786700000000000 : ℝ)*(4169/25000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (78643230890915628109/78670000000000000000 : ℝ)+2*(1639553529093/786700000000000 : ℝ)*(4169/25000 : ℝ)=(2000709629597507/2000000000000000 : ℝ) by norm_num, show 1+2*(717301076244957/1000000000000000000 : ℝ)=(500717301076244957/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (78643230890915628109/78670000000000000000 : ℝ)*(X 1 0+X 2 0)+(1639553529093/786700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (4169/25000 : ℝ)) (c := (78643230890915628109/78670000000000000000 : ℝ)) (alpha := (1639553529093/786700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (78643230890915628109/78670000000000000000 : ℝ)*(X 0 1+X 2 1)+(1639553529093/786700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (4169/25000 : ℝ)) (c := (78643230890915628109/78670000000000000000 : ℝ)) (alpha := (1639553529093/786700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (78643230890915628109/78670000000000000000 : ℝ)*(X 0 2+X 1 2)+(1639553529093/786700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (4169/25000 : ℝ)) (c := (78643230890915628109/78670000000000000000 : ℝ)) (alpha := (1639553529093/786700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-547370847/2500000000 : ℝ)*X 0 0+(1358808949/2500000000 : ℝ)*X 0 1+(5226512093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355179607/10000000000 : ℝ)*X 1 0+(-574078479/2500000000 : ℝ)*X 1 1+(1306628011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355179517/10000000000 : ℝ)*X 2 0+(5226512471/10000000000 : ℝ)*X 2 1+(-574078369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184987819/5000000000 : ℝ)*X 0 0+(4169486043/10000000000 : ℝ)*X 0 1+(183207169/400000000 : ℝ)*X 0 2+(2184987819/5000000000 : ℝ)*X 1 0+(4169486043/10000000000 : ℝ)*X 1 1+(183207169/400000000 : ℝ)*X 1 2+(2184987819/5000000000 : ℝ)*X 2 0+(4169486043/10000000000 : ℝ)*X 2 1+(183207169/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68422019/312500000 : ℝ)*X 0 0+(5227355307/10000000000 : ℝ)*X 0 1+(5434387583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060504261/2000000000 : ℝ)*X 1 0+(-2088438229/10000000000 : ℝ)*X 1 1+(5434387879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325630367/2500000000 : ℝ)*X 2 0+(1358596903/2500000000 : ℝ)*X 2 1+(-2088438373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370016919/10000000000 : ℝ)*X 0 0+(4578521027/10000000000 : ℝ)*X 0 1+(4171154107/10000000000 : ℝ)*X 0 2+(4370016919/10000000000 : ℝ)*X 1 0+(4578521027/10000000000 : ℝ)*X 1 1+(4171154107/10000000000 : ℝ)*X 1 2+(4370016919/10000000000 : ℝ)*X 2 0+(4578521027/10000000000 : ℝ)*X 2 1+(4171154107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18838381599077372095507274757/1966750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (600216977/25000000000000 : ℝ)*(base19) + (1882179393/100000000000000 : ℝ)*(base23) + (29330881/12500000000000 : ℝ)*(lower2) + (9489597/6250000000000 : ℝ)*(upper3) + (29383849/12500000000000 : ℝ)*(upper5) + (1806514009163091/50000000000000 : ℝ)*(major0) + (1806514009163091/50000000000000 : ℝ)*(major1) + (1806514009163091/50000000000000 : ℝ)*(major2) + (4791062975319139/100000000000000 : ℝ)*(sp0) + (4791107272665477/100000000000000 : ℝ)*(sp1) + (598888473919249/12500000000000 : ℝ)*(sp2) + (19022864853649/781250000000 : ℝ)*(sp3) + (23349107123/50000000000000 : ℝ)*(sp4) + (2417821353/12500000000000 : ℝ)*(sp7) + (304368255479737/12500000000000 : ℝ)*(f.failure) + (958221934706677/20000000000000 : ℝ)*(f.sum) + (127761757901553/19667500000000000000000000000 : ℝ)*base65 + (22046460308253775081/3933500000000000000000000000000000 : ℝ)*base68 + (29739258192254275081/3933500000000000000000000000000000 : ℝ)*base70 + (52706893960057275081/3933500000000000000000000000000000 : ℝ)*base72 + (139323106608453/19667500000000000000000000000 : ℝ)*base73 + (47870468287005224919/3933500000000000000000000000000000 : ℝ)*base75 + (38978057152555224919/3933500000000000000000000000000000 : ℝ)*base77 + (22423411806364775081/3933500000000000000000000000000000 : ℝ)*base80 + (35887624952517/19667500000000000000000000000 : ℝ)*base82 + (1887453/625000000000000000000 : ℝ)*base90 + (1887453/625000000000000000000 : ℝ)*base92 + (1887453/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4730228021124574994150011083/491687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1785115919/100000000000000 : ℝ)*(base19) + (1106752743/50000000000000 : ℝ)*(base23) + (283485647/100000000000000 : ℝ)*(upper3) + (15042983/12500000000000 : ℝ)*(lower4) + (108551051/100000000000000 : ℝ)*(upper5) + (455309388647171/12500000000000 : ℝ)*(major0) + (455309388647171/12500000000000 : ℝ)*(major1) + (455309388647171/12500000000000 : ℝ)*(major2) + (32447337159/100000000000000 : ℝ)*(sp1) + (18889917321/50000000000000 : ℝ)*(sp2) + (2415079214306399/50000000000000 : ℝ)*(sp4) + (4830124196159721/100000000000000 : ℝ)*(sp5) + (483011843527267/10000000000000 : ℝ)*(sp6) + (153424466816381/6250000000000 : ℝ)*(sp7) + (153424466816381/6250000000000 : ℝ)*(f.failure) + (2415079214306399/50000000000000 : ℝ)*(f.sum) + (24396080640147/4916875000000000000000000000 : ℝ)*base66 + (3100251213174520361/983375000000000000000000000000000 : ℝ)*base68 + (4920544774128479639/983375000000000000000000000000000 : ℝ)*base69 + (992055566235520361/983375000000000000000000000000000 : ℝ)*base72 + (215224963689841/39335000000000000000000000000 : ℝ)*base74 + (2927659104415104639/983375000000000000000000000000000 : ℝ)*base75 + (2470766685570479639/983375000000000000000000000000000 : ℝ)*base77 + (6588386626198979639/983375000000000000000000000000000 : ℝ)*base79 + (110037738915363/19667500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (716911/312500000000000000000 : ℝ)*base89 + (716911/312500000000000000000 : ℝ)*base91 + (716911/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7439/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s4_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548242813/2500000000 : ℝ)*x 0 + (5404731961/10000000000 : ℝ)*x 1 + (5254736469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548242813/2500000000 : ℝ)^8279 ≤ (3329539646447/25000000000000 : ℝ)^6231 := by
    have hnat : (548242813 : ℕ)^8279*25000000000000^6231 ≤ 3329539646447^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548242813 2500000000 3329539646447 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404731961/10000000000 : ℝ)^8279 ≤ (8830241581397/20000000000000 : ℝ)^6231 := by
    have hnat : (5404731961 : ℕ)^8279*20000000000000^6231 ≤ 8830241581397^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404731961 10000000000 8830241581397 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254736469/10000000000 : ℝ)^8279 ≤ (10632658371953/25000000000000 : ℝ)^6231 := by
    have hnat : (5254736469 : ℕ)^8279*25000000000000^6231 ≤ 10632658371953^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254736469 10000000000 10632658371953 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548242813/2500000000 : ℝ), (5404731961/10000000000 : ℝ), (5254736469/10000000000 : ℝ)] ![(3329539646447/25000000000000 : ℝ), (8830241581397/20000000000000 : ℝ), (10632658371953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548242813/2500000000 : ℝ)|^8279 ≤ (3329539646447/25000000000000 : ℝ)^6231
        have hw : |(-548242813/2500000000 : ℝ)|=(548242813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404731961/10000000000 : ℝ)|^8279 ≤ (8830241581397/20000000000000 : ℝ)^6231
        have hw : |(5404731961/10000000000 : ℝ)|=(5404731961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254736469/10000000000 : ℝ)|^8279 ≤ (10632658371953/25000000000000 : ℝ)^6231
        have hw : |(5254736469/10000000000 : ℝ)|=(5254736469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336901549/2500000000 : ℝ)*x 0 + (-2269245411/10000000000 : ℝ)*x 1 + (5254736281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336901549/2500000000 : ℝ)^8279 ≤ (43532246219117/100000000000000 : ℝ)^6231 := by
    have hnat : (1336901549 : ℕ)^8279*100000000000000^6231 ≤ 43532246219117^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336901549 2500000000 43532246219117 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269245411/10000000000 : ℝ)^8279 ≤ (13937122304861/100000000000000 : ℝ)^6231 := by
    have hnat : (2269245411 : ℕ)^8279*100000000000000^6231 ≤ 13937122304861^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269245411 10000000000 13937122304861 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254736281/10000000000 : ℝ)^8279 ≤ (8506126293211/20000000000000 : ℝ)^6231 := by
    have hnat : (5254736281 : ℕ)^8279*20000000000000^6231 ≤ 8506126293211^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254736281 10000000000 8506126293211 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336901549/2500000000 : ℝ), (-2269245411/10000000000 : ℝ), (5254736281/10000000000 : ℝ)] ![(43532246219117/100000000000000 : ℝ), (13937122304861/100000000000000 : ℝ), (8506126293211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336901549/2500000000 : ℝ)|^8279 ≤ (43532246219117/100000000000000 : ℝ)^6231
        have hw : |(1336901549/2500000000 : ℝ)|=(1336901549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269245411/10000000000 : ℝ)|^8279 ≤ (13937122304861/100000000000000 : ℝ)^6231
        have hw : |(-2269245411/10000000000 : ℝ)|=(2269245411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254736281/10000000000 : ℝ)|^8279 ≤ (8506126293211/20000000000000 : ℝ)^6231
        have hw : |(5254736281/10000000000 : ℝ)|=(5254736281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347606343/10000000000 : ℝ)*x 0 + (525473627/1000000000 : ℝ)*x 1 + (-2269245231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347606343/10000000000 : ℝ)^8279 ≤ (680191372017/1562500000000 : ℝ)^6231 := by
    have hnat : (5347606343 : ℕ)^8279*1562500000000^6231 ≤ 680191372017^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347606343 10000000000 680191372017 1562500000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525473627/1000000000 : ℝ)^8279 ≤ (42530631347761/100000000000000 : ℝ)^6231 := by
    have hnat : (525473627 : ℕ)^8279*100000000000000^6231 ≤ 42530631347761^6231*1000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525473627 1000000000 42530631347761 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269245231/10000000000 : ℝ)^8279 ≤ (3484280208997/25000000000000 : ℝ)^6231 := by
    have hnat : (2269245231 : ℕ)^8279*25000000000000^6231 ≤ 3484280208997^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269245231 10000000000 3484280208997 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347606343/10000000000 : ℝ), (525473627/1000000000 : ℝ), (-2269245231/10000000000 : ℝ)] ![(680191372017/1562500000000 : ℝ), (42530631347761/100000000000000 : ℝ), (3484280208997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347606343/10000000000 : ℝ)|^8279 ≤ (680191372017/1562500000000 : ℝ)^6231
        have hw : |(5347606343/10000000000 : ℝ)|=(5347606343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525473627/1000000000 : ℝ)|^8279 ≤ (42530631347761/100000000000000 : ℝ)^6231
        have hw : |(525473627/1000000000 : ℝ)|=(525473627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2269245231/10000000000 : ℝ)|^8279 ≤ (3484280208997/25000000000000 : ℝ)^6231
        have hw : |(-2269245231/10000000000 : ℝ)|=(2269245231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093012809/2500000000 : ℝ)*x 0 + (1056748067/2500000000 : ℝ)*x 1 + (226106517/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093012809/2500000000 : ℝ)^8279 ≤ (33310868908767/100000000000000 : ℝ)^6231 := by
    have hnat : (1093012809 : ℕ)^8279*100000000000000^6231 ≤ 33310868908767^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093012809 2500000000 33310868908767 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056748067/2500000000 : ℝ)^8279 ≤ (1990654058971/6250000000000 : ℝ)^6231 := by
    have hnat : (1056748067 : ℕ)^8279*6250000000000^6231 ≤ 1990654058971^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056748067 2500000000 1990654058971 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226106517/500000000 : ℝ)^8279 ≤ (6967733226871/20000000000000 : ℝ)^6231 := by
    have hnat : (226106517 : ℕ)^8279*20000000000000^6231 ≤ 6967733226871^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226106517 500000000 6967733226871 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093012809/2500000000 : ℝ), (1056748067/2500000000 : ℝ), (226106517/500000000 : ℝ)] ![(33310868908767/100000000000000 : ℝ), (1990654058971/6250000000000 : ℝ), (6967733226871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093012809/2500000000 : ℝ)|^8279 ≤ (33310868908767/100000000000000 : ℝ)^6231
        have hw : |(1093012809/2500000000 : ℝ)|=(1093012809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056748067/2500000000 : ℝ)|^8279 ≤ (1990654058971/6250000000000 : ℝ)^6231
        have hw : |(1056748067/2500000000 : ℝ)|=(1056748067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226106517/500000000 : ℝ)|^8279 ≤ (6967733226871/20000000000000 : ℝ)^6231
        have hw : |(226106517/500000000 : ℝ)|=(226106517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192979343/10000000000 : ℝ)*x 0 + (2627586261/5000000000 : ℝ)*x 1 + (675536737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192979343/10000000000 : ℝ)^8279 ≤ (665911193693/5000000000000 : ℝ)^6231 := by
    have hnat : (2192979343 : ℕ)^8279*5000000000000^6231 ≤ 665911193693^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192979343 10000000000 665911193693 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627586261/5000000000 : ℝ)^8279 ≤ (4253532287663/10000000000000 : ℝ)^6231 := by
    have hnat : (2627586261 : ℕ)^8279*10000000000000^6231 ≤ 4253532287663^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627586261 5000000000 4253532287663 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675536737/1250000000 : ℝ)^8279 ≤ (4414645322657/10000000000000 : ℝ)^6231 := by
    have hnat : (675536737 : ℕ)^8279*10000000000000^6231 ≤ 4414645322657^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675536737 1250000000 4414645322657 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192979343/10000000000 : ℝ), (2627586261/5000000000 : ℝ), (675536737/1250000000 : ℝ)] ![(665911193693/5000000000000 : ℝ), (4253532287663/10000000000000 : ℝ), (4414645322657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192979343/10000000000 : ℝ)|^8279 ≤ (665911193693/5000000000000 : ℝ)^6231
        have hw : |(-2192979343/10000000000 : ℝ)|=(2192979343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627586261/5000000000 : ℝ)|^8279 ≤ (4253532287663/10000000000000 : ℝ)^6231
        have hw : |(2627586261/5000000000 : ℝ)|=(2627586261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675536737/1250000000 : ℝ)|^8279 ≤ (4414645322657/10000000000000 : ℝ)^6231
        have hw : |(675536737/1250000000 : ℝ)|=(675536737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309767967/10000000000 : ℝ)*x 0 + (-529921829/2500000000 : ℝ)*x 1 + (5404293911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309767967/10000000000 : ℝ)^8279 ≤ (21561729886689/50000000000000 : ℝ)^6231 := by
    have hnat : (5309767967 : ℕ)^8279*50000000000000^6231 ≤ 21561729886689^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309767967 10000000000 21561729886689 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529921829/2500000000 : ℝ)^8279 ≤ (1591260853637/12500000000000 : ℝ)^6231 := by
    have hnat : (529921829 : ℕ)^8279*12500000000000^6231 ≤ 1591260853637^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529921829 2500000000 1591260853637 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404293911/10000000000 : ℝ)^8279 ≤ (70634325423/160000000000 : ℝ)^6231 := by
    have hnat : (5404293911 : ℕ)^8279*160000000000^6231 ≤ 70634325423^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404293911 10000000000 70634325423 160000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309767967/10000000000 : ℝ), (-529921829/2500000000 : ℝ), (5404293911/10000000000 : ℝ)] ![(21561729886689/50000000000000 : ℝ), (1591260853637/12500000000000 : ℝ), (70634325423/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309767967/10000000000 : ℝ)|^8279 ≤ (21561729886689/50000000000000 : ℝ)^6231
        have hw : |(5309767967/10000000000 : ℝ)|=(5309767967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529921829/2500000000 : ℝ)|^8279 ≤ (1591260853637/12500000000000 : ℝ)^6231
        have hw : |(-529921829/2500000000 : ℝ)|=(529921829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404293911/10000000000 : ℝ)|^8279 ≤ (70634325423/160000000000 : ℝ)^6231
        have hw : |(5404293911/10000000000 : ℝ)|=(5404293911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327441969/2500000000 : ℝ)*x 0 + (135107347/250000000 : ℝ)*x 1 + (-1059843741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327441969/2500000000 : ℝ)^8279 ≤ (8624691758281/20000000000000 : ℝ)^6231 := by
    have hnat : (1327441969 : ℕ)^8279*20000000000000^6231 ≤ 8624691758281^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327441969 2500000000 8624691758281 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135107347/250000000 : ℝ)^8279 ≤ (44146453052911/100000000000000 : ℝ)^6231 := by
    have hnat : (135107347 : ℕ)^8279*100000000000000^6231 ≤ 44146453052911^6231*250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135107347 250000000 44146453052911 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059843741/5000000000 : ℝ)^8279 ≤ (2546017630741/20000000000000 : ℝ)^6231 := by
    have hnat : (1059843741 : ℕ)^8279*20000000000000^6231 ≤ 2546017630741^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059843741 5000000000 2546017630741 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327441969/2500000000 : ℝ), (135107347/250000000 : ℝ), (-1059843741/5000000000 : ℝ)] ![(8624691758281/20000000000000 : ℝ), (44146453052911/100000000000000 : ℝ), (2546017630741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327441969/2500000000 : ℝ)|^8279 ≤ (8624691758281/20000000000000 : ℝ)^6231
        have hw : |(1327441969/2500000000 : ℝ)|=(1327441969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135107347/250000000 : ℝ)|^8279 ≤ (44146453052911/100000000000000 : ℝ)^6231
        have hw : |(135107347/250000000 : ℝ)|=(135107347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059843741/5000000000 : ℝ)|^8279 ≤ (2546017630741/20000000000000 : ℝ)^6231
        have hw : |(-1059843741/5000000000 : ℝ)|=(1059843741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s4_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372066639/10000000000 : ℝ)*x 0 + (565159011/1250000000 : ℝ)*x 1 + (211392707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372066639/10000000000 : ℝ)^8279 ≤ (8327756209399/25000000000000 : ℝ)^6231 := by
    have hnat : (4372066639 : ℕ)^8279*25000000000000^6231 ≤ 8327756209399^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372066639 10000000000 8327756209399 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565159011/1250000000 : ℝ)^8279 ≤ (4353735146633/12500000000000 : ℝ)^6231 := by
    have hnat : (565159011 : ℕ)^8279*12500000000000^6231 ≤ 4353735146633^6231*1250000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565159011 1250000000 4353735146633 12500000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211392707/500000000 : ℝ)^8279 ≤ (1592954698477/5000000000000 : ℝ)^6231 := by
    have hnat : (211392707 : ℕ)^8279*5000000000000^6231 ≤ 1592954698477^6231*500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211392707 500000000 1592954698477 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372066639/10000000000 : ℝ), (565159011/1250000000 : ℝ), (211392707/500000000 : ℝ)] ![(8327756209399/25000000000000 : ℝ), (4353735146633/12500000000000 : ℝ), (1592954698477/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372066639/10000000000 : ℝ)|^8279 ≤ (8327756209399/25000000000000 : ℝ)^6231
        have hw : |(4372066639/10000000000 : ℝ)|=(4372066639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565159011/1250000000 : ℝ)|^8279 ≤ (4353735146633/12500000000000 : ℝ)^6231
        have hw : |(565159011/1250000000 : ℝ)|=(565159011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211392707/500000000 : ℝ)|^8279 ≤ (1592954698477/5000000000000 : ℝ)^6231
        have hw : |(211392707/500000000 : ℝ)|=(211392707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1383/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7439/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7439/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7439/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10461/100000 : ℝ) ^ (4139/1024 : ℝ) ≤ (5446186970125673/50000000000000000000 : ℝ) := by
    have hpowers : (10461/100000 : ℝ)^4139 ≤ (5446186970125673/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10461 : ℕ)^4139*50000000000000000000^1024 ≤ 5446186970125673^1024*100000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10461 100000 5446186970125673 50000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10461/100000 : ℝ)) (X := (5446186970125673/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7439/50000 : ℝ) ^ (4139/1024 : ℝ) ≤ (45230517141919701/100000000000000000000 : ℝ) := by
    have hpowers : (7439/50000 : ℝ)^4139 ≤ (45230517141919701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7439 : ℕ)^4139*100000000000000000000^1024 ≤ 45230517141919701^1024*50000^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7439 50000 45230517141919701 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7439/50000 : ℝ)) (X := (45230517141919701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005446186970125673/25000000000000000000 : ℝ) ≤ (10000538916486653/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (25005446186970125673/25000000000000000000 : ℝ)^1024 ≤ (10000538916486653/10000000000000000 : ℝ)^4139 := by
      have hnat : (25005446186970125673 : ℕ)^1024*10000000000000000^4139 ≤ 10000538916486653^4139*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005446186970125673 25000000000000000000 10000538916486653 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538916486653/10000000000000000 : ℝ)) (X := (25005446186970125673/25000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056122891082171047/100000000000000000000 : ℝ) ≤ (5000694101321691/5000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (100056122891082171047/100000000000000000000 : ℝ)^1024 ≤ (5000694101321691/5000000000000000 : ℝ)^4139 := by
      have hnat : (100056122891082171047 : ℕ)^1024*5000000000000000^4139 ≤ 5000694101321691^4139*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056122891082171047 100000000000000000000 5000694101321691 5000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000694101321691/5000000000000000 : ℝ)) (X := (100056122891082171047/100000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045230517141919701/50000000000000000000 : ℝ) ≤ (10002237488800111/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50045230517141919701/50000000000000000000 : ℝ)^1024 ≤ (10002237488800111/10000000000000000 : ℝ)^4139 := by
      have hnat : (50045230517141919701 : ℕ)^1024*10000000000000000^4139 ≤ 10002237488800111^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045230517141919701 50000000000000000000 10002237488800111 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002237488800111/10000000000000000 : ℝ)) (X := (50045230517141919701/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5446186970125673/50000000000000000000 : ℝ) ≤ ((44154611629150462163/44170000000000000000 : ℝ)+2*(849286156729/441700000000000 : ℝ)*(10461/100000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (44154611629150462163/44170000000000000000 : ℝ)+2*(849286156729/441700000000000 : ℝ)*(10461/100000 : ℝ)=(10000538916486653/10000000000000000 : ℝ) by norm_num, show 1+2*(5446186970125673/50000000000000000000 : ℝ)=(25005446186970125673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45230517141919701/100000000000000000000 : ℝ)+(5446186970125673/50000000000000000000 : ℝ) ≤ ((44154611629150462163/44170000000000000000 : ℝ)+(849286156729/441700000000000 : ℝ)*((7439/50000 : ℝ)+(10461/100000 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (44154611629150462163/44170000000000000000 : ℝ)+(849286156729/441700000000000 : ℝ)*((7439/50000 : ℝ)+(10461/100000 : ℝ))=(5000694101321691/5000000000000000 : ℝ) by norm_num, show 1+(45230517141919701/100000000000000000000 : ℝ)+(5446186970125673/50000000000000000000 : ℝ)=(100056122891082171047/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45230517141919701/100000000000000000000 : ℝ) ≤ ((44154611629150462163/44170000000000000000 : ℝ)+2*(849286156729/441700000000000 : ℝ)*(7439/50000 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (44154611629150462163/44170000000000000000 : ℝ)+2*(849286156729/441700000000000 : ℝ)*(7439/50000 : ℝ)=(10002237488800111/10000000000000000 : ℝ) by norm_num, show 1+2*(45230517141919701/100000000000000000000 : ℝ)=(50045230517141919701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44154611629150462163/44170000000000000000 : ℝ)*(X 1 0+X 2 0)+(849286156729/441700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (7439/50000 : ℝ)) (c := (44154611629150462163/44170000000000000000 : ℝ)) (alpha := (849286156729/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44154611629150462163/44170000000000000000 : ℝ)*(X 0 1+X 2 1)+(849286156729/441700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (7439/50000 : ℝ)) (c := (44154611629150462163/44170000000000000000 : ℝ)) (alpha := (849286156729/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44154611629150462163/44170000000000000000 : ℝ)*(X 0 2+X 1 2)+(849286156729/441700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (7439/50000 : ℝ)) (c := (44154611629150462163/44170000000000000000 : ℝ)) (alpha := (849286156729/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548242813/2500000000 : ℝ)*X 0 0+(5404731961/10000000000 : ℝ)*X 0 1+(5254736469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336901549/2500000000 : ℝ)*X 1 0+(-2269245411/10000000000 : ℝ)*X 1 1+(5254736281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347606343/10000000000 : ℝ)*X 2 0+(525473627/1000000000 : ℝ)*X 2 1+(-2269245231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093012809/2500000000 : ℝ)*X 0 0+(1056748067/2500000000 : ℝ)*X 0 1+(226106517/500000000 : ℝ)*X 0 2+(1093012809/2500000000 : ℝ)*X 1 0+(1056748067/2500000000 : ℝ)*X 1 1+(226106517/500000000 : ℝ)*X 1 2+(1093012809/2500000000 : ℝ)*X 2 0+(1056748067/2500000000 : ℝ)*X 2 1+(226106517/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2192979343/10000000000 : ℝ)*X 0 0+(2627586261/5000000000 : ℝ)*X 0 1+(675536737/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309767967/10000000000 : ℝ)*X 1 0+(-529921829/2500000000 : ℝ)*X 1 1+(5404293911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327441969/2500000000 : ℝ)*X 2 0+(135107347/250000000 : ℝ)*X 2 1+(-1059843741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372066639/10000000000 : ℝ)*X 0 0+(565159011/1250000000 : ℝ)*X 0 1+(211392707/500000000 : ℝ)*X 0 2+(4372066639/10000000000 : ℝ)*X 1 0+(565159011/1250000000 : ℝ)*X 1 1+(211392707/500000000 : ℝ)*X 1 2+(4372066639/10000000000 : ℝ)*X 2 0+(565159011/1250000000 : ℝ)*X 2 1+(211392707/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4117283604390195641589498753/441700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214807151/25000000000000 : ℝ)*(base19) + (263302259/50000000000000 : ℝ)*(base23) + (40327659/12500000000000 : ℝ)*(lower2) + (53916471/50000000000000 : ℝ)*(upper3) + (9348757/20000000000000 : ℝ)*(lower4) + (1005514329991977/20000000000000 : ℝ)*(major0) + (1005514329991977/20000000000000 : ℝ)*(major1) + (1005514329991977/20000000000000 : ℝ)*(major2) + (6666874808994147/100000000000000 : ℝ)*(sp0) + (6666885621283907/100000000000000 : ℝ)*(sp1) + (6666885953907993/100000000000000 : ℝ)*(sp2) + (3388247984473827/100000000000000 : ℝ)*(sp3) + (2917879591/25000000000000 : ℝ)*(sp4) + (8524218489/100000000000000 : ℝ)*(sp7) + (847064127173079/25000000000000 : ℝ)*(f.failure) + (6666886480512511/100000000000000 : ℝ)*(f.sum) + (5677101428367/2208500000000000000000000000 : ℝ)*base65 + (8719458737090833749/883400000000000000000000000000000 : ℝ)*base68 + (6818053121476433749/883400000000000000000000000000000 : ℝ)*base70 + (1912813567055633749/883400000000000000000000000000000 : ℝ)*base72 + (670640261657/2208500000000000000000000000 : ℝ)*base74 + (4799737471071566251/883400000000000000000000000000000 : ℝ)*base75 + (8284350524972566251/883400000000000000000000000000000 : ℝ)*base77 + (31684307323329833749/883400000000000000000000000000000 : ℝ)*base80 + (1422476520621/276062500000000000000000000 : ℝ)*base82 + (1262349/1250000000000000000000 : ℝ)*base89 + (1262349/1250000000000000000000 : ℝ)*base91 + (1262349/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10619971535212680405232865583/2208500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (938936299/100000000000000 : ℝ)*(base19) + (44748611/4000000000000 : ℝ)*(base23) + (15634239/50000000000000 : ℝ)*(upper3) + (161864989/100000000000000 : ℝ)*(lower4) + (24000903/50000000000000 : ℝ)*(upper5) + (5057023986515149/100000000000000 : ℝ)*(major0) + (5057023986515149/100000000000000 : ℝ)*(major1) + (5057023986515149/100000000000000 : ℝ)*(major2) + (2743410437/10000000000000 : ℝ)*(sp1) + (203214441/781250000000 : ℝ)*(sp2) + (6705942343560827/100000000000000 : ℝ)*(sp4) + (6705913970520157/100000000000000 : ℝ)*(sp5) + (419119700837319/6250000000000 : ℝ)*(sp6) + (3408105469180103/100000000000000 : ℝ)*(sp7) + (3408105469180103/100000000000000 : ℝ)*(f.failure) + (6705942343560827/100000000000000 : ℝ)*(f.sum) + (15712248947361/22085000000000000000000000000 : ℝ)*base65 + (35908350816173092713/4417000000000000000000000000000000 : ℝ)*base68 + (67289491163891092713/4417000000000000000000000000000000 : ℝ)*base70 + (34324902244139092713/4417000000000000000000000000000000 : ℝ)*base72 + (80847859298849/22085000000000000000000000000 : ℝ)*base74 + (3228415085976092713/4417000000000000000000000000000000 : ℝ)*base76 + (61285605172032092713/4417000000000000000000000000000000 : ℝ)*base78 + (64228992199935092713/4417000000000000000000000000000000 : ℝ)*base80 + (5330407411281/22085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (34266493/5000000000000000000000 : ℝ)*base89 + (34266493/5000000000000000000000 : ℝ)*base91 + (34266493/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7439/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1086_s5_0 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193746467/10000000000 : ℝ)*x 0 + (337276871/625000000 : ℝ)*x 1 + (5262529923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193746467/10000000000 : ℝ)^8279 ≤ (832775895433/6250000000000 : ℝ)^6231 := by
    have hnat : (2193746467 : ℕ)^8279*6250000000000^6231 ≤ 832775895433^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193746467 10000000000 832775895433 6250000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337276871/625000000 : ℝ)^8279 ≤ (22030560371639/50000000000000 : ℝ)^6231 := by
    have hnat : (337276871 : ℕ)^8279*50000000000000^6231 ≤ 22030560371639^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337276871 625000000 22030560371639 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262529923/10000000000 : ℝ)^8279 ≤ (42614464908127/100000000000000 : ℝ)^6231 := by
    have hnat : (5262529923 : ℕ)^8279*100000000000000^6231 ≤ 42614464908127^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262529923 10000000000 42614464908127 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193746467/10000000000 : ℝ), (337276871/625000000 : ℝ), (5262529923/10000000000 : ℝ)] ![(832775895433/6250000000000 : ℝ), (22030560371639/50000000000000 : ℝ), (42614464908127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193746467/10000000000 : ℝ)|^8279 ≤ (832775895433/6250000000000 : ℝ)^6231
        have hw : |(-2193746467/10000000000 : ℝ)|=(2193746467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337276871/625000000 : ℝ)|^8279 ≤ (22030560371639/50000000000000 : ℝ)^6231
        have hw : |(337276871/625000000 : ℝ)|=(337276871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262529923/10000000000 : ℝ)|^8279 ≤ (42614464908127/100000000000000 : ℝ)^6231
        have hw : |(5262529923/10000000000 : ℝ)|=(5262529923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_1 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345536351/10000000000 : ℝ)*x 0 + (-1130856893/5000000000 : ℝ)*x 1 + (5262528101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345536351/10000000000 : ℝ)^8279 ≤ (43509859936277/100000000000000 : ℝ)^6231 := by
    have hnat : (5345536351 : ℕ)^8279*100000000000000^6231 ≤ 43509859936277^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345536351 10000000000 43509859936277 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130856893/5000000000 : ℝ)^8279 ≤ (2775138946811/20000000000000 : ℝ)^6231 := by
    have hnat : (1130856893 : ℕ)^8279*20000000000000^6231 ≤ 2775138946811^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130856893 5000000000 2775138946811 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262528101/10000000000 : ℝ)^8279 ≤ (10653611326187/25000000000000 : ℝ)^6231 := by
    have hnat : (5262528101 : ℕ)^8279*25000000000000^6231 ≤ 10653611326187^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262528101 10000000000 10653611326187 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345536351/10000000000 : ℝ), (-1130856893/5000000000 : ℝ), (5262528101/10000000000 : ℝ)] ![(43509859936277/100000000000000 : ℝ), (2775138946811/20000000000000 : ℝ), (10653611326187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345536351/10000000000 : ℝ)|^8279 ≤ (43509859936277/100000000000000 : ℝ)^6231
        have hw : |(5345536351/10000000000 : ℝ)|=(5345536351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1130856893/5000000000 : ℝ)|^8279 ≤ (2775138946811/20000000000000 : ℝ)^6231
        have hw : |(-1130856893/5000000000 : ℝ)|=(1130856893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262528101/10000000000 : ℝ)|^8279 ≤ (10653611326187/25000000000000 : ℝ)^6231
        have hw : |(5262528101/10000000000 : ℝ)|=(5262528101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_2 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345535561/10000000000 : ℝ)*x 0 + (5262529667/10000000000 : ℝ)*x 1 + (-2261712769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345535561/10000000000 : ℝ)^8279 ≤ (43509851392623/100000000000000 : ℝ)^6231 := by
    have hnat : (5345535561 : ℕ)^8279*100000000000000^6231 ≤ 43509851392623^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345535561 10000000000 43509851392623 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262529667/10000000000 : ℝ)^8279 ≤ (8522892430751/20000000000000 : ℝ)^6231 := by
    have hnat : (5262529667 : ℕ)^8279*20000000000000^6231 ≤ 8522892430751^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262529667 10000000000 8522892430751 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261712769/10000000000 : ℝ)^8279 ≤ (6937843221993/50000000000000 : ℝ)^6231 := by
    have hnat : (2261712769 : ℕ)^8279*50000000000000^6231 ≤ 6937843221993^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261712769 10000000000 6937843221993 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345535561/10000000000 : ℝ), (5262529667/10000000000 : ℝ), (-2261712769/10000000000 : ℝ)] ![(43509851392623/100000000000000 : ℝ), (8522892430751/20000000000000 : ℝ), (6937843221993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345535561/10000000000 : ℝ)|^8279 ≤ (43509851392623/100000000000000 : ℝ)^6231
        have hw : |(5345535561/10000000000 : ℝ)|=(5345535561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262529667/10000000000 : ℝ)|^8279 ≤ (8522892430751/20000000000000 : ℝ)^6231
        have hw : |(5262529667/10000000000 : ℝ)|=(5262529667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2261712769/10000000000 : ℝ)|^8279 ≤ (6937843221993/50000000000000 : ℝ)^6231
        have hw : |(-2261712769/10000000000 : ℝ)|=(2261712769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_3 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186250697/5000000000 : ℝ)*x 0 + (4242768221/10000000000 : ℝ)*x 1 + (901247331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186250697/5000000000 : ℝ)^8279 ≤ (33315426057163/100000000000000 : ℝ)^6231 := by
    have hnat : (2186250697 : ℕ)^8279*100000000000000^6231 ≤ 33315426057163^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186250697 5000000000 33315426057163 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242768221/10000000000 : ℝ)^8279 ≤ (32008504618469/100000000000000 : ℝ)^6231 := by
    have hnat : (4242768221 : ℕ)^8279*100000000000000^6231 ≤ 32008504618469^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242768221 10000000000 32008504618469 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901247331/2000000000 : ℝ)^8279 ≤ (3467606931001/10000000000000 : ℝ)^6231 := by
    have hnat : (901247331 : ℕ)^8279*10000000000000^6231 ≤ 3467606931001^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901247331 2000000000 3467606931001 10000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186250697/5000000000 : ℝ), (4242768221/10000000000 : ℝ), (901247331/2000000000 : ℝ)] ![(33315426057163/100000000000000 : ℝ), (32008504618469/100000000000000 : ℝ), (3467606931001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186250697/5000000000 : ℝ)|^8279 ≤ (33315426057163/100000000000000 : ℝ)^6231
        have hw : |(2186250697/5000000000 : ℝ)|=(2186250697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242768221/10000000000 : ℝ)|^8279 ≤ (32008504618469/100000000000000 : ℝ)^6231
        have hw : |(4242768221/10000000000 : ℝ)|=(4242768221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901247331/2000000000 : ℝ)|^8279 ≤ (3467606931001/10000000000000 : ℝ)^6231
        have hw : |(901247331/2000000000 : ℝ)|=(901247331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_4 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096876057/5000000000 : ℝ)*x 0 + (1052575487/2000000000 : ℝ)*x 1 + (215843243/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096876057/5000000000 : ℝ)^8279 ≤ (13324459899107/100000000000000 : ℝ)^6231 := by
    have hnat : (1096876057 : ℕ)^8279*100000000000000^6231 ≤ 13324459899107^6231*5000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096876057 5000000000 13324459899107 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052575487/2000000000 : ℝ)^8279 ≤ (42618203922301/100000000000000 : ℝ)^6231 := by
    have hnat : (1052575487 : ℕ)^8279*100000000000000^6231 ≤ 42618203922301^6231*2000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052575487 2000000000 42618203922301 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215843243/400000000 : ℝ)^8279 ≤ (11014334042463/25000000000000 : ℝ)^6231 := by
    have hnat : (215843243 : ℕ)^8279*25000000000000^6231 ≤ 11014334042463^6231*400000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215843243 400000000 11014334042463 25000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096876057/5000000000 : ℝ), (1052575487/2000000000 : ℝ), (215843243/400000000 : ℝ)] ![(13324459899107/100000000000000 : ℝ), (42618203922301/100000000000000 : ℝ), (11014334042463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096876057/5000000000 : ℝ)|^8279 ≤ (13324459899107/100000000000000 : ℝ)^6231
        have hw : |(-1096876057/5000000000 : ℝ)|=(1096876057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052575487/2000000000 : ℝ)|^8279 ≤ (42618203922301/100000000000000 : ℝ)^6231
        have hw : |(1052575487/2000000000 : ℝ)|=(1052575487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215843243/400000000 : ℝ)|^8279 ≤ (11014334042463/25000000000000 : ℝ)^6231
        have hw : |(215843243/400000000 : ℝ)|=(215843243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_5 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331984709/625000000 : ℝ)*x 0 + (-2128162189/10000000000 : ℝ)*x 1 + (1349020269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331984709/625000000 : ℝ)^8279 ≤ (21572453352197/50000000000000 : ℝ)^6231 := by
    have hnat : (331984709 : ℕ)^8279*50000000000000^6231 ≤ 21572453352197^6231*625000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331984709 625000000 21572453352197 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128162189/10000000000 : ℝ)^8279 ≤ (6398878549071/50000000000000 : ℝ)^6231 := by
    have hnat : (2128162189 : ℕ)^8279*50000000000000^6231 ≤ 6398878549071^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128162189 10000000000 6398878549071 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349020269/2500000000 : ℝ)^8279 ≤ (44057336180701/100000000000000 : ℝ)^6231 := by
    have hnat : (1349020269 : ℕ)^8279*100000000000000^6231 ≤ 44057336180701^6231*2500000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349020269 2500000000 44057336180701 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331984709/625000000 : ℝ), (-2128162189/10000000000 : ℝ), (1349020269/2500000000 : ℝ)] ![(21572453352197/50000000000000 : ℝ), (6398878549071/50000000000000 : ℝ), (44057336180701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331984709/625000000 : ℝ)|^8279 ≤ (21572453352197/50000000000000 : ℝ)^6231
        have hw : |(331984709/625000000 : ℝ)|=(331984709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128162189/10000000000 : ℝ)|^8279 ≤ (6398878549071/50000000000000 : ℝ)^6231
        have hw : |(-2128162189/10000000000 : ℝ)|=(2128162189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349020269/2500000000 : ℝ)|^8279 ≤ (44057336180701/100000000000000 : ℝ)^6231
        have hw : |(1349020269/2500000000 : ℝ)|=(1349020269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_6 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311755349/10000000000 : ℝ)*x 0 + (5396081071/10000000000 : ℝ)*x 1 + (-2128162189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311755349/10000000000 : ℝ)^8279 ≤ (8628981351671/20000000000000 : ℝ)^6231 := by
    have hnat : (5311755349 : ℕ)^8279*20000000000000^6231 ≤ 8628981351671^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311755349 10000000000 8628981351671 20000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396081071/10000000000 : ℝ)^8279 ≤ (44057336126459/100000000000000 : ℝ)^6231 := by
    have hnat : (5396081071 : ℕ)^8279*100000000000000^6231 ≤ 44057336126459^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396081071 10000000000 44057336126459 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128162189/10000000000 : ℝ)^8279 ≤ (6398878549071/50000000000000 : ℝ)^6231 := by
    have hnat : (2128162189 : ℕ)^8279*50000000000000^6231 ≤ 6398878549071^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128162189 10000000000 6398878549071 50000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311755349/10000000000 : ℝ), (5396081071/10000000000 : ℝ), (-2128162189/10000000000 : ℝ)] ![(8628981351671/20000000000000 : ℝ), (44057336126459/100000000000000 : ℝ), (6398878549071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311755349/10000000000 : ℝ)|^8279 ≤ (8628981351671/20000000000000 : ℝ)^6231
        have hw : |(5311755349/10000000000 : ℝ)|=(5311755349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396081071/10000000000 : ℝ)|^8279 ≤ (44057336126459/100000000000000 : ℝ)^6231
        have hw : |(5396081071/10000000000 : ℝ)|=(5396081071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128162189/10000000000 : ℝ)|^8279 ≤ (6398878549071/50000000000000 : ℝ)^6231
        have hw : |(-2128162189/10000000000 : ℝ)|=(2128162189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1086_s5_7 (p : ℝ) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372512573/10000000000 : ℝ)*x 0 + (4505552369/10000000000 : ℝ)*x 1 + (4243454867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372512573/10000000000 : ℝ)^8279 ≤ (33315539229083/100000000000000 : ℝ)^6231 := by
    have hnat : (4372512573 : ℕ)^8279*100000000000000^6231 ≤ 33315539229083^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372512573 10000000000 33315539229083 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505552369/10000000000 : ℝ)^8279 ≤ (1733453655019/5000000000000 : ℝ)^6231 := by
    have hnat : (4505552369 : ℕ)^8279*5000000000000^6231 ≤ 1733453655019^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505552369 10000000000 1733453655019 5000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243454867/10000000000 : ℝ)^8279 ≤ (32015387664181/100000000000000 : ℝ)^6231 := by
    have hnat : (4243454867 : ℕ)^8279*100000000000000^6231 ≤ 32015387664181^6231*10000000000^8279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243454867 10000000000 32015387664181 100000000000000 8279 6231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8279/2048 : ℝ)) 8279 6231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372512573/10000000000 : ℝ), (4505552369/10000000000 : ℝ), (4243454867/10000000000 : ℝ)] ![(33315539229083/100000000000000 : ℝ), (1733453655019/5000000000000 : ℝ), (32015387664181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372512573/10000000000 : ℝ)|^8279 ≤ (33315539229083/100000000000000 : ℝ)^6231
        have hw : |(4372512573/10000000000 : ℝ)|=(4372512573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505552369/10000000000 : ℝ)|^8279 ≤ (1733453655019/5000000000000 : ℝ)^6231
        have hw : |(4505552369/10000000000 : ℝ)|=(4505552369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243454867/10000000000 : ℝ)|^8279 ≤ (32015387664181/100000000000000 : ℝ)^6231
        have hw : |(4243454867/10000000000 : ℝ)|=(4243454867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1086_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1123/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1383/12500 : ℝ) ^ (4139/1024 : ℝ) ≤ (13661564876631089/100000000000000000000 : ℝ) := by
    have hpowers : (1383/12500 : ℝ)^4139 ≤ (13661564876631089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1383 : ℕ)^4139*100000000000000000000^1024 ≤ 13661564876631089^1024*12500^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1383 12500 13661564876631089 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1383/12500 : ℝ)) (X := (13661564876631089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (4139/1024 : ℝ) ≤ (37887329062298829/100000000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^4139 ≤ (37887329062298829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4139*100000000000000000000^1024 ≤ 37887329062298829^1024*625^4139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 37887329062298829 100000000000000000000 4139 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (37887329062298829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013661564876631089/50000000000000000000 : ℝ) ≤ (10000675912264647/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50013661564876631089/50000000000000000000 : ℝ)^1024 ≤ (10000675912264647/10000000000000000 : ℝ)^4139 := by
      have hnat : (50013661564876631089 : ℕ)^1024*10000000000000000^4139 ≤ 10000675912264647^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013661564876631089 50000000000000000000 10000675912264647 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000675912264647/10000000000000000 : ℝ)) (X := (50013661564876631089/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025774446969464959/50000000000000000000 : ℝ) ≤ (1250159385815269/1250000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50025774446969464959/50000000000000000000 : ℝ)^1024 ≤ (1250159385815269/1250000000000000 : ℝ)^4139 := by
      have hnat : (50025774446969464959 : ℕ)^1024*1250000000000000^4139 ≤ 1250159385815269^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025774446969464959 50000000000000000000 1250159385815269 1250000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159385815269/1250000000000000 : ℝ)) (X := (50025774446969464959/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037887329062298829/50000000000000000000 : ℝ) ≤ (10001874260779657/10000000000000000 : ℝ) ^ (4139/1024 : ℝ) := by
    have hpowers : (50037887329062298829/50000000000000000000 : ℝ)^1024 ≤ (10001874260779657/10000000000000000 : ℝ)^4139 := by
      have hnat : (50037887329062298829 : ℕ)^1024*10000000000000000^4139 ≤ 10001874260779657^4139*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037887329062298829 50000000000000000000 10001874260779657 10000000000000000 1024 4139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001874260779657/10000000000000000 : ℝ)) (X := (50037887329062298829/50000000000000000000 : ℝ)) (by norm_num) 4139 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13661564876631089/100000000000000000000 : ℝ) ≤ ((3968611021172806029/3970000000000000000 : ℝ)+2*(119834851501/63520000000000 : ℝ)*(1383/12500 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (3968611021172806029/3970000000000000000 : ℝ)+2*(119834851501/63520000000000 : ℝ)*(1383/12500 : ℝ)=(10000675912264647/10000000000000000 : ℝ) by norm_num, show 1+2*(13661564876631089/100000000000000000000 : ℝ)=(50013661564876631089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37887329062298829/100000000000000000000 : ℝ)+(13661564876631089/100000000000000000000 : ℝ) ≤ ((3968611021172806029/3970000000000000000 : ℝ)+(119834851501/63520000000000 : ℝ)*((89/625 : ℝ)+(1383/12500 : ℝ)))^(4139/1024 : ℝ) := by
    rw [show (3968611021172806029/3970000000000000000 : ℝ)+(119834851501/63520000000000 : ℝ)*((89/625 : ℝ)+(1383/12500 : ℝ))=(1250159385815269/1250000000000000 : ℝ) by norm_num, show 1+(37887329062298829/100000000000000000000 : ℝ)+(13661564876631089/100000000000000000000 : ℝ)=(50025774446969464959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37887329062298829/100000000000000000000 : ℝ) ≤ ((3968611021172806029/3970000000000000000 : ℝ)+2*(119834851501/63520000000000 : ℝ)*(89/625 : ℝ))^(4139/1024 : ℝ) := by
    rw [show (3968611021172806029/3970000000000000000 : ℝ)+2*(119834851501/63520000000000 : ℝ)*(89/625 : ℝ)=(10001874260779657/10000000000000000 : ℝ) by norm_num, show 1+2*(37887329062298829/100000000000000000000 : ℝ)=(50037887329062298829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3968611021172806029/3970000000000000000 : ℝ)*(X 1 0+X 2 0)+(119834851501/63520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (89/625 : ℝ)) (c := (3968611021172806029/3970000000000000000 : ℝ)) (alpha := (119834851501/63520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3968611021172806029/3970000000000000000 : ℝ)*(X 0 1+X 2 1)+(119834851501/63520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (89/625 : ℝ)) (c := (3968611021172806029/3970000000000000000 : ℝ)) (alpha := (119834851501/63520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3968611021172806029/3970000000000000000 : ℝ)*(X 0 2+X 1 2)+(119834851501/63520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4139/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (89/625 : ℝ)) (c := (3968611021172806029/3970000000000000000 : ℝ)) (alpha := (119834851501/63520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193746467/10000000000 : ℝ)*X 0 0+(337276871/625000000 : ℝ)*X 0 1+(5262529923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345536351/10000000000 : ℝ)*X 1 0+(-1130856893/5000000000 : ℝ)*X 1 1+(5262528101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345535561/10000000000 : ℝ)*X 2 0+(5262529667/10000000000 : ℝ)*X 2 1+(-2261712769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186250697/5000000000 : ℝ)*X 0 0+(4242768221/10000000000 : ℝ)*X 0 1+(901247331/2000000000 : ℝ)*X 0 2+(2186250697/5000000000 : ℝ)*X 1 0+(4242768221/10000000000 : ℝ)*X 1 1+(901247331/2000000000 : ℝ)*X 1 2+(2186250697/5000000000 : ℝ)*X 2 0+(4242768221/10000000000 : ℝ)*X 2 1+(901247331/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096876057/5000000000 : ℝ)*X 0 0+(1052575487/2000000000 : ℝ)*X 0 1+(215843243/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331984709/625000000 : ℝ)*X 1 0+(-2128162189/10000000000 : ℝ)*X 1 1+(1349020269/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311755349/10000000000 : ℝ)*X 2 0+(5396081071/10000000000 : ℝ)*X 2 1+(-2128162189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372512573/10000000000 : ℝ)*X 0 0+(4505552369/10000000000 : ℝ)*X 0 1+(4243454867/10000000000 : ℝ)*X 0 2+(4372512573/10000000000 : ℝ)*X 1 0+(4505552369/10000000000 : ℝ)*X 1 1+(4243454867/10000000000 : ℝ)*X 1 2+(4372512573/10000000000 : ℝ)*X 2 0+(4505552369/10000000000 : ℝ)*X 2 1+(4243454867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1086_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142683152947345183678070037/99250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3724448069/100000000000000 : ℝ)*(base19) + (1448412533/50000000000000 : ℝ)*(base23) + (33732031/50000000000000 : ℝ)*(lower3) + (7906813/50000000000000 : ℝ)*(upper4) + (2816012366519851/50000000000000 : ℝ)*(major0) + (2816012366519851/50000000000000 : ℝ)*(major1) + (2816012366519851/50000000000000 : ℝ)*(major2) + (7468347166133901/100000000000000 : ℝ)*(sp0) + (7468378721920011/100000000000000 : ℝ)*(sp1) + (3734213961520487/50000000000000 : ℝ)*(sp2) + (759114481350631/20000000000000 : ℝ)*(sp3) + (83653732139/100000000000000 : ℝ)*(sp4) + (1209337449/2500000000000 : ℝ)*(sp5) + (11547884937/25000000000000 : ℝ)*(sp7) + (1897809299146451/50000000000000 : ℝ)*(f.failure) + (186710770496651/2500000000000 : ℝ)*(f.sum) + (7593449309483/1588000000000000000000000000 : ℝ)*base65 + (831821260600080821/198500000000000000000000000000000 : ℝ)*base68 + (764975397268580821/198500000000000000000000000000000 : ℝ)*base70 + (1167277458560419179/198500000000000000000000000000000 : ℝ)*base71 + (1067445713077/1588000000000000000000000000 : ℝ)*base74 + (730822484334080821/198500000000000000000000000000000 : ℝ)*base76 + (877634533429919179/198500000000000000000000000000000 : ℝ)*base77 + (1211617634214580821/198500000000000000000000000000000 : ℝ)*base80 + (1846373773229/1588000000000000000000000000 : ℝ)*base82 + (15673919/2500000000000000000000 : ℝ)*base90 + (15673919/2500000000000000000000 : ℝ)*base92 + (15673919/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44187011302321313914746717/9925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403752509/50000000000000 : ℝ)*(base19) + (110573127/12500000000000 : ℝ)*(base23) + (8750871/10000000000000 : ℝ)*(upper3) + (7980307/25000000000000 : ℝ)*(lower4) + (90939421/100000000000000 : ℝ)*(upper5) + (283066891531509/5000000000000 : ℝ)*(major0) + (283066891531509/5000000000000 : ℝ)*(major1) + (283066891531509/5000000000000 : ℝ)*(major2) + (21340654041/100000000000000 : ℝ)*(sp1) + (22900687733/100000000000000 : ℝ)*(sp2) + (3753650896044291/50000000000000 : ℝ)*(sp4) + (7507279643929523/100000000000000 : ℝ)*(sp5) + (938409750851979/12500000000000 : ℝ)*(sp6) + (3815373720768713/100000000000000 : ℝ)*(sp7) + (3815373720768713/100000000000000 : ℝ)*(f.failure) + (3753650896044291/50000000000000 : ℝ)*(f.sum) + (224947138549/794000000000000000000000000 : ℝ)*base66 + (87058474511780261/19850000000000000000000000000000 : ℝ)*base67 + (60797250964880261/19850000000000000000000000000000 : ℝ)*base69 + (190951009850469739/19850000000000000000000000000000 : ℝ)*base72 + (3933429501989/794000000000000000000000000 : ℝ)*base73 + (65443595270730261/19850000000000000000000000000000 : ℝ)*base75 + (11441371418769739/19850000000000000000000000000000 : ℝ)*base78 + (88550324823730261/19850000000000000000000000000000 : ℝ)*base79 + (1343464051721/794000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6884403/5000000000000000000000 : ℝ)*base89 + (6884403/5000000000000000000000 : ℝ)*base91 + (6884403/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1086_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1086_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1086_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1086_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1086_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1086_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4139/1024 : ℝ) ≤ p) (hpb : p ≤ (8279/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74191131/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4169/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1086_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

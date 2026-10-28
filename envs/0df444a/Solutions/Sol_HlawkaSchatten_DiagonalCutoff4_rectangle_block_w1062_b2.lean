-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:04:23.745039+00:00
-- url     : https://prove2.me/submissions/f0424725-62e5-4b55-9a32-7fe55a22e5bb

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
theorem support_rectangle_w1062_s6_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102844313/5000000000 : ℝ)*x 0 + (5394999949/10000000000 : ℝ)*x 1 + (5263839391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102844313/5000000000 : ℝ)^8255 ≤ (2679023803147/20000000000000 : ℝ)^6207 := by
    have hnat : (1102844313 : ℕ)^8255*20000000000000^6207 ≤ 2679023803147^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102844313 5000000000 2679023803147 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394999949/10000000000 : ℝ)^8255 ≤ (2200553904157/5000000000000 : ℝ)^6207 := by
    have hnat : (5394999949 : ℕ)^8255*5000000000000^6207 ≤ 2200553904157^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394999949 10000000000 2200553904157 5000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263839391/10000000000 : ℝ)^8255 ≤ (42593802879073/100000000000000 : ℝ)^6207 := by
    have hnat : (5263839391 : ℕ)^8255*100000000000000^6207 ≤ 42593802879073^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263839391 10000000000 42593802879073 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102844313/5000000000 : ℝ), (5394999949/10000000000 : ℝ), (5263839391/10000000000 : ℝ)] ![(2679023803147/20000000000000 : ℝ), (2200553904157/5000000000000 : ℝ), (42593802879073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102844313/5000000000 : ℝ)|^8255 ≤ (2679023803147/20000000000000 : ℝ)^6207
        have hw : |(-1102844313/5000000000 : ℝ)|=(1102844313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394999949/10000000000 : ℝ)|^8255 ≤ (2200553904157/5000000000000 : ℝ)^6207
        have hw : |(5394999949/10000000000 : ℝ)|=(5394999949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263839391/10000000000 : ℝ)|^8255 ≤ (42593802879073/100000000000000 : ℝ)^6207
        have hw : |(5263839391/10000000000 : ℝ)|=(5263839391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336282893/2500000000 : ℝ)*x 0 + (-2272244551/10000000000 : ℝ)*x 1 + (82247491/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336282893/2500000000 : ℝ)^8255 ≤ (43470862663437/100000000000000 : ℝ)^6207 := by
    have hnat : (1336282893 : ℕ)^8255*100000000000000^6207 ≤ 43470862663437^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336282893 2500000000 43470862663437 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272244551/10000000000 : ℝ)^8255 ≤ (870958380243/6250000000000 : ℝ)^6207 := by
    have hnat : (2272244551 : ℕ)^8255*6250000000000^6207 ≤ 870958380243^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272244551 10000000000 870958380243 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82247491/156250000 : ℝ)^8255 ≤ (42593803234207/100000000000000 : ℝ)^6207 := by
    have hnat : (82247491 : ℕ)^8255*100000000000000^6207 ≤ 42593803234207^6207*156250000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82247491 156250000 42593803234207 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336282893/2500000000 : ℝ), (-2272244551/10000000000 : ℝ), (82247491/156250000 : ℝ)] ![(43470862663437/100000000000000 : ℝ), (870958380243/6250000000000 : ℝ), (42593803234207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336282893/2500000000 : ℝ)|^8255 ≤ (43470862663437/100000000000000 : ℝ)^6207
        have hw : |(1336282893/2500000000 : ℝ)|=(1336282893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272244551/10000000000 : ℝ)|^8255 ≤ (870958380243/6250000000000 : ℝ)^6207
        have hw : |(-2272244551/10000000000 : ℝ)|=(2272244551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82247491/156250000 : ℝ)|^8255 ≤ (42593803234207/100000000000000 : ℝ)^6207
        have hw : |(82247491/156250000 : ℝ)|=(82247491/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345131337/10000000000 : ℝ)*x 0 + (1052767913/2000000000 : ℝ)*x 1 + (-2272244677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345131337/10000000000 : ℝ)^8255 ≤ (43470860121627/100000000000000 : ℝ)^6207 := by
    have hnat : (5345131337 : ℕ)^8255*100000000000000^6207 ≤ 43470860121627^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345131337 10000000000 43470860121627 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052767913/2000000000 : ℝ)^8255 ≤ (42593804751601/100000000000000 : ℝ)^6207 := by
    have hnat : (1052767913 : ℕ)^8255*100000000000000^6207 ≤ 42593804751601^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052767913 2000000000 42593804751601 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272244677/10000000000 : ℝ)^8255 ≤ (13935335111593/100000000000000 : ℝ)^6207 := by
    have hnat : (2272244677 : ℕ)^8255*100000000000000^6207 ≤ 13935335111593^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272244677 10000000000 13935335111593 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345131337/10000000000 : ℝ), (1052767913/2000000000 : ℝ), (-2272244677/10000000000 : ℝ)] ![(43470860121627/100000000000000 : ℝ), (42593804751601/100000000000000 : ℝ), (13935335111593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345131337/10000000000 : ℝ)|^8255 ≤ (43470860121627/100000000000000 : ℝ)^6207
        have hw : |(5345131337/10000000000 : ℝ)|=(5345131337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052767913/2000000000 : ℝ)|^8255 ≤ (42593804751601/100000000000000 : ℝ)^6207
        have hw : |(1052767913/2000000000 : ℝ)|=(1052767913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2272244677/10000000000 : ℝ)|^8255 ≤ (13935335111593/100000000000000 : ℝ)^6207
        have hw : |(-2272244677/10000000000 : ℝ)|=(2272244677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188019651/5000000000 : ℝ)*x 0 + (4249524007/10000000000 : ℝ)*x 1 + (4506376469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188019651/5000000000 : ℝ)^8255 ≤ (33316236788221/100000000000000 : ℝ)^6207 := by
    have hnat : (2188019651 : ℕ)^8255*100000000000000^6207 ≤ 33316236788221^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188019651 5000000000 33316236788221 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249524007/10000000000 : ℝ)^8255 ≤ (3204137492709/10000000000000 : ℝ)^6207 := by
    have hnat : (4249524007 : ℕ)^8255*10000000000000^6207 ≤ 3204137492709^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249524007 10000000000 3204137492709 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506376469/10000000000 : ℝ)^8255 ≤ (34642388261879/100000000000000 : ℝ)^6207 := by
    have hnat : (4506376469 : ℕ)^8255*100000000000000^6207 ≤ 34642388261879^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506376469 10000000000 34642388261879 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188019651/5000000000 : ℝ), (4249524007/10000000000 : ℝ), (4506376469/10000000000 : ℝ)] ![(33316236788221/100000000000000 : ℝ), (3204137492709/10000000000000 : ℝ), (34642388261879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188019651/5000000000 : ℝ)|^8255 ≤ (33316236788221/100000000000000 : ℝ)^6207
        have hw : |(2188019651/5000000000 : ℝ)|=(2188019651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249524007/10000000000 : ℝ)|^8255 ≤ (3204137492709/10000000000000 : ℝ)^6207
        have hw : |(4249524007/10000000000 : ℝ)|=(4249524007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506376469/10000000000 : ℝ)|^8255 ≤ (34642388261879/100000000000000 : ℝ)^6207
        have hw : |(4506376469/10000000000 : ℝ)|=(4506376469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-551423441/2500000000 : ℝ)*x 0 + (5264170697/10000000000 : ℝ)*x 1 + (5394667491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551423441/2500000000 : ℝ)^8255 ≤ (6697580257097/50000000000000 : ℝ)^6207 := by
    have hnat : (551423441 : ℕ)^8255*50000000000000^6207 ≤ 6697580257097^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551423441 2500000000 6697580257097 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264170697/10000000000 : ℝ)^8255 ≤ (1331167759919/3125000000000 : ℝ)^6207 := by
    have hnat : (5264170697 : ℕ)^8255*3125000000000^6207 ≤ 1331167759919^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264170697 10000000000 1331167759919 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394667491/10000000000 : ℝ)^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207 := by
    have hnat : (5394667491 : ℕ)^8255*25000000000000^6207 ≤ 11001867787137^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394667491 10000000000 11001867787137 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551423441/2500000000 : ℝ), (5264170697/10000000000 : ℝ), (5394667491/10000000000 : ℝ)] ![(6697580257097/50000000000000 : ℝ), (1331167759919/3125000000000 : ℝ), (11001867787137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551423441/2500000000 : ℝ)|^8255 ≤ (6697580257097/50000000000000 : ℝ)^6207
        have hw : |(-551423441/2500000000 : ℝ)|=(551423441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264170697/10000000000 : ℝ)|^8255 ≤ (1331167759919/3125000000000 : ℝ)^6207
        have hw : |(5264170697/10000000000 : ℝ)|=(5264170697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394667491/10000000000 : ℝ)|^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207
        have hw : |(5394667491/10000000000 : ℝ)|=(5394667491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312105321/10000000000 : ℝ)*x 0 + (-428283317/2000000000 : ℝ)*x 1 + (5394667491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312105321/10000000000 : ℝ)^8255 ≤ (43114008362427/100000000000000 : ℝ)^6207 := by
    have hnat : (5312105321 : ℕ)^8255*100000000000000^6207 ≤ 43114008362427^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312105321 10000000000 43114008362427 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428283317/2000000000 : ℝ)^8255 ≤ (2575704093623/20000000000000 : ℝ)^6207 := by
    have hnat : (428283317 : ℕ)^8255*20000000000000^6207 ≤ 2575704093623^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428283317 2000000000 2575704093623 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394667491/10000000000 : ℝ)^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207 := by
    have hnat : (5394667491 : ℕ)^8255*25000000000000^6207 ≤ 11001867787137^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394667491 10000000000 11001867787137 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312105321/10000000000 : ℝ), (-428283317/2000000000 : ℝ), (5394667491/10000000000 : ℝ)] ![(43114008362427/100000000000000 : ℝ), (2575704093623/20000000000000 : ℝ), (11001867787137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312105321/10000000000 : ℝ)|^8255 ≤ (43114008362427/100000000000000 : ℝ)^6207
        have hw : |(5312105321/10000000000 : ℝ)|=(5312105321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428283317/2000000000 : ℝ)|^8255 ≤ (2575704093623/20000000000000 : ℝ)^6207
        have hw : |(-428283317/2000000000 : ℝ)|=(428283317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394667491/10000000000 : ℝ)|^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207
        have hw : |(5394667491/10000000000 : ℝ)|=(5394667491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312105321/10000000000 : ℝ)*x 0 + (5394667491/10000000000 : ℝ)*x 1 + (-428283317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312105321/10000000000 : ℝ)^8255 ≤ (43114008362427/100000000000000 : ℝ)^6207 := by
    have hnat : (5312105321 : ℕ)^8255*100000000000000^6207 ≤ 43114008362427^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312105321 10000000000 43114008362427 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394667491/10000000000 : ℝ)^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207 := by
    have hnat : (5394667491 : ℕ)^8255*25000000000000^6207 ≤ 11001867787137^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394667491 10000000000 11001867787137 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428283317/2000000000 : ℝ)^8255 ≤ (2575704093623/20000000000000 : ℝ)^6207 := by
    have hnat : (428283317 : ℕ)^8255*20000000000000^6207 ≤ 2575704093623^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428283317 2000000000 2575704093623 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312105321/10000000000 : ℝ), (5394667491/10000000000 : ℝ), (-428283317/2000000000 : ℝ)] ![(43114008362427/100000000000000 : ℝ), (11001867787137/25000000000000 : ℝ), (2575704093623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312105321/10000000000 : ℝ)|^8255 ≤ (43114008362427/100000000000000 : ℝ)^6207
        have hw : |(5312105321/10000000000 : ℝ)|=(5312105321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394667491/10000000000 : ℝ)|^8255 ≤ (11001867787137/25000000000000 : ℝ)^6207
        have hw : |(5394667491/10000000000 : ℝ)|=(5394667491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428283317/2000000000 : ℝ)|^8255 ≤ (2575704093623/20000000000000 : ℝ)^6207
        have hw : |(-428283317/2000000000 : ℝ)|=(428283317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s6_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875209897/2000000000 : ℝ)*x 0 + (4505727661/10000000000 : ℝ)*x 1 + (1062543797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875209897/2000000000 : ℝ)^8255 ≤ (33316339894703/100000000000000 : ℝ)^6207 := by
    have hnat : (875209897 : ℕ)^8255*100000000000000^6207 ≤ 33316339894703^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875209897 2000000000 33316339894703 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505727661/10000000000 : ℝ)^8255 ≤ (1385430203407/4000000000000 : ℝ)^6207 := by
    have hnat : (4505727661 : ℕ)^8255*4000000000000^6207 ≤ 1385430203407^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505727661 10000000000 1385430203407 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062543797/2500000000 : ℝ)^8255 ≤ (32047905012893/100000000000000 : ℝ)^6207 := by
    have hnat : (1062543797 : ℕ)^8255*100000000000000^6207 ≤ 32047905012893^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062543797 2500000000 32047905012893 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875209897/2000000000 : ℝ), (4505727661/10000000000 : ℝ), (1062543797/2500000000 : ℝ)] ![(33316339894703/100000000000000 : ℝ), (1385430203407/4000000000000 : ℝ), (32047905012893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875209897/2000000000 : ℝ)|^8255 ≤ (33316339894703/100000000000000 : ℝ)^6207
        have hw : |(875209897/2000000000 : ℝ)|=(875209897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505727661/10000000000 : ℝ)|^8255 ≤ (1385430203407/4000000000000 : ℝ)^6207
        have hw : |(4505727661/10000000000 : ℝ)|=(4505727661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062543797/2500000000 : ℝ)|^8255 ≤ (32047905012893/100000000000000 : ℝ)^6207
        have hw : |(1062543797/2500000000 : ℝ)|=(1062543797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1399/12500 : ℝ) ^ (4127/1024 : ℝ) ≤ (7341891751788907/50000000000000000000 : ℝ) := by
    have hpowers : (1399/12500 : ℝ)^4127 ≤ (7341891751788907/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4127*50000000000000000000^1024 ≤ 7341891751788907^1024*12500^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 12500 7341891751788907 50000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/12500 : ℝ)) (X := (7341891751788907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (4127/1024 : ℝ) ≤ (36793776044453591/100000000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^4127 ≤ (36793776044453591/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14057 : ℕ)^4127*100000000000000000000^1024 ≤ 36793776044453591^1024*100000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 36793776044453591 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (36793776044453591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007341891751788907/25000000000000000000 : ℝ) ≤ (10000728593871311/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (25007341891751788907/25000000000000000000 : ℝ)^1024 ≤ (10000728593871311/10000000000000000 : ℝ)^4127 := by
      have hnat : (25007341891751788907 : ℕ)^1024*10000000000000000^4127 ≤ 10000728593871311^4127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007341891751788907 25000000000000000000 10000728593871311 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000728593871311/10000000000000000 : ℝ)) (X := (25007341891751788907/25000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010295511909606281/20000000000000000000 : ℝ) ≤ (10001277025025393/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (20010295511909606281/20000000000000000000 : ℝ)^1024 ≤ (10001277025025393/10000000000000000 : ℝ)^4127 := by
      have hnat : (20010295511909606281 : ℕ)^1024*10000000000000000^4127 ≤ 10001277025025393^4127*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010295511909606281 20000000000000000000 10001277025025393 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277025025393/10000000000000000 : ℝ)) (X := (20010295511909606281/20000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036793776044453591/50000000000000000000 : ℝ) ≤ (400073018247179/400000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50036793776044453591/50000000000000000000 : ℝ)^1024 ≤ (400073018247179/400000000000000 : ℝ)^4127 := by
      have hnat : (50036793776044453591 : ℕ)^1024*400000000000000^4127 ≤ 400073018247179^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036793776044453591 50000000000000000000 400073018247179 400000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400073018247179/400000000000000 : ℝ)) (X := (50036793776044453591/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7341891751788907/50000000000000000000 : ℝ) ≤ ((9546603779496111509/9550000000000000000 : ℝ)+2*(91405192347/47750000000000 : ℝ)*(1399/12500 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (9546603779496111509/9550000000000000000 : ℝ)+2*(91405192347/47750000000000 : ℝ)*(1399/12500 : ℝ)=(10000728593871311/10000000000000000 : ℝ) by norm_num, show 1+2*(7341891751788907/50000000000000000000 : ℝ)=(25007341891751788907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36793776044453591/100000000000000000000 : ℝ)+(7341891751788907/50000000000000000000 : ℝ) ≤ ((9546603779496111509/9550000000000000000 : ℝ)+(91405192347/47750000000000 : ℝ)*((14057/100000 : ℝ)+(1399/12500 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (9546603779496111509/9550000000000000000 : ℝ)+(91405192347/47750000000000 : ℝ)*((14057/100000 : ℝ)+(1399/12500 : ℝ))=(10001277025025393/10000000000000000 : ℝ) by norm_num, show 1+(36793776044453591/100000000000000000000 : ℝ)+(7341891751788907/50000000000000000000 : ℝ)=(20010295511909606281/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36793776044453591/100000000000000000000 : ℝ) ≤ ((9546603779496111509/9550000000000000000 : ℝ)+2*(91405192347/47750000000000 : ℝ)*(14057/100000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (9546603779496111509/9550000000000000000 : ℝ)+2*(91405192347/47750000000000 : ℝ)*(14057/100000 : ℝ)=(400073018247179/400000000000000 : ℝ) by norm_num, show 1+2*(36793776044453591/100000000000000000000 : ℝ)=(50036793776044453591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9546603779496111509/9550000000000000000 : ℝ)*(X 1 0+X 2 0)+(91405192347/47750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (9546603779496111509/9550000000000000000 : ℝ)) (alpha := (91405192347/47750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9546603779496111509/9550000000000000000 : ℝ)*(X 0 1+X 2 1)+(91405192347/47750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (9546603779496111509/9550000000000000000 : ℝ)) (alpha := (91405192347/47750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9546603779496111509/9550000000000000000 : ℝ)*(X 0 2+X 1 2)+(91405192347/47750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (9546603779496111509/9550000000000000000 : ℝ)) (alpha := (91405192347/47750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1102844313/5000000000 : ℝ)*X 0 0+(5394999949/10000000000 : ℝ)*X 0 1+(5263839391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336282893/2500000000 : ℝ)*X 1 0+(-2272244551/10000000000 : ℝ)*X 1 1+(82247491/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345131337/10000000000 : ℝ)*X 2 0+(1052767913/2000000000 : ℝ)*X 2 1+(-2272244677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188019651/5000000000 : ℝ)*X 0 0+(4249524007/10000000000 : ℝ)*X 0 1+(4506376469/10000000000 : ℝ)*X 0 2+(2188019651/5000000000 : ℝ)*X 1 0+(4249524007/10000000000 : ℝ)*X 1 1+(4506376469/10000000000 : ℝ)*X 1 2+(2188019651/5000000000 : ℝ)*X 2 0+(4249524007/10000000000 : ℝ)*X 2 1+(4506376469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551423441/2500000000 : ℝ)*X 0 0+(5264170697/10000000000 : ℝ)*X 0 1+(5394667491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312105321/10000000000 : ℝ)*X 1 0+(-428283317/2000000000 : ℝ)*X 1 1+(5394667491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312105321/10000000000 : ℝ)*X 2 0+(5394667491/10000000000 : ℝ)*X 2 1+(-428283317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875209897/2000000000 : ℝ)*X 0 0+(4505727661/10000000000 : ℝ)*X 0 1+(1062543797/2500000000 : ℝ)*X 0 2+(875209897/2000000000 : ℝ)*X 1 0+(4505727661/10000000000 : ℝ)*X 1 1+(1062543797/2500000000 : ℝ)*X 1 2+(875209897/2000000000 : ℝ)*X 2 0+(4505727661/10000000000 : ℝ)*X 2 1+(1062543797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2308878396548256519931751631/238750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2116036241/100000000000000 : ℝ)*(base19) + (1734386453/100000000000000 : ℝ)*(base23) + (12412207/50000000000000 : ℝ)*(lower2) + (46563731/12500000000000 : ℝ)*(upper3) + (38912647/50000000000000 : ℝ)*(upper5) + (5758853887497153/100000000000000 : ℝ)*(major0) + (5758853887497153/100000000000000 : ℝ)*(major1) + (2879426943748577/50000000000000 : ℝ)*(major2) + (3812154970151859/50000000000000 : ℝ)*(sp0) + (7624357877679527/100000000000000 : ℝ)*(sp1) + (1906089564832329/25000000000000 : ℝ)*(sp2) + (3893314283557863/100000000000000 : ℝ)*(sp3) + (50053412051/100000000000000 : ℝ)*(sp4) + (3317536417/10000000000000 : ℝ)*(sp7) + (243334216182627/6250000000000 : ℝ)*(f.failure) + (953044999214471/12500000000000 : ℝ)*(f.sum) + (13682411843429/4775000000000000000000000000 : ℝ)*base65 + (9762868257804366123/955000000000000000000000000000000 : ℝ)*base68 + (171602256896172693/477500000000000000000000000000000 : ℝ)*base69 + (824839114704366123/955000000000000000000000000000000 : ℝ)*base72 + (9503046593821/4775000000000000000000000000 : ℝ)*base74 + (9087496467551327307/477500000000000000000000000000000 : ℝ)*base76 + (6275779994013766123/955000000000000000000000000000000 : ℝ)*base78 + (27477115564778766123/955000000000000000000000000000000 : ℝ)*base80 + (24829130875557/4775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4641837/625000000000000000000 : ℝ)*base89 + (4641837/625000000000000000000 : ℝ)*base91 + (1608163/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5208624683107930384700274057/477500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028789741/100000000000000 : ℝ)*(base19) + (137938723/6250000000000 : ℝ)*(base23) + (54600611/25000000000000 : ℝ)*(upper3) + (81118431/100000000000000 : ℝ)*(lower4) + (13921631/6250000000000 : ℝ)*(upper5) + (5788055964979203/100000000000000 : ℝ)*(major0) + (5788055964979203/100000000000000 : ℝ)*(major1) + (5788055964979203/100000000000000 : ℝ)*(major2) + (6840301041/12500000000000 : ℝ)*(sp1) + (58828388233/100000000000000 : ℝ)*(sp2) + (6130417332999/80000000000 : ℝ)*(sp4) + (7662964915050681/100000000000000 : ℝ)*(sp5) + (1915740157710237/25000000000000 : ℝ)*(sp6) + (3913089900105827/100000000000000 : ℝ)*(sp7) + (3913089900105827/100000000000000 : ℝ)*(f.failure) + (6130417332999/80000000000 : ℝ)*(f.sum) + (27041393784743/4775000000000000000000000000 : ℝ)*base66 + (6556421648307147327/955000000000000000000000000000000 : ℝ)*base67 + (16881167949112147327/955000000000000000000000000000000 : ℝ)*base69 + (5210927004482147327/955000000000000000000000000000000 : ℝ)*base71 + (990919854501/149218750000000000000000000 : ℝ)*base73 + (12090841924797147327/955000000000000000000000000000000 : ℝ)*base75 + (14195054540022147327/955000000000000000000000000000000 : ℝ)*base77 + (28950998446642147327/955000000000000000000000000000000 : ℝ)*base79 + (19786058521243/4775000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25151037/10000000000000000000000 : ℝ)*base89 + (25151037/10000000000000000000000 : ℝ)*base91 + (25151037/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s7_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-22057297/100000000 : ℝ)*x 0 + (5394531153/10000000000 : ℝ)*x 1 + (526428117/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22057297/100000000 : ℝ)^8255 ≤ (13395450761997/100000000000000 : ℝ)^6207 := by
    have hnat : (22057297 : ℕ)^8255*100000000000000^6207 ≤ 13395450761997^6207*100000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22057297 100000000 13395450761997 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394531153/10000000000 : ℝ)^8255 ≤ (2750374499919/6250000000000 : ℝ)^6207 := by
    have hnat : (5394531153 : ℕ)^8255*6250000000000^6207 ≤ 2750374499919^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394531153 10000000000 2750374499919 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526428117/1000000000 : ℝ)^8255 ≤ (42598557218673/100000000000000 : ℝ)^6207 := by
    have hnat : (526428117 : ℕ)^8255*100000000000000^6207 ≤ 42598557218673^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526428117 1000000000 42598557218673 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22057297/100000000 : ℝ), (5394531153/10000000000 : ℝ), (526428117/1000000000 : ℝ)] ![(13395450761997/100000000000000 : ℝ), (2750374499919/6250000000000 : ℝ), (42598557218673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22057297/100000000 : ℝ)|^8255 ≤ (13395450761997/100000000000000 : ℝ)^6207
        have hw : |(-22057297/100000000 : ℝ)|=(22057297/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394531153/10000000000 : ℝ)|^8255 ≤ (2750374499919/6250000000000 : ℝ)^6207
        have hw : |(5394531153/10000000000 : ℝ)|=(5394531153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526428117/1000000000 : ℝ)|^8255 ≤ (42598557218673/100000000000000 : ℝ)^6207
        have hw : |(526428117/1000000000 : ℝ)|=(526428117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336253603/2500000000 : ℝ)*x 0 + (-141988561/625000000 : ℝ)*x 1 + (2632140613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336253603/2500000000 : ℝ)^8255 ≤ (21734797720311/50000000000000 : ℝ)^6207 := by
    have hnat : (1336253603 : ℕ)^8255*50000000000000^6207 ≤ 21734797720311^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336253603 2500000000 21734797720311 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141988561/625000000 : ℝ)^8255 ≤ (1393184672641/10000000000000 : ℝ)^6207 := by
    have hnat : (141988561 : ℕ)^8255*10000000000000^6207 ≤ 1393184672641^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141988561 625000000 1393184672641 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632140613/5000000000 : ℝ)^8255 ≤ (42598557821343/100000000000000 : ℝ)^6207 := by
    have hnat : (2632140613 : ℕ)^8255*100000000000000^6207 ≤ 42598557821343^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632140613 5000000000 42598557821343 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336253603/2500000000 : ℝ), (-141988561/625000000 : ℝ), (2632140613/5000000000 : ℝ)] ![(21734797720311/50000000000000 : ℝ), (1393184672641/10000000000000 : ℝ), (42598557821343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336253603/2500000000 : ℝ)|^8255 ≤ (21734797720311/50000000000000 : ℝ)^6207
        have hw : |(1336253603/2500000000 : ℝ)|=(1336253603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141988561/625000000 : ℝ)|^8255 ≤ (1393184672641/10000000000000 : ℝ)^6207
        have hw : |(-141988561/625000000 : ℝ)|=(141988561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632140613/5000000000 : ℝ)|^8255 ≤ (42598557821343/100000000000000 : ℝ)^6207
        have hw : |(2632140613/5000000000 : ℝ)|=(2632140613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672507223/5000000000 : ℝ)*x 0 + (1316070299/2500000000 : ℝ)*x 1 + (-2271816971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672507223/5000000000 : ℝ)^8255 ≤ (4346959580837/10000000000000 : ℝ)^6207 := by
    have hnat : (2672507223 : ℕ)^8255*10000000000000^6207 ≤ 4346959580837^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672507223 5000000000 4346959580837 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316070299/2500000000 : ℝ)^8255 ≤ (10649639374621/25000000000000 : ℝ)^6207 := by
    have hnat : (1316070299 : ℕ)^8255*25000000000000^6207 ≤ 10649639374621^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316070299 2500000000 10649639374621 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271816971/10000000000 : ℝ)^8255 ≤ (1393184668563/10000000000000 : ℝ)^6207 := by
    have hnat : (2271816971 : ℕ)^8255*10000000000000^6207 ≤ 1393184668563^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271816971 10000000000 1393184668563 10000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672507223/5000000000 : ℝ), (1316070299/2500000000 : ℝ), (-2271816971/10000000000 : ℝ)] ![(4346959580837/10000000000000 : ℝ), (10649639374621/25000000000000 : ℝ), (1393184668563/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672507223/5000000000 : ℝ)|^8255 ≤ (4346959580837/10000000000000 : ℝ)^6207
        have hw : |(2672507223/5000000000 : ℝ)|=(2672507223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316070299/2500000000 : ℝ)|^8255 ≤ (10649639374621/25000000000000 : ℝ)^6207
        have hw : |(1316070299/2500000000 : ℝ)|=(1316070299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271816971/10000000000 : ℝ)|^8255 ≤ (1393184668563/10000000000000 : ℝ)^6207
        have hw : |(-2271816971/10000000000 : ℝ)|=(2271816971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376062697/10000000000 : ℝ)*x 0 + (4250412583/10000000000 : ℝ)*x 1 + (901096341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376062697/10000000000 : ℝ)^8255 ≤ (33316473671001/100000000000000 : ℝ)^6207 := by
    have hnat : (4376062697 : ℕ)^8255*100000000000000^6207 ≤ 33316473671001^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376062697 10000000000 33316473671001 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250412583/10000000000 : ℝ)^8255 ≤ (32050285707647/100000000000000 : ℝ)^6207 := by
    have hnat : (4250412583 : ℕ)^8255*100000000000000^6207 ≤ 32050285707647^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250412583 10000000000 32050285707647 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901096341/2000000000 : ℝ)^8255 ≤ (17316620301491/50000000000000 : ℝ)^6207 := by
    have hnat : (901096341 : ℕ)^8255*50000000000000^6207 ≤ 17316620301491^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901096341 2000000000 17316620301491 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376062697/10000000000 : ℝ), (4250412583/10000000000 : ℝ), (901096341/2000000000 : ℝ)] ![(33316473671001/100000000000000 : ℝ), (32050285707647/100000000000000 : ℝ), (17316620301491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376062697/10000000000 : ℝ)|^8255 ≤ (33316473671001/100000000000000 : ℝ)^6207
        have hw : |(4376062697/10000000000 : ℝ)|=(4376062697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250412583/10000000000 : ℝ)|^8255 ≤ (32050285707647/100000000000000 : ℝ)^6207
        have hw : |(4250412583/10000000000 : ℝ)|=(4250412583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901096341/2000000000 : ℝ)|^8255 ≤ (17316620301491/50000000000000 : ℝ)^6207
        have hw : |(901096341/2000000000 : ℝ)|=(901096341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102867417/5000000000 : ℝ)*x 0 + (2632303869/5000000000 : ℝ)*x 1 + (269710169/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102867417/5000000000 : ℝ)^8255 ≤ (3348873057101/25000000000000 : ℝ)^6207 := by
    have hnat : (1102867417 : ℕ)^8255*25000000000000^6207 ≤ 3348873057101^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102867417 5000000000 3348873057101 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632303869/5000000000 : ℝ)^8255 ≤ (8520414352909/20000000000000 : ℝ)^6207 := by
    have hnat : (2632303869 : ℕ)^8255*20000000000000^6207 ≤ 8520414352909^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303869 5000000000 8520414352909 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269710169/500000000 : ℝ)^8255 ≤ (44002435994507/100000000000000 : ℝ)^6207 := by
    have hnat : (269710169 : ℕ)^8255*100000000000000^6207 ≤ 44002435994507^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269710169 500000000 44002435994507 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102867417/5000000000 : ℝ), (2632303869/5000000000 : ℝ), (269710169/500000000 : ℝ)] ![(3348873057101/25000000000000 : ℝ), (8520414352909/20000000000000 : ℝ), (44002435994507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102867417/5000000000 : ℝ)|^8255 ≤ (3348873057101/25000000000000 : ℝ)^6207
        have hw : |(-1102867417/5000000000 : ℝ)|=(1102867417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632303869/5000000000 : ℝ)|^8255 ≤ (8520414352909/20000000000000 : ℝ)^6207
        have hw : |(2632303869/5000000000 : ℝ)|=(2632303869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269710169/500000000 : ℝ)|^8255 ≤ (44002435994507/100000000000000 : ℝ)^6207
        have hw : |(269710169/500000000 : ℝ)|=(269710169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212488719/400000000 : ℝ)*x 0 + (-428378989/2000000000 : ℝ)*x 1 + (674275341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212488719/400000000 : ℝ)^8255 ≤ (21557612183479/50000000000000 : ℝ)^6207 := by
    have hnat : (212488719 : ℕ)^8255*50000000000000^6207 ≤ 21557612183479^6207*400000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212488719 400000000 21557612183479 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428378989/2000000000 : ℝ)^8255 ≤ (1610293337189/12500000000000 : ℝ)^6207 := by
    have hnat : (428378989 : ℕ)^8255*12500000000000^6207 ≤ 1610293337189^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428378989 2000000000 1610293337189 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674275341/1250000000 : ℝ)^8255 ≤ (550030361513/1250000000000 : ℝ)^6207 := by
    have hnat : (674275341 : ℕ)^8255*1250000000000^6207 ≤ 550030361513^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674275341 1250000000 550030361513 1250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212488719/400000000 : ℝ), (-428378989/2000000000 : ℝ), (674275341/1250000000 : ℝ)] ![(21557612183479/50000000000000 : ℝ), (1610293337189/12500000000000 : ℝ), (550030361513/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212488719/400000000 : ℝ)|^8255 ≤ (21557612183479/50000000000000 : ℝ)^6207
        have hw : |(212488719/400000000 : ℝ)|=(212488719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428378989/2000000000 : ℝ)|^8255 ≤ (1610293337189/12500000000000 : ℝ)^6207
        have hw : |(-428378989/2000000000 : ℝ)|=(428378989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674275341/1250000000 : ℝ)|^8255 ≤ (550030361513/1250000000000 : ℝ)^6207
        have hw : |(674275341/1250000000 : ℝ)|=(674275341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656108957/5000000000 : ℝ)*x 0 + (539420287/1000000000 : ℝ)*x 1 + (-428378967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656108957/5000000000 : ℝ)^8255 ≤ (1347350740891/3125000000000 : ℝ)^6207 := by
    have hnat : (2656108957 : ℕ)^8255*3125000000000^6207 ≤ 1347350740891^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656108957 5000000000 1347350740891 3125000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539420287/1000000000 : ℝ)^8255 ≤ (44002430461581/100000000000000 : ℝ)^6207 := by
    have hnat : (539420287 : ℕ)^8255*100000000000000^6207 ≤ 44002430461581^6207*1000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539420287 1000000000 44002430461581 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428378967/2000000000 : ℝ)^8255 ≤ (12882345817629/100000000000000 : ℝ)^6207 := by
    have hnat : (428378967 : ℕ)^8255*100000000000000^6207 ≤ 12882345817629^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428378967 2000000000 12882345817629 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656108957/5000000000 : ℝ), (539420287/1000000000 : ℝ), (-428378967/2000000000 : ℝ)] ![(1347350740891/3125000000000 : ℝ), (44002430461581/100000000000000 : ℝ), (12882345817629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656108957/5000000000 : ℝ)|^8255 ≤ (1347350740891/3125000000000 : ℝ)^6207
        have hw : |(2656108957/5000000000 : ℝ)|=(2656108957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539420287/1000000000 : ℝ)|^8255 ≤ (44002430461581/100000000000000 : ℝ)^6207
        have hw : |(539420287/1000000000 : ℝ)|=(539420287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428378967/2000000000 : ℝ)|^8255 ≤ (12882345817629/100000000000000 : ℝ)^6207
        have hw : |(-428378967/2000000000 : ℝ)|=(428378967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s7_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273504499/625000000 : ℝ)*x 0 + (4504842581/10000000000 : ℝ)*x 1 + (4251054709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273504499/625000000 : ℝ)^8255 ≤ (2082285481583/6250000000000 : ℝ)^6207 := by
    have hnat : (273504499 : ℕ)^8255*6250000000000^6207 ≤ 2082285481583^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273504499 625000000 2082285481583 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504842581/10000000000 : ℝ)^8255 ≤ (4328338357223/12500000000000 : ℝ)^6207 := by
    have hnat : (4504842581 : ℕ)^8255*12500000000000^6207 ≤ 4328338357223^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504842581 10000000000 4328338357223 12500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251054709/10000000000 : ℝ)^8255 ≤ (5129076069/16000000000 : ℝ)^6207 := by
    have hnat : (4251054709 : ℕ)^8255*16000000000^6207 ≤ 5129076069^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251054709 10000000000 5129076069 16000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273504499/625000000 : ℝ), (4504842581/10000000000 : ℝ), (4251054709/10000000000 : ℝ)] ![(2082285481583/6250000000000 : ℝ), (4328338357223/12500000000000 : ℝ), (5129076069/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273504499/625000000 : ℝ)|^8255 ≤ (2082285481583/6250000000000 : ℝ)^6207
        have hw : |(273504499/625000000 : ℝ)|=(273504499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504842581/10000000000 : ℝ)|^8255 ≤ (4328338357223/12500000000000 : ℝ)^6207
        have hw : |(4504842581/10000000000 : ℝ)|=(4504842581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251054709/10000000000 : ℝ)|^8255 ≤ (5129076069/16000000000 : ℝ)^6207
        have hw : |(4251054709/10000000000 : ℝ)|=(4251054709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (4127/1024 : ℝ) ≤ (372678294996709/2500000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^4127 ≤ (372678294996709/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5617 : ℕ)^4127*2500000000000000000^1024 ≤ 372678294996709^1024*50000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 372678294996709 2500000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (372678294996709/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14013/100000 : ℝ) ^ (4127/1024 : ℝ) ≤ (36331811417808003/100000000000000000000 : ℝ) := by
    have hpowers : (14013/100000 : ℝ)^4127 ≤ (36331811417808003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14013 : ℕ)^4127*100000000000000000000^1024 ≤ 36331811417808003^1024*100000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14013 100000 36331811417808003 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14013/100000 : ℝ)) (X := (36331811417808003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250372678294996709/1250000000000000000 : ℝ) ≤ (5000369837468337/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (1250372678294996709/1250000000000000000 : ℝ)^1024 ≤ (5000369837468337/5000000000000000 : ℝ)^4127 := by
      have hnat : (1250372678294996709 : ℕ)^1024*5000000000000000^4127 ≤ 5000369837468337^4127*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250372678294996709 1250000000000000000 5000369837468337 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000369837468337/5000000000000000 : ℝ)) (X := (1250372678294996709/1250000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051238943217676363/100000000000000000000 : ℝ) ≤ (5000635553355787/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (100051238943217676363/100000000000000000000 : ℝ)^1024 ≤ (5000635553355787/5000000000000000 : ℝ)^4127 := by
      have hnat : (100051238943217676363 : ℕ)^1024*5000000000000000^4127 ≤ 5000635553355787^4127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051238943217676363 100000000000000000000 5000635553355787 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000635553355787/5000000000000000 : ℝ)) (X := (100051238943217676363/100000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036331811417808003/50000000000000000000 : ℝ) ≤ (5000901269243237/5000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50036331811417808003/50000000000000000000 : ℝ)^1024 ≤ (5000901269243237/5000000000000000 : ℝ)^4127 := by
      have hnat : (50036331811417808003 : ℕ)^1024*5000000000000000^4127 ≤ 5000901269243237^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036331811417808003 50000000000000000000 5000901269243237 5000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000901269243237/5000000000000000 : ℝ)) (X := (50036331811417808003/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372678294996709/2500000000000000000 : ℝ) ≤ ((13890057673765281923/13895000000000000000 : ℝ)+2*(5314317749/2779000000000 : ℝ)*(5617/50000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (13890057673765281923/13895000000000000000 : ℝ)+2*(5314317749/2779000000000 : ℝ)*(5617/50000 : ℝ)=(5000369837468337/5000000000000000 : ℝ) by norm_num, show 1+2*(372678294996709/2500000000000000000 : ℝ)=(1250372678294996709/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36331811417808003/100000000000000000000 : ℝ)+(372678294996709/2500000000000000000 : ℝ) ≤ ((13890057673765281923/13895000000000000000 : ℝ)+(5314317749/2779000000000 : ℝ)*((14013/100000 : ℝ)+(5617/50000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (13890057673765281923/13895000000000000000 : ℝ)+(5314317749/2779000000000 : ℝ)*((14013/100000 : ℝ)+(5617/50000 : ℝ))=(5000635553355787/5000000000000000 : ℝ) by norm_num, show 1+(36331811417808003/100000000000000000000 : ℝ)+(372678294996709/2500000000000000000 : ℝ)=(100051238943217676363/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36331811417808003/100000000000000000000 : ℝ) ≤ ((13890057673765281923/13895000000000000000 : ℝ)+2*(5314317749/2779000000000 : ℝ)*(14013/100000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (13890057673765281923/13895000000000000000 : ℝ)+2*(5314317749/2779000000000 : ℝ)*(14013/100000 : ℝ)=(5000901269243237/5000000000000000 : ℝ) by norm_num, show 1+2*(36331811417808003/100000000000000000000 : ℝ)=(50036331811417808003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13890057673765281923/13895000000000000000 : ℝ)*(X 1 0+X 2 0)+(5314317749/2779000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (13890057673765281923/13895000000000000000 : ℝ)) (alpha := (5314317749/2779000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13890057673765281923/13895000000000000000 : ℝ)*(X 0 1+X 2 1)+(5314317749/2779000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (13890057673765281923/13895000000000000000 : ℝ)) (alpha := (5314317749/2779000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13890057673765281923/13895000000000000000 : ℝ)*(X 0 2+X 1 2)+(5314317749/2779000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (13890057673765281923/13895000000000000000 : ℝ)) (alpha := (5314317749/2779000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22057297/100000000 : ℝ)*X 0 0+(5394531153/10000000000 : ℝ)*X 0 1+(526428117/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336253603/2500000000 : ℝ)*X 1 0+(-141988561/625000000 : ℝ)*X 1 1+(2632140613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672507223/5000000000 : ℝ)*X 2 0+(1316070299/2500000000 : ℝ)*X 2 1+(-2271816971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376062697/10000000000 : ℝ)*X 0 0+(4250412583/10000000000 : ℝ)*X 0 1+(901096341/2000000000 : ℝ)*X 0 2+(4376062697/10000000000 : ℝ)*X 1 0+(4250412583/10000000000 : ℝ)*X 1 1+(901096341/2000000000 : ℝ)*X 1 2+(4376062697/10000000000 : ℝ)*X 2 0+(4250412583/10000000000 : ℝ)*X 2 1+(901096341/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102867417/5000000000 : ℝ)*X 0 0+(2632303869/5000000000 : ℝ)*X 0 1+(269710169/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212488719/400000000 : ℝ)*X 1 0+(-428378989/2000000000 : ℝ)*X 1 1+(674275341/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656108957/5000000000 : ℝ)*X 2 0+(539420287/1000000000 : ℝ)*X 2 1+(-428378967/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273504499/625000000 : ℝ)*X 0 0+(4504842581/10000000000 : ℝ)*X 0 1+(4251054709/10000000000 : ℝ)*X 0 2+(273504499/625000000 : ℝ)*X 1 0+(4504842581/10000000000 : ℝ)*X 1 1+(4251054709/10000000000 : ℝ)*X 1 2+(273504499/625000000 : ℝ)*X 2 0+(4504842581/10000000000 : ℝ)*X 2 1+(4251054709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420354807350058540203963709/99250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907507577/100000000000000 : ℝ)*(base19) + (903939493/100000000000000 : ℝ)*(base23) + (875343/3125000000000 : ℝ)*(lower2) + (3842873/3125000000000 : ℝ)*(upper3) + (6337607/6250000000000 : ℝ)*(upper5) + (5799065376805827/100000000000000 : ℝ)*(major0) + (5799065376805827/100000000000000 : ℝ)*(major1) + (5799065376805827/100000000000000 : ℝ)*(major2) + (3838785367102117/50000000000000 : ℝ)*(sp0) + (7677596749936131/100000000000000 : ℝ)*(sp1) + (959699594188027/12500000000000 : ℝ)*(sp2) + (3920518914531833/100000000000000 : ℝ)*(sp3) + (13461619737/50000000000000 : ℝ)*(sp4) + (54845543/390625000000 : ℝ)*(sp7) + (98013323874771/2500000000000 : ℝ)*(f.failure) + (1919399414360927/25000000000000 : ℝ)*(f.sum) + (2159288997949/397000000000000000000000000 : ℝ)*base66 + (1237885931205762097/198500000000000000000000000000000 : ℝ)*base68 + (1948167312498237903/198500000000000000000000000000000 : ℝ)*base69 + (2505677550689762097/198500000000000000000000000000000 : ℝ)*base72 + (152349219327/397000000000000000000000000 : ℝ)*base74 + (768743692357237903/198500000000000000000000000000000 : ℝ)*base75 + (1586103346943762097/198500000000000000000000000000000 : ℝ)*base78 + (3534644219522762097/198500000000000000000000000000000 : ℝ)*base80 + (880256568017/397000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (37101/250000000000000000000 : ℝ)*base89 + (37101/250000000000000000000 : ℝ)*base91 + (37101/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4786329613806106776039716223/694750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (556885729/25000000000000 : ℝ)*(base19) + (42838461/1562500000000 : ℝ)*(base23) + (254686259/100000000000000 : ℝ)*(upper2) + (6284339/12500000000000 : ℝ)*(upper3) + (34889409/100000000000000 : ℝ)*(upper5) + (5828298935451367/100000000000000 : ℝ)*(major0) + (5828298935451367/100000000000000 : ℝ)*(major1) + (5828298935451367/100000000000000 : ℝ)*(major2) + (18187273337/50000000000000 : ℝ)*(sp1) + (1126885693/2000000000000 : ℝ)*(sp2) + (3858150480919317/50000000000000 : ℝ)*(sp4) + (1929065589937261/25000000000000 : ℝ)*(sp5) + (6028313965541/78125000000 : ℝ)*(sp6) + (788059335884263/20000000000000 : ℝ)*(sp7) + (788059335884263/20000000000000 : ℝ)*(f.failure) + (3858150480919317/50000000000000 : ℝ)*(f.sum) + (2388862561593/347375000000000000000000000 : ℝ)*base65 + (769256638335823037/198500000000000000000000000000000 : ℝ)*base68 + (1439976495913823037/198500000000000000000000000000000 : ℝ)*base70 + (506303043425676963/198500000000000000000000000000000 : ℝ)*base71 + (10945833312691/2779000000000000000000000000 : ℝ)*base73 + (1480024155959823037/198500000000000000000000000000000 : ℝ)*base76 + (455207350573676963/198500000000000000000000000000000 : ℝ)*base77 + (4586433296273823037/198500000000000000000000000000000 : ℝ)*base80 + (441041661251/555800000000000000000000000 : ℝ)*base82 + (10909753/2000000000000000000000 : ℝ)*base89 + (10909753/2000000000000000000000 : ℝ)*base91 + (10909753/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1062_s8_0 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102868747/5000000000 : ℝ)*x 0 + (5394424511/10000000000 : ℝ)*x 1 + (2632191413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102868747/5000000000 : ℝ)^8255 ≤ (3348878428191/25000000000000 : ℝ)^6207 := by
    have hnat : (1102868747 : ℕ)^8255*25000000000000^6207 ≤ 3348878428191^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102868747 5000000000 3348878428191 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394424511/10000000000 : ℝ)^8255 ≤ (1760193401339/4000000000000 : ℝ)^6207 := by
    have hnat : (5394424511 : ℕ)^8255*4000000000000^6207 ≤ 1760193401339^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394424511 10000000000 1760193401339 4000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632191413/5000000000 : ℝ)^8255 ≤ (42599651239389/100000000000000 : ℝ)^6207 := by
    have hnat : (2632191413 : ℕ)^8255*100000000000000^6207 ≤ 42599651239389^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632191413 5000000000 42599651239389 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102868747/5000000000 : ℝ), (5394424511/10000000000 : ℝ), (2632191413/5000000000 : ℝ)] ![(3348878428191/25000000000000 : ℝ), (1760193401339/4000000000000 : ℝ), (42599651239389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102868747/5000000000 : ℝ)|^8255 ≤ (3348878428191/25000000000000 : ℝ)^6207
        have hw : |(-1102868747/5000000000 : ℝ)|=(1102868747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394424511/10000000000 : ℝ)|^8255 ≤ (1760193401339/4000000000000 : ℝ)^6207
        have hw : |(5394424511/10000000000 : ℝ)|=(5394424511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632191413/5000000000 : ℝ)|^8255 ≤ (42599651239389/100000000000000 : ℝ)^6207
        have hw : |(2632191413/5000000000 : ℝ)|=(2632191413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_1 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344988279/10000000000 : ℝ)*x 0 + (-113585877/500000000 : ℝ)*x 1 + (2632191423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344988279/10000000000 : ℝ)^8255 ≤ (21734656391413/50000000000000 : ℝ)^6207 := by
    have hnat : (5344988279 : ℕ)^8255*50000000000000^6207 ≤ 21734656391413^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344988279 10000000000 21734656391413 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113585877/500000000 : ℝ)^8255 ≤ (6965517872229/50000000000000 : ℝ)^6207 := by
    have hnat : (113585877 : ℕ)^8255*50000000000000^6207 ≤ 6965517872229^6207*500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113585877 500000000 6965517872229 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632191423/5000000000 : ℝ)^8255 ≤ (42599651454629/100000000000000 : ℝ)^6207 := by
    have hnat : (2632191423 : ℕ)^8255*100000000000000^6207 ≤ 42599651454629^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632191423 5000000000 42599651454629 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344988279/10000000000 : ℝ), (-113585877/500000000 : ℝ), (2632191423/5000000000 : ℝ)] ![(21734656391413/50000000000000 : ℝ), (6965517872229/50000000000000 : ℝ), (42599651454629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344988279/10000000000 : ℝ)|^8255 ≤ (21734656391413/50000000000000 : ℝ)^6207
        have hw : |(5344988279/10000000000 : ℝ)|=(5344988279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113585877/500000000 : ℝ)|^8255 ≤ (6965517872229/50000000000000 : ℝ)^6207
        have hw : |(-113585877/500000000 : ℝ)|=(113585877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632191423/5000000000 : ℝ)|^8255 ≤ (42599651454629/100000000000000 : ℝ)^6207
        have hw : |(2632191423/5000000000 : ℝ)|=(2632191423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_2 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66812353/125000000 : ℝ)*x 0 + (5264382851/10000000000 : ℝ)*x 1 + (-454343517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66812353/125000000 : ℝ)^8255 ≤ (43469312360997/100000000000000 : ℝ)^6207 := by
    have hnat : (66812353 : ℕ)^8255*100000000000000^6207 ≤ 43469312360997^6207*125000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66812353 125000000 43469312360997 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264382851/10000000000 : ℝ)^8255 ≤ (1064991287711/2500000000000 : ℝ)^6207 := by
    have hnat : (5264382851 : ℕ)^8255*2500000000000^6207 ≤ 1064991287711^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264382851 10000000000 1064991287711 2500000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454343517/2000000000 : ℝ)^8255 ≤ (13931036111467/100000000000000 : ℝ)^6207 := by
    have hnat : (454343517 : ℕ)^8255*100000000000000^6207 ≤ 13931036111467^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454343517 2000000000 13931036111467 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66812353/125000000 : ℝ), (5264382851/10000000000 : ℝ), (-454343517/2000000000 : ℝ)] ![(43469312360997/100000000000000 : ℝ), (1064991287711/2500000000000 : ℝ), (13931036111467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66812353/125000000 : ℝ)|^8255 ≤ (43469312360997/100000000000000 : ℝ)^6207
        have hw : |(66812353/125000000 : ℝ)|=(66812353/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264382851/10000000000 : ℝ)|^8255 ≤ (1064991287711/2500000000000 : ℝ)^6207
        have hw : |(5264382851/10000000000 : ℝ)|=(5264382851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454343517/2000000000 : ℝ)|^8255 ≤ (13931036111467/100000000000000 : ℝ)^6207
        have hw : |(-454343517/2000000000 : ℝ)|=(454343517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_3 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376067927/10000000000 : ℝ)*x 0 + (850123177/2000000000 : ℝ)*x 1 + (1126319273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376067927/10000000000 : ℝ)^8255 ≤ (33316526626687/100000000000000 : ℝ)^6207 := by
    have hnat : (4376067927 : ℕ)^8255*100000000000000^6207 ≤ 33316526626687^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376067927 10000000000 33316526626687 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850123177/2000000000 : ℝ)^8255 ≤ (400654056733/1250000000000 : ℝ)^6207 := by
    have hnat : (850123177 : ℕ)^8255*1250000000000^6207 ≤ 400654056733^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850123177 2000000000 400654056733 1250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126319273/2500000000 : ℝ)^8255 ≤ (34631148817229/100000000000000 : ℝ)^6207 := by
    have hnat : (1126319273 : ℕ)^8255*100000000000000^6207 ≤ 34631148817229^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126319273 2500000000 34631148817229 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376067927/10000000000 : ℝ), (850123177/2000000000 : ℝ), (1126319273/2500000000 : ℝ)] ![(33316526626687/100000000000000 : ℝ), (400654056733/1250000000000 : ℝ), (34631148817229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376067927/10000000000 : ℝ)|^8255 ≤ (33316526626687/100000000000000 : ℝ)^6207
        have hw : |(4376067927/10000000000 : ℝ)|=(4376067927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850123177/2000000000 : ℝ)|^8255 ≤ (400654056733/1250000000000 : ℝ)^6207
        have hw : |(850123177/2000000000 : ℝ)|=(850123177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126319273/2500000000 : ℝ)|^8255 ≤ (34631148817229/100000000000000 : ℝ)^6207
        have hw : |(1126319273/2500000000 : ℝ)|=(1126319273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_4 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102871263/5000000000 : ℝ)*x 0 + (5264708459/10000000000 : ℝ)*x 1 + (674262217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102871263/5000000000 : ℝ)^8255 ≤ (6697777177691/50000000000000 : ℝ)^6207 := by
    have hnat : (1102871263 : ℕ)^8255*50000000000000^6207 ≤ 6697777177691^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102871263 5000000000 6697777177691 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264708459/10000000000 : ℝ)^8255 ≤ (10650788936239/25000000000000 : ℝ)^6207 := by
    have hnat : (5264708459 : ℕ)^8255*25000000000000^6207 ≤ 10650788936239^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264708459 10000000000 10650788936239 25000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674262217/1250000000 : ℝ)^8255 ≤ (44001289879581/100000000000000 : ℝ)^6207 := by
    have hnat : (674262217 : ℕ)^8255*100000000000000^6207 ≤ 44001289879581^6207*1250000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674262217 1250000000 44001289879581 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102871263/5000000000 : ℝ), (5264708459/10000000000 : ℝ), (674262217/1250000000 : ℝ)] ![(6697777177691/50000000000000 : ℝ), (10650788936239/25000000000000 : ℝ), (44001289879581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102871263/5000000000 : ℝ)|^8255 ≤ (6697777177691/50000000000000 : ℝ)^6207
        have hw : |(-1102871263/5000000000 : ℝ)|=(1102871263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264708459/10000000000 : ℝ)|^8255 ≤ (10650788936239/25000000000000 : ℝ)^6207
        have hw : |(5264708459/10000000000 : ℝ)|=(5264708459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674262217/1250000000 : ℝ)|^8255 ≤ (44001289879581/100000000000000 : ℝ)^6207
        have hw : |(674262217/1250000000 : ℝ)|=(674262217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_5 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312243727/10000000000 : ℝ)*x 0 + (-535500663/2500000000 : ℝ)*x 1 + (1348524423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312243727/10000000000 : ℝ)^8255 ≤ (8623100467837/20000000000000 : ℝ)^6207 := by
    have hnat : (5312243727 : ℕ)^8255*20000000000000^6207 ≤ 8623100467837^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312243727 10000000000 8623100467837 20000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535500663/2500000000 : ℝ)^8255 ≤ (6441604122957/50000000000000 : ℝ)^6207 := by
    have hnat : (535500663 : ℕ)^8255*50000000000000^6207 ≤ 6441604122957^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535500663 2500000000 6441604122957 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348524423/2500000000 : ℝ)^8255 ≤ (44001289402233/100000000000000 : ℝ)^6207 := by
    have hnat : (1348524423 : ℕ)^8255*100000000000000^6207 ≤ 44001289402233^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348524423 2500000000 44001289402233 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312243727/10000000000 : ℝ), (-535500663/2500000000 : ℝ), (1348524423/2500000000 : ℝ)] ![(8623100467837/20000000000000 : ℝ), (6441604122957/50000000000000 : ℝ), (44001289402233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312243727/10000000000 : ℝ)|^8255 ≤ (8623100467837/20000000000000 : ℝ)^6207
        have hw : |(5312243727/10000000000 : ℝ)|=(5312243727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535500663/2500000000 : ℝ)|^8255 ≤ (6441604122957/50000000000000 : ℝ)^6207
        have hw : |(-535500663/2500000000 : ℝ)|=(535500663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348524423/2500000000 : ℝ)|^8255 ≤ (44001289402233/100000000000000 : ℝ)^6207
        have hw : |(1348524423/2500000000 : ℝ)|=(1348524423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_6 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328060909/2500000000 : ℝ)*x 0 + (1078819529/2000000000 : ℝ)*x 1 + (-1071001419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328060909/2500000000 : ℝ)^8255 ≤ (2694718834807/6250000000000 : ℝ)^6207 := by
    have hnat : (1328060909 : ℕ)^8255*6250000000000^6207 ≤ 2694718834807^6207*2500000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328060909 2500000000 2694718834807 6250000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078819529/2000000000 : ℝ)^8255 ≤ (44001288892339/100000000000000 : ℝ)^6207 := by
    have hnat : (1078819529 : ℕ)^8255*100000000000000^6207 ≤ 44001288892339^6207*2000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078819529 2000000000 44001288892339 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071001419/5000000000 : ℝ)^8255 ≤ (12883209733741/100000000000000 : ℝ)^6207 := by
    have hnat : (1071001419 : ℕ)^8255*100000000000000^6207 ≤ 12883209733741^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071001419 5000000000 12883209733741 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328060909/2500000000 : ℝ), (1078819529/2000000000 : ℝ), (-1071001419/5000000000 : ℝ)] ![(2694718834807/6250000000000 : ℝ), (44001288892339/100000000000000 : ℝ), (12883209733741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328060909/2500000000 : ℝ)|^8255 ≤ (2694718834807/6250000000000 : ℝ)^6207
        have hw : |(1328060909/2500000000 : ℝ)|=(1328060909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078819529/2000000000 : ℝ)|^8255 ≤ (44001288892339/100000000000000 : ℝ)^6207
        have hw : |(1078819529/2000000000 : ℝ)|=(1078819529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071001419/5000000000 : ℝ)|^8255 ≤ (12883209733741/100000000000000 : ℝ)^6207
        have hw : |(-1071001419/5000000000 : ℝ)|=(1071001419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1062_s8_7 (p : ℝ) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376077669/10000000000 : ℝ)*x 0 + (2252319727/5000000000 : ℝ)*x 1 + (265703501/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376077669/10000000000 : ℝ)^8255 ≤ (33316625268099/100000000000000 : ℝ)^6207 := by
    have hnat : (4376077669 : ℕ)^8255*100000000000000^6207 ≤ 33316625268099^6207*10000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376077669 10000000000 33316625268099 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252319727/5000000000 : ℝ)^8255 ≤ (17312315180347/50000000000000 : ℝ)^6207 := by
    have hnat : (2252319727 : ℕ)^8255*50000000000000^6207 ≤ 17312315180347^6207*5000000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252319727 5000000000 17312315180347 50000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265703501/625000000 : ℝ)^8255 ≤ (32058744355689/100000000000000 : ℝ)^6207 := by
    have hnat : (265703501 : ℕ)^8255*100000000000000^6207 ≤ 32058744355689^6207*625000000^8255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265703501 625000000 32058744355689 100000000000000 8255 6207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8255/2048 : ℝ)) 8255 6207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376077669/10000000000 : ℝ), (2252319727/5000000000 : ℝ), (265703501/625000000 : ℝ)] ![(33316625268099/100000000000000 : ℝ), (17312315180347/50000000000000 : ℝ), (32058744355689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376077669/10000000000 : ℝ)|^8255 ≤ (33316625268099/100000000000000 : ℝ)^6207
        have hw : |(4376077669/10000000000 : ℝ)|=(4376077669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252319727/5000000000 : ℝ)|^8255 ≤ (17312315180347/50000000000000 : ℝ)^6207
        have hw : |(2252319727/5000000000 : ℝ)|=(2252319727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265703501/625000000 : ℝ)|^8255 ≤ (32058744355689/100000000000000 : ℝ)^6207
        have hw : |(265703501/625000000 : ℝ)|=(265703501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1062_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7/50 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (4127/1024 : ℝ) ≤ (14960684315605383/100000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^4127 ≤ (14960684315605383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2811 : ℕ)^4127*100000000000000000000^1024 ≤ 14960684315605383^1024*25000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 14960684315605383 100000000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (14960684315605383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (4127/1024 : ℝ) ≤ (905685764133247/2500000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^4127 ≤ (905685764133247/2500000000000000000 : ℝ)^1024 := by
      have hnat : (14003 : ℕ)^4127*2500000000000000000^1024 ≤ 905685764133247^1024*100000^4127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 905685764133247 2500000000000000000 4127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (905685764133247/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014960684315605383/50000000000000000000 : ℝ) ≤ (10000742331852809/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (50014960684315605383/50000000000000000000 : ℝ)^1024 ≤ (10000742331852809/10000000000000000 : ℝ)^4127 := by
      have hnat : (50014960684315605383 : ℕ)^1024*10000000000000000^4127 ≤ 10000742331852809^4127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014960684315605383 50000000000000000000 10000742331852809 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000742331852809/10000000000000000 : ℝ)) (X := (50014960684315605383/50000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051188114880935263/100000000000000000000 : ℝ) ≤ (312539682688547/312500000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (100051188114880935263/100000000000000000000 : ℝ)^1024 ≤ (312539682688547/312500000000000 : ℝ)^4127 := by
      have hnat : (100051188114880935263 : ℕ)^1024*312500000000000^4127 ≤ 312539682688547^4127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051188114880935263 100000000000000000000 312539682688547 312500000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312539682688547/312500000000000 : ℝ)) (X := (100051188114880935263/100000000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250905685764133247/1250000000000000000 : ℝ) ≤ (10001797360214199/10000000000000000 : ℝ) ^ (4127/1024 : ℝ) := by
    have hpowers : (1250905685764133247/1250000000000000000 : ℝ)^1024 ≤ (10001797360214199/10000000000000000 : ℝ)^4127 := by
      have hnat : (1250905685764133247 : ℕ)^1024*10000000000000000^4127 ≤ 10001797360214199^4127*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250905685764133247 1250000000000000000 10001797360214199 10000000000000000 1024 4127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001797360214199/10000000000000000 : ℝ)) (X := (1250905685764133247/1250000000000000000 : ℝ)) (by norm_num) 4127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14960684315605383/100000000000000000000 : ℝ) ≤ ((27580185354686430871/27590000000000000000 : ℝ)+2*(105502836139/55180000000000 : ℝ)*(2811/25000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (27580185354686430871/27590000000000000000 : ℝ)+2*(105502836139/55180000000000 : ℝ)*(2811/25000 : ℝ)=(10000742331852809/10000000000000000 : ℝ) by norm_num, show 1+2*(14960684315605383/100000000000000000000 : ℝ)=(50014960684315605383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(905685764133247/2500000000000000000 : ℝ)+(14960684315605383/100000000000000000000 : ℝ) ≤ ((27580185354686430871/27590000000000000000 : ℝ)+(105502836139/55180000000000 : ℝ)*((14003/100000 : ℝ)+(2811/25000 : ℝ)))^(4127/1024 : ℝ) := by
    rw [show (27580185354686430871/27590000000000000000 : ℝ)+(105502836139/55180000000000 : ℝ)*((14003/100000 : ℝ)+(2811/25000 : ℝ))=(312539682688547/312500000000000 : ℝ) by norm_num, show 1+(905685764133247/2500000000000000000 : ℝ)+(14960684315605383/100000000000000000000 : ℝ)=(100051188114880935263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(905685764133247/2500000000000000000 : ℝ) ≤ ((27580185354686430871/27590000000000000000 : ℝ)+2*(105502836139/55180000000000 : ℝ)*(14003/100000 : ℝ))^(4127/1024 : ℝ) := by
    rw [show (27580185354686430871/27590000000000000000 : ℝ)+2*(105502836139/55180000000000 : ℝ)*(14003/100000 : ℝ)=(10001797360214199/10000000000000000 : ℝ) by norm_num, show 1+2*(905685764133247/2500000000000000000 : ℝ)=(1250905685764133247/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27580185354686430871/27590000000000000000 : ℝ)*(X 1 0+X 2 0)+(105502836139/55180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27580185354686430871/27590000000000000000 : ℝ)) (alpha := (105502836139/55180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27580185354686430871/27590000000000000000 : ℝ)*(X 0 1+X 2 1)+(105502836139/55180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27580185354686430871/27590000000000000000 : ℝ)) (alpha := (105502836139/55180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27580185354686430871/27590000000000000000 : ℝ)*(X 0 2+X 1 2)+(105502836139/55180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4127/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27580185354686430871/27590000000000000000 : ℝ)) (alpha := (105502836139/55180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1102868747/5000000000 : ℝ)*X 0 0+(5394424511/10000000000 : ℝ)*X 0 1+(2632191413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344988279/10000000000 : ℝ)*X 1 0+(-113585877/500000000 : ℝ)*X 1 1+(2632191423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66812353/125000000 : ℝ)*X 2 0+(5264382851/10000000000 : ℝ)*X 2 1+(-454343517/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376067927/10000000000 : ℝ)*X 0 0+(850123177/2000000000 : ℝ)*X 0 1+(1126319273/2500000000 : ℝ)*X 0 2+(4376067927/10000000000 : ℝ)*X 1 0+(850123177/2000000000 : ℝ)*X 1 1+(1126319273/2500000000 : ℝ)*X 1 2+(4376067927/10000000000 : ℝ)*X 2 0+(850123177/2000000000 : ℝ)*X 2 1+(1126319273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102871263/5000000000 : ℝ)*X 0 0+(5264708459/10000000000 : ℝ)*X 0 1+(674262217/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312243727/10000000000 : ℝ)*X 1 0+(-535500663/2500000000 : ℝ)*X 1 1+(1348524423/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328060909/2500000000 : ℝ)*X 2 0+(1078819529/2000000000 : ℝ)*X 2 1+(-1071001419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376077669/10000000000 : ℝ)*X 0 0+(2252319727/5000000000 : ℝ)*X 0 1+(265703501/625000000 : ℝ)*X 0 2+(4376077669/10000000000 : ℝ)*X 1 0+(2252319727/5000000000 : ℝ)*X 1 1+(265703501/625000000 : ℝ)*X 1 2+(4376077669/10000000000 : ℝ)*X 2 0+(2252319727/5000000000 : ℝ)*X 2 1+(265703501/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1062_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2034046820237034324818575173/344875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59961247/5000000000000 : ℝ)*(base19) + (557657183/50000000000000 : ℝ)*(base23) + (14859457/100000000000000 : ℝ)*(lower2) + (43576689/25000000000000 : ℝ)*(upper3) + (1126689/1562500000000 : ℝ)*(upper5) + (1452091286961879/25000000000000 : ℝ)*(major0) + (1452091286961879/25000000000000 : ℝ)*(major1) + (5808365147847517/100000000000000 : ℝ)*(major2) + (7689878384778673/100000000000000 : ℝ)*(sp0) + (7689908714703481/100000000000000 : ℝ)*(sp1) + (3844954399307027/50000000000000 : ℝ)*(sp2) + (1963400985760183/50000000000000 : ℝ)*(sp3) + (31529149747/100000000000000 : ℝ)*(sp4) + (2276706093/12500000000000 : ℝ)*(sp7) + (392682018516911/10000000000000 : ℝ)*(f.failure) + (384495495696421/5000000000000 : ℝ)*(f.sum) + (584344126273/220720000000000000000000000 : ℝ)*base66 + (289535595604488439/22250000000000000000000000000000 : ℝ)*base67 + (2459206711337497307/2759000000000000000000000000000000 : ℝ)*base69 + (318476732305738439/22250000000000000000000000000000 : ℝ)*base71 + (3314969458441/5518000000000000000000000000 : ℝ)*base74 + (50245816435786502693/2759000000000000000000000000000000 : ℝ)*base76 + (1192429121689233391/689750000000000000000000000000000 : ℝ)*base78 + (10758990757446266609/689750000000000000000000000000000 : ℝ)*base79 + (163235264413/55180000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7971441/1000000000000000000000 : ℝ)*base89 + (7971441/1000000000000000000000 : ℝ)*base91 + (2028559/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117387877728300218153097699/43109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169859723/50000000000000 : ℝ)*(base19) + (122819481/50000000000000 : ℝ)*(base23) + (3467479/12500000000000 : ℝ)*(lower1) + (52904137/100000000000000 : ℝ)*(upper2) + (1007499/12500000000000 : ℝ)*(upper5) + (364850026091027/6250000000000 : ℝ)*(major0) + (364850026091027/6250000000000 : ℝ)*(major1) + (364850026091027/6250000000000 : ℝ)*(major2) + (2638455289/100000000000000 : ℝ)*(sp0) + (9941068451/100000000000000 : ℝ)*(sp1) + (7728613039371643/100000000000000 : ℝ)*(sp4) + (1932151349259759/25000000000000 : ℝ)*(sp5) + (7728615432187971/100000000000000 : ℝ)*(sp6) + (1973292533159223/50000000000000 : ℝ)*(sp7) + (1973292533159223/50000000000000 : ℝ)*(f.failure) + (7728615677826933/100000000000000 : ℝ)*(f.sum) + (930145523019/1379500000000000000000000000 : ℝ)*base65 + (2756781272846644517/172437500000000000000000000000000 : ℝ)*base67 + (1336490699741519517/172437500000000000000000000000000 : ℝ)*base69 + (870916816788832017/172437500000000000000000000000000 : ℝ)*base71 + (807908161/13795000000000000000000000 : ℝ)*base74 + (797049382275019517/172437500000000000000000000000000 : ℝ)*base75 + (1939393099148519517/172437500000000000000000000000000 : ℝ)*base77 + (771705806563417983/172437500000000000000000000000000 : ℝ)*base80 + (2326305678303/1379500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (29825513/5000000000000000000000 : ℝ)*base89 + (29825513/5000000000000000000000 : ℝ)*base91 + (29825513/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1062_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1062_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1062_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1062_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1062_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1062_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4127/1024 : ℝ) ≤ p) (hpb : p ≤ (8255/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147915231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1062_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

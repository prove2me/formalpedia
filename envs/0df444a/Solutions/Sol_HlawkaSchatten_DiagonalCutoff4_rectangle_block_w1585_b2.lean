-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:28.039483+00:00
-- url     : https://prove2.me/submissions/336e5894-8373-4605-9b43-292298e9ad35

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
theorem support_rectangle_w1585_s6_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347258837/10000000000 : ℝ)*x 0 + (2610273961/5000000000 : ℝ)*x 1 + (-37386457/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347258837/10000000000 : ℝ)^4667 ≤ (22422416910601/50000000000000 : ℝ)^3643 := by
    have hnat : (5347258837 : ℕ)^4667*50000000000000^3643 ≤ 22422416910601^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347258837 10000000000 22422416910601 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610273961/5000000000 : ℝ)^4667 ≤ (1359000966193/3125000000000 : ℝ)^3643 := by
    have hnat : (2610273961 : ℕ)^4667*3125000000000^3643 ≤ 1359000966193^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610273961 5000000000 1359000966193 3125000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37386457/200000000 : ℝ)^4667 ≤ (11667135234969/100000000000000 : ℝ)^3643 := by
    have hnat : (37386457 : ℕ)^4667*100000000000000^3643 ≤ 11667135234969^3643*200000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37386457 200000000 11667135234969 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347258837/10000000000 : ℝ), (2610273961/5000000000 : ℝ), (-37386457/200000000 : ℝ)] ![(22422416910601/50000000000000 : ℝ), (1359000966193/3125000000000 : ℝ), (11667135234969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347258837/10000000000 : ℝ)|^4667 ≤ (22422416910601/50000000000000 : ℝ)^3643
        have hw : |(5347258837/10000000000 : ℝ)|=(5347258837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610273961/5000000000 : ℝ)|^4667 ≤ (1359000966193/3125000000000 : ℝ)^3643
        have hw : |(2610273961/5000000000 : ℝ)|=(2610273961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37386457/200000000 : ℝ)|^4667 ≤ (11667135234969/100000000000000 : ℝ)^3643
        have hw : |(-37386457/200000000 : ℝ)|=(37386457/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s6_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882675167/5000000000 : ℝ)*x 0 + (1305402537/2500000000 : ℝ)*x 1 + (5422818989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882675167/5000000000 : ℝ)^4667 ≤ (10842385642023/100000000000000 : ℝ)^3643 := by
    have hnat : (882675167 : ℕ)^4667*100000000000000^3643 ≤ 10842385642023^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882675167 5000000000 10842385642023 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305402537/2500000000 : ℝ)^4667 ≤ (43499366965039/100000000000000 : ℝ)^3643 := by
    have hnat : (1305402537 : ℕ)^4667*100000000000000^3643 ≤ 43499366965039^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305402537 2500000000 43499366965039 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422818989/10000000000 : ℝ)^4667 ≤ (22829123689979/50000000000000 : ℝ)^3643 := by
    have hnat : (5422818989 : ℕ)^4667*50000000000000^3643 ≤ 22829123689979^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422818989 10000000000 22829123689979 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882675167/5000000000 : ℝ), (1305402537/2500000000 : ℝ), (5422818989/10000000000 : ℝ)] ![(10842385642023/100000000000000 : ℝ), (43499366965039/100000000000000 : ℝ), (22829123689979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882675167/5000000000 : ℝ)|^4667 ≤ (10842385642023/100000000000000 : ℝ)^3643
        have hw : |(-882675167/5000000000 : ℝ)|=(882675167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305402537/2500000000 : ℝ)|^4667 ≤ (43499366965039/100000000000000 : ℝ)^3643
        have hw : |(1305402537/2500000000 : ℝ)|=(1305402537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422818989/10000000000 : ℝ)|^4667 ≤ (22829123689979/50000000000000 : ℝ)^3643
        have hw : |(5422818989/10000000000 : ℝ)|=(5422818989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s6_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293367961/10000000000 : ℝ)*x 0 + (-1667051559/10000000000 : ℝ)*x 1 + (5422819023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293367961/10000000000 : ℝ)^4667 ≤ (22133330277121/50000000000000 : ℝ)^3643 := by
    have hnat : (5293367961 : ℕ)^4667*50000000000000^3643 ≤ 22133330277121^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293367961 10000000000 22133330277121 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1667051559/10000000000 : ℝ)^4667 ≤ (10075091684619/100000000000000 : ℝ)^3643 := by
    have hnat : (1667051559 : ℕ)^4667*100000000000000^3643 ≤ 10075091684619^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667051559 10000000000 10075091684619 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422819023/10000000000 : ℝ)^4667 ≤ (11414561936673/25000000000000 : ℝ)^3643 := by
    have hnat : (5422819023 : ℕ)^4667*25000000000000^3643 ≤ 11414561936673^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422819023 10000000000 11414561936673 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293367961/10000000000 : ℝ), (-1667051559/10000000000 : ℝ), (5422819023/10000000000 : ℝ)] ![(22133330277121/50000000000000 : ℝ), (10075091684619/100000000000000 : ℝ), (11414561936673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293367961/10000000000 : ℝ)|^4667 ≤ (22133330277121/50000000000000 : ℝ)^3643
        have hw : |(5293367961/10000000000 : ℝ)|=(5293367961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1667051559/10000000000 : ℝ)|^4667 ≤ (10075091684619/100000000000000 : ℝ)^3643
        have hw : |(-1667051559/10000000000 : ℝ)|=(1667051559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422819023/10000000000 : ℝ)|^4667 ≤ (11414561936673/25000000000000 : ℝ)^3643
        have hw : |(5422819023/10000000000 : ℝ)|=(5422819023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s6_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293367973/10000000000 : ℝ)*x 0 + (84731547/156250000 : ℝ)*x 1 + (-833525781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293367973/10000000000 : ℝ)^4667 ≤ (44266660682801/100000000000000 : ℝ)^3643 := by
    have hnat : (5293367973 : ℕ)^4667*100000000000000^3643 ≤ 44266660682801^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293367973 10000000000 44266660682801 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84731547/156250000 : ℝ)^4667 ≤ (22829123792449/50000000000000 : ℝ)^3643 := by
    have hnat : (84731547 : ℕ)^4667*50000000000000^3643 ≤ 22829123792449^3643*156250000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84731547 156250000 22829123792449 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833525781/5000000000 : ℝ)^4667 ≤ (10075091707847/100000000000000 : ℝ)^3643 := by
    have hnat : (833525781 : ℕ)^4667*100000000000000^3643 ≤ 10075091707847^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833525781 5000000000 10075091707847 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293367973/10000000000 : ℝ), (84731547/156250000 : ℝ), (-833525781/5000000000 : ℝ)] ![(44266660682801/100000000000000 : ℝ), (22829123792449/50000000000000 : ℝ), (10075091707847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293367973/10000000000 : ℝ)|^4667 ≤ (44266660682801/100000000000000 : ℝ)^3643
        have hw : |(5293367973/10000000000 : ℝ)|=(5293367973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84731547/156250000 : ℝ)|^4667 ≤ (22829123792449/50000000000000 : ℝ)^3643
        have hw : |(84731547/156250000 : ℝ)|=(84731547/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-833525781/5000000000 : ℝ)|^4667 ≤ (10075091707847/100000000000000 : ℝ)^3643
        have hw : |(-833525781/5000000000 : ℝ)|=(833525781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_s6_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237010113/10000000000 : ℝ)*x 0 + (280151261/625000000 : ℝ)*x 1 + (4002596913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237010113/10000000000 : ℝ)^4667 ≤ (33283636352657/100000000000000 : ℝ)^3643 := by
    have hnat : (4237010113 : ℕ)^4667*100000000000000^3643 ≤ 33283636352657^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237010113 10000000000 33283636352657 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280151261/625000000 : ℝ)^4667 ≤ (17886578592233/50000000000000 : ℝ)^3643 := by
    have hnat : (280151261 : ℕ)^4667*50000000000000^3643 ≤ 17886578592233^3643*625000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280151261 625000000 17886578592233 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4002596913/10000000000 : ℝ)^4667 ≤ (15471603226639/50000000000000 : ℝ)^3643 := by
    have hnat : (4002596913 : ℕ)^4667*50000000000000^3643 ≤ 15471603226639^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002596913 10000000000 15471603226639 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237010113/10000000000 : ℝ), (280151261/625000000 : ℝ), (4002596913/10000000000 : ℝ)] ![(33283636352657/100000000000000 : ℝ), (17886578592233/50000000000000 : ℝ), (15471603226639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237010113/10000000000 : ℝ)|^4667 ≤ (33283636352657/100000000000000 : ℝ)^3643
        have hw : |(4237010113/10000000000 : ℝ)|=(4237010113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280151261/625000000 : ℝ)|^4667 ≤ (17886578592233/50000000000000 : ℝ)^3643
        have hw : |(280151261/625000000 : ℝ)|=(280151261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4002596913/10000000000 : ℝ)|^4667 ≤ (15471603226639/50000000000000 : ℝ)^3643
        have hw : |(4002596913/10000000000 : ℝ)|=(4002596913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11169/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (4603338562674371/100000000000000000000 : ℝ) := by
    have hpowers : (11169/100000 : ℝ)^4665 ≤ (4603338562674371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11169 : ℕ)^4665*100000000000000000000^1024 ≤ 4603338562674371^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169 100000 4603338562674371 100000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11169/100000 : ℝ)) (X := (4603338562674371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4665/1024 : ℝ) ≤ (20388244713518773/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4665 ≤ (20388244713518773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4665*100000000000000000000^1024 ≤ 20388244713518773^1024*25000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 20388244713518773 100000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (20388244713518773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004603338562674371/50000000000000000000 : ℝ) ≤ (10000202085716437/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50004603338562674371/50000000000000000000 : ℝ)^1024 ≤ (10000202085716437/10000000000000000 : ℝ)^4665 := by
      have hnat : (50004603338562674371 : ℕ)^1024*10000000000000000^4665 ≤ 10000202085716437^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004603338562674371 50000000000000000000 10000202085716437 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000202085716437/10000000000000000 : ℝ)) (X := (50004603338562674371/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503123947909524143/12500000000000000000 : ℝ) ≤ (5000274264584659/5000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (12503123947909524143/12500000000000000000 : ℝ)^1024 ≤ (5000274264584659/5000000000000000 : ℝ)^4665 := by
      have hnat : (12503123947909524143 : ℕ)^1024*5000000000000000^4665 ≤ 5000274264584659^4665*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503123947909524143 12500000000000000000 5000274264584659 5000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000274264584659/5000000000000000 : ℝ)) (X := (12503123947909524143/12500000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020388244713518773/50000000000000000000 : ℝ) ≤ (10000894972622199/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50020388244713518773/50000000000000000000 : ℝ)^1024 ≤ (10000894972622199/10000000000000000 : ℝ)^4665 := by
      have hnat : (50020388244713518773 : ℕ)^1024*10000000000000000^4665 ≤ 10000894972622199^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020388244713518773 50000000000000000000 10000894972622199 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000894972622199/10000000000000000 : ℝ)) (X := (50020388244713518773/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4603338562674371/100000000000000000000 : ℝ) ≤ ((43143133146015969877/43150000000000000000 : ℝ)+2*(346443452881/431500000000000 : ℝ)*(11169/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (43143133146015969877/43150000000000000000 : ℝ)+2*(346443452881/431500000000000 : ℝ)*(11169/100000 : ℝ)=(10000202085716437/10000000000000000 : ℝ) by norm_num, show 1+2*(4603338562674371/100000000000000000000 : ℝ)=(50004603338562674371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20388244713518773/100000000000000000000 : ℝ)+(4603338562674371/100000000000000000000 : ℝ) ≤ ((43143133146015969877/43150000000000000000 : ℝ)+(346443452881/431500000000000 : ℝ)*((3871/25000 : ℝ)+(11169/100000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (43143133146015969877/43150000000000000000 : ℝ)+(346443452881/431500000000000 : ℝ)*((3871/25000 : ℝ)+(11169/100000 : ℝ))=(5000274264584659/5000000000000000 : ℝ) by norm_num, show 1+(20388244713518773/100000000000000000000 : ℝ)+(4603338562674371/100000000000000000000 : ℝ)=(12503123947909524143/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20388244713518773/100000000000000000000 : ℝ) ≤ ((43143133146015969877/43150000000000000000 : ℝ)+2*(346443452881/431500000000000 : ℝ)*(3871/25000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (43143133146015969877/43150000000000000000 : ℝ)+2*(346443452881/431500000000000 : ℝ)*(3871/25000 : ℝ)=(10000894972622199/10000000000000000 : ℝ) by norm_num, show 1+2*(20388244713518773/100000000000000000000 : ℝ)=(50020388244713518773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43143133146015969877/43150000000000000000 : ℝ)*(X 1 0+X 2 0)+(346443452881/431500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43143133146015969877/43150000000000000000 : ℝ)) (alpha := (346443452881/431500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43143133146015969877/43150000000000000000 : ℝ)*(X 0 1+X 2 1)+(346443452881/431500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43143133146015969877/43150000000000000000 : ℝ)) (alpha := (346443452881/431500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43143133146015969877/43150000000000000000 : ℝ)*(X 0 2+X 1 2)+(346443452881/431500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43143133146015969877/43150000000000000000 : ℝ)) (alpha := (346443452881/431500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347258837/10000000000 : ℝ)*X 2 0+(2610273961/5000000000 : ℝ)*X 2 1+(-37386457/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-882675167/5000000000 : ℝ)*X 0 0+(1305402537/2500000000 : ℝ)*X 0 1+(5422818989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5293367961/10000000000 : ℝ)*X 1 0+(-1667051559/10000000000 : ℝ)*X 1 1+(5422819023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5293367973/10000000000 : ℝ)*X 2 0+(84731547/156250000 : ℝ)*X 2 1+(-833525781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4237010113/10000000000 : ℝ)*X 0 0+(280151261/625000000 : ℝ)*X 0 1+(4002596913/10000000000 : ℝ)*X 0 2+(4237010113/10000000000 : ℝ)*X 1 0+(280151261/625000000 : ℝ)*X 1 1+(4002596913/10000000000 : ℝ)*X 1 2+(4237010113/10000000000 : ℝ)*X 2 0+(280151261/625000000 : ℝ)*X 2 1+(4002596913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98425273949859455702367/21575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30042169/4000000000000 : ℝ)*(base19) + (788151619/100000000000000 : ℝ)*(base23) + (63858191/25000000000000 : ℝ)*(lower1) + (52618079/50000000000000 : ℝ)*(upper3) + (10260557/100000000000000 : ℝ)*(lower4) + (90393663/100000000000000 : ℝ)*(upper5) + (110219420978233/3125000000000 : ℝ)*(major0) + (110219420978233/3125000000000 : ℝ)*(major1) + (110219420978233/3125000000000 : ℝ)*(major2) + (79153831/12500000000000 : ℝ)*(sp0) + (4969947270256007/100000000000000 : ℝ)*(sp1) + (4969946519201781/100000000000000 : ℝ)*(sp2) + (4969945848873739/100000000000000 : ℝ)*(sp3) + (416819104056803/20000000000000 : ℝ)*(sp4) + (416819104056803/20000000000000 : ℝ)*(f.failure) + (4969947270256007/100000000000000 : ℝ)*(f.sum) + (39677111270539/21575000000000000000000000000 : ℝ)*base66 + (5408393262654862341/134843750000000000000000000000000 : ℝ)*base67 + (1542669490617950159/134843750000000000000000000000000 : ℝ)*base70 + (16547817035892362341/134843750000000000000000000000000 : ℝ)*base71 + (53734597640661/21575000000000000000000000000 : ℝ)*base73 + (14100851725542950159/134843750000000000000000000000000 : ℝ)*base76 + (679261752272674841/134843750000000000000000000000000 : ℝ)*base77 + (807254384457012659/134843750000000000000000000000000 : ℝ)*base80 + (20937393407961/21575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1573537/500000000000000000000 : ℝ)*base89 + (1573537/500000000000000000000 : ℝ)*base91 + (1573537/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1585_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1585_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1585_box_0 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-781948377/5000000000 : ℝ)*x 0 + (5394987337/10000000000 : ℝ)*x 1 + (2697493719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (781948377/5000000000 : ℝ)^4667 ≤ (9283471987163/100000000000000 : ℝ)^3643 := by
    have hnat : (781948377 : ℕ)^4667*100000000000000^3643 ≤ 9283471987163^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781948377 5000000000 9283471987163 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394987337/10000000000 : ℝ)^4667 ≤ (22679131728077/50000000000000 : ℝ)^3643 := by
    have hnat : (5394987337 : ℕ)^4667*50000000000000^3643 ≤ 22679131728077^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394987337 10000000000 22679131728077 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697493719/5000000000 : ℝ)^4667 ≤ (11339566135999/25000000000000 : ℝ)^3643 := by
    have hnat : (2697493719 : ℕ)^4667*25000000000000^3643 ≤ 11339566135999^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697493719 5000000000 11339566135999 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-781948377/5000000000 : ℝ), (5394987337/10000000000 : ℝ), (2697493719/5000000000 : ℝ)] ![(9283471987163/100000000000000 : ℝ), (22679131728077/50000000000000 : ℝ), (11339566135999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-781948377/5000000000 : ℝ)|^4667 ≤ (9283471987163/100000000000000 : ℝ)^3643
        have hw : |(-781948377/5000000000 : ℝ)|=(781948377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394987337/10000000000 : ℝ)|^4667 ≤ (22679131728077/50000000000000 : ℝ)^3643
        have hw : |(5394987337/10000000000 : ℝ)|=(5394987337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697493719/5000000000 : ℝ)|^4667 ≤ (11339566135999/25000000000000 : ℝ)^3643
        have hw : |(2697493719/5000000000 : ℝ)|=(2697493719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_1 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271125311/10000000000 : ℝ)*x 0 + (-217019711/1250000000 : ℝ)*x 1 + (1348746783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271125311/10000000000 : ℝ)^4667 ≤ (44028509218721/100000000000000 : ℝ)^3643 := by
    have hnat : (5271125311 : ℕ)^4667*100000000000000^3643 ≤ 44028509218721^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271125311 10000000000 44028509218721 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217019711/1250000000 : ℝ)^4667 ≤ (424529180387/4000000000000 : ℝ)^3643 := by
    have hnat : (217019711 : ℕ)^4667*4000000000000^3643 ≤ 424529180387^3643*1250000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217019711 1250000000 424529180387 4000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348746783/2500000000 : ℝ)^4667 ≤ (45358261248157/100000000000000 : ℝ)^3643 := by
    have hnat : (1348746783 : ℕ)^4667*100000000000000^3643 ≤ 45358261248157^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348746783 2500000000 45358261248157 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271125311/10000000000 : ℝ), (-217019711/1250000000 : ℝ), (1348746783/2500000000 : ℝ)] ![(44028509218721/100000000000000 : ℝ), (424529180387/4000000000000 : ℝ), (45358261248157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271125311/10000000000 : ℝ)|^4667 ≤ (44028509218721/100000000000000 : ℝ)^3643
        have hw : |(5271125311/10000000000 : ℝ)|=(5271125311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217019711/1250000000 : ℝ)|^4667 ≤ (424529180387/4000000000000 : ℝ)^3643
        have hw : |(-217019711/1250000000 : ℝ)|=(217019711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348746783/2500000000 : ℝ)|^4667 ≤ (45358261248157/100000000000000 : ℝ)^3643
        have hw : |(1348746783/2500000000 : ℝ)|=(1348746783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_2 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271124711/10000000000 : ℝ)*x 0 + (5394987843/10000000000 : ℝ)*x 1 + (-1736157531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271124711/10000000000 : ℝ)^4667 ≤ (5503562849793/12500000000000 : ℝ)^3643 := by
    have hnat : (5271124711 : ℕ)^4667*12500000000000^3643 ≤ 5503562849793^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271124711 10000000000 5503562849793 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394987843/10000000000 : ℝ)^4667 ≤ (45358268906137/100000000000000 : ℝ)^3643 := by
    have hnat : (5394987843 : ℕ)^4667*100000000000000^3643 ≤ 45358268906137^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394987843 10000000000 45358268906137 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736157531/10000000000 : ℝ)^4667 ≤ (1326653535019/12500000000000 : ℝ)^3643 := by
    have hnat : (1736157531 : ℕ)^4667*12500000000000^3643 ≤ 1326653535019^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736157531 10000000000 1326653535019 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271124711/10000000000 : ℝ), (5394987843/10000000000 : ℝ), (-1736157531/10000000000 : ℝ)] ![(5503562849793/12500000000000 : ℝ), (45358268906137/100000000000000 : ℝ), (1326653535019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271124711/10000000000 : ℝ)|^4667 ≤ (5503562849793/12500000000000 : ℝ)^3643
        have hw : |(5271124711/10000000000 : ℝ)|=(5271124711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394987843/10000000000 : ℝ)|^4667 ≤ (45358268906137/100000000000000 : ℝ)^3643
        have hw : |(5394987843/10000000000 : ℝ)|=(5394987843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736157531/10000000000 : ℝ)|^4667 ≤ (1326653535019/12500000000000 : ℝ)^3643
        have hw : |(-1736157531/10000000000 : ℝ)|=(1736157531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_3 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4437092513/10000000000 : ℝ)*x 0 + (828685553/2000000000 : ℝ)*x 1 + (4143427773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4437092513/10000000000 : ℝ)^4667 ≤ (35310384738427/100000000000000 : ℝ)^3643 := by
    have hnat : (4437092513 : ℕ)^4667*100000000000000^3643 ≤ 35310384738427^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437092513 10000000000 35310384738427 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828685553/2000000000 : ℝ)^4667 ≤ (32344807585203/100000000000000 : ℝ)^3643 := by
    have hnat : (828685553 : ℕ)^4667*100000000000000^3643 ≤ 32344807585203^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828685553 2000000000 32344807585203 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143427773/10000000000 : ℝ)^4667 ≤ (4043100958151/12500000000000 : ℝ)^3643 := by
    have hnat : (4143427773 : ℕ)^4667*12500000000000^3643 ≤ 4043100958151^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143427773 10000000000 4043100958151 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4437092513/10000000000 : ℝ), (828685553/2000000000 : ℝ), (4143427773/10000000000 : ℝ)] ![(35310384738427/100000000000000 : ℝ), (32344807585203/100000000000000 : ℝ), (4043100958151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4437092513/10000000000 : ℝ)|^4667 ≤ (35310384738427/100000000000000 : ℝ)^3643
        have hw : |(4437092513/10000000000 : ℝ)|=(4437092513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828685553/2000000000 : ℝ)|^4667 ≤ (32344807585203/100000000000000 : ℝ)^3643
        have hw : |(828685553/2000000000 : ℝ)|=(828685553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143427773/10000000000 : ℝ)|^4667 ≤ (4043100958151/12500000000000 : ℝ)^3643
        have hw : |(4143427773/10000000000 : ℝ)|=(4143427773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_4 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98606651/500000000 : ℝ)*x 0 + (5245292419/10000000000 : ℝ)*x 1 + (5245292973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98606651/500000000 : ℝ)^4667 ≤ (12495450724471/100000000000000 : ℝ)^3643 := by
    have hnat : (98606651 : ℕ)^4667*100000000000000^3643 ≤ 12495450724471^3643*500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98606651 500000000 12495450724471 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245292419/10000000000 : ℝ)^4667 ≤ (43752271671517/100000000000000 : ℝ)^3643 := by
    have hnat : (5245292419 : ℕ)^4667*100000000000000^3643 ≤ 43752271671517^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245292419 10000000000 43752271671517 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245292973/10000000000 : ℝ)^4667 ≤ (10938069397871/25000000000000 : ℝ)^3643 := by
    have hnat : (5245292973 : ℕ)^4667*25000000000000^3643 ≤ 10938069397871^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245292973 10000000000 10938069397871 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98606651/500000000 : ℝ), (5245292419/10000000000 : ℝ), (5245292973/10000000000 : ℝ)] ![(12495450724471/100000000000000 : ℝ), (43752271671517/100000000000000 : ℝ), (10938069397871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98606651/500000000 : ℝ)|^4667 ≤ (12495450724471/100000000000000 : ℝ)^3643
        have hw : |(-98606651/500000000 : ℝ)|=(98606651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245292419/10000000000 : ℝ)|^4667 ≤ (43752271671517/100000000000000 : ℝ)^3643
        have hw : |(5245292419/10000000000 : ℝ)|=(5245292419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245292973/10000000000 : ℝ)|^4667 ≤ (10938069397871/25000000000000 : ℝ)^3643
        have hw : |(5245292973/10000000000 : ℝ)|=(5245292973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_5 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374775281/10000000000 : ℝ)*x 0 + (-56215547/312500000 : ℝ)*x 1 + (2622646533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374775281/10000000000 : ℝ)^4667 ≤ (9028135969739/20000000000000 : ℝ)^3643 := by
    have hnat : (5374775281 : ℕ)^4667*20000000000000^3643 ≤ 9028135969739^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374775281 10000000000 9028135969739 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56215547/312500000 : ℝ)^4667 ≤ (11107041549491/100000000000000 : ℝ)^3643 := by
    have hnat : (56215547 : ℕ)^4667*100000000000000^3643 ≤ 11107041549491^3643*312500000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56215547 312500000 11107041549491 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622646533/5000000000 : ℝ)^4667 ≤ (4375227858527/10000000000000 : ℝ)^3643 := by
    have hnat : (2622646533 : ℕ)^4667*10000000000000^3643 ≤ 4375227858527^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622646533 5000000000 4375227858527 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374775281/10000000000 : ℝ), (-56215547/312500000 : ℝ), (2622646533/5000000000 : ℝ)] ![(9028135969739/20000000000000 : ℝ), (11107041549491/100000000000000 : ℝ), (4375227858527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374775281/10000000000 : ℝ)|^4667 ≤ (9028135969739/20000000000000 : ℝ)^3643
        have hw : |(5374775281/10000000000 : ℝ)|=(5374775281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56215547/312500000 : ℝ)|^4667 ≤ (11107041549491/100000000000000 : ℝ)^3643
        have hw : |(-56215547/312500000 : ℝ)|=(56215547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622646533/5000000000 : ℝ)|^4667 ≤ (4375227858527/10000000000000 : ℝ)^3643
        have hw : |(2622646533/5000000000 : ℝ)|=(2622646533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_6 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687387741/5000000000 : ℝ)*x 0 + (5245292861/10000000000 : ℝ)*x 1 + (-1798897507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687387741/5000000000 : ℝ)^4667 ≤ (22570341005663/50000000000000 : ℝ)^3643 := by
    have hnat : (2687387741 : ℕ)^4667*50000000000000^3643 ≤ 22570341005663^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687387741 5000000000 22570341005663 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245292861/10000000000 : ℝ)^4667 ≤ (10938069098667/25000000000000 : ℝ)^3643 := by
    have hnat : (5245292861 : ℕ)^4667*25000000000000^3643 ≤ 10938069098667^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245292861 10000000000 10938069098667 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1798897507/10000000000 : ℝ)^4667 ≤ (11107041573221/100000000000000 : ℝ)^3643 := by
    have hnat : (1798897507 : ℕ)^4667*100000000000000^3643 ≤ 11107041573221^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798897507 10000000000 11107041573221 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687387741/5000000000 : ℝ), (5245292861/10000000000 : ℝ), (-1798897507/10000000000 : ℝ)] ![(22570341005663/50000000000000 : ℝ), (10938069098667/25000000000000 : ℝ), (11107041573221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687387741/5000000000 : ℝ)|^4667 ≤ (22570341005663/50000000000000 : ℝ)^3643
        have hw : |(2687387741/5000000000 : ℝ)|=(2687387741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245292861/10000000000 : ℝ)|^4667 ≤ (10938069098667/25000000000000 : ℝ)^3643
        have hw : |(5245292861/10000000000 : ℝ)|=(5245292861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1798897507/10000000000 : ℝ)|^4667 ≤ (11107041573221/100000000000000 : ℝ)^3643
        have hw : |(-1798897507/10000000000 : ℝ)|=(1798897507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_7 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2017022689/5000000000 : ℝ)*x 0 + (868965029/2000000000 : ℝ)*x 1 + (1086206459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017022689/5000000000 : ℝ)^4667 ≤ (31255009208249/100000000000000 : ℝ)^3643 := by
    have hnat : (2017022689 : ℕ)^4667*100000000000000^3643 ≤ 31255009208249^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017022689 5000000000 31255009208249 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868965029/2000000000 : ℝ)^4667 ≤ (6874498377429/20000000000000 : ℝ)^3643 := by
    have hnat : (868965029 : ℕ)^4667*20000000000000^3643 ≤ 6874498377429^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868965029 2000000000 6874498377429 20000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086206459/2500000000 : ℝ)^4667 ≤ (34372498890327/100000000000000 : ℝ)^3643 := by
    have hnat : (1086206459 : ℕ)^4667*100000000000000^3643 ≤ 34372498890327^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086206459 2500000000 34372498890327 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2017022689/5000000000 : ℝ), (868965029/2000000000 : ℝ), (1086206459/2500000000 : ℝ)] ![(31255009208249/100000000000000 : ℝ), (6874498377429/20000000000000 : ℝ), (34372498890327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2017022689/5000000000 : ℝ)|^4667 ≤ (31255009208249/100000000000000 : ℝ)^3643
        have hw : |(2017022689/5000000000 : ℝ)|=(2017022689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(868965029/2000000000 : ℝ)|^4667 ≤ (6874498377429/20000000000000 : ℝ)^3643
        have hw : |(868965029/2000000000 : ℝ)|=(868965029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086206459/2500000000 : ℝ)|^4667 ≤ (34372498890327/100000000000000 : ℝ)^3643
        have hw : |(1086206459/2500000000 : ℝ)|=(1086206459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_8 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885540907/10000000000 : ℝ)*x 0 + (2569837367/5000000000 : ℝ)*x 1 + (5415207749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885540907/10000000000 : ℝ)^4667 ≤ (11796968358151/100000000000000 : ℝ)^3643 := by
    have hnat : (1885540907 : ℕ)^4667*100000000000000^3643 ≤ 11796968358151^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885540907 10000000000 11796968358151 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569837367/5000000000 : ℝ)^4667 ≤ (5328358150777/12500000000000 : ℝ)^3643 := by
    have hnat : (2569837367 : ℕ)^4667*12500000000000^3643 ≤ 5328358150777^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569837367 5000000000 5328358150777 12500000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415207749/10000000000 : ℝ)^4667 ≤ (45576166412219/100000000000000 : ℝ)^3643 := by
    have hnat : (5415207749 : ℕ)^4667*100000000000000^3643 ≤ 45576166412219^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415207749 10000000000 45576166412219 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885540907/10000000000 : ℝ), (2569837367/5000000000 : ℝ), (5415207749/10000000000 : ℝ)] ![(11796968358151/100000000000000 : ℝ), (5328358150777/12500000000000 : ℝ), (45576166412219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885540907/10000000000 : ℝ)|^4667 ≤ (11796968358151/100000000000000 : ℝ)^3643
        have hw : |(-1885540907/10000000000 : ℝ)|=(1885540907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569837367/5000000000 : ℝ)|^4667 ≤ (5328358150777/12500000000000 : ℝ)^3643
        have hw : |(2569837367/5000000000 : ℝ)|=(2569837367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415207749/10000000000 : ℝ)|^4667 ≤ (45576166412219/100000000000000 : ℝ)^3643
        have hw : |(5415207749/10000000000 : ℝ)|=(5415207749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_9 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257121407/10000000000 : ℝ)*x 0 + (-431863601/2500000000 : ℝ)*x 1 + (5415207737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257121407/10000000000 : ℝ)^4667 ≤ (10969678659491/25000000000000 : ℝ)^3643 := by
    have hnat : (5257121407 : ℕ)^4667*25000000000000^3643 ≤ 10969678659491^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257121407 10000000000 10969678659491 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431863601/2500000000 : ℝ)^4667 ≤ (2636279766103/25000000000000 : ℝ)^3643 := by
    have hnat : (431863601 : ℕ)^4667*25000000000000^3643 ≤ 2636279766103^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431863601 2500000000 2636279766103 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415207737/10000000000 : ℝ)^4667 ≤ (22788083141417/50000000000000 : ℝ)^3643 := by
    have hnat : (5415207737 : ℕ)^4667*50000000000000^3643 ≤ 22788083141417^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415207737 10000000000 22788083141417 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257121407/10000000000 : ℝ), (-431863601/2500000000 : ℝ), (5415207737/10000000000 : ℝ)] ![(10969678659491/25000000000000 : ℝ), (2636279766103/25000000000000 : ℝ), (22788083141417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257121407/10000000000 : ℝ)|^4667 ≤ (10969678659491/25000000000000 : ℝ)^3643
        have hw : |(5257121407/10000000000 : ℝ)|=(5257121407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431863601/2500000000 : ℝ)|^4667 ≤ (2636279766103/25000000000000 : ℝ)^3643
        have hw : |(-431863601/2500000000 : ℝ)|=(431863601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415207737/10000000000 : ℝ)|^4667 ≤ (22788083141417/50000000000000 : ℝ)^3643
        have hw : |(5415207737/10000000000 : ℝ)|=(5415207737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_10 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257121269/10000000000 : ℝ)*x 0 + (54152079/100000000 : ℝ)*x 1 + (-1727454367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257121269/10000000000 : ℝ)^4667 ≤ (43878713162381/100000000000000 : ℝ)^3643 := by
    have hnat : (5257121269 : ℕ)^4667*100000000000000^3643 ≤ 43878713162381^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257121269 10000000000 43878713162381 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54152079/100000000 : ℝ)^4667 ≤ (11394042010077/25000000000000 : ℝ)^3643 := by
    have hnat : (54152079 : ℕ)^4667*25000000000000^3643 ≤ 11394042010077^3643*100000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54152079 100000000 11394042010077 25000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727454367/10000000000 : ℝ)^4667 ≤ (527255938753/5000000000000 : ℝ)^3643 := by
    have hnat : (1727454367 : ℕ)^4667*5000000000000^3643 ≤ 527255938753^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727454367 10000000000 527255938753 5000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257121269/10000000000 : ℝ), (54152079/100000000 : ℝ), (-1727454367/10000000000 : ℝ)] ![(43878713162381/100000000000000 : ℝ), (11394042010077/25000000000000 : ℝ), (527255938753/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257121269/10000000000 : ℝ)|^4667 ≤ (43878713162381/100000000000000 : ℝ)^3643
        have hw : |(5257121269/10000000000 : ℝ)|=(5257121269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54152079/100000000 : ℝ)|^4667 ≤ (11394042010077/25000000000000 : ℝ)^3643
        have hw : |(54152079/100000000 : ℝ)|=(54152079/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727454367/10000000000 : ℝ)|^4667 ≤ (527255938753/5000000000000 : ℝ)^3643
        have hw : |(-1727454367/10000000000 : ℝ)|=(1727454367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_11 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1122598057/2500000000 : ℝ)*x 0 + (4116189121/10000000000 : ℝ)*x 1 + (2058094493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122598057/2500000000 : ℝ)^4667 ≤ (35854684277073/100000000000000 : ℝ)^3643 := by
    have hnat : (1122598057 : ℕ)^4667*100000000000000^3643 ≤ 35854684277073^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122598057 2500000000 35854684277073 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116189121/10000000000 : ℝ)^4667 ≤ (16036329262797/50000000000000 : ℝ)^3643 := by
    have hnat : (4116189121 : ℕ)^4667*50000000000000^3643 ≤ 16036329262797^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116189121 10000000000 16036329262797 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058094493/5000000000 : ℝ)^4667 ≤ (16036328589011/50000000000000 : ℝ)^3643 := by
    have hnat : (2058094493 : ℕ)^4667*50000000000000^3643 ≤ 16036328589011^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058094493 5000000000 16036328589011 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1122598057/2500000000 : ℝ), (4116189121/10000000000 : ℝ), (2058094493/5000000000 : ℝ)] ![(35854684277073/100000000000000 : ℝ), (16036329262797/50000000000000 : ℝ), (16036328589011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1122598057/2500000000 : ℝ)|^4667 ≤ (35854684277073/100000000000000 : ℝ)^3643
        have hw : |(1122598057/2500000000 : ℝ)|=(1122598057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116189121/10000000000 : ℝ)|^4667 ≤ (16036329262797/50000000000000 : ℝ)^3643
        have hw : |(4116189121/10000000000 : ℝ)|=(4116189121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2058094493/5000000000 : ℝ)|^4667 ≤ (16036328589011/50000000000000 : ℝ)^3643
        have hw : |(2058094493/5000000000 : ℝ)|=(2058094493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_12 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412520907/2500000000 : ℝ)*x 0 + (2748714281/5000000000 : ℝ)*x 1 + (2615122091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412520907/2500000000 : ℝ)^4667 ≤ (9943906659483/100000000000000 : ℝ)^3643 := by
    have hnat : (412520907 : ℕ)^4667*100000000000000^3643 ≤ 9943906659483^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412520907 2500000000 9943906659483 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748714281/5000000000 : ℝ)^4667 ≤ (23232280070131/50000000000000 : ℝ)^3643 := by
    have hnat : (2748714281 : ℕ)^4667*50000000000000^3643 ≤ 23232280070131^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748714281 5000000000 23232280070131 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615122091/5000000000 : ℝ)^4667 ≤ (21795766589943/50000000000000 : ℝ)^3643 := by
    have hnat : (2615122091 : ℕ)^4667*50000000000000^3643 ≤ 21795766589943^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615122091 5000000000 21795766589943 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412520907/2500000000 : ℝ), (2748714281/5000000000 : ℝ), (2615122091/5000000000 : ℝ)] ![(9943906659483/100000000000000 : ℝ), (23232280070131/50000000000000 : ℝ), (21795766589943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412520907/2500000000 : ℝ)|^4667 ≤ (9943906659483/100000000000000 : ℝ)^3643
        have hw : |(-412520907/2500000000 : ℝ)|=(412520907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748714281/5000000000 : ℝ)|^4667 ≤ (23232280070131/50000000000000 : ℝ)^3643
        have hw : |(2748714281/5000000000 : ℝ)|=(2748714281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615122091/5000000000 : ℝ)|^4667 ≤ (21795766589943/50000000000000 : ℝ)^3643
        have hw : |(2615122091/5000000000 : ℝ)|=(2615122091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_13 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385196933/10000000000 : ℝ)*x 0 + (-902518379/5000000000 : ℝ)*x 1 + (209209769/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385196933/10000000000 : ℝ)^4667 ≤ (22626420345351/50000000000000 : ℝ)^3643 := by
    have hnat : (5385196933 : ℕ)^4667*50000000000000^3643 ≤ 22626420345351^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385196933 10000000000 22626420345351 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902518379/5000000000 : ℝ)^4667 ≤ (11155625664483/100000000000000 : ℝ)^3643 := by
    have hnat : (902518379 : ℕ)^4667*100000000000000^3643 ≤ 11155625664483^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902518379 5000000000 11155625664483 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209209769/400000000 : ℝ)^4667 ≤ (43591533639007/100000000000000 : ℝ)^3643 := by
    have hnat : (209209769 : ℕ)^4667*100000000000000^3643 ≤ 43591533639007^3643*400000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209209769 400000000 43591533639007 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385196933/10000000000 : ℝ), (-902518379/5000000000 : ℝ), (209209769/400000000 : ℝ)] ![(22626420345351/50000000000000 : ℝ), (11155625664483/100000000000000 : ℝ), (43591533639007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385196933/10000000000 : ℝ)|^4667 ≤ (22626420345351/50000000000000 : ℝ)^3643
        have hw : |(5385196933/10000000000 : ℝ)|=(5385196933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902518379/5000000000 : ℝ)|^4667 ≤ (11155625664483/100000000000000 : ℝ)^3643
        have hw : |(-902518379/5000000000 : ℝ)|=(902518379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209209769/400000000 : ℝ)|^4667 ≤ (43591533639007/100000000000000 : ℝ)^3643
        have hw : |(209209769/400000000 : ℝ)|=(209209769/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_14 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692598609/5000000000 : ℝ)*x 0 + (1307561053/2500000000 : ℝ)*x 1 + (-1805036387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692598609/5000000000 : ℝ)^4667 ≤ (4525284375879/10000000000000 : ℝ)^3643 := by
    have hnat : (2692598609 : ℕ)^4667*10000000000000^3643 ≤ 4525284375879^3643*5000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692598609 5000000000 4525284375879 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307561053/2500000000 : ℝ)^4667 ≤ (43591533500203/100000000000000 : ℝ)^3643 := by
    have hnat : (1307561053 : ℕ)^4667*100000000000000^3643 ≤ 43591533500203^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307561053 2500000000 43591533500203 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805036387/10000000000 : ℝ)^4667 ≤ (11155622727101/100000000000000 : ℝ)^3643 := by
    have hnat : (1805036387 : ℕ)^4667*100000000000000^3643 ≤ 11155622727101^3643*10000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805036387 10000000000 11155622727101 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692598609/5000000000 : ℝ), (1307561053/2500000000 : ℝ), (-1805036387/10000000000 : ℝ)] ![(4525284375879/10000000000000 : ℝ), (43591533500203/100000000000000 : ℝ), (11155622727101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692598609/5000000000 : ℝ)|^4667 ≤ (4525284375879/10000000000000 : ℝ)^3643
        have hw : |(2692598609/5000000000 : ℝ)|=(2692598609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307561053/2500000000 : ℝ)|^4667 ≤ (43591533500203/100000000000000 : ℝ)^3643
        have hw : |(1307561053/2500000000 : ℝ)|=(1307561053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805036387/10000000000 : ℝ)|^4667 ≤ (11155622727101/100000000000000 : ℝ)^3643
        have hw : |(-1805036387/10000000000 : ℝ)|=(1805036387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1585_box_15 (p : ℝ) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (24954147/62500000 : ℝ)*x 0 + (873009327/2000000000 : ℝ)*x 1 + (1091261719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24954147/62500000 : ℝ)^4667 ≤ (3084486239829/10000000000000 : ℝ)^3643 := by
    have hnat : (24954147 : ℕ)^4667*10000000000000^3643 ≤ 3084486239829^3643*62500000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24954147 62500000 3084486239829 10000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873009327/2000000000 : ℝ)^4667 ≤ (17288783784831/50000000000000 : ℝ)^3643 := by
    have hnat : (873009327 : ℕ)^4667*50000000000000^3643 ≤ 17288783784831^3643*2000000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873009327 2000000000 17288783784831 50000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091261719/2500000000 : ℝ)^4667 ≤ (34577570015351/100000000000000 : ℝ)^3643 := by
    have hnat : (1091261719 : ℕ)^4667*100000000000000^3643 ≤ 34577570015351^3643*2500000000^4667 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091261719 2500000000 34577570015351 100000000000000 4667 3643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4667/1024 : ℝ)) 4667 3643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24954147/62500000 : ℝ), (873009327/2000000000 : ℝ), (1091261719/2500000000 : ℝ)] ![(3084486239829/10000000000000 : ℝ), (17288783784831/50000000000000 : ℝ), (34577570015351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24954147/62500000 : ℝ)|^4667 ≤ (3084486239829/10000000000000 : ℝ)^3643
        have hw : |(24954147/62500000 : ℝ)|=(24954147/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873009327/2000000000 : ℝ)|^4667 ≤ (17288783784831/50000000000000 : ℝ)^3643
        have hw : |(873009327/2000000000 : ℝ)|=(873009327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091261719/2500000000 : ℝ)|^4667 ≤ (34577570015351/100000000000000 : ℝ)^3643
        have hw : |(1091261719/2500000000 : ℝ)|=(1091261719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1585_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3991/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29487/50000 : ℝ) ∧ (81069/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43229/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11169/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (4603338562674371/100000000000000000000 : ℝ) := by
    have hpowers : (11169/100000 : ℝ)^4665 ≤ (4603338562674371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11169 : ℕ)^4665*100000000000000000000^1024 ≤ 4603338562674371^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169 100000 4603338562674371 100000000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11169/100000 : ℝ)) (X := (4603338562674371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4665/1024 : ℝ) ≤ (1273890426465483/6250000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4665 ≤ (1273890426465483/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4665*6250000000000000000^1024 ≤ 1273890426465483^1024*100000^4665 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 1273890426465483 6250000000000000000 4665 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (1273890426465483/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004603338562674371/50000000000000000000 : ℝ) ≤ (10000202085716437/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (50004603338562674371/50000000000000000000 : ℝ)^1024 ≤ (10000202085716437/10000000000000000 : ℝ)^4665 := by
      have hnat : (50004603338562674371 : ℕ)^1024*10000000000000000^4665 ≤ 10000202085716437^4665*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004603338562674371 50000000000000000000 10000202085716437 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000202085716437/10000000000000000 : ℝ)) (X := (50004603338562674371/50000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024985585386122099/100000000000000000000 : ℝ) ≤ (80004387180297/80000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (100024985585386122099/100000000000000000000 : ℝ)^1024 ≤ (80004387180297/80000000000000 : ℝ)^4665 := by
      have hnat : (100024985585386122099 : ℕ)^1024*80000000000000^4665 ≤ 80004387180297^4665*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024985585386122099 100000000000000000000 80004387180297 80000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80004387180297/80000000000000 : ℝ)) (X := (100024985585386122099/100000000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126273890426465483/3125000000000000000 : ℝ) ≤ (10000894709357813/10000000000000000 : ℝ) ^ (4665/1024 : ℝ) := by
    have hpowers : (3126273890426465483/3125000000000000000 : ℝ)^1024 ≤ (10000894709357813/10000000000000000 : ℝ)^4665 := by
      have hnat : (3126273890426465483 : ℕ)^1024*10000000000000000^4665 ≤ 10000894709357813^4665*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126273890426465483 3125000000000000000 10000894709357813 10000000000000000 1024 4665 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000894709357813/10000000000000000 : ℝ)) (X := (3126273890426465483/3125000000000000000 : ℝ)) (by norm_num) 4665 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4603338562674371/100000000000000000000 : ℝ) ≤ ((7188855980721696779/7190000000000000000 : ℝ)+2*(21644488793/26962500000000 : ℝ)*(11169/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (7188855980721696779/7190000000000000000 : ℝ)+2*(21644488793/26962500000000 : ℝ)*(11169/100000 : ℝ)=(10000202085716437/10000000000000000 : ℝ) by norm_num, show 1+2*(4603338562674371/100000000000000000000 : ℝ)=(50004603338562674371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1273890426465483/6250000000000000000 : ℝ)+(4603338562674371/100000000000000000000 : ℝ) ≤ ((7188855980721696779/7190000000000000000 : ℝ)+(21644488793/26962500000000 : ℝ)*((15483/100000 : ℝ)+(11169/100000 : ℝ)))^(4665/1024 : ℝ) := by
    rw [show (7188855980721696779/7190000000000000000 : ℝ)+(21644488793/26962500000000 : ℝ)*((15483/100000 : ℝ)+(11169/100000 : ℝ))=(80004387180297/80000000000000 : ℝ) by norm_num, show 1+(1273890426465483/6250000000000000000 : ℝ)+(4603338562674371/100000000000000000000 : ℝ)=(100024985585386122099/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1273890426465483/6250000000000000000 : ℝ) ≤ ((7188855980721696779/7190000000000000000 : ℝ)+2*(21644488793/26962500000000 : ℝ)*(15483/100000 : ℝ))^(4665/1024 : ℝ) := by
    rw [show (7188855980721696779/7190000000000000000 : ℝ)+2*(21644488793/26962500000000 : ℝ)*(15483/100000 : ℝ)=(10000894709357813/10000000000000000 : ℝ) by norm_num, show 1+2*(1273890426465483/6250000000000000000 : ℝ)=(3126273890426465483/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7188855980721696779/7190000000000000000 : ℝ)*(X 1 0+X 2 0)+(21644488793/26962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7188855980721696779/7190000000000000000 : ℝ)) (alpha := (21644488793/26962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7188855980721696779/7190000000000000000 : ℝ)*(X 0 1+X 2 1)+(21644488793/26962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7188855980721696779/7190000000000000000 : ℝ)) (alpha := (21644488793/26962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7188855980721696779/7190000000000000000 : ℝ)*(X 0 2+X 1 2)+(21644488793/26962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4665/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7188855980721696779/7190000000000000000 : ℝ)) (alpha := (21644488793/26962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-781948377/5000000000 : ℝ)*X 0 0+(5394987337/10000000000 : ℝ)*X 0 1+(2697493719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271125311/10000000000 : ℝ)*X 1 0+(-217019711/1250000000 : ℝ)*X 1 1+(1348746783/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271124711/10000000000 : ℝ)*X 2 0+(5394987843/10000000000 : ℝ)*X 2 1+(-1736157531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4437092513/10000000000 : ℝ)*X 0 0+(828685553/2000000000 : ℝ)*X 0 1+(4143427773/10000000000 : ℝ)*X 0 2+(4437092513/10000000000 : ℝ)*X 1 0+(828685553/2000000000 : ℝ)*X 1 1+(4143427773/10000000000 : ℝ)*X 1 2+(4437092513/10000000000 : ℝ)*X 2 0+(828685553/2000000000 : ℝ)*X 2 1+(4143427773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98606651/500000000 : ℝ)*X 0 0+(5245292419/10000000000 : ℝ)*X 0 1+(5245292973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374775281/10000000000 : ℝ)*X 1 0+(-56215547/312500000 : ℝ)*X 1 1+(2622646533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2687387741/5000000000 : ℝ)*X 2 0+(5245292861/10000000000 : ℝ)*X 2 1+(-1798897507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2017022689/5000000000 : ℝ)*X 0 0+(868965029/2000000000 : ℝ)*X 0 1+(1086206459/2500000000 : ℝ)*X 0 2+(2017022689/5000000000 : ℝ)*X 1 0+(868965029/2000000000 : ℝ)*X 1 1+(1086206459/2500000000 : ℝ)*X 1 2+(2017022689/5000000000 : ℝ)*X 2 0+(868965029/2000000000 : ℝ)*X 2 1+(1086206459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1885540907/10000000000 : ℝ)*X 0 0+(2569837367/5000000000 : ℝ)*X 0 1+(5415207749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257121407/10000000000 : ℝ)*X 1 0+(-431863601/2500000000 : ℝ)*X 1 1+(5415207737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257121269/10000000000 : ℝ)*X 2 0+(54152079/100000000 : ℝ)*X 2 1+(-1727454367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1122598057/2500000000 : ℝ)*X 0 0+(4116189121/10000000000 : ℝ)*X 0 1+(2058094493/5000000000 : ℝ)*X 0 2+(1122598057/2500000000 : ℝ)*X 1 0+(4116189121/10000000000 : ℝ)*X 1 1+(2058094493/5000000000 : ℝ)*X 1 2+(1122598057/2500000000 : ℝ)*X 2 0+(4116189121/10000000000 : ℝ)*X 2 1+(2058094493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-412520907/2500000000 : ℝ)*X 0 0+(2748714281/5000000000 : ℝ)*X 0 1+(2615122091/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5385196933/10000000000 : ℝ)*X 1 0+(-902518379/5000000000 : ℝ)*X 1 1+(209209769/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2692598609/5000000000 : ℝ)*X 2 0+(1307561053/2500000000 : ℝ)*X 2 1+(-1805036387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((24954147/62500000 : ℝ)*X 0 0+(873009327/2000000000 : ℝ)*X 0 1+(1091261719/2500000000 : ℝ)*X 0 2+(24954147/62500000 : ℝ)*X 1 0+(873009327/2000000000 : ℝ)*X 1 1+(1091261719/2500000000 : ℝ)*X 1 2+(24954147/62500000 : ℝ)*X 2 0+(873009327/2000000000 : ℝ)*X 2 1+(1091261719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1585_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3991/6250 : ℝ) ≤ (-28694088523093749749163711587983/44937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26330923/100000000000000 : ℝ)*(lower3) + (33227219/100000000000000 : ℝ)*(lower4) + (25475629/20000000000000 : ℝ)*(upper5) + (582305857638641/25000000000000 : ℝ)*(major0) + (582305857638641/25000000000000 : ℝ)*(major1) + (582305857638641/25000000000000 : ℝ)*(major2) + (2701492099/50000000000000 : ℝ)*(sp2) + (1971537163/100000000000000 : ℝ)*(sp3) + (825850852020349/25000000000000 : ℝ)*(sp4) + (825841374115753/25000000000000 : ℝ)*(sp5) + (1651700975935311/50000000000000 : ℝ)*(sp6) + (1376321976829773/100000000000000 : ℝ)*(sp7) + (157870937/4000000000000 : ℝ)*(sp12) + (163509343/390625000000 : ℝ)*(sp13) + (172040493545867/12500000000000 : ℝ)*(f.failure) + (165170367742741/5000000000000 : ℝ)*(f.sum) + (9108849544489/10785000000000000000000000000 : ℝ)*base66 + (8213232768727187983/539250000000000000000000000000000 : ℝ)*base68 + (3024872505718937983/539250000000000000000000000000000 : ℝ)*base70 + (3071891958655937983/539250000000000000000000000000000 : ℝ)*base72 + (9564243975091/2696250000000000000000000000 : ℝ)*base74 + (38558247371562017/539250000000000000000000000000000 : ℝ)*base75 + (1885366888986437983/539250000000000000000000000000000 : ℝ)*base78 + (2385036392495687983/539250000000000000000000000000000 : ℝ)*base80 + (16135177196959/10785000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (766393/312500000000000000000 : ℝ)*base89 + (766393/312500000000000000000 : ℝ)*base91 + (766393/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29487/50000 : ℝ) ≤ (106010684487140974548709675533789/179750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2875749/12500000000000 : ℝ)*(lower0) + (6984303/100000000000000 : ℝ)*(upper1) + (64867067/100000000000000 : ℝ)*(upper2) + (1205243250513201/50000000000000 : ℝ)*(major0) + (1205243250513201/50000000000000 : ℝ)*(major1) + (1205243250513201/50000000000000 : ℝ)*(major2) + (3376970592574027/100000000000000 : ℝ)*(sp0) + (3376938448148813/100000000000000 : ℝ)*(sp1) + (844240892416681/25000000000000 : ℝ)*(sp2) + (712169751705307/50000000000000 : ℝ)*(sp3) + (4358999671/50000000000000 : ℝ)*(sp6) + (8459879313/25000000000000 : ℝ)*(sp9) + (2298692917/100000000000000 : ℝ)*(sp11) + (1695092039/100000000000000 : ℝ)*(sp12) + (1424341802103531/100000000000000 : ℝ)*(f.failure) + (1688486143833033/50000000000000 : ℝ)*(f.sum) + (26710249737/28085937500000000000000000 : ℝ)*base65 + (1976557896565479579/359500000000000000000000000000000 : ℝ)*base67 + (2010111101437479579/359500000000000000000000000000000 : ℝ)*base69 + (3535517502295979579/359500000000000000000000000000000 : ℝ)*base71 + (14575939437671/3595000000000000000000000000 : ℝ)*base73 + (2712173936235479579/359500000000000000000000000000000 : ℝ)*base75 + (1000815945036479579/359500000000000000000000000000000 : ℝ)*base77 + (2688576486733979579/359500000000000000000000000000000 : ℝ)*base79 + (942790745887/1797500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (21801351/2500000000000000000000 : ℝ)*base90 + (21801351/2500000000000000000000 : ℝ)*base92 + (21801351/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81069/100000 : ℝ) ≤ (72862572095794248885603566578503/89875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4003/48828125000 : ℝ)*(upper1) + (3184897/100000000000000 : ℝ)*(upper2) + (6798861/100000000000000 : ℝ)*(upper3) + (21421581/100000000000000 : ℝ)*(lower5) + (648700954878319/25000000000000 : ℝ)*(major0) + (648700954878319/25000000000000 : ℝ)*(major1) + (648700954878319/25000000000000 : ℝ)*(major2) + (730926653/50000000000000 : ℝ)*(sp0) + (33491665179/100000000000000 : ℝ)*(sp2) + (11533005811/100000000000000 : ℝ)*(sp3) + (3629328722728367/100000000000000 : ℝ)*(sp8) + (3629330184581673/100000000000000 : ℝ)*(sp9) + (1814648346458247/50000000000000 : ℝ)*(sp10) + (1533242250749847/100000000000000 : ℝ)*(sp11) + (766626891877829/50000000000000 : ℝ)*(f.failure) + (3629330184581673/100000000000000 : ℝ)*(f.sum) + (19392251241317/5392500000000000000000000000 : ℝ)*base65 + (1702483869372803503/539250000000000000000000000000000 : ℝ)*base67 + (8206686531621696497/539250000000000000000000000000000 : ℝ)*base70 + (2495487686096196497/539250000000000000000000000000000 : ℝ)*base72 + (9756854352047/5392500000000000000000000000 : ℝ)*base73 + (6194592761654196497/539250000000000000000000000000000 : ℝ)*base76 + (14572638576803503/539250000000000000000000000000000 : ℝ)*base77 + (4252969402009446497/539250000000000000000000000000000 : ℝ)*base80 + (47168601067993/5392500000000000000000000000 : ℝ)*base82 + (12160791/1250000000000000000000 : ℝ)*base89 + (12160791/1250000000000000000000 : ℝ)*base91 + (12160791/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43229/50000 : ℝ) ≤ (-77701734194686224312560817830157/89875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9962853/20000000000000 : ℝ)*(lower1) + (33503129/25000000000000 : ℝ)*(lower2) + (55232611/50000000000000 : ℝ)*(upper5) + (658913130775861/25000000000000 : ℝ)*(major0) + (658913130775861/25000000000000 : ℝ)*(major1) + (658913130775861/25000000000000 : ℝ)*(major2) + (2624688791/100000000000000 : ℝ)*(sp0) + (12785119701/25000000000000 : ℝ)*(sp5) + (3112747517/12500000000000 : ℝ)*(sp6) + (889532419/10000000000000 : ℝ)*(sp7) + (1871364916563259/50000000000000 : ℝ)*(sp12) + (1871340658668253/50000000000000 : ℝ)*(sp13) + (1871353777917587/50000000000000 : ℝ)*(sp14) + (778691069379251/50000000000000 : ℝ)*(sp15) + (389347758520673/25000000000000 : ℝ)*(f.failure) + (374273245781531/10000000000000 : ℝ)*(f.sum) + (20226842485867/5392500000000000000000000000 : ℝ)*base66 + (293776471714605157/539250000000000000000000000000000 : ℝ)*base67 + (4237315322286855157/539250000000000000000000000000000 : ℝ)*base69 + (975119696036144843/539250000000000000000000000000000 : ℝ)*base72 + (16608408199181/2696250000000000000000000000 : ℝ)*base74 + (92895868971855157/539250000000000000000000000000000 : ℝ)*base75 + (1423447541919644843/539250000000000000000000000000000 : ℝ)*base78 + (4100625165650355157/539250000000000000000000000000000 : ℝ)*base79 + (6055630046333/5392500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4111733/625000000000000000000 : ℝ)*base90 + (4111733/625000000000000000000 : ℝ)*base92 + (4111733/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1585_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3991/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (81069/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43229/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1585_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1585_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3991/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (81069/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43229/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1585_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1585_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4665/1024 : ℝ) ≤ p) (hpb : p ≤ (4667/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42308779/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3991/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29487/50000 : ℝ) else (81069/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43229/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1585_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

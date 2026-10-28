-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:03.943465+00:00
-- url     : https://prove2.me/submissions/fa6160b3-a9f9-4192-98c9-81f05089b658

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
theorem support_rectangle_w1197_s9_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344519909/10000000000 : ℝ)*x 0 + (5266632463/10000000000 : ℝ)*x 1 + (-88176993/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344519909/10000000000 : ℝ)^4195 ≤ (10913981431489/25000000000000 : ℝ)^3171 := by
    have hnat : (5344519909 : ℕ)^4195*25000000000000^3171 ≤ 10913981431489^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344519909 10000000000 10913981431489 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266632463/10000000000 : ℝ)^4195 ≤ (42816250818341/100000000000000 : ℝ)^3171 := by
    have hnat : (5266632463 : ℕ)^4195*100000000000000^3171 ≤ 42816250818341^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266632463 10000000000 42816250818341 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88176993/400000000 : ℝ)^4195 ≤ (13527823442601/100000000000000 : ℝ)^3171 := by
    have hnat : (88176993 : ℕ)^4195*100000000000000^3171 ≤ 13527823442601^3171*400000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88176993 400000000 13527823442601 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344519909/10000000000 : ℝ), (5266632463/10000000000 : ℝ), (-88176993/400000000 : ℝ)] ![(10913981431489/25000000000000 : ℝ), (42816250818341/100000000000000 : ℝ), (13527823442601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344519909/10000000000 : ℝ)|^4195 ≤ (10913981431489/25000000000000 : ℝ)^3171
        have hw : |(5344519909/10000000000 : ℝ)|=(5344519909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266632463/10000000000 : ℝ)|^4195 ≤ (42816250818341/100000000000000 : ℝ)^3171
        have hw : |(5266632463/10000000000 : ℝ)|=(5266632463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88176993/400000000 : ℝ)|^4195 ≤ (13527823442601/100000000000000 : ℝ)^3171
        have hw : |(-88176993/400000000 : ℝ)|=(88176993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s9_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140864969/10000000000 : ℝ)*x 0 + (1316737101/2500000000 : ℝ)*x 1 + (5391665519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140864969/10000000000 : ℝ)^4195 ≤ (13014239632713/100000000000000 : ℝ)^3171 := by
    have hnat : (2140864969 : ℕ)^4195*100000000000000^3171 ≤ 13014239632713^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140864969 10000000000 13014239632713 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316737101/2500000000 : ℝ)^4195 ≤ (10704912201001/25000000000000 : ℝ)^3171 := by
    have hnat : (1316737101 : ℕ)^4195*25000000000000^3171 ≤ 10704912201001^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316737101 2500000000 10704912201001 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391665519/10000000000 : ℝ)^4195 ≤ (44166111555933/100000000000000 : ℝ)^3171 := by
    have hnat : (5391665519 : ℕ)^4195*100000000000000^3171 ≤ 44166111555933^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391665519 10000000000 44166111555933 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140864969/10000000000 : ℝ), (1316737101/2500000000 : ℝ), (5391665519/10000000000 : ℝ)] ![(13014239632713/100000000000000 : ℝ), (10704912201001/25000000000000 : ℝ), (44166111555933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140864969/10000000000 : ℝ)|^4195 ≤ (13014239632713/100000000000000 : ℝ)^3171
        have hw : |(-2140864969/10000000000 : ℝ)|=(2140864969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316737101/2500000000 : ℝ)|^4195 ≤ (10704912201001/25000000000000 : ℝ)^3171
        have hw : |(1316737101/2500000000 : ℝ)|=(1316737101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391665519/10000000000 : ℝ)|^4195 ≤ (44166111555933/100000000000000 : ℝ)^3171
        have hw : |(5391665519/10000000000 : ℝ)|=(5391665519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s9_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265631733/500000000 : ℝ)*x 0 + (-1039696427/5000000000 : ℝ)*x 1 + (2695832759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265631733/500000000 : ℝ)^4195 ≤ (21655850951967/50000000000000 : ℝ)^3171 := by
    have hnat : (265631733 : ℕ)^4195*50000000000000^3171 ≤ 21655850951967^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265631733 500000000 21655850951967 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039696427/5000000000 : ℝ)^4195 ≤ (2504437306459/20000000000000 : ℝ)^3171 := by
    have hnat : (1039696427 : ℕ)^4195*20000000000000^3171 ≤ 2504437306459^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039696427 5000000000 2504437306459 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695832759/5000000000 : ℝ)^4195 ≤ (5520763943137/12500000000000 : ℝ)^3171 := by
    have hnat : (2695832759 : ℕ)^4195*12500000000000^3171 ≤ 5520763943137^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695832759 5000000000 5520763943137 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265631733/500000000 : ℝ), (-1039696427/5000000000 : ℝ), (2695832759/5000000000 : ℝ)] ![(21655850951967/50000000000000 : ℝ), (2504437306459/20000000000000 : ℝ), (5520763943137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265631733/500000000 : ℝ)|^4195 ≤ (21655850951967/50000000000000 : ℝ)^3171
        have hw : |(265631733/500000000 : ℝ)|=(265631733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039696427/5000000000 : ℝ)|^4195 ≤ (2504437306459/20000000000000 : ℝ)^3171
        have hw : |(-1039696427/5000000000 : ℝ)|=(1039696427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695832759/5000000000 : ℝ)|^4195 ≤ (5520763943137/12500000000000 : ℝ)^3171
        have hw : |(2695832759/5000000000 : ℝ)|=(2695832759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s9_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656317339/5000000000 : ℝ)*x 0 + (5391665519/10000000000 : ℝ)*x 1 + (-2079392829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656317339/5000000000 : ℝ)^4195 ≤ (10827925524517/25000000000000 : ℝ)^3171 := by
    have hnat : (2656317339 : ℕ)^4195*25000000000000^3171 ≤ 10827925524517^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656317339 5000000000 10827925524517 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391665519/10000000000 : ℝ)^4195 ≤ (44166111555933/100000000000000 : ℝ)^3171 := by
    have hnat : (5391665519 : ℕ)^4195*100000000000000^3171 ≤ 44166111555933^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391665519 10000000000 44166111555933 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079392829/10000000000 : ℝ)^4195 ≤ (12522186333127/100000000000000 : ℝ)^3171 := by
    have hnat : (2079392829 : ℕ)^4195*100000000000000^3171 ≤ 12522186333127^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079392829 10000000000 12522186333127 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656317339/5000000000 : ℝ), (5391665519/10000000000 : ℝ), (-2079392829/10000000000 : ℝ)] ![(10827925524517/25000000000000 : ℝ), (44166111555933/100000000000000 : ℝ), (12522186333127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656317339/5000000000 : ℝ)|^4195 ≤ (10827925524517/25000000000000 : ℝ)^3171
        have hw : |(2656317339/5000000000 : ℝ)|=(2656317339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391665519/10000000000 : ℝ)|^4195 ≤ (44166111555933/100000000000000 : ℝ)^3171
        have hw : |(5391665519/10000000000 : ℝ)|=(5391665519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079392829/10000000000 : ℝ)|^4195 ≤ (12522186333127/100000000000000 : ℝ)^3171
        have hw : |(-2079392829/10000000000 : ℝ)|=(2079392829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s9_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254877/9765625 : ℝ)*x 0 + (4484177003/10000000000 : ℝ)*x 1 + (4233375973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254877/9765625 : ℝ)^4195 ≤ (16658691022727/50000000000000 : ℝ)^3171 := by
    have hnat : (4254877 : ℕ)^4195*50000000000000^3171 ≤ 16658691022727^3171*9765625^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254877 9765625 16658691022727 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484177003/10000000000 : ℝ)^4195 ≤ (34610021428061/100000000000000 : ℝ)^3171 := by
    have hnat : (4484177003 : ℕ)^4195*100000000000000^3171 ≤ 34610021428061^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484177003 10000000000 34610021428061 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233375973/10000000000 : ℝ)^4195 ≤ (8018149125623/25000000000000 : ℝ)^3171 := by
    have hnat : (4233375973 : ℕ)^4195*25000000000000^3171 ≤ 8018149125623^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233375973 10000000000 8018149125623 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254877/9765625 : ℝ), (4484177003/10000000000 : ℝ), (4233375973/10000000000 : ℝ)] ![(16658691022727/50000000000000 : ℝ), (34610021428061/100000000000000 : ℝ), (8018149125623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254877/9765625 : ℝ)|^4195 ≤ (16658691022727/50000000000000 : ℝ)^3171
        have hw : |(4254877/9765625 : ℝ)|=(4254877/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484177003/10000000000 : ℝ)|^4195 ≤ (34610021428061/100000000000000 : ℝ)^3171
        have hw : |(4484177003/10000000000 : ℝ)|=(4484177003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233375973/10000000000 : ℝ)|^4195 ≤ (8018149125623/25000000000000 : ℝ)^3171
        have hw : |(4233375973/10000000000 : ℝ)|=(4233375973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (357/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (357/3125 : ℝ) ^ (8389/2048 : ℝ) ≤ (13824294750381837/100000000000000000000 : ℝ) := by
    have hpowers : (357/3125 : ℝ)^8389 ≤ (13824294750381837/100000000000000000000 : ℝ)^2048 := by
      have hnat : (357 : ℕ)^8389*100000000000000000000^2048 ≤ 13824294750381837^2048*3125^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        357 3125 13824294750381837 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (357/3125 : ℝ)) (X := (13824294750381837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (8389/2048 : ℝ) ≤ (32547190907988483/100000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^8389 ≤ (32547190907988483/100000000000000000000 : ℝ)^2048 := by
      have hnat : (88 : ℕ)^8389*100000000000000000000^2048 ≤ 32547190907988483^2048*625^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 32547190907988483 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (32547190907988483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013824294750381837/50000000000000000000 : ℝ) ≤ (5000337456165009/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50013824294750381837/50000000000000000000 : ℝ)^2048 ≤ (5000337456165009/5000000000000000 : ℝ)^8389 := by
      have hnat : (50013824294750381837 : ℕ)^2048*5000000000000000^8389 ≤ 5000337456165009^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013824294750381837 50000000000000000000 5000337456165009 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337456165009/5000000000000000 : ℝ)) (X := (50013824294750381837/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250579643570729629/1250000000000000000 : ℝ) ≤ (10001131865102603/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (1250579643570729629/1250000000000000000 : ℝ)^2048 ≤ (10001131865102603/10000000000000000 : ℝ)^8389 := by
      have hnat : (1250579643570729629 : ℕ)^2048*10000000000000000^8389 ≤ 10001131865102603^8389*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250579643570729629 1250000000000000000 10001131865102603 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001131865102603/10000000000000000 : ℝ)) (X := (1250579643570729629/1250000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032547190907988483/50000000000000000000 : ℝ) ≤ (2500397204468797/2500000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50032547190907988483/50000000000000000000 : ℝ)^2048 ≤ (2500397204468797/2500000000000000 : ℝ)^8389 := by
      have hnat : (50032547190907988483 : ℕ)^2048*2500000000000000^8389 ≤ 2500397204468797^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032547190907988483 50000000000000000000 2500397204468797 2500000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500397204468797/2500000000000000 : ℝ)) (X := (50032547190907988483/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13824294750381837/100000000000000000000 : ℝ) ≤ ((207432438360941451/207500000000000000 : ℝ)+2*(91390554517/53120000000000 : ℝ)*(357/3125 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (207432438360941451/207500000000000000 : ℝ)+2*(91390554517/53120000000000 : ℝ)*(357/3125 : ℝ)=(5000337456165009/5000000000000000 : ℝ) by norm_num, show 1+2*(13824294750381837/100000000000000000000 : ℝ)=(50013824294750381837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32547190907988483/100000000000000000000 : ℝ)+(13824294750381837/100000000000000000000 : ℝ) ≤ ((207432438360941451/207500000000000000 : ℝ)+(91390554517/53120000000000 : ℝ)*((88/625 : ℝ)+(357/3125 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (207432438360941451/207500000000000000 : ℝ)+(91390554517/53120000000000 : ℝ)*((88/625 : ℝ)+(357/3125 : ℝ))=(10001131865102603/10000000000000000 : ℝ) by norm_num, show 1+(32547190907988483/100000000000000000000 : ℝ)+(13824294750381837/100000000000000000000 : ℝ)=(1250579643570729629/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32547190907988483/100000000000000000000 : ℝ) ≤ ((207432438360941451/207500000000000000 : ℝ)+2*(91390554517/53120000000000 : ℝ)*(88/625 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (207432438360941451/207500000000000000 : ℝ)+2*(91390554517/53120000000000 : ℝ)*(88/625 : ℝ)=(2500397204468797/2500000000000000 : ℝ) by norm_num, show 1+2*(32547190907988483/100000000000000000000 : ℝ)=(50032547190907988483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (207432438360941451/207500000000000000 : ℝ)*(X 1 0+X 2 0)+(91390554517/53120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (88/625 : ℝ)) (c := (207432438360941451/207500000000000000 : ℝ)) (alpha := (91390554517/53120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (207432438360941451/207500000000000000 : ℝ)*(X 0 1+X 2 1)+(91390554517/53120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (88/625 : ℝ)) (c := (207432438360941451/207500000000000000 : ℝ)) (alpha := (91390554517/53120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (207432438360941451/207500000000000000 : ℝ)*(X 0 2+X 1 2)+(91390554517/53120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (88/625 : ℝ)) (c := (207432438360941451/207500000000000000 : ℝ)) (alpha := (91390554517/53120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344519909/10000000000 : ℝ)*X 2 0+(5266632463/10000000000 : ℝ)*X 2 1+(-88176993/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2140864969/10000000000 : ℝ)*X 0 0+(1316737101/2500000000 : ℝ)*X 0 1+(5391665519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((265631733/500000000 : ℝ)*X 1 0+(-1039696427/5000000000 : ℝ)*X 1 1+(2695832759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656317339/5000000000 : ℝ)*X 2 0+(5391665519/10000000000 : ℝ)*X 2 1+(-2079392829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4254877/9765625 : ℝ)*X 0 0+(4484177003/10000000000 : ℝ)*X 0 1+(4233375973/10000000000 : ℝ)*X 0 2+(4254877/9765625 : ℝ)*X 1 0+(4484177003/10000000000 : ℝ)*X 1 1+(4233375973/10000000000 : ℝ)*X 1 2+(4254877/9765625 : ℝ)*X 2 0+(4484177003/10000000000 : ℝ)*X 2 1+(4233375973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4444549696962323169293019/2075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234223751/100000000000000 : ℝ)*(base19) + (17255067/4000000000000 : ℝ)*(base23) + (36782687/50000000000000 : ℝ)*(lower1) + (33570961/100000000000000 : ℝ)*(upper3) + (35858143/50000000000000 : ℝ)*(lower4) + (3205833/10000000000000 : ℝ)*(upper5) + (600267968078099/10000000000000 : ℝ)*(major0) + (600267968078099/10000000000000 : ℝ)*(major1) + (600267968078099/10000000000000 : ℝ)*(major2) + (1457665029/25000000000000 : ℝ)*(sp0) + (8018138181600621/100000000000000 : ℝ)*(sp1) + (801813794737687/10000000000000 : ℝ)*(sp2) + (801813191956383/10000000000000 : ℝ)*(sp3) + (3987221108562939/100000000000000 : ℝ)*(sp4) + (3987221108562939/100000000000000 : ℝ)*(f.failure) + (8018138181600621/100000000000000 : ℝ)*(f.sum) + (5718524838971/1328000000000000000000000000 : ℝ)*base65 + (127185671731460971/8300000000000000000000000000000 : ℝ)*base67 + (106763948602039029/8300000000000000000000000000000 : ℝ)*base70 + (1438717648007839029/8300000000000000000000000000000 : ℝ)*base72 + (5848572307621/1328000000000000000000000000 : ℝ)*base74 + (722778876101660971/8300000000000000000000000000000 : ℝ)*base75 + (1343833475039029/8300000000000000000000000000000 : ℝ)*base78 + (108817894398739029/8300000000000000000000000000000 : ℝ)*base80 + (329809400741/1328000000000000000000000000 : ℝ)*base82 + (20987989/10000000000000000000000 : ℝ)*base89 + (20987989/10000000000000000000000 : ℝ)*base91 + (20987989/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1197_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1197_box_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201575977/1000000000 : ℝ)*x 0 + (268775487/500000000 : ℝ)*x 1 + (2687754859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201575977/1000000000 : ℝ)^4195 ≤ (12017762192911/100000000000000 : ℝ)^3171 := by
    have hnat : (201575977 : ℕ)^4195*100000000000000^3171 ≤ 12017762192911^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201575977 1000000000 12017762192911 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268775487/500000000 : ℝ)^4195 ≤ (8798223802887/20000000000000 : ℝ)^3171 := by
    have hnat : (268775487 : ℕ)^4195*20000000000000^3171 ≤ 8798223802887^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268775487 500000000 8798223802887 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687754859/5000000000 : ℝ)^4195 ≤ (687361230879/1562500000000 : ℝ)^3171 := by
    have hnat : (2687754859 : ℕ)^4195*1562500000000^3171 ≤ 687361230879^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687754859 5000000000 687361230879 1562500000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201575977/1000000000 : ℝ), (268775487/500000000 : ℝ), (2687754859/5000000000 : ℝ)] ![(12017762192911/100000000000000 : ℝ), (8798223802887/20000000000000 : ℝ), (687361230879/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201575977/1000000000 : ℝ)|^4195 ≤ (12017762192911/100000000000000 : ℝ)^3171
        have hw : |(-201575977/1000000000 : ℝ)|=(201575977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268775487/500000000 : ℝ)|^4195 ≤ (8798223802887/20000000000000 : ℝ)^3171
        have hw : |(268775487/500000000 : ℝ)|=(268775487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687754859/5000000000 : ℝ)|^4195 ≤ (687361230879/1562500000000 : ℝ)^3171
        have hw : |(2687754859/5000000000 : ℝ)|=(2687754859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331028797/625000000 : ℝ)*x 0 + (-1061547953/5000000000 : ℝ)*x 1 + (215020393/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331028797/625000000 : ℝ)^4195 ≤ (43137347746563/100000000000000 : ℝ)^3171 := by
    have hnat : (331028797 : ℕ)^4195*100000000000000^3171 ≤ 43137347746563^3171*625000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331028797 625000000 43137347746563 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061547953/5000000000 : ℝ)^4195 ≤ (12871532304939/100000000000000 : ℝ)^3171 := by
    have hnat : (1061547953 : ℕ)^4195*100000000000000^3171 ≤ 12871532304939^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061547953 5000000000 12871532304939 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215020393/400000000 : ℝ)^4195 ≤ (43991119934673/100000000000000 : ℝ)^3171 := by
    have hnat : (215020393 : ℕ)^4195*100000000000000^3171 ≤ 43991119934673^3171*400000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215020393 400000000 43991119934673 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331028797/625000000 : ℝ), (-1061547953/5000000000 : ℝ), (215020393/400000000 : ℝ)] ![(43137347746563/100000000000000 : ℝ), (12871532304939/100000000000000 : ℝ), (43991119934673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331028797/625000000 : ℝ)|^4195 ≤ (43137347746563/100000000000000 : ℝ)^3171
        have hw : |(331028797/625000000 : ℝ)|=(331028797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061547953/5000000000 : ℝ)|^4195 ≤ (12871532304939/100000000000000 : ℝ)^3171
        have hw : |(-1061547953/5000000000 : ℝ)|=(1061547953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215020393/400000000 : ℝ)|^4195 ≤ (43991119934673/100000000000000 : ℝ)^3171
        have hw : |(215020393/400000000 : ℝ)|=(215020393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296460443/10000000000 : ℝ)*x 0 + (671938757/1250000000 : ℝ)*x 1 + (-2123096009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296460443/10000000000 : ℝ)^4195 ≤ (8627468883439/20000000000000 : ℝ)^3171 := by
    have hnat : (5296460443 : ℕ)^4195*20000000000000^3171 ≤ 8627468883439^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296460443 10000000000 8627468883439 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671938757/1250000000 : ℝ)^4195 ≤ (21995561217777/50000000000000 : ℝ)^3171 := by
    have hnat : (671938757 : ℕ)^4195*50000000000000^3171 ≤ 21995561217777^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671938757 1250000000 21995561217777 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123096009/10000000000 : ℝ)^4195 ≤ (12871533131041/100000000000000 : ℝ)^3171 := by
    have hnat : (2123096009 : ℕ)^4195*100000000000000^3171 ≤ 12871533131041^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123096009 10000000000 12871533131041 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296460443/10000000000 : ℝ), (671938757/1250000000 : ℝ), (-2123096009/10000000000 : ℝ)] ![(8627468883439/20000000000000 : ℝ), (21995561217777/50000000000000 : ℝ), (12871533131041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296460443/10000000000 : ℝ)|^4195 ≤ (8627468883439/20000000000000 : ℝ)^3171
        have hw : |(5296460443/10000000000 : ℝ)|=(5296460443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671938757/1250000000 : ℝ)|^4195 ≤ (21995561217777/50000000000000 : ℝ)^3171
        have hw : |(671938757/1250000000 : ℝ)|=(671938757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123096009/10000000000 : ℝ)|^4195 ≤ (12871533131041/100000000000000 : ℝ)^3171
        have hw : |(-2123096009/10000000000 : ℝ)|=(2123096009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4463952231/10000000000 : ℝ)*x 0 + (4305570981/10000000000 : ℝ)*x 1 + (4305571187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4463952231/10000000000 : ℝ)^4195 ≤ (6880732641911/20000000000000 : ℝ)^3171 := by
    have hnat : (4463952231 : ℕ)^4195*20000000000000^3171 ≤ 6880732641911^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4463952231 10000000000 6880732641911 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4305570981/10000000000 : ℝ)^4195 ≤ (32798167350849/100000000000000 : ℝ)^3171 := by
    have hnat : (4305570981 : ℕ)^4195*100000000000000^3171 ≤ 32798167350849^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305570981 10000000000 32798167350849 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4305571187/10000000000 : ℝ)^4195 ≤ (16399084713411/50000000000000 : ℝ)^3171 := by
    have hnat : (4305571187 : ℕ)^4195*50000000000000^3171 ≤ 16399084713411^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305571187 10000000000 16399084713411 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4463952231/10000000000 : ℝ), (4305570981/10000000000 : ℝ), (4305571187/10000000000 : ℝ)] ![(6880732641911/20000000000000 : ℝ), (32798167350849/100000000000000 : ℝ), (16399084713411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4463952231/10000000000 : ℝ)|^4195 ≤ (6880732641911/20000000000000 : ℝ)^3171
        have hw : |(4463952231/10000000000 : ℝ)|=(4463952231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4305570981/10000000000 : ℝ)|^4195 ≤ (32798167350849/100000000000000 : ℝ)^3171
        have hw : |(4305570981/10000000000 : ℝ)|=(4305570981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4305571187/10000000000 : ℝ)|^4195 ≤ (16399084713411/50000000000000 : ℝ)^3171
        have hw : |(4305571187/10000000000 : ℝ)|=(4305571187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1133674489/5000000000 : ℝ)*x 0 + (1056360817/2000000000 : ℝ)*x 1 + (5281804133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133674489/5000000000 : ℝ)^4195 ≤ (14041003847137/100000000000000 : ℝ)^3171 := by
    have hnat : (1133674489 : ℕ)^4195*100000000000000^3171 ≤ 14041003847137^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133674489 5000000000 14041003847137 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056360817/2000000000 : ℝ)^4195 ≤ (21489748904769/50000000000000 : ℝ)^3171 := by
    have hnat : (1056360817 : ℕ)^4195*50000000000000^3171 ≤ 21489748904769^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056360817 2000000000 21489748904769 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281804133/10000000000 : ℝ)^4195 ≤ (42979498326259/100000000000000 : ℝ)^3171 := by
    have hnat : (5281804133 : ℕ)^4195*100000000000000^3171 ≤ 42979498326259^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281804133 10000000000 42979498326259 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1133674489/5000000000 : ℝ), (1056360817/2000000000 : ℝ), (5281804133/10000000000 : ℝ)] ![(14041003847137/100000000000000 : ℝ), (21489748904769/50000000000000 : ℝ), (42979498326259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1133674489/5000000000 : ℝ)|^4195 ≤ (14041003847137/100000000000000 : ℝ)^3171
        have hw : |(-1133674489/5000000000 : ℝ)|=(1133674489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056360817/2000000000 : ℝ)|^4195 ≤ (21489748904769/50000000000000 : ℝ)^3171
        have hw : |(1056360817/2000000000 : ℝ)|=(1056360817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281804133/10000000000 : ℝ)|^4195 ≤ (42979498326259/100000000000000 : ℝ)^3171
        have hw : |(5281804133/10000000000 : ℝ)|=(5281804133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362581751/10000000000 : ℝ)*x 0 + (-1080058671/5000000000 : ℝ)*x 1 + (528180403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362581751/10000000000 : ℝ)^4195 ≤ (43851210776959/100000000000000 : ℝ)^3171 := by
    have hnat : (5362581751 : ℕ)^4195*100000000000000^3171 ≤ 43851210776959^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362581751 10000000000 43851210776959 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080058671/5000000000 : ℝ)^4195 ≤ (2633858398603/20000000000000 : ℝ)^3171 := by
    have hnat : (1080058671 : ℕ)^4195*20000000000000^3171 ≤ 2633858398603^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080058671 5000000000 2633858398603 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528180403/1000000000 : ℝ)^4195 ≤ (21489748608731/50000000000000 : ℝ)^3171 := by
    have hnat : (528180403 : ℕ)^4195*50000000000000^3171 ≤ 21489748608731^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528180403 1000000000 21489748608731 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362581751/10000000000 : ℝ), (-1080058671/5000000000 : ℝ), (528180403/1000000000 : ℝ)] ![(43851210776959/100000000000000 : ℝ), (2633858398603/20000000000000 : ℝ), (21489748608731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362581751/10000000000 : ℝ)|^4195 ≤ (43851210776959/100000000000000 : ℝ)^3171
        have hw : |(5362581751/10000000000 : ℝ)|=(5362581751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1080058671/5000000000 : ℝ)|^4195 ≤ (2633858398603/20000000000000 : ℝ)^3171
        have hw : |(-1080058671/5000000000 : ℝ)|=(1080058671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528180403/1000000000 : ℝ)|^4195 ≤ (21489748608731/50000000000000 : ℝ)^3171
        have hw : |(528180403/1000000000 : ℝ)|=(528180403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072516471/2000000000 : ℝ)*x 0 + (2640902051/5000000000 : ℝ)*x 1 + (-540029109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072516471/2000000000 : ℝ)^4195 ≤ (43851217310977/100000000000000 : ℝ)^3171 := by
    have hnat : (1072516471 : ℕ)^4195*100000000000000^3171 ≤ 43851217310977^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072516471 2000000000 43851217310977 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640902051/5000000000 : ℝ)^4195 ≤ (42979497992543/100000000000000 : ℝ)^3171 := by
    have hnat : (2640902051 : ℕ)^4195*100000000000000^3171 ≤ 42979497992543^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640902051 5000000000 42979497992543 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540029109/2500000000 : ℝ)^4195 ≤ (13169284685849/100000000000000 : ℝ)^3171 := by
    have hnat : (540029109 : ℕ)^4195*100000000000000^3171 ≤ 13169284685849^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540029109 2500000000 13169284685849 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072516471/2000000000 : ℝ), (2640902051/5000000000 : ℝ), (-540029109/2500000000 : ℝ)] ![(43851217310977/100000000000000 : ℝ), (42979497992543/100000000000000 : ℝ), (13169284685849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072516471/2000000000 : ℝ)|^4195 ≤ (43851217310977/100000000000000 : ℝ)^3171
        have hw : |(1072516471/2000000000 : ℝ)|=(1072516471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640902051/5000000000 : ℝ)|^4195 ≤ (42979497992543/100000000000000 : ℝ)^3171
        have hw : |(2640902051/5000000000 : ℝ)|=(2640902051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540029109/2500000000 : ℝ)|^4195 ≤ (13169284685849/100000000000000 : ℝ)^3171
        have hw : |(-540029109/2500000000 : ℝ)|=(540029109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249632301/10000000000 : ℝ)*x 0 + (441271129/1000000000 : ℝ)*x 1 + (275794373/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249632301/10000000000 : ℝ)^4195 ≤ (32235629087121/100000000000000 : ℝ)^3171 := by
    have hnat : (4249632301 : ℕ)^4195*100000000000000^3171 ≤ 32235629087121^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249632301 10000000000 32235629087121 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441271129/1000000000 : ℝ)^4195 ≤ (4235274020819/12500000000000 : ℝ)^3171 := by
    have hnat : (441271129 : ℕ)^4195*12500000000000^3171 ≤ 4235274020819^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441271129 1000000000 4235274020819 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275794373/625000000 : ℝ)^4195 ≤ (16941089368939/50000000000000 : ℝ)^3171 := by
    have hnat : (275794373 : ℕ)^4195*50000000000000^3171 ≤ 16941089368939^3171*625000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275794373 625000000 16941089368939 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249632301/10000000000 : ℝ), (441271129/1000000000 : ℝ), (275794373/625000000 : ℝ)] ![(32235629087121/100000000000000 : ℝ), (4235274020819/12500000000000 : ℝ), (16941089368939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249632301/10000000000 : ℝ)|^4195 ≤ (32235629087121/100000000000000 : ℝ)^3171
        have hw : |(4249632301/10000000000 : ℝ)|=(4249632301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441271129/1000000000 : ℝ)|^4195 ≤ (4235274020819/12500000000000 : ℝ)^3171
        have hw : |(441271129/1000000000 : ℝ)|=(441271129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275794373/625000000 : ℝ)|^4195 ≤ (16941089368939/50000000000000 : ℝ)^3171
        have hw : |(275794373/625000000 : ℝ)|=(275794373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_8 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214676679/10000000000 : ℝ)*x 0 + (260898557/500000000 : ℝ)*x 1 + (2692560621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214676679/10000000000 : ℝ)^4195 ≤ (6805557062101/50000000000000 : ℝ)^3171 := by
    have hnat : (2214676679 : ℕ)^4195*50000000000000^3171 ≤ 6805557062101^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214676679 10000000000 6805557062101 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260898557/500000000 : ℝ)^4195 ≤ (1057341989109/2500000000000 : ℝ)^3171 := by
    have hnat : (260898557 : ℕ)^4195*2500000000000^3171 ≤ 1057341989109^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260898557 500000000 1057341989109 2500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692560621/5000000000 : ℝ)^4195 ≤ (44095206292539/100000000000000 : ℝ)^3171 := by
    have hnat : (2692560621 : ℕ)^4195*100000000000000^3171 ≤ 44095206292539^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692560621 5000000000 44095206292539 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214676679/10000000000 : ℝ), (260898557/500000000 : ℝ), (2692560621/5000000000 : ℝ)] ![(6805557062101/50000000000000 : ℝ), (1057341989109/2500000000000 : ℝ), (44095206292539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214676679/10000000000 : ℝ)|^4195 ≤ (6805557062101/50000000000000 : ℝ)^3171
        have hw : |(-2214676679/10000000000 : ℝ)|=(2214676679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260898557/500000000 : ℝ)|^4195 ≤ (1057341989109/2500000000000 : ℝ)^3171
        have hw : |(260898557/500000000 : ℝ)|=(260898557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692560621/5000000000 : ℝ)|^4195 ≤ (44095206292539/100000000000000 : ℝ)^3171
        have hw : |(2692560621/5000000000 : ℝ)|=(2692560621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_9 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289675293/10000000000 : ℝ)*x 0 + (-1059615423/5000000000 : ℝ)*x 1 + (2692560609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289675293/10000000000 : ℝ)^4195 ≤ (43064251889381/100000000000000 : ℝ)^3171 := by
    have hnat : (5289675293 : ℕ)^4195*100000000000000^3171 ≤ 43064251889381^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289675293 10000000000 43064251889381 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059615423/5000000000 : ℝ)^4195 ≤ (6420271034839/50000000000000 : ℝ)^3171 := by
    have hnat : (1059615423 : ℕ)^4195*50000000000000^3171 ≤ 6420271034839^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059615423 5000000000 6420271034839 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692560609/5000000000 : ℝ)^4195 ≤ (22047603016279/50000000000000 : ℝ)^3171 := by
    have hnat : (2692560609 : ℕ)^4195*50000000000000^3171 ≤ 22047603016279^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692560609 5000000000 22047603016279 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289675293/10000000000 : ℝ), (-1059615423/5000000000 : ℝ), (2692560609/5000000000 : ℝ)] ![(43064251889381/100000000000000 : ℝ), (6420271034839/50000000000000 : ℝ), (22047603016279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289675293/10000000000 : ℝ)|^4195 ≤ (43064251889381/100000000000000 : ℝ)^3171
        have hw : |(5289675293/10000000000 : ℝ)|=(5289675293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059615423/5000000000 : ℝ)|^4195 ≤ (6420271034839/50000000000000 : ℝ)^3171
        have hw : |(-1059615423/5000000000 : ℝ)|=(1059615423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692560609/5000000000 : ℝ)|^4195 ≤ (22047603016279/50000000000000 : ℝ)^3171
        have hw : |(2692560609/5000000000 : ℝ)|=(2692560609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_10 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289675357/10000000000 : ℝ)*x 0 + (5385121229/10000000000 : ℝ)*x 1 + (-423846149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289675357/10000000000 : ℝ)^4195 ≤ (21532126289337/50000000000000 : ℝ)^3171 := by
    have hnat : (5289675357 : ℕ)^4195*50000000000000^3171 ≤ 21532126289337^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289675357 10000000000 21532126289337 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385121229/10000000000 : ℝ)^4195 ≤ (11023801537929/25000000000000 : ℝ)^3171 := by
    have hnat : (5385121229 : ℕ)^4195*25000000000000^3171 ≤ 11023801537929^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385121229 10000000000 11023801537929 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423846149/2000000000 : ℝ)^4195 ≤ (6420270630047/50000000000000 : ℝ)^3171 := by
    have hnat : (423846149 : ℕ)^4195*50000000000000^3171 ≤ 6420270630047^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423846149 2000000000 6420270630047 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289675357/10000000000 : ℝ), (5385121229/10000000000 : ℝ), (-423846149/2000000000 : ℝ)] ![(21532126289337/50000000000000 : ℝ), (11023801537929/25000000000000 : ℝ), (6420270630047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289675357/10000000000 : ℝ)|^4195 ≤ (21532126289337/50000000000000 : ℝ)^3171
        have hw : |(5289675357/10000000000 : ℝ)|=(5289675357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385121229/10000000000 : ℝ)|^4195 ≤ (11023801537929/25000000000000 : ℝ)^3171
        have hw : |(5385121229/10000000000 : ℝ)|=(5385121229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423846149/2000000000 : ℝ)|^4195 ≤ (6420270630047/50000000000000 : ℝ)^3171
        have hw : |(-423846149/2000000000 : ℝ)|=(423846149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_11 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (224283097/500000000 : ℝ)*x 0 + (4294575649/10000000000 : ℝ)*x 1 + (536821971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224283097/500000000 : ℝ)^4195 ≤ (34625184461463/100000000000000 : ℝ)^3171 := by
    have hnat : (224283097 : ℕ)^4195*100000000000000^3171 ≤ 34625184461463^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224283097 500000000 34625184461463 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4294575649/10000000000 : ℝ)^4195 ≤ (6537481432837/20000000000000 : ℝ)^3171 := by
    have hnat : (4294575649 : ℕ)^4195*20000000000000^3171 ≤ 6537481432837^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294575649 10000000000 6537481432837 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536821971/1250000000 : ℝ)^4195 ≤ (32687408362423/100000000000000 : ℝ)^3171 := by
    have hnat : (536821971 : ℕ)^4195*100000000000000^3171 ≤ 32687408362423^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536821971 1250000000 32687408362423 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224283097/500000000 : ℝ), (4294575649/10000000000 : ℝ), (536821971/1250000000 : ℝ)] ![(34625184461463/100000000000000 : ℝ), (6537481432837/20000000000000 : ℝ), (32687408362423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224283097/500000000 : ℝ)|^4195 ≤ (34625184461463/100000000000000 : ℝ)^3171
        have hw : |(224283097/500000000 : ℝ)|=(224283097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4294575649/10000000000 : ℝ)|^4195 ≤ (6537481432837/20000000000000 : ℝ)^3171
        have hw : |(4294575649/10000000000 : ℝ)|=(4294575649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536821971/1250000000 : ℝ)|^4195 ≤ (32687408362423/100000000000000 : ℝ)^3171
        have hw : |(536821971/1250000000 : ℝ)|=(536821971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_12 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034358861/5000000000 : ℝ)*x 0 + (5438103827/10000000000 : ℝ)*x 1 + (1318435597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034358861/5000000000 : ℝ)^4195 ≤ (12437211363203/100000000000000 : ℝ)^3171 := by
    have hnat : (1034358861 : ℕ)^4195*100000000000000^3171 ≤ 12437211363203^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034358861 5000000000 12437211363203 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438103827/10000000000 : ℝ)^4195 ≤ (44670053736101/100000000000000 : ℝ)^3171 := by
    have hnat : (5438103827 : ℕ)^4195*100000000000000^3171 ≤ 44670053736101^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438103827 10000000000 44670053736101 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318435597/2500000000 : ℝ)^4195 ≤ (21446367444389/50000000000000 : ℝ)^3171 := by
    have hnat : (1318435597 : ℕ)^4195*50000000000000^3171 ≤ 21446367444389^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318435597 2500000000 21446367444389 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034358861/5000000000 : ℝ), (5438103827/10000000000 : ℝ), (1318435597/2500000000 : ℝ)] ![(12437211363203/100000000000000 : ℝ), (44670053736101/100000000000000 : ℝ), (21446367444389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034358861/5000000000 : ℝ)|^4195 ≤ (12437211363203/100000000000000 : ℝ)^3171
        have hw : |(-1034358861/5000000000 : ℝ)|=(1034358861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438103827/10000000000 : ℝ)|^4195 ≤ (44670053736101/100000000000000 : ℝ)^3171
        have hw : |(5438103827/10000000000 : ℝ)|=(5438103827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318435597/2500000000 : ℝ)|^4195 ≤ (21446367444389/50000000000000 : ℝ)^3171
        have hw : |(1318435597/2500000000 : ℝ)|=(1318435597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_13 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073653779/2000000000 : ℝ)*x 0 + (-432648971/2000000000 : ℝ)*x 1 + (1318435563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073653779/2000000000 : ℝ)^4195 ≤ (43912744324489/100000000000000 : ℝ)^3171 := by
    have hnat : (1073653779 : ℕ)^4195*100000000000000^3171 ≤ 43912744324489^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073653779 2000000000 43912744324489 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432648971/2000000000 : ℝ)^4195 ≤ (13194522234763/100000000000000 : ℝ)^3171 := by
    have hnat : (432648971 : ℕ)^4195*100000000000000^3171 ≤ 13194522234763^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432648971 2000000000 13194522234763 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318435563/2500000000 : ℝ)^4195 ≤ (42892733425457/100000000000000 : ℝ)^3171 := by
    have hnat : (1318435563 : ℕ)^4195*100000000000000^3171 ≤ 42892733425457^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318435563 2500000000 42892733425457 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073653779/2000000000 : ℝ), (-432648971/2000000000 : ℝ), (1318435563/2500000000 : ℝ)] ![(43912744324489/100000000000000 : ℝ), (13194522234763/100000000000000 : ℝ), (42892733425457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073653779/2000000000 : ℝ)|^4195 ≤ (43912744324489/100000000000000 : ℝ)^3171
        have hw : |(1073653779/2000000000 : ℝ)|=(1073653779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432648971/2000000000 : ℝ)|^4195 ≤ (13194522234763/100000000000000 : ℝ)^3171
        have hw : |(-432648971/2000000000 : ℝ)|=(432648971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318435563/2500000000 : ℝ)|^4195 ≤ (42892733425457/100000000000000 : ℝ)^3171
        have hw : |(1318435563/2500000000 : ℝ)|=(1318435563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_14 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671033619/1250000000 : ℝ)*x 0 + (5273742201/10000000000 : ℝ)*x 1 + (-2163244847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671033619/1250000000 : ℝ)^4195 ≤ (43912744941321/100000000000000 : ℝ)^3171 := by
    have hnat : (671033619 : ℕ)^4195*100000000000000^3171 ≤ 43912744941321^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671033619 1250000000 43912744941321 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273742201/10000000000 : ℝ)^4195 ≤ (5361591609589/12500000000000 : ℝ)^3171 := by
    have hnat : (5273742201 : ℕ)^4195*12500000000000^3171 ≤ 5361591609589^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273742201 10000000000 5361591609589 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163244847/10000000000 : ℝ)^4195 ≤ (1319452217021/10000000000000 : ℝ)^3171 := by
    have hnat : (2163244847 : ℕ)^4195*10000000000000^3171 ≤ 1319452217021^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163244847 10000000000 1319452217021 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671033619/1250000000 : ℝ), (5273742201/10000000000 : ℝ), (-2163244847/10000000000 : ℝ)] ![(43912744941321/100000000000000 : ℝ), (5361591609589/12500000000000 : ℝ), (1319452217021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671033619/1250000000 : ℝ)|^4195 ≤ (43912744941321/100000000000000 : ℝ)^3171
        have hw : |(671033619/1250000000 : ℝ)|=(671033619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273742201/10000000000 : ℝ)|^4195 ≤ (5361591609589/12500000000000 : ℝ)^3171
        have hw : |(5273742201/10000000000 : ℝ)|=(5273742201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163244847/10000000000 : ℝ)|^4195 ≤ (1319452217021/10000000000000 : ℝ)^3171
        have hw : |(-2163244847/10000000000 : ℝ)|=(2163244847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_box_15 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (846192467/2000000000 : ℝ)*x 0 + (4421923193/10000000000 : ℝ)*x 1 + (4421923067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (846192467/2000000000 : ℝ)^4195 ≤ (1281936306257/4000000000000 : ℝ)^3171 := by
    have hnat : (846192467 : ℕ)^4195*4000000000000^3171 ≤ 1281936306257^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846192467 2000000000 1281936306257 4000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4421923193/10000000000 : ℝ)^4195 ≤ (33975796802831/100000000000000 : ℝ)^3171 := by
    have hnat : (4421923193 : ℕ)^4195*100000000000000^3171 ≤ 33975796802831^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421923193 10000000000 33975796802831 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421923067/10000000000 : ℝ)^4195 ≤ (212348722013/625000000000 : ℝ)^3171 := by
    have hnat : (4421923067 : ℕ)^4195*625000000000^3171 ≤ 212348722013^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421923067 10000000000 212348722013 625000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(846192467/2000000000 : ℝ), (4421923193/10000000000 : ℝ), (4421923067/10000000000 : ℝ)] ![(1281936306257/4000000000000 : ℝ), (33975796802831/100000000000000 : ℝ), (212348722013/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(846192467/2000000000 : ℝ)|^4195 ≤ (1281936306257/4000000000000 : ℝ)^3171
        have hw : |(846192467/2000000000 : ℝ)|=(846192467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4421923193/10000000000 : ℝ)|^4195 ≤ (33975796802831/100000000000000 : ℝ)^3171
        have hw : |(4421923193/10000000000 : ℝ)|=(4421923193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421923067/10000000000 : ℝ)|^4195 ≤ (212348722013/625000000000 : ℝ)^3171
        have hw : |(4421923067/10000000000 : ℝ)|=(4421923067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62239/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29671/50000 : ℝ) ∧ (3199/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83247/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (357/3125 : ℝ) ^ (8389/2048 : ℝ) ≤ (13824294750381837/100000000000000000000 : ℝ) := by
    have hpowers : (357/3125 : ℝ)^8389 ≤ (13824294750381837/100000000000000000000 : ℝ)^2048 := by
      have hnat : (357 : ℕ)^8389*100000000000000000000^2048 ≤ 13824294750381837^2048*3125^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        357 3125 13824294750381837 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (357/3125 : ℝ)) (X := (13824294750381837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (8134430808212613/25000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^8389 ≤ (8134430808212613/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14079 : ℕ)^8389*25000000000000000000^2048 ≤ 8134430808212613^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 8134430808212613 25000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (8134430808212613/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013824294750381837/50000000000000000000 : ℝ) ≤ (5000337456165009/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50013824294750381837/50000000000000000000 : ℝ)^2048 ≤ (5000337456165009/5000000000000000 : ℝ)^8389 := by
      have hnat : (50013824294750381837 : ℕ)^2048*5000000000000000^8389 ≤ 5000337456165009^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013824294750381837 50000000000000000000 5000337456165009 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337456165009/5000000000000000 : ℝ)) (X := (50013824294750381837/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046362017983232289/100000000000000000000 : ℝ) ≤ (2500282908512491/2500000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (100046362017983232289/100000000000000000000 : ℝ)^2048 ≤ (2500282908512491/2500000000000000 : ℝ)^8389 := by
      have hnat : (100046362017983232289 : ℕ)^2048*2500000000000000^8389 ≤ 2500282908512491^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046362017983232289 100000000000000000000 2500282908512491 2500000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500282908512491/2500000000000000 : ℝ)) (X := (100046362017983232289/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508134430808212613/12500000000000000000 : ℝ) ≤ (1000158835576991/1000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (12508134430808212613/12500000000000000000 : ℝ)^2048 ≤ (1000158835576991/1000000000000000 : ℝ)^8389 := by
      have hnat : (12508134430808212613 : ℕ)^2048*1000000000000000^8389 ≤ 1000158835576991^8389*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508134430808212613 12500000000000000000 1000158835576991 1000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000158835576991/1000000000000000 : ℝ)) (X := (12508134430808212613/12500000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13824294750381837/100000000000000000000 : ℝ) ≤ ((4423559452396478597/4425000000000000000 : ℝ)+2*(228360859973/132750000000000 : ℝ)*(357/3125 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (4423559452396478597/4425000000000000000 : ℝ)+2*(228360859973/132750000000000 : ℝ)*(357/3125 : ℝ)=(5000337456165009/5000000000000000 : ℝ) by norm_num, show 1+2*(13824294750381837/100000000000000000000 : ℝ)=(50013824294750381837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8134430808212613/25000000000000000000 : ℝ)+(13824294750381837/100000000000000000000 : ℝ) ≤ ((4423559452396478597/4425000000000000000 : ℝ)+(228360859973/132750000000000 : ℝ)*((14079/100000 : ℝ)+(357/3125 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (4423559452396478597/4425000000000000000 : ℝ)+(228360859973/132750000000000 : ℝ)*((14079/100000 : ℝ)+(357/3125 : ℝ))=(2500282908512491/2500000000000000 : ℝ) by norm_num, show 1+(8134430808212613/25000000000000000000 : ℝ)+(13824294750381837/100000000000000000000 : ℝ)=(100046362017983232289/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8134430808212613/25000000000000000000 : ℝ) ≤ ((4423559452396478597/4425000000000000000 : ℝ)+2*(228360859973/132750000000000 : ℝ)*(14079/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (4423559452396478597/4425000000000000000 : ℝ)+2*(228360859973/132750000000000 : ℝ)*(14079/100000 : ℝ)=(1000158835576991/1000000000000000 : ℝ) by norm_num, show 1+2*(8134430808212613/25000000000000000000 : ℝ)=(12508134430808212613/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4423559452396478597/4425000000000000000 : ℝ)*(X 1 0+X 2 0)+(228360859973/132750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (4423559452396478597/4425000000000000000 : ℝ)) (alpha := (228360859973/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4423559452396478597/4425000000000000000 : ℝ)*(X 0 1+X 2 1)+(228360859973/132750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (4423559452396478597/4425000000000000000 : ℝ)) (alpha := (228360859973/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4423559452396478597/4425000000000000000 : ℝ)*(X 0 2+X 1 2)+(228360859973/132750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (4423559452396478597/4425000000000000000 : ℝ)) (alpha := (228360859973/132750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-201575977/1000000000 : ℝ)*X 0 0+(268775487/500000000 : ℝ)*X 0 1+(2687754859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((331028797/625000000 : ℝ)*X 1 0+(-1061547953/5000000000 : ℝ)*X 1 1+(215020393/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296460443/10000000000 : ℝ)*X 2 0+(671938757/1250000000 : ℝ)*X 2 1+(-2123096009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4463952231/10000000000 : ℝ)*X 0 0+(4305570981/10000000000 : ℝ)*X 0 1+(4305571187/10000000000 : ℝ)*X 0 2+(4463952231/10000000000 : ℝ)*X 1 0+(4305570981/10000000000 : ℝ)*X 1 1+(4305571187/10000000000 : ℝ)*X 1 2+(4463952231/10000000000 : ℝ)*X 2 0+(4305570981/10000000000 : ℝ)*X 2 1+(4305571187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1133674489/5000000000 : ℝ)*X 0 0+(1056360817/2000000000 : ℝ)*X 0 1+(5281804133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362581751/10000000000 : ℝ)*X 1 0+(-1080058671/5000000000 : ℝ)*X 1 1+(528180403/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072516471/2000000000 : ℝ)*X 2 0+(2640902051/5000000000 : ℝ)*X 2 1+(-540029109/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249632301/10000000000 : ℝ)*X 0 0+(441271129/1000000000 : ℝ)*X 0 1+(275794373/625000000 : ℝ)*X 0 2+(4249632301/10000000000 : ℝ)*X 1 0+(441271129/1000000000 : ℝ)*X 1 1+(275794373/625000000 : ℝ)*X 1 2+(4249632301/10000000000 : ℝ)*X 2 0+(441271129/1000000000 : ℝ)*X 2 1+(275794373/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2214676679/10000000000 : ℝ)*X 0 0+(260898557/500000000 : ℝ)*X 0 1+(2692560621/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289675293/10000000000 : ℝ)*X 1 0+(-1059615423/5000000000 : ℝ)*X 1 1+(2692560609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289675357/10000000000 : ℝ)*X 2 0+(5385121229/10000000000 : ℝ)*X 2 1+(-423846149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((224283097/500000000 : ℝ)*X 0 0+(4294575649/10000000000 : ℝ)*X 0 1+(536821971/1250000000 : ℝ)*X 0 2+(224283097/500000000 : ℝ)*X 1 0+(4294575649/10000000000 : ℝ)*X 1 1+(536821971/1250000000 : ℝ)*X 1 2+(224283097/500000000 : ℝ)*X 2 0+(4294575649/10000000000 : ℝ)*X 2 1+(536821971/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1034358861/5000000000 : ℝ)*X 0 0+(5438103827/10000000000 : ℝ)*X 0 1+(1318435597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073653779/2000000000 : ℝ)*X 1 0+(-432648971/2000000000 : ℝ)*X 1 1+(1318435563/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671033619/1250000000 : ℝ)*X 2 0+(5273742201/10000000000 : ℝ)*X 2 1+(-2163244847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((846192467/2000000000 : ℝ)*X 0 0+(4421923193/10000000000 : ℝ)*X 0 1+(4421923067/10000000000 : ℝ)*X 0 2+(846192467/2000000000 : ℝ)*X 1 0+(4421923193/10000000000 : ℝ)*X 1 1+(4421923067/10000000000 : ℝ)*X 1 2+(846192467/2000000000 : ℝ)*X 2 0+(4421923193/10000000000 : ℝ)*X 2 1+(4421923067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62239/100000 : ℝ) ≤ (-6884877151832885551922264101981/11062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129099563/100000000000000 : ℝ)*(upper1) + (571969039/100000000000000 : ℝ)*(upper4) + (122965591/100000000000000 : ℝ)*(upper5) + (198319477120091/5000000000000 : ℝ)*(major0) + (198319477120091/5000000000000 : ℝ)*(major1) + (198319477120091/5000000000000 : ℝ)*(major2) + (27924923949/100000000000000 : ℝ)*(sp1) + (5236161431/100000000000000 : ℝ)*(sp3) + (5318856602883817/100000000000000 : ℝ)*(sp4) + (1063772239601393/20000000000000 : ℝ)*(sp5) + (332423309057819/6250000000000 : ℝ)*(sp6) + (1317315059129591/50000000000000 : ℝ)*(sp7) + (32520047097/100000000000000 : ℝ)*(sp8) + (11617800581/10000000000000 : ℝ)*(sp14) + (658658838605153/25000000000000 : ℝ)*(f.failure) + (2659444561465457/50000000000000 : ℝ)*(f.sum) + (2939332532513/1327500000000000000000000000 : ℝ)*base66 + (83542873582876981/66375000000000000000000000000000 : ℝ)*base67 + (549469268826376981/66375000000000000000000000000000 : ℝ)*base69 + (375538838359126981/66375000000000000000000000000000 : ℝ)*base71 + (39904237886041/2655000000000000000000000000 : ℝ)*base74 + (636565366333876981/66375000000000000000000000000000 : ℝ)*base75 + (159596700951748019/66375000000000000000000000000000 : ℝ)*base78 + (23479605127498019/66375000000000000000000000000000 : ℝ)*base80 + (17520425632801/2655000000000000000000000000 : ℝ)*base82 + (17808497/2500000000000000000000 : ℝ)*base90 + (17808497/2500000000000000000000 : ℝ)*base92 + (17808497/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29671/50000 : ℝ) ≤ (4376621394948623292014820217877/7375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1188943/3125000000000 : ℝ)*(lower0) + (22999127/100000000000000 : ℝ)*(lower1) + (27817083/20000000000000 : ℝ)*(lower4) + (403142517933241/10000000000000 : ℝ)*(major0) + (403142517933241/10000000000000 : ℝ)*(major1) + (403142517933241/10000000000000 : ℝ)*(major2) + (2146092310333/40000000000 : ℝ)*(sp0) + (335326674606377/6250000000000 : ℝ)*(sp1) + (2682611377880763/50000000000000 : ℝ)*(sp2) + (33472878383477/1250000000000 : ℝ)*(sp3) + (7586889419/100000000000000 : ℝ)*(sp5) + (464993197/4000000000000 : ℝ)*(sp6) + (1091939253/25000000000000 : ℝ)*(sp7) + (3604758951/100000000000000 : ℝ)*(sp12) + (669458659608793/25000000000000 : ℝ)*(f.failure) + (5365234380591451/100000000000000 : ℝ)*(f.sum) + (1922217403861/1327500000000000000000000000 : ℝ)*base65 + (773317874538421369/132750000000000000000000000000000 : ℝ)*base68 + (464048867671369/132750000000000000000000000000000 : ℝ)*base70 + (1173156147045421369/132750000000000000000000000000000 : ℝ)*base72 + (15435097586639/1327500000000000000000000000 : ℝ)*base74 + (281540362771828631/132750000000000000000000000000000 : ℝ)*base75 + (1176640656660421369/132750000000000000000000000000000 : ℝ)*base78 + (8431022541286828631/132750000000000000000000000000000 : ℝ)*base79 + (6040242473581/1327500000000000000000000000 : ℝ)*base81 + (2266857/2500000000000000000000 : ℝ)*base90 + (2266857/2500000000000000000000 : ℝ)*base92 + (2266857/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3199/4000 : ℝ) ≤ (1179667603833357864510922463589/1475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5552529/50000000000000 : ℝ)*(upper0) + (463497/5000000000000 : ℝ)*(lower1) + (73304829/100000000000000 : ℝ)*(lower3) + (42332617/100000000000000 : ℝ)*(upper4) + (89975890897821/2000000000000 : ℝ)*(major0) + (89975890897821/2000000000000 : ℝ)*(major1) + (89975890897821/2000000000000 : ℝ)*(major2) + (51685046067/100000000000000 : ℝ)*(sp1) + (57647514451/100000000000000 : ℝ)*(sp2) + (5453632201/20000000000000 : ℝ)*(sp3) + (5982649778963977/100000000000000 : ℝ)*(sp8) + (598259809391791/10000000000000 : ℝ)*(sp9) + (2991296065724763/50000000000000 : ℝ)*(sp10) + (1494126443884109/50000000000000 : ℝ)*(sp11) + (1494140077964611/50000000000000 : ℝ)*(f.failure) + (5982649778963977/100000000000000 : ℝ)*(f.sum) + (10877854817/1475000000000000000000000 : ℝ)*base66 + (17285227357862379/2950000000000000000000000000000 : ℝ)*base67 + (20319123511162379/2950000000000000000000000000000 : ℝ)*base69 + (2370936187962379/2950000000000000000000000000000 : ℝ)*base71 + (157317597527/59000000000000000000000000 : ℝ)*base74 + (4590245009212379/2950000000000000000000000000000 : ℝ)*base75 + (8007700133012379/2950000000000000000000000000000 : ℝ)*base77 + (3494617714362379/2950000000000000000000000000000 : ℝ)*base79 + (385922999111/29500000000000000000000000 : ℝ)*base82 + (63437939/5000000000000000000000 : ℝ)*base90 + (63437939/5000000000000000000000 : ℝ)*base92 + (63437939/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83247/100000 : ℝ) ≤ (-184177977585920648334120056768303/221250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2520101/4000000000000 : ℝ)*(upper1) + (22554219/100000000000000 : ℝ)*(upper3) + (71548839/100000000000000 : ℝ)*(upper5) + (4534059627080767/100000000000000 : ℝ)*(major0) + (4534059627080767/100000000000000 : ℝ)*(major1) + (4534059627080767/100000000000000 : ℝ)*(major2) + (814153421/5000000000000 : ℝ)*(sp4) + (6874823279/10000000000000 : ℝ)*(sp5) + (64869936769/50000000000000 : ℝ)*(sp6) + (122288283683/100000000000000 : ℝ)*(sp7) + (380259151545133/6250000000000 : ℝ)*(sp12) + (6084093959557757/100000000000000 : ℝ)*(sp13) + (608403296791701/10000000000000 : ℝ)*(sp14) + (3011582352638841/100000000000000 : ℝ)*(sp15) + (752926160230631/25000000000000 : ℝ)*(f.failure) + (1521040676947637/25000000000000 : ℝ)*(f.sum) + (7341604382867/3318750000000000000000000000 : ℝ)*base66 + (6596833545975868303/1327500000000000000000000000000000 : ℝ)*base68 + (19405520830634131697/1327500000000000000000000000000000 : ℝ)*base69 + (3950173145235868303/1327500000000000000000000000000000 : ℝ)*base72 + (12578555923309/6637500000000000000000000000 : ℝ)*base74 + (56983792207784131697/1327500000000000000000000000000000 : ℝ)*base75 + (8852646183623368303/1327500000000000000000000000000000 : ℝ)*base78 + (9110471164050868303/1327500000000000000000000000000000 : ℝ)*base80 + (456822382140007/13275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9487081/2500000000000000000000 : ℝ)*base89 + (9487081/2500000000000000000000 : ℝ)*base91 + (9487081/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1197_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (3199/4000 : ℝ) ≤ X j i ∧ X j i ≤ (83247/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1197_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1197_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (3199/4000 : ℝ) ≤ X j i ∧ X j i ≤ (83247/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1197_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1197_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (3199/4000 : ℝ) ≤ X j i ∧ X j i ≤ (83247/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

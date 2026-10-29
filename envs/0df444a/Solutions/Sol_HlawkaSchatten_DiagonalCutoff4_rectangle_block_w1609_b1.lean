-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:02.975869+00:00
-- url     : https://prove2.me/submissions/1ecf2afb-e8bf-42ec-9b3c-f66d38122c26

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
theorem support_rectangle_w1609_s3_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85334163/500000000 : ℝ)*x 0 + (5460343727/10000000000 : ℝ)*x 1 + (518019827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85334163/500000000 : ℝ)^4755 ≤ (10505379196381/100000000000000 : ℝ)^3731 := by
    have hnat : (85334163 : ℕ)^4755*100000000000000^3731 ≤ 10505379196381^3731*500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85334163 500000000 10505379196381 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460343727/10000000000 : ℝ)^4755 ≤ (11562136969991/25000000000000 : ℝ)^3731 := by
    have hnat : (5460343727 : ℕ)^4755*25000000000000^3731 ≤ 11562136969991^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460343727 10000000000 11562136969991 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518019827/1000000000 : ℝ)^4755 ≤ (43246072910947/100000000000000 : ℝ)^3731 := by
    have hnat : (518019827 : ℕ)^4755*100000000000000^3731 ≤ 43246072910947^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518019827 1000000000 43246072910947 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85334163/500000000 : ℝ), (5460343727/10000000000 : ℝ), (518019827/1000000000 : ℝ)] ![(10505379196381/100000000000000 : ℝ), (11562136969991/25000000000000 : ℝ), (43246072910947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85334163/500000000 : ℝ)|^4755 ≤ (10505379196381/100000000000000 : ℝ)^3731
        have hw : |(-85334163/500000000 : ℝ)|=(85334163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460343727/10000000000 : ℝ)|^4755 ≤ (11562136969991/25000000000000 : ℝ)^3731
        have hw : |(5460343727/10000000000 : ℝ)|=(5460343727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518019827/1000000000 : ℝ)|^4755 ≤ (43246072910947/100000000000000 : ℝ)^3731
        have hw : |(518019827/1000000000 : ℝ)|=(518019827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353862341/10000000000 : ℝ)*x 0 + (-1851163523/10000000000 : ℝ)*x 1 + (5180197661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353862341/10000000000 : ℝ)^4755 ≤ (11275555708697/25000000000000 : ℝ)^3731 := by
    have hnat : (5353862341 : ℕ)^4755*25000000000000^3731 ≤ 11275555708697^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353862341 10000000000 11275555708697 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1851163523/10000000000 : ℝ)^4755 ≤ (11651710722551/100000000000000 : ℝ)^3731 := by
    have hnat : (1851163523 : ℕ)^4755*100000000000000^3731 ≤ 11651710722551^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851163523 10000000000 11651710722551 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180197661/10000000000 : ℝ)^4755 ≤ (43246066431427/100000000000000 : ℝ)^3731 := by
    have hnat : (5180197661 : ℕ)^4755*100000000000000^3731 ≤ 43246066431427^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180197661 10000000000 43246066431427 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353862341/10000000000 : ℝ), (-1851163523/10000000000 : ℝ), (5180197661/10000000000 : ℝ)] ![(11275555708697/25000000000000 : ℝ), (11651710722551/100000000000000 : ℝ), (43246066431427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353862341/10000000000 : ℝ)|^4755 ≤ (11275555708697/25000000000000 : ℝ)^3731
        have hw : |(5353862341/10000000000 : ℝ)|=(5353862341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1851163523/10000000000 : ℝ)|^4755 ≤ (11651710722551/100000000000000 : ℝ)^3731
        have hw : |(-1851163523/10000000000 : ℝ)|=(1851163523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180197661/10000000000 : ℝ)|^4755 ≤ (43246066431427/100000000000000 : ℝ)^3731
        have hw : |(5180197661/10000000000 : ℝ)|=(5180197661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353862251/10000000000 : ℝ)*x 0 + (5180197697/10000000000 : ℝ)*x 1 + (-370232719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353862251/10000000000 : ℝ)^4755 ≤ (22551110934259/50000000000000 : ℝ)^3731 := by
    have hnat : (5353862251 : ℕ)^4755*50000000000000^3731 ≤ 22551110934259^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353862251 10000000000 22551110934259 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180197697/10000000000 : ℝ)^4755 ≤ (43246066814453/100000000000000 : ℝ)^3731 := by
    have hnat : (5180197697 : ℕ)^4755*100000000000000^3731 ≤ 43246066814453^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180197697 10000000000 43246066814453 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370232719/2000000000 : ℝ)^4755 ≤ (5825855650059/50000000000000 : ℝ)^3731 := by
    have hnat : (370232719 : ℕ)^4755*50000000000000^3731 ≤ 5825855650059^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370232719 2000000000 5825855650059 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353862251/10000000000 : ℝ), (5180197697/10000000000 : ℝ), (-370232719/2000000000 : ℝ)] ![(22551110934259/50000000000000 : ℝ), (43246066814453/100000000000000 : ℝ), (5825855650059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353862251/10000000000 : ℝ)|^4755 ≤ (22551110934259/50000000000000 : ℝ)^3731
        have hw : |(5353862251/10000000000 : ℝ)|=(5353862251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180197697/10000000000 : ℝ)|^4755 ≤ (43246066814453/100000000000000 : ℝ)^3731
        have hw : |(5180197697/10000000000 : ℝ)|=(5180197697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370232719/2000000000 : ℝ)|^4755 ≤ (5825855650059/50000000000000 : ℝ)^3731
        have hw : |(-370232719/2000000000 : ℝ)|=(370232719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2106646861/5000000000 : ℝ)*x 0 + (3880355053/10000000000 : ℝ)*x 1 + (1141965737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106646861/5000000000 : ℝ)^4755 ≤ (1038595584481/3125000000000 : ℝ)^3731 := by
    have hnat : (2106646861 : ℕ)^4755*3125000000000^3731 ≤ 1038595584481^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106646861 5000000000 1038595584481 3125000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3880355053/10000000000 : ℝ)^4755 ≤ (5985001368589/20000000000000 : ℝ)^3731 := by
    have hnat : (3880355053 : ℕ)^4755*20000000000000^3731 ≤ 5985001368589^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880355053 10000000000 5985001368589 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141965737/2500000000 : ℝ)^4755 ≤ (36839934441053/100000000000000 : ℝ)^3731 := by
    have hnat : (1141965737 : ℕ)^4755*100000000000000^3731 ≤ 36839934441053^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141965737 2500000000 36839934441053 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106646861/5000000000 : ℝ), (3880355053/10000000000 : ℝ), (1141965737/2500000000 : ℝ)] ![(1038595584481/3125000000000 : ℝ), (5985001368589/20000000000000 : ℝ), (36839934441053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106646861/5000000000 : ℝ)|^4755 ≤ (1038595584481/3125000000000 : ℝ)^3731
        have hw : |(2106646861/5000000000 : ℝ)|=(2106646861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3880355053/10000000000 : ℝ)|^4755 ≤ (5985001368589/20000000000000 : ℝ)^3731
        have hw : |(3880355053/10000000000 : ℝ)|=(3880355053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141965737/2500000000 : ℝ)|^4755 ≤ (36839934441053/100000000000000 : ℝ)^3731
        have hw : |(1141965737/2500000000 : ℝ)|=(1141965737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1706754639/10000000000 : ℝ)*x 0 + (207291487/400000000 : ℝ)*x 1 + (5458232699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706754639/10000000000 : ℝ)^4755 ≤ (10505939156411/100000000000000 : ℝ)^3731 := by
    have hnat : (1706754639 : ℕ)^4755*100000000000000^3731 ≤ 10505939156411^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706754639 10000000000 10505939156411 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207291487/400000000 : ℝ)^4755 ≤ (10817074816977/25000000000000 : ℝ)^3731 := by
    have hnat : (207291487 : ℕ)^4755*25000000000000^3731 ≤ 10817074816977^3731*400000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207291487 400000000 10817074816977 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458232699/10000000000 : ℝ)^4755 ≤ (46225761552151/100000000000000 : ℝ)^3731 := by
    have hnat : (5458232699 : ℕ)^4755*100000000000000^3731 ≤ 46225761552151^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458232699 10000000000 46225761552151 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1706754639/10000000000 : ℝ), (207291487/400000000 : ℝ), (5458232699/10000000000 : ℝ)] ![(10505939156411/100000000000000 : ℝ), (10817074816977/25000000000000 : ℝ), (46225761552151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1706754639/10000000000 : ℝ)|^4755 ≤ (10505939156411/100000000000000 : ℝ)^3731
        have hw : |(-1706754639/10000000000 : ℝ)|=(1706754639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207291487/400000000 : ℝ)|^4755 ≤ (10817074816977/25000000000000 : ℝ)^3731
        have hw : |(207291487/400000000 : ℝ)|=(207291487/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458232699/10000000000 : ℝ)|^4755 ≤ (46225761552151/100000000000000 : ℝ)^3731
        have hw : |(5458232699/10000000000 : ℝ)|=(5458232699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105589507/200000000 : ℝ)*x 0 + (-786564037/5000000000 : ℝ)*x 1 + (2729116327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105589507/200000000 : ℝ)^4755 ≤ (886102142793/2000000000000 : ℝ)^3731 := by
    have hnat : (105589507 : ℕ)^4755*2000000000000^3731 ≤ 886102142793^3731*200000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105589507 200000000 886102142793 2000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (786564037/5000000000 : ℝ)^4755 ≤ (4734565885797/50000000000000 : ℝ)^3731 := by
    have hnat : (786564037 : ℕ)^4755*50000000000000^3731 ≤ 4734565885797^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786564037 5000000000 4734565885797 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729116327/5000000000 : ℝ)^4755 ≤ (46225761066449/100000000000000 : ℝ)^3731 := by
    have hnat : (2729116327 : ℕ)^4755*100000000000000^3731 ≤ 46225761066449^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729116327 5000000000 46225761066449 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105589507/200000000 : ℝ), (-786564037/5000000000 : ℝ), (2729116327/5000000000 : ℝ)] ![(886102142793/2000000000000 : ℝ), (4734565885797/50000000000000 : ℝ), (46225761066449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105589507/200000000 : ℝ)|^4755 ≤ (886102142793/2000000000000 : ℝ)^3731
        have hw : |(105589507/200000000 : ℝ)|=(105589507/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-786564037/5000000000 : ℝ)|^4755 ≤ (4734565885797/50000000000000 : ℝ)^3731
        have hw : |(-786564037/5000000000 : ℝ)|=(786564037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729116327/5000000000 : ℝ)|^4755 ≤ (46225761066449/100000000000000 : ℝ)^3731
        have hw : |(2729116327/5000000000 : ℝ)|=(2729116327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279474989/10000000000 : ℝ)*x 0 + (5458232953/10000000000 : ℝ)*x 1 + (-786564079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279474989/10000000000 : ℝ)^4755 ≤ (1384534477459/3125000000000 : ℝ)^3731 := by
    have hnat : (5279474989 : ℕ)^4755*3125000000000^3731 ≤ 1384534477459^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279474989 10000000000 1384534477459 3125000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458232953/10000000000 : ℝ)^4755 ≤ (11556441073417/25000000000000 : ℝ)^3731 := by
    have hnat : (5458232953 : ℕ)^4755*25000000000000^3731 ≤ 11556441073417^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458232953 10000000000 11556441073417 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (786564079/5000000000 : ℝ)^4755 ≤ (4734566207993/50000000000000 : ℝ)^3731 := by
    have hnat : (786564079 : ℕ)^4755*50000000000000^3731 ≤ 4734566207993^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786564079 5000000000 4734566207993 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279474989/10000000000 : ℝ), (5458232953/10000000000 : ℝ), (-786564079/5000000000 : ℝ)] ![(1384534477459/3125000000000 : ℝ), (11556441073417/25000000000000 : ℝ), (4734566207993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279474989/10000000000 : ℝ)|^4755 ≤ (1384534477459/3125000000000 : ℝ)^3731
        have hw : |(5279474989/10000000000 : ℝ)|=(5279474989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458232953/10000000000 : ℝ)|^4755 ≤ (11556441073417/25000000000000 : ℝ)^3731
        have hw : |(5458232953/10000000000 : ℝ)|=(5458232953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-786564079/5000000000 : ℝ)|^4755 ≤ (4734566207993/50000000000000 : ℝ)^3731
        have hw : |(-786564079/5000000000 : ℝ)|=(786564079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s3_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105336711/250000000 : ℝ)*x 0 + (4562736423/10000000000 : ℝ)*x 1 + (3885535817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105336711/250000000 : ℝ)^4755 ≤ (16618407585423/50000000000000 : ℝ)^3731 := by
    have hnat : (105336711 : ℕ)^4755*50000000000000^3731 ≤ 16618407585423^3731*250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105336711 250000000 16618407585423 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562736423/10000000000 : ℝ)^4755 ≤ (183936247059/500000000000 : ℝ)^3731 := by
    have hnat : (4562736423 : ℕ)^4755*500000000000^3731 ≤ 183936247059^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562736423 10000000000 183936247059 500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3885535817/10000000000 : ℝ)^4755 ≤ (29975935404723/100000000000000 : ℝ)^3731 := by
    have hnat : (3885535817 : ℕ)^4755*100000000000000^3731 ≤ 29975935404723^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885535817 10000000000 29975935404723 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105336711/250000000 : ℝ), (4562736423/10000000000 : ℝ), (3885535817/10000000000 : ℝ)] ![(16618407585423/50000000000000 : ℝ), (183936247059/500000000000 : ℝ), (29975935404723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105336711/250000000 : ℝ)|^4755 ≤ (16618407585423/50000000000000 : ℝ)^3731
        have hw : |(105336711/250000000 : ℝ)|=(105336711/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562736423/10000000000 : ℝ)|^4755 ≤ (183936247059/500000000000 : ℝ)^3731
        have hw : |(4562736423/10000000000 : ℝ)|=(4562736423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3885535817/10000000000 : ℝ)|^4755 ≤ (29975935404723/100000000000000 : ℝ)^3731
        have hw : |(3885535817/10000000000 : ℝ)|=(3885535817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4089/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8249/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8249/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8249/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8249/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8249/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8249/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10289/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (20933830117937/800000000000000000 : ℝ) := by
    have hpowers : (10289/100000 : ℝ)^4751 ≤ (20933830117937/800000000000000000 : ℝ)^1024 := by
      have hnat : (10289 : ℕ)^4751*800000000000000000^1024 ≤ 20933830117937^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10289 100000 20933830117937 800000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10289/100000 : ℝ)) (X := (20933830117937/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8249/50000 : ℝ) ^ (4751/1024 : ℝ) ≤ (23396793953347009/100000000000000000000 : ℝ) := by
    have hpowers : (8249/50000 : ℝ)^4751 ≤ (23396793953347009/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8249 : ℕ)^4751*100000000000000000000^1024 ≤ 23396793953347009^1024*50000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8249 50000 23396793953347009 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8249/50000 : ℝ)) (X := (23396793953347009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (400020933830117937/400000000000000000 : ℝ) ≤ (10000112796264077/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (400020933830117937/400000000000000000 : ℝ)^1024 ≤ (10000112796264077/10000000000000000 : ℝ)^4751 := by
      have hnat : (400020933830117937 : ℕ)^1024*10000000000000000^4751 ≤ 10000112796264077^4751*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400020933830117937 400000000000000000 10000112796264077 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112796264077/10000000000000000 : ℝ)) (X := (400020933830117937/400000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013006761359044567/50000000000000000000 : ℝ) ≤ (10000560621547597/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50013006761359044567/50000000000000000000 : ℝ)^1024 ≤ (10000560621547597/10000000000000000 : ℝ)^4751 := by
      have hnat : (50013006761359044567 : ℕ)^1024*10000000000000000^4751 ≤ 10000560621547597^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013006761359044567 50000000000000000000 10000560621547597 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000560621547597/10000000000000000 : ℝ)) (X := (50013006761359044567/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023396793953347009/50000000000000000000 : ℝ) ≤ (10001008446831117/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50023396793953347009/50000000000000000000 : ℝ)^1024 ≤ (10001008446831117/10000000000000000 : ℝ)^4751 := by
      have hnat : (50023396793953347009 : ℕ)^1024*10000000000000000^4751 ≤ 10001008446831117^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023396793953347009 50000000000000000000 10001008446831117 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001008446831117/10000000000000000 : ℝ)) (X := (50023396793953347009/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20933830117937/800000000000000000 : ℝ) ≤ ((62081485003319379533/62090000000000000000 : ℝ)+2*(1399454011/1940312500000 : ℝ)*(10289/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (62081485003319379533/62090000000000000000 : ℝ)+2*(1399454011/1940312500000 : ℝ)*(10289/100000 : ℝ)=(10000112796264077/10000000000000000 : ℝ) by norm_num, show 1+2*(20933830117937/800000000000000000 : ℝ)=(400020933830117937/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23396793953347009/100000000000000000000 : ℝ)+(20933830117937/800000000000000000 : ℝ) ≤ ((62081485003319379533/62090000000000000000 : ℝ)+(1399454011/1940312500000 : ℝ)*((8249/50000 : ℝ)+(10289/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (62081485003319379533/62090000000000000000 : ℝ)+(1399454011/1940312500000 : ℝ)*((8249/50000 : ℝ)+(10289/100000 : ℝ))=(10000560621547597/10000000000000000 : ℝ) by norm_num, show 1+(23396793953347009/100000000000000000000 : ℝ)+(20933830117937/800000000000000000 : ℝ)=(50013006761359044567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23396793953347009/100000000000000000000 : ℝ) ≤ ((62081485003319379533/62090000000000000000 : ℝ)+2*(1399454011/1940312500000 : ℝ)*(8249/50000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (62081485003319379533/62090000000000000000 : ℝ)+2*(1399454011/1940312500000 : ℝ)*(8249/50000 : ℝ)=(10001008446831117/10000000000000000 : ℝ) by norm_num, show 1+2*(23396793953347009/100000000000000000000 : ℝ)=(50023396793953347009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62081485003319379533/62090000000000000000 : ℝ)*(X 1 0+X 2 0)+(1399454011/1940312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10289/100000 : ℝ)) (hi := (8249/50000 : ℝ)) (c := (62081485003319379533/62090000000000000000 : ℝ)) (alpha := (1399454011/1940312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62081485003319379533/62090000000000000000 : ℝ)*(X 0 1+X 2 1)+(1399454011/1940312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10289/100000 : ℝ)) (hi := (8249/50000 : ℝ)) (c := (62081485003319379533/62090000000000000000 : ℝ)) (alpha := (1399454011/1940312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62081485003319379533/62090000000000000000 : ℝ)*(X 0 2+X 1 2)+(1399454011/1940312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10289/100000 : ℝ)) (hi := (8249/50000 : ℝ)) (c := (62081485003319379533/62090000000000000000 : ℝ)) (alpha := (1399454011/1940312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85334163/500000000 : ℝ)*X 0 0+(5460343727/10000000000 : ℝ)*X 0 1+(518019827/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353862341/10000000000 : ℝ)*X 1 0+(-1851163523/10000000000 : ℝ)*X 1 1+(5180197661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353862251/10000000000 : ℝ)*X 2 0+(5180197697/10000000000 : ℝ)*X 2 1+(-370232719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2106646861/5000000000 : ℝ)*X 0 0+(3880355053/10000000000 : ℝ)*X 0 1+(1141965737/2500000000 : ℝ)*X 0 2+(2106646861/5000000000 : ℝ)*X 1 0+(3880355053/10000000000 : ℝ)*X 1 1+(1141965737/2500000000 : ℝ)*X 1 2+(2106646861/5000000000 : ℝ)*X 2 0+(3880355053/10000000000 : ℝ)*X 2 1+(1141965737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1706754639/10000000000 : ℝ)*X 0 0+(207291487/400000000 : ℝ)*X 0 1+(5458232699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105589507/200000000 : ℝ)*X 1 0+(-786564037/5000000000 : ℝ)*X 1 1+(2729116327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279474989/10000000000 : ℝ)*X 2 0+(5458232953/10000000000 : ℝ)*X 2 1+(-786564079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105336711/250000000 : ℝ)*X 0 0+(4562736423/10000000000 : ℝ)*X 0 1+(3885535817/10000000000 : ℝ)*X 0 2+(105336711/250000000 : ℝ)*X 1 0+(4562736423/10000000000 : ℝ)*X 1 1+(3885535817/10000000000 : ℝ)*X 1 2+(105336711/250000000 : ℝ)*X 2 0+(4562736423/10000000000 : ℝ)*X 2 1+(3885535817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8284169098762590594962824323/1552250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (894639273/100000000000000 : ℝ)*(base19) + (831181663/100000000000000 : ℝ)*(base23) + (1848117/100000000000000 : ℝ)*(lower2) + (153883059/100000000000000 : ℝ)*(upper3) + (88025129/100000000000000 : ℝ)*(upper5) + (2512057237785251/100000000000000 : ℝ)*(major0) + (2512057237785251/100000000000000 : ℝ)*(major1) + (628014309446313/25000000000000 : ℝ)*(major2) + (89239451418989/2500000000000 : ℝ)*(sp0) + (892394829383773/25000000000000 : ℝ)*(sp1) + (1784789690496351/50000000000000 : ℝ)*(sp2) + (1454531190063439/100000000000000 : ℝ)*(sp3) + (538853701/25000000000000 : ℝ)*(sp4) + (1447718377/50000000000000 : ℝ)*(sp7) + (1454534085500193/100000000000000 : ℝ)*(f.failure) + (892395053043591/25000000000000 : ℝ)*(f.sum) + (2679815832699/3104500000000000000000000000 : ℝ)*base65 + (21452726791938332217/6209000000000000000000000000000000 : ℝ)*base68 + (4451980324395988171/1552250000000000000000000000000000 : ℝ)*base70 + (62597454213687332217/6209000000000000000000000000000000 : ℝ)*base72 + (20398967582619/6209000000000000000000000000 : ℝ)*base73 + (7935823240081988171/1552250000000000000000000000000000 : ℝ)*base76 + (3750646826358476031/887000000000000000000000000000000 : ℝ)*base78 + (13277416736479476031/887000000000000000000000000000000 : ℝ)*base80 + (5931875214949/1552250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (19924001/2000000000000000000000 : ℝ)*base89 + (19924001/2000000000000000000000 : ℝ)*base91 + (75999/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71568073305574782149540973/11087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308877883/20000000000000 : ℝ)*(base19) + (719593117/50000000000000 : ℝ)*(base23) + (59243171/100000000000000 : ℝ)*(upper2) + (56248701/25000000000000 : ℝ)*(upper3) + (42992671/50000000000000 : ℝ)*(upper5) + (63757082786089/2500000000000 : ℝ)*(major0) + (63757082786089/2500000000000 : ℝ)*(major1) + (63757082786089/2500000000000 : ℝ)*(major2) + (8274559059/50000000000000 : ℝ)*(sp1) + (18705039539/100000000000000 : ℝ)*(sp2) + (1811949309956939/50000000000000 : ℝ)*(sp4) + (1811940263203173/50000000000000 : ℝ)*(sp5) + (452984809461013/12500000000000 : ℝ)*(sp6) + (738333893905899/50000000000000 : ℝ)*(sp7) + (738333893905899/50000000000000 : ℝ)*(f.failure) + (1811949309956939/50000000000000 : ℝ)*(f.sum) + (1990140780933/443500000000000000000000000 : ℝ)*base66 + (132979051902740509/22175000000000000000000000000000 : ℝ)*base68 + (62095167235440509/22175000000000000000000000000000 : ℝ)*base70 + (120374499260190509/22175000000000000000000000000000 : ℝ)*base72 + (694305578503/221750000000000000000000000 : ℝ)*base74 + (106951811878440509/22175000000000000000000000000000 : ℝ)*base76 + (3011462619584491/22175000000000000000000000000000 : ℝ)*base77 + (60814523231884491/22175000000000000000000000000000 : ℝ)*base79 + (652327414003/887000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (9995243/1000000000000000000000 : ℝ)*base89 + (9995243/1000000000000000000000 : ℝ)*base91 + (9995243/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1609_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1609_s4_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1706801937/10000000000 : ℝ)*x 0 + (1364936873/2500000000 : ℝ)*x 1 + (2590357833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706801937/10000000000 : ℝ)^4755 ≤ (656644387957/6250000000000 : ℝ)^3731 := by
    have hnat : (1706801937 : ℕ)^4755*6250000000000^3731 ≤ 656644387957^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706801937 10000000000 656644387957 6250000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364936873/2500000000 : ℝ)^4755 ≤ (11560527976237/25000000000000 : ℝ)^3731 := by
    have hnat : (1364936873 : ℕ)^4755*25000000000000^3731 ≤ 11560527976237^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364936873 2500000000 11560527976237 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590357833/5000000000 : ℝ)^4755 ≤ (43251577876239/100000000000000 : ℝ)^3731 := by
    have hnat : (2590357833 : ℕ)^4755*100000000000000^3731 ≤ 43251577876239^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590357833 5000000000 43251577876239 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1706801937/10000000000 : ℝ), (1364936873/2500000000 : ℝ), (2590357833/5000000000 : ℝ)] ![(656644387957/6250000000000 : ℝ), (11560527976237/25000000000000 : ℝ), (43251577876239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1706801937/10000000000 : ℝ)|^4755 ≤ (656644387957/6250000000000 : ℝ)^3731
        have hw : |(-1706801937/10000000000 : ℝ)|=(1706801937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364936873/2500000000 : ℝ)|^4755 ≤ (11560527976237/25000000000000 : ℝ)^3731
        have hw : |(1364936873/2500000000 : ℝ)|=(1364936873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590357833/5000000000 : ℝ)|^4755 ≤ (43251577876239/100000000000000 : ℝ)^3731
        have hw : |(2590357833/5000000000 : ℝ)|=(2590357833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353702847/10000000000 : ℝ)*x 0 + (-925344941/5000000000 : ℝ)*x 1 + (647589461/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353702847/10000000000 : ℝ)^4755 ≤ (9020102092183/20000000000000 : ℝ)^3731 := by
    have hnat : (5353702847 : ℕ)^4755*20000000000000^3731 ≤ 9020102092183^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353702847 10000000000 9020102092183 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925344941/5000000000 : ℝ)^4755 ≤ (2329582283401/20000000000000 : ℝ)^3731 := by
    have hnat : (925344941 : ℕ)^4755*20000000000000^3731 ≤ 2329582283401^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925344941 5000000000 2329582283401 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647589461/1250000000 : ℝ)^4755 ≤ (43251578110317/100000000000000 : ℝ)^3731 := by
    have hnat : (647589461 : ℕ)^4755*100000000000000^3731 ≤ 43251578110317^3731*1250000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647589461 1250000000 43251578110317 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353702847/10000000000 : ℝ), (-925344941/5000000000 : ℝ), (647589461/1250000000 : ℝ)] ![(9020102092183/20000000000000 : ℝ), (2329582283401/20000000000000 : ℝ), (43251578110317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353702847/10000000000 : ℝ)|^4755 ≤ (9020102092183/20000000000000 : ℝ)^3731
        have hw : |(5353702847/10000000000 : ℝ)|=(5353702847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-925344941/5000000000 : ℝ)|^4755 ≤ (2329582283401/20000000000000 : ℝ)^3731
        have hw : |(-925344941/5000000000 : ℝ)|=(925344941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647589461/1250000000 : ℝ)|^4755 ≤ (43251578110317/100000000000000 : ℝ)^3731
        have hw : |(647589461/1250000000 : ℝ)|=(647589461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353702823/10000000000 : ℝ)*x 0 + (5180715731/10000000000 : ℝ)*x 1 + (-1850689857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353702823/10000000000 : ℝ)^4755 ≤ (9020102040649/20000000000000 : ℝ)^3731 := by
    have hnat : (5353702823 : ℕ)^4755*20000000000000^3731 ≤ 9020102040649^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353702823 10000000000 9020102040649 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180715731/10000000000 : ℝ)^4755 ≤ (43251578567833/100000000000000 : ℝ)^3731 := by
    have hnat : (5180715731 : ℕ)^4755*100000000000000^3731 ≤ 43251578567833^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180715731 10000000000 43251578567833 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850689857/10000000000 : ℝ)^4755 ≤ (465916448659/4000000000000 : ℝ)^3731 := by
    have hnat : (1850689857 : ℕ)^4755*4000000000000^3731 ≤ 465916448659^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850689857 10000000000 465916448659 4000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353702823/10000000000 : ℝ), (5180715731/10000000000 : ℝ), (-1850689857/10000000000 : ℝ)] ![(9020102040649/20000000000000 : ℝ), (43251578567833/100000000000000 : ℝ), (465916448659/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353702823/10000000000 : ℝ)|^4755 ≤ (9020102040649/20000000000000 : ℝ)^3731
        have hw : |(5353702823/10000000000 : ℝ)|=(5353702823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180715731/10000000000 : ℝ)|^4755 ≤ (43251578567833/100000000000000 : ℝ)^3731
        have hw : |(5180715731/10000000000 : ℝ)|=(5180715731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1850689857/10000000000 : ℝ)|^4755 ≤ (465916448659/4000000000000 : ℝ)^3731
        have hw : |(-1850689857/10000000000 : ℝ)|=(1850689857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2106685659/5000000000 : ℝ)*x 0 + (3881713991/10000000000 : ℝ)*x 1 + (1141621873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106685659/5000000000 : ℝ)^4755 ≤ (33235838785681/100000000000000 : ℝ)^3731 := by
    have hnat : (2106685659 : ℕ)^4755*100000000000000^3731 ≤ 33235838785681^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106685659 5000000000 33235838785681 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3881713991/10000000000 : ℝ)^4755 ≤ (2993836383223/10000000000000 : ℝ)^3731 := by
    have hnat : (3881713991 : ℕ)^4755*10000000000000^3731 ≤ 2993836383223^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881713991 10000000000 2993836383223 10000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141621873/2500000000 : ℝ)^4755 ≤ (7365159471593/20000000000000 : ℝ)^3731 := by
    have hnat : (1141621873 : ℕ)^4755*20000000000000^3731 ≤ 7365159471593^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141621873 2500000000 7365159471593 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106685659/5000000000 : ℝ), (3881713991/10000000000 : ℝ), (1141621873/2500000000 : ℝ)] ![(33235838785681/100000000000000 : ℝ), (2993836383223/10000000000000 : ℝ), (7365159471593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106685659/5000000000 : ℝ)|^4755 ≤ (33235838785681/100000000000000 : ℝ)^3731
        have hw : |(2106685659/5000000000 : ℝ)|=(2106685659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3881713991/10000000000 : ℝ)|^4755 ≤ (2993836383223/10000000000000 : ℝ)^3731
        have hw : |(3881713991/10000000000 : ℝ)|=(3881713991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141621873/2500000000 : ℝ)|^4755 ≤ (7365159471593/20000000000000 : ℝ)^3731
        have hw : |(1141621873/2500000000 : ℝ)|=(1141621873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1706872363/10000000000 : ℝ)*x 0 + (5182788293/10000000000 : ℝ)*x 1 + (2728826543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706872363/10000000000 : ℝ)^4755 ≤ (2626715675417/25000000000000 : ℝ)^3731 := by
    have hnat : (1706872363 : ℕ)^4755*25000000000000^3731 ≤ 2626715675417^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706872363 10000000000 2626715675417 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182788293/10000000000 : ℝ)^4755 ≤ (10818407906747/25000000000000 : ℝ)^3731 := by
    have hnat : (5182788293 : ℕ)^4755*25000000000000^3731 ≤ 10818407906747^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182788293 10000000000 10818407906747 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728826543/5000000000 : ℝ)^4755 ≤ (23109752831183/50000000000000 : ℝ)^3731 := by
    have hnat : (2728826543 : ℕ)^4755*50000000000000^3731 ≤ 23109752831183^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728826543 5000000000 23109752831183 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1706872363/10000000000 : ℝ), (5182788293/10000000000 : ℝ), (2728826543/5000000000 : ℝ)] ![(2626715675417/25000000000000 : ℝ), (10818407906747/25000000000000 : ℝ), (23109752831183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1706872363/10000000000 : ℝ)|^4755 ≤ (2626715675417/25000000000000 : ℝ)^3731
        have hw : |(-1706872363/10000000000 : ℝ)|=(1706872363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182788293/10000000000 : ℝ)|^4755 ≤ (10818407906747/25000000000000 : ℝ)^3731
        have hw : |(5182788293/10000000000 : ℝ)|=(5182788293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728826543/5000000000 : ℝ)|^4755 ≤ (23109752831183/50000000000000 : ℝ)^3731
        have hw : |(2728826543/5000000000 : ℝ)|=(2728826543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639806173/5000000000 : ℝ)*x 0 + (-1573752469/10000000000 : ℝ)*x 1 + (2728826543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639806173/5000000000 : ℝ)^4755 ≤ (44306572342417/100000000000000 : ℝ)^3731 := by
    have hnat : (2639806173 : ℕ)^4755*100000000000000^3731 ≤ 44306572342417^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639806173 5000000000 44306572342417 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1573752469/10000000000 : ℝ)^4755 ≤ (9473921980123/100000000000000 : ℝ)^3731 := by
    have hnat : (1573752469 : ℕ)^4755*100000000000000^3731 ≤ 9473921980123^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573752469 10000000000 9473921980123 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728826543/5000000000 : ℝ)^4755 ≤ (23109752831183/50000000000000 : ℝ)^3731 := by
    have hnat : (2728826543 : ℕ)^4755*50000000000000^3731 ≤ 23109752831183^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728826543 5000000000 23109752831183 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639806173/5000000000 : ℝ), (-1573752469/10000000000 : ℝ), (2728826543/5000000000 : ℝ)] ![(44306572342417/100000000000000 : ℝ), (9473921980123/100000000000000 : ℝ), (23109752831183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639806173/5000000000 : ℝ)|^4755 ≤ (44306572342417/100000000000000 : ℝ)^3731
        have hw : |(2639806173/5000000000 : ℝ)|=(2639806173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1573752469/10000000000 : ℝ)|^4755 ≤ (9473921980123/100000000000000 : ℝ)^3731
        have hw : |(-1573752469/10000000000 : ℝ)|=(1573752469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728826543/5000000000 : ℝ)|^4755 ≤ (23109752831183/50000000000000 : ℝ)^3731
        have hw : |(2728826543/5000000000 : ℝ)|=(2728826543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279612347/10000000000 : ℝ)*x 0 + (1091530617/2000000000 : ℝ)*x 1 + (-393438117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279612347/10000000000 : ℝ)^4755 ≤ (5538321544139/12500000000000 : ℝ)^3731 := by
    have hnat : (5279612347 : ℕ)^4755*12500000000000^3731 ≤ 5538321544139^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279612347 10000000000 5538321544139 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091530617/2000000000 : ℝ)^4755 ≤ (46219505651573/100000000000000 : ℝ)^3731 := by
    have hnat : (1091530617 : ℕ)^4755*100000000000000^3731 ≤ 46219505651573^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091530617 2000000000 46219505651573 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393438117/2500000000 : ℝ)^4755 ≤ (9473921972451/100000000000000 : ℝ)^3731 := by
    have hnat : (393438117 : ℕ)^4755*100000000000000^3731 ≤ 9473921972451^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393438117 2500000000 9473921972451 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279612347/10000000000 : ℝ), (1091530617/2000000000 : ℝ), (-393438117/2500000000 : ℝ)] ![(5538321544139/12500000000000 : ℝ), (46219505651573/100000000000000 : ℝ), (9473921972451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279612347/10000000000 : ℝ)|^4755 ≤ (5538321544139/12500000000000 : ℝ)^3731
        have hw : |(5279612347/10000000000 : ℝ)|=(5279612347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091530617/2000000000 : ℝ)|^4755 ≤ (46219505651573/100000000000000 : ℝ)^3731
        have hw : |(1091530617/2000000000 : ℝ)|=(1091530617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393438117/2500000000 : ℝ)|^4755 ≤ (9473921972451/100000000000000 : ℝ)^3731
        have hw : |(-393438117/2500000000 : ℝ)|=(393438117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s4_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213544129/10000000000 : ℝ)*x 0 + (1140350273/2500000000 : ℝ)*x 1 + (1943426919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213544129/10000000000 : ℝ)^4755 ≤ (33237576090439/100000000000000 : ℝ)^3731 := by
    have hnat : (4213544129 : ℕ)^4755*100000000000000^3731 ≤ 33237576090439^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213544129 10000000000 33237576090439 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140350273/2500000000 : ℝ)^4755 ≤ (36773528951059/100000000000000 : ℝ)^3731 := by
    have hnat : (1140350273 : ℕ)^4755*100000000000000^3731 ≤ 36773528951059^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140350273 2500000000 36773528951059 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943426919/5000000000 : ℝ)^4755 ≤ (14994447473217/50000000000000 : ℝ)^3731 := by
    have hnat : (1943426919 : ℕ)^4755*50000000000000^3731 ≤ 14994447473217^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943426919 5000000000 14994447473217 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213544129/10000000000 : ℝ), (1140350273/2500000000 : ℝ), (1943426919/5000000000 : ℝ)] ![(33237576090439/100000000000000 : ℝ), (36773528951059/100000000000000 : ℝ), (14994447473217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213544129/10000000000 : ℝ)|^4755 ≤ (33237576090439/100000000000000 : ℝ)^3731
        have hw : |(4213544129/10000000000 : ℝ)|=(4213544129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140350273/2500000000 : ℝ)|^4755 ≤ (36773528951059/100000000000000 : ℝ)^3731
        have hw : |(1140350273/2500000000 : ℝ)|=(1140350273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1943426919/5000000000 : ℝ)|^4755 ≤ (14994447473217/50000000000000 : ℝ)^3731
        have hw : |(1943426919/5000000000 : ℝ)|=(1943426919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2607/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2043/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10417/100000 : ℝ) ^ (4751/1024 : ℝ) ≤ (1385610899352207/50000000000000000000 : ℝ) := by
    have hpowers : (10417/100000 : ℝ)^4751 ≤ (1385610899352207/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10417 : ℕ)^4751*50000000000000000000^1024 ≤ 1385610899352207^1024*100000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10417 100000 1385610899352207 50000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10417/100000 : ℝ)) (X := (1385610899352207/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4089/25000 : ℝ) ^ (4751/1024 : ℝ) ≤ (22476992174457769/100000000000000000000 : ℝ) := by
    have hpowers : (4089/25000 : ℝ)^4751 ≤ (22476992174457769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4089 : ℕ)^4751*100000000000000000000^1024 ≤ 22476992174457769^1024*25000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4089 25000 22476992174457769 100000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4089/25000 : ℝ)) (X := (22476992174457769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001385610899352207/25000000000000000000 : ℝ) ≤ (156251866494839/156250000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (25001385610899352207/25000000000000000000 : ℝ)^1024 ≤ (156251866494839/156250000000000 : ℝ)^4751 := by
      have hnat : (25001385610899352207 : ℕ)^1024*156250000000000^4751 ≤ 156251866494839^4751*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001385610899352207 25000000000000000000 156251866494839 156250000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156251866494839/156250000000000 : ℝ)) (X := (25001385610899352207/25000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025248213973162183/100000000000000000000 : ℝ) ≤ (10000544129890671/10000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (100025248213973162183/100000000000000000000 : ℝ)^1024 ≤ (10000544129890671/10000000000000000 : ℝ)^4751 := by
      have hnat : (100025248213973162183 : ℕ)^1024*10000000000000000^4751 ≤ 10000544129890671^4751*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025248213973162183 100000000000000000000 10000544129890671 10000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000544129890671/10000000000000000 : ℝ)) (X := (100025248213973162183/100000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022476992174457769/50000000000000000000 : ℝ) ≤ (5000484402055823/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (50022476992174457769/50000000000000000000 : ℝ)^1024 ≤ (5000484402055823/5000000000000000 : ℝ)^4751 := by
      have hnat : (50022476992174457769 : ℕ)^1024*5000000000000000^4751 ≤ 5000484402055823^4751*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022476992174457769 50000000000000000000 5000484402055823 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000484402055823/5000000000000000 : ℝ)) (X := (50022476992174457769/50000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1385610899352207/50000000000000000000 : ℝ) ≤ ((29690930892251265697/29695000000000000000 : ℝ)+2*(16986968839/23756000000000 : ℝ)*(10417/100000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (29690930892251265697/29695000000000000000 : ℝ)+2*(16986968839/23756000000000 : ℝ)*(10417/100000 : ℝ)=(156251866494839/156250000000000 : ℝ) by norm_num, show 1+2*(1385610899352207/50000000000000000000 : ℝ)=(25001385610899352207/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22476992174457769/100000000000000000000 : ℝ)+(1385610899352207/50000000000000000000 : ℝ) ≤ ((29690930892251265697/29695000000000000000 : ℝ)+(16986968839/23756000000000 : ℝ)*((4089/25000 : ℝ)+(10417/100000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (29690930892251265697/29695000000000000000 : ℝ)+(16986968839/23756000000000 : ℝ)*((4089/25000 : ℝ)+(10417/100000 : ℝ))=(10000544129890671/10000000000000000 : ℝ) by norm_num, show 1+(22476992174457769/100000000000000000000 : ℝ)+(1385610899352207/50000000000000000000 : ℝ)=(100025248213973162183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22476992174457769/100000000000000000000 : ℝ) ≤ ((29690930892251265697/29695000000000000000 : ℝ)+2*(16986968839/23756000000000 : ℝ)*(4089/25000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (29690930892251265697/29695000000000000000 : ℝ)+2*(16986968839/23756000000000 : ℝ)*(4089/25000 : ℝ)=(5000484402055823/5000000000000000 : ℝ) by norm_num, show 1+2*(22476992174457769/100000000000000000000 : ℝ)=(50022476992174457769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29690930892251265697/29695000000000000000 : ℝ)*(X 1 0+X 2 0)+(16986968839/23756000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10417/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (29690930892251265697/29695000000000000000 : ℝ)) (alpha := (16986968839/23756000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29690930892251265697/29695000000000000000 : ℝ)*(X 0 1+X 2 1)+(16986968839/23756000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10417/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (29690930892251265697/29695000000000000000 : ℝ)) (alpha := (16986968839/23756000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29690930892251265697/29695000000000000000 : ℝ)*(X 0 2+X 1 2)+(16986968839/23756000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (10417/100000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (29690930892251265697/29695000000000000000 : ℝ)) (alpha := (16986968839/23756000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1706801937/10000000000 : ℝ)*X 0 0+(1364936873/2500000000 : ℝ)*X 0 1+(2590357833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353702847/10000000000 : ℝ)*X 1 0+(-925344941/5000000000 : ℝ)*X 1 1+(647589461/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353702823/10000000000 : ℝ)*X 2 0+(5180715731/10000000000 : ℝ)*X 2 1+(-1850689857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2106685659/5000000000 : ℝ)*X 0 0+(3881713991/10000000000 : ℝ)*X 0 1+(1141621873/2500000000 : ℝ)*X 0 2+(2106685659/5000000000 : ℝ)*X 1 0+(3881713991/10000000000 : ℝ)*X 1 1+(1141621873/2500000000 : ℝ)*X 1 2+(2106685659/5000000000 : ℝ)*X 2 0+(3881713991/10000000000 : ℝ)*X 2 1+(1141621873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1706872363/10000000000 : ℝ)*X 0 0+(5182788293/10000000000 : ℝ)*X 0 1+(2728826543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639806173/5000000000 : ℝ)*X 1 0+(-1573752469/10000000000 : ℝ)*X 1 1+(2728826543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279612347/10000000000 : ℝ)*X 2 0+(1091530617/2000000000 : ℝ)*X 2 1+(-393438117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213544129/10000000000 : ℝ)*X 0 0+(1140350273/2500000000 : ℝ)*X 0 1+(1943426919/5000000000 : ℝ)*X 0 2+(4213544129/10000000000 : ℝ)*X 1 0+(1140350273/2500000000 : ℝ)*X 1 1+(1943426919/5000000000 : ℝ)*X 1 2+(4213544129/10000000000 : ℝ)*X 2 0+(1140350273/2500000000 : ℝ)*X 2 1+(1943426919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161104179955474926702708531/23199218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (112665033/10000000000000 : ℝ)*(base19) + (1030678823/100000000000000 : ℝ)*(base23) + (21389529/50000000000000 : ℝ)*(lower2) + (41408061/25000000000000 : ℝ)*(upper3) + (61782761/50000000000000 : ℝ)*(upper5) + (100883940338953/4000000000000 : ℝ)*(major0) + (100883940338953/4000000000000 : ℝ)*(major1) + (1261049254236913/50000000000000 : ℝ)*(major2) + (895958670677907/25000000000000 : ℝ)*(sp0) + (3583847465956483/100000000000000 : ℝ)*(sp1) + (358384756192799/10000000000000 : ℝ)*(sp2) + (14603422506623/1000000000000 : ℝ)*(sp3) + (2781979037/20000000000000 : ℝ)*(sp4) + (5942199213/100000000000000 : ℝ)*(sp7) + (1460348192861513/100000000000000 : ℝ)*(f.failure) + (3583848592606813/100000000000000 : ℝ)*(f.sum) + (73437748069163/11878000000000000000000000000 : ℝ)*base66 + (1063004331383564759/118780000000000000000000000000000 : ℝ)*base68 + (14674488600975448361/1484750000000000000000000000000000 : ℝ)*base69 + (397622871964344759/118780000000000000000000000000000 : ℝ)*base72 + (1713215292299/475120000000000000000000000 : ℝ)*base74 + (7975816046701948361/1484750000000000000000000000000000 : ℝ)*base75 + (1440233240110114759/118780000000000000000000000000000 : ℝ)*base78 + (597630837404534759/118780000000000000000000000000000 : ℝ)*base80 + (20278017915379/5939000000000000000000000000 : ℝ)*base81 + (13639241/2000000000000000000000 : ℝ)*base89 + (13639241/2000000000000000000000 : ℝ)*base91 + (6360759/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2266295801940195325728292911/185593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468448311/25000000000000 : ℝ)*(base19) + (405828147/20000000000000 : ℝ)*(base23) + (297422093/50000000000000 : ℝ)*(lower1) + (128148853/50000000000000 : ℝ)*(upper3) + (34775839/50000000000000 : ℝ)*(lower4) + (126532981/50000000000000 : ℝ)*(upper5) + (320037304573007/12500000000000 : ℝ)*(major0) + (320037304573007/12500000000000 : ℝ)*(major1) + (320037304573007/12500000000000 : ℝ)*(major2) + (816701219/50000000000000 : ℝ)*(sp2) + (181906485489157/5000000000000 : ℝ)*(sp4) + (454765979498737/12500000000000 : ℝ)*(sp5) + (113691438976249/3125000000000 : ℝ)*(sp6) + (148246675634973/10000000000000 : ℝ)*(sp7) + (148246675634973/10000000000000 : ℝ)*(f.failure) + (181906485489157/5000000000000 : ℝ)*(f.sum) + (834842445127/593900000000000000000000000 : ℝ)*base65 + (17561927737268759121/371187500000000000000000000000000 : ℝ)*base68 + (2296785601981259121/371187500000000000000000000000000 : ℝ)*base70 + (21622053079120884121/371187500000000000000000000000000 : ℝ)*base72 + (2329781561623/742375000000000000000000000 : ℝ)*base74 + (16905778708607759121/371187500000000000000000000000000 : ℝ)*base76 + (1461936199833759121/371187500000000000000000000000000 : ℝ)*base78 + (1649146871536384121/371187500000000000000000000000000 : ℝ)*base80 + (1756922901273/593900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1586461/200000000000000000000 : ℝ)*base89 + (1586461/200000000000000000000 : ℝ)*base91 + (1586461/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1609_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1609_s5_0 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68272463/400000000 : ℝ)*x 0 + (1364924511/2500000000 : ℝ)*x 1 + (1295189681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68272463/400000000 : ℝ)^4755 ≤ (10506385817379/100000000000000 : ℝ)^3731 := by
    have hnat : (68272463 : ℕ)^4755*100000000000000^3731 ≤ 10506385817379^3731*400000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68272463 400000000 10506385817379 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364924511/2500000000 : ℝ)^4755 ≤ (23120789077057/50000000000000 : ℝ)^3731 := by
    have hnat : (1364924511 : ℕ)^4755*50000000000000^3731 ≤ 23120789077057^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364924511 2500000000 23120789077057 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295189681/2500000000 : ℝ)^4755 ≤ (5406504501187/12500000000000 : ℝ)^3731 := by
    have hnat : (1295189681 : ℕ)^4755*12500000000000^3731 ≤ 5406504501187^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295189681 2500000000 5406504501187 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68272463/400000000 : ℝ), (1364924511/2500000000 : ℝ), (1295189681/2500000000 : ℝ)] ![(10506385817379/100000000000000 : ℝ), (23120789077057/50000000000000 : ℝ), (5406504501187/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68272463/400000000 : ℝ)|^4755 ≤ (10506385817379/100000000000000 : ℝ)^3731
        have hw : |(-68272463/400000000 : ℝ)|=(68272463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364924511/2500000000 : ℝ)|^4755 ≤ (23120789077057/50000000000000 : ℝ)^3731
        have hw : |(1364924511/2500000000 : ℝ)|=(1364924511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295189681/2500000000 : ℝ)|^4755 ≤ (5406504501187/12500000000000 : ℝ)^3731
        have hw : |(1295189681/2500000000 : ℝ)|=(1295189681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_1 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338422427/2500000000 : ℝ)*x 0 + (-185065037/1000000000 : ℝ)*x 1 + (5180758733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338422427/2500000000 : ℝ)^4755 ≤ (22550184698711/50000000000000 : ℝ)^3731 := by
    have hnat : (1338422427 : ℕ)^4755*50000000000000^3731 ≤ 22550184698711^3731*2500000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338422427 2500000000 22550184698711 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185065037/1000000000 : ℝ)^4755 ≤ (2329518896807/20000000000000 : ℝ)^3731 := by
    have hnat : (185065037 : ℕ)^4755*20000000000000^3731 ≤ 2329518896807^3731*1000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185065037 1000000000 2329518896807 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180758733/10000000000 : ℝ)^4755 ≤ (8650407221051/20000000000000 : ℝ)^3731 := by
    have hnat : (5180758733 : ℕ)^4755*20000000000000^3731 ≤ 8650407221051^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180758733 10000000000 8650407221051 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338422427/2500000000 : ℝ), (-185065037/1000000000 : ℝ), (5180758733/10000000000 : ℝ)] ![(22550184698711/50000000000000 : ℝ), (2329518896807/20000000000000 : ℝ), (8650407221051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338422427/2500000000 : ℝ)|^4755 ≤ (22550184698711/50000000000000 : ℝ)^3731
        have hw : |(1338422427/2500000000 : ℝ)|=(1338422427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185065037/1000000000 : ℝ)|^4755 ≤ (2329518896807/20000000000000 : ℝ)^3731
        have hw : |(-185065037/1000000000 : ℝ)|=(185065037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180758733/10000000000 : ℝ)|^4755 ≤ (8650407221051/20000000000000 : ℝ)^3731
        have hw : |(5180758733/10000000000 : ℝ)|=(5180758733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_2 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353689711/10000000000 : ℝ)*x 0 + (5180758727/10000000000 : ℝ)*x 1 + (-925325187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353689711/10000000000 : ℝ)^4755 ≤ (45100369429631/100000000000000 : ℝ)^3731 := by
    have hnat : (5353689711 : ℕ)^4755*100000000000000^3731 ≤ 45100369429631^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353689711 10000000000 45100369429631 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180758727/10000000000 : ℝ)^4755 ≤ (5406504505177/12500000000000 : ℝ)^3731 := by
    have hnat : (5180758727 : ℕ)^4755*12500000000000^3731 ≤ 5406504505177^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180758727 10000000000 5406504505177 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925325187/5000000000 : ℝ)^4755 ≤ (11647594516119/100000000000000 : ℝ)^3731 := by
    have hnat : (925325187 : ℕ)^4755*100000000000000^3731 ≤ 11647594516119^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925325187 5000000000 11647594516119 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353689711/10000000000 : ℝ), (5180758727/10000000000 : ℝ), (-925325187/5000000000 : ℝ)] ![(45100369429631/100000000000000 : ℝ), (5406504505177/12500000000000 : ℝ), (11647594516119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353689711/10000000000 : ℝ)|^4755 ≤ (45100369429631/100000000000000 : ℝ)^3731
        have hw : |(5353689711/10000000000 : ℝ)|=(5353689711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180758727/10000000000 : ℝ)|^4755 ≤ (5406504505177/12500000000000 : ℝ)^3731
        have hw : |(5180758727/10000000000 : ℝ)|=(5180758727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-925325187/5000000000 : ℝ)|^4755 ≤ (11647594516119/100000000000000 : ℝ)^3731
        have hw : |(-925325187/5000000000 : ℝ)|=(925325187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_3 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842675549/2000000000 : ℝ)*x 0 + (3881826787/10000000000 : ℝ)*x 1 + (4566373329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842675549/2000000000 : ℝ)^4755 ≤ (33235903397293/100000000000000 : ℝ)^3731 := by
    have hnat : (842675549 : ℕ)^4755*100000000000000^3731 ≤ 33235903397293^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842675549 2000000000 33235903397293 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3881826787/10000000000 : ℝ)^4755 ≤ (29939472560783/100000000000000 : ℝ)^3731 := by
    have hnat : (3881826787 : ℕ)^4755*100000000000000^3731 ≤ 29939472560783^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881826787 10000000000 29939472560783 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4566373329/10000000000 : ℝ)^4755 ≤ (36824624031027/100000000000000 : ℝ)^3731 := by
    have hnat : (4566373329 : ℕ)^4755*100000000000000^3731 ≤ 36824624031027^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566373329 10000000000 36824624031027 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842675549/2000000000 : ℝ), (3881826787/10000000000 : ℝ), (4566373329/10000000000 : ℝ)] ![(33235903397293/100000000000000 : ℝ), (29939472560783/100000000000000 : ℝ), (36824624031027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842675549/2000000000 : ℝ)|^4755 ≤ (33235903397293/100000000000000 : ℝ)^3731
        have hw : |(842675549/2000000000 : ℝ)|=(842675549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3881826787/10000000000 : ℝ)|^4755 ≤ (29939472560783/100000000000000 : ℝ)^3731
        have hw : |(3881826787/10000000000 : ℝ)|=(3881826787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4566373329/10000000000 : ℝ)|^4755 ≤ (36824624031027/100000000000000 : ℝ)^3731
        have hw : |(4566373329/10000000000 : ℝ)|=(4566373329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_4 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341376391/2000000000 : ℝ)*x 0 + (2591414999/5000000000 : ℝ)*x 1 + (1091520999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341376391/2000000000 : ℝ)^4755 ≤ (10506937951717/100000000000000 : ℝ)^3731 := by
    have hnat : (341376391 : ℕ)^4755*100000000000000^3731 ≤ 10506937951717^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341376391 2000000000 10506937951717 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591414999/5000000000 : ℝ)^4755 ≤ (21637037706573/50000000000000 : ℝ)^3731 := by
    have hnat : (2591414999 : ℕ)^4755*50000000000000^3731 ≤ 21637037706573^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591414999 5000000000 21637037706573 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091520999/2000000000 : ℝ)^4755 ≤ (9243797322777/20000000000000 : ℝ)^3731 := by
    have hnat : (1091520999 : ℕ)^4755*20000000000000^3731 ≤ 9243797322777^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091520999 2000000000 9243797322777 20000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341376391/2000000000 : ℝ), (2591414999/5000000000 : ℝ), (1091520999/2000000000 : ℝ)] ![(10506937951717/100000000000000 : ℝ), (21637037706573/50000000000000 : ℝ), (9243797322777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341376391/2000000000 : ℝ)|^4755 ≤ (10506937951717/100000000000000 : ℝ)^3731
        have hw : |(-341376391/2000000000 : ℝ)|=(341376391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591414999/5000000000 : ℝ)|^4755 ≤ (21637037706573/50000000000000 : ℝ)^3731
        have hw : |(2591414999/5000000000 : ℝ)|=(2591414999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091520999/2000000000 : ℝ)|^4755 ≤ (9243797322777/20000000000000 : ℝ)^3731
        have hw : |(1091520999/2000000000 : ℝ)|=(1091520999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_5 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639811931/5000000000 : ℝ)*x 0 + (-1573804037/10000000000 : ℝ)*x 1 + (2728802509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639811931/5000000000 : ℝ)^4755 ≤ (1107667387727/2500000000000 : ℝ)^3731 := by
    have hnat : (2639811931 : ℕ)^4755*2500000000000^3731 ≤ 1107667387727^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639811931 5000000000 1107667387727 2500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1573804037/10000000000 : ℝ)^4755 ≤ (236857940519/2500000000000 : ℝ)^3731 := by
    have hnat : (1573804037 : ℕ)^4755*2500000000000^3731 ≤ 236857940519^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573804037 10000000000 236857940519 2500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728802509/5000000000 : ℝ)^4755 ≤ (11554746715531/25000000000000 : ℝ)^3731 := by
    have hnat : (2728802509 : ℕ)^4755*25000000000000^3731 ≤ 11554746715531^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728802509 5000000000 11554746715531 25000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639811931/5000000000 : ℝ), (-1573804037/10000000000 : ℝ), (2728802509/5000000000 : ℝ)] ![(1107667387727/2500000000000 : ℝ), (236857940519/2500000000000 : ℝ), (11554746715531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639811931/5000000000 : ℝ)|^4755 ≤ (1107667387727/2500000000000 : ℝ)^3731
        have hw : |(2639811931/5000000000 : ℝ)|=(2639811931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1573804037/10000000000 : ℝ)|^4755 ≤ (236857940519/2500000000000 : ℝ)^3731
        have hw : |(-1573804037/10000000000 : ℝ)|=(1573804037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728802509/5000000000 : ℝ)|^4755 ≤ (11554746715531/25000000000000 : ℝ)^3731
        have hw : |(2728802509/5000000000 : ℝ)|=(2728802509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_6 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055924773/2000000000 : ℝ)*x 0 + (5457605017/10000000000 : ℝ)*x 1 + (-786902017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055924773/2000000000 : ℝ)^4755 ≤ (22153347770583/50000000000000 : ℝ)^3731 := by
    have hnat : (1055924773 : ℕ)^4755*50000000000000^3731 ≤ 22153347770583^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055924773 2000000000 22153347770583 50000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457605017/10000000000 : ℝ)^4755 ≤ (46218986851331/100000000000000 : ℝ)^3731 := by
    have hnat : (5457605017 : ℕ)^4755*100000000000000^3731 ≤ 46218986851331^3731*10000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457605017 10000000000 46218986851331 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (786902017/5000000000 : ℝ)^4755 ≤ (592144849859/6250000000000 : ℝ)^3731 := by
    have hnat : (786902017 : ℕ)^4755*6250000000000^3731 ≤ 592144849859^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786902017 5000000000 592144849859 6250000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055924773/2000000000 : ℝ), (5457605017/10000000000 : ℝ), (-786902017/5000000000 : ℝ)] ![(22153347770583/50000000000000 : ℝ), (46218986851331/100000000000000 : ℝ), (592144849859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055924773/2000000000 : ℝ)|^4755 ≤ (22153347770583/50000000000000 : ℝ)^3731
        have hw : |(1055924773/2000000000 : ℝ)|=(1055924773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457605017/10000000000 : ℝ)|^4755 ≤ (46218986851331/100000000000000 : ℝ)^3731
        have hw : |(5457605017/10000000000 : ℝ)|=(5457605017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-786902017/5000000000 : ℝ)|^4755 ≤ (592144849859/6250000000000 : ℝ)^3731
        have hw : |(-786902017/5000000000 : ℝ)|=(786902017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1609_s5_7 (p : ℝ) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2106775173/5000000000 : ℝ)*x 0 + (912258061/2000000000 : ℝ)*x 1 + (1943481621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106775173/5000000000 : ℝ)^4755 ≤ (4154704823949/12500000000000 : ℝ)^3731 := by
    have hnat : (2106775173 : ℕ)^4755*12500000000000^3731 ≤ 4154704823949^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106775173 5000000000 4154704823949 12500000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912258061/2000000000 : ℝ)^4755 ≤ (3677239066957/10000000000000 : ℝ)^3731 := by
    have hnat : (912258061 : ℕ)^4755*10000000000000^3731 ≤ 3677239066957^3731*2000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912258061 2000000000 3677239066957 10000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943481621/5000000000 : ℝ)^4755 ≤ (29989970723803/100000000000000 : ℝ)^3731 := by
    have hnat : (1943481621 : ℕ)^4755*100000000000000^3731 ≤ 29989970723803^3731*5000000000^4755 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943481621 5000000000 29989970723803 100000000000000 4755 3731 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4755/1024 : ℝ)) 4755 3731 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106775173/5000000000 : ℝ), (912258061/2000000000 : ℝ), (1943481621/5000000000 : ℝ)] ![(4154704823949/12500000000000 : ℝ), (3677239066957/10000000000000 : ℝ), (29989970723803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106775173/5000000000 : ℝ)|^4755 ≤ (4154704823949/12500000000000 : ℝ)^3731
        have hw : |(2106775173/5000000000 : ℝ)|=(2106775173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(912258061/2000000000 : ℝ)|^4755 ≤ (3677239066957/10000000000000 : ℝ)^3731
        have hw : |(912258061/2000000000 : ℝ)|=(912258061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1943481621/5000000000 : ℝ)|^4755 ≤ (29989970723803/100000000000000 : ℝ)^3731
        have hw : |(1943481621/5000000000 : ℝ)|=(1943481621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1609_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16343/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2043/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2043/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2607/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2043/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2043/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2607/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2043/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2043/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2607/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2607/25000 : ℝ) ^ (4751/1024 : ℝ) ≤ (87025781056209/3125000000000000000 : ℝ) := by
    have hpowers : (2607/25000 : ℝ)^4751 ≤ (87025781056209/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2607 : ℕ)^4751*3125000000000000000^1024 ≤ 87025781056209^1024*25000^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2607 25000 87025781056209 3125000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2607/25000 : ℝ)) (X := (87025781056209/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2043/12500 : ℝ) ^ (4751/1024 : ℝ) ≤ (4480116528248009/20000000000000000000 : ℝ) := by
    have hpowers : (2043/12500 : ℝ)^4751 ≤ (4480116528248009/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2043 : ℕ)^4751*20000000000000000000^1024 ≤ 4480116528248009^1024*12500^4751 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2043 12500 4480116528248009 20000000000000000000 4751 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2043/12500 : ℝ)) (X := (4480116528248009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562587025781056209/1562500000000000000 : ℝ) ≤ (312503751313537/312500000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (1562587025781056209/1562500000000000000 : ℝ)^1024 ≤ (312503751313537/312500000000000 : ℝ)^4751 := by
      have hnat : (1562587025781056209 : ℕ)^1024*312500000000000^4751 ≤ 312503751313537^4751*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562587025781056209 1562500000000000000 312503751313537 312500000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312503751313537/312500000000000 : ℝ)) (X := (1562587025781056209/1562500000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025185407635038733/100000000000000000000 : ℝ) ≤ (2000108555294191/2000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (100025185407635038733/100000000000000000000 : ℝ)^1024 ≤ (2000108555294191/2000000000000000 : ℝ)^4751 := by
      have hnat : (100025185407635038733 : ℕ)^1024*2000000000000000^4751 ≤ 2000108555294191^4751*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025185407635038733 100000000000000000000 2000108555294191 2000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000108555294191/2000000000000000 : ℝ)) (X := (100025185407635038733/100000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004480116528248009/10000000000000000000 : ℝ) ≤ (5000482755454363/5000000000000000 : ℝ) ^ (4751/1024 : ℝ) := by
    have hpowers : (10004480116528248009/10000000000000000000 : ℝ)^1024 ≤ (5000482755454363/5000000000000000 : ℝ)^4751 := by
      have hnat : (10004480116528248009 : ℕ)^1024*5000000000000000^4751 ≤ 5000482755454363^4751*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004480116528248009 10000000000000000000 5000482755454363 5000000000000000 1024 4751 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000482755454363/5000000000000000 : ℝ)) (X := (10004480116528248009/10000000000000000000 : ℝ)) (by norm_num) 4751 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87025781056209/3125000000000000000 : ℝ) ≤ ((2464662234134756857/2465000000000000000 : ℝ)+2*(140911479257/197200000000000 : ℝ)*(2607/25000 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (2464662234134756857/2465000000000000000 : ℝ)+2*(140911479257/197200000000000 : ℝ)*(2607/25000 : ℝ)=(312503751313537/312500000000000 : ℝ) by norm_num, show 1+2*(87025781056209/3125000000000000000 : ℝ)=(1562587025781056209/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4480116528248009/20000000000000000000 : ℝ)+(87025781056209/3125000000000000000 : ℝ) ≤ ((2464662234134756857/2465000000000000000 : ℝ)+(140911479257/197200000000000 : ℝ)*((2043/12500 : ℝ)+(2607/25000 : ℝ)))^(4751/1024 : ℝ) := by
    rw [show (2464662234134756857/2465000000000000000 : ℝ)+(140911479257/197200000000000 : ℝ)*((2043/12500 : ℝ)+(2607/25000 : ℝ))=(2000108555294191/2000000000000000 : ℝ) by norm_num, show 1+(4480116528248009/20000000000000000000 : ℝ)+(87025781056209/3125000000000000000 : ℝ)=(100025185407635038733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4480116528248009/20000000000000000000 : ℝ) ≤ ((2464662234134756857/2465000000000000000 : ℝ)+2*(140911479257/197200000000000 : ℝ)*(2043/12500 : ℝ))^(4751/1024 : ℝ) := by
    rw [show (2464662234134756857/2465000000000000000 : ℝ)+2*(140911479257/197200000000000 : ℝ)*(2043/12500 : ℝ)=(5000482755454363/5000000000000000 : ℝ) by norm_num, show 1+2*(4480116528248009/20000000000000000000 : ℝ)=(10004480116528248009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2464662234134756857/2465000000000000000 : ℝ)*(X 1 0+X 2 0)+(140911479257/197200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (2464662234134756857/2465000000000000000 : ℝ)) (alpha := (140911479257/197200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2464662234134756857/2465000000000000000 : ℝ)*(X 0 1+X 2 1)+(140911479257/197200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (2464662234134756857/2465000000000000000 : ℝ)) (alpha := (140911479257/197200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2464662234134756857/2465000000000000000 : ℝ)*(X 0 2+X 1 2)+(140911479257/197200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4751/1024 : ℝ)) (lo := (2607/25000 : ℝ)) (hi := (2043/12500 : ℝ)) (c := (2464662234134756857/2465000000000000000 : ℝ)) (alpha := (140911479257/197200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-68272463/400000000 : ℝ)*X 0 0+(1364924511/2500000000 : ℝ)*X 0 1+(1295189681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338422427/2500000000 : ℝ)*X 1 0+(-185065037/1000000000 : ℝ)*X 1 1+(5180758733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353689711/10000000000 : ℝ)*X 2 0+(5180758727/10000000000 : ℝ)*X 2 1+(-925325187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((842675549/2000000000 : ℝ)*X 0 0+(3881826787/10000000000 : ℝ)*X 0 1+(4566373329/10000000000 : ℝ)*X 0 2+(842675549/2000000000 : ℝ)*X 1 0+(3881826787/10000000000 : ℝ)*X 1 1+(4566373329/10000000000 : ℝ)*X 1 2+(842675549/2000000000 : ℝ)*X 2 0+(3881826787/10000000000 : ℝ)*X 2 1+(4566373329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-341376391/2000000000 : ℝ)*X 0 0+(2591414999/5000000000 : ℝ)*X 0 1+(1091520999/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639811931/5000000000 : ℝ)*X 1 0+(-1573804037/10000000000 : ℝ)*X 1 1+(2728802509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055924773/2000000000 : ℝ)*X 2 0+(5457605017/10000000000 : ℝ)*X 2 1+(-786902017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106775173/5000000000 : ℝ)*X 0 0+(912258061/2000000000 : ℝ)*X 0 1+(1943481621/5000000000 : ℝ)*X 0 2+(2106775173/5000000000 : ℝ)*X 1 0+(912258061/2000000000 : ℝ)*X 1 1+(1943481621/5000000000 : ℝ)*X 1 2+(2106775173/5000000000 : ℝ)*X 2 0+(912258061/2000000000 : ℝ)*X 2 1+(1943481621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1609_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46972092197212795367684817/7703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126254261/12500000000000 : ℝ)*(base19) + (469661433/50000000000000 : ℝ)*(base23) + (4866513/12500000000000 : ℝ)*(lower2) + (154949269/100000000000000 : ℝ)*(upper3) + (49569397/50000000000000 : ℝ)*(upper5) + (307975168829/12207031250 : ℝ)*(major0) + (307975168829/12207031250 : ℝ)*(major1) + (307975168829/12207031250 : ℝ)*(major2) + (3585021721298797/100000000000000 : ℝ)*(sp0) + (1792516406590837/50000000000000 : ℝ)*(sp1) + (112032277621653/3125000000000 : ℝ)*(sp2) + (365206438573647/25000000000000 : ℝ)*(sp3) + (6050958483/50000000000000 : ℝ)*(sp4) + (67316551/1250000000000 : ℝ)*(sp7) + (365207784904667/25000000000000 : ℝ)*(f.failure) + (1792516911607881/50000000000000 : ℝ)*(f.sum) + (2702623628769/2465000000000000000000000000 : ℝ)*base65 + (10114006818034133/1925781250000000000000000000000 : ℝ)*base68 + (43564009635865141/3851562500000000000000000000000 : ℝ)*base70 + (7786679441653367/1925781250000000000000000000000 : ℝ)*base71 + (844339963081/154062500000000000000000000 : ℝ)*base74 + (21120059816541109/3851562500000000000000000000000 : ℝ)*base75 + (7568715930122117/1925781250000000000000000000000 : ℝ)*base77 + (30568306470215867/1925781250000000000000000000000 : ℝ)*base79 + (3994912562919/616250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2413019/500000000000000000000 : ℝ)*base89 + (2413019/500000000000000000000 : ℝ)*base91 + (2413019/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76423938810393063375678057/6162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79322223/4000000000000 : ℝ)*(base19) + (423796459/20000000000000 : ℝ)*(base23) + (158851197/25000000000000 : ℝ)*(lower1) + (273747811/100000000000000 : ℝ)*(upper3) + (14303521/25000000000000 : ℝ)*(lower4) + (61649331/25000000000000 : ℝ)*(upper5) + (256113384647383/10000000000000 : ℝ)*(major0) + (256113384647383/10000000000000 : ℝ)*(major1) + (256113384647383/10000000000000 : ℝ)*(major2) + (1817074487/100000000000000 : ℝ)*(sp2) + (3639316803282727/100000000000000 : ℝ)*(sp4) + (227457176264197/6250000000000 : ℝ)*(sp5) + (454914108403243/12500000000000 : ℝ)*(sp6) + (741475238141621/50000000000000 : ℝ)*(sp7) + (741475238141621/50000000000000 : ℝ)*(f.failure) + (3639316803282727/100000000000000 : ℝ)*(f.sum) + (3964736066311/986000000000000000000000000 : ℝ)*base66 + (172391654091342731/24650000000000000000000000000000 : ℝ)*base67 + (75872149266892731/24650000000000000000000000000000 : ℝ)*base69 + (314889284618657269/24650000000000000000000000000000 : ℝ)*base72 + (104244607007/197200000000000000000000000 : ℝ)*base73 + (337590384571742731/24650000000000000000000000000000 : ℝ)*base75 + (91772715083892731/24650000000000000000000000000000 : ℝ)*base77 + (157344935409192731/24650000000000000000000000000000 : ℝ)*base79 + (4735703154949/986000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5033397/1000000000000000000000 : ℝ)*base89 + (5033397/1000000000000000000000 : ℝ)*base91 + (5033397/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1609_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1609_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1609_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1609_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1609_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1609_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4751/1024 : ℝ) ≤ p) (hpb : p ≤ (4755/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34541057/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8249/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16343/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1609_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

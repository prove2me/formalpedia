-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:38.703656+00:00
-- url     : https://prove2.me/submissions/5fc952c9-ff31-4e14-b3e6-702c6f36d8c7

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
theorem support_rectangle_w1333_box_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-941903183/5000000000 : ℝ)*x 0 + (5390313839/10000000000 : ℝ)*x 1 + (168447309/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941903183/5000000000 : ℝ)^4293 ≤ (5583603016937/50000000000000 : ℝ)^3269 := by
    have hnat : (941903183 : ℕ)^4293*50000000000000^3269 ≤ 5583603016937^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941903183 5000000000 5583603016937 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390313839/10000000000 : ℝ)^4293 ≤ (11104099177119/25000000000000 : ℝ)^3269 := by
    have hnat : (5390313839 : ℕ)^4293*25000000000000^3269 ≤ 11104099177119^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390313839 10000000000 11104099177119 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168447309/312500000 : ℝ)^4293 ≤ (22208198619357/50000000000000 : ℝ)^3269 := by
    have hnat : (168447309 : ℕ)^4293*50000000000000^3269 ≤ 22208198619357^3269*312500000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168447309 312500000 22208198619357 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941903183/5000000000 : ℝ), (5390313839/10000000000 : ℝ), (168447309/312500000 : ℝ)] ![(5583603016937/50000000000000 : ℝ), (11104099177119/25000000000000 : ℝ), (22208198619357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941903183/5000000000 : ℝ)|^4293 ≤ (5583603016937/50000000000000 : ℝ)^3269
        have hw : |(-941903183/5000000000 : ℝ)|=(941903183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390313839/10000000000 : ℝ)|^4293 ≤ (11104099177119/25000000000000 : ℝ)^3269
        have hw : |(5390313839/10000000000 : ℝ)|=(5390313839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168447309/312500000 : ℝ)|^4293 ≤ (22208198619357/50000000000000 : ℝ)^3269
        have hw : |(168447309/312500000 : ℝ)|=(168447309/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285038661/10000000000 : ℝ)*x 0 + (-2027991797/10000000000 : ℝ)*x 1 + (539031417/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285038661/10000000000 : ℝ)^4293 ≤ (43280693867657/100000000000000 : ℝ)^3269 := by
    have hnat : (5285038661 : ℕ)^4293*100000000000000^3269 ≤ 43280693867657^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285038661 10000000000 43280693867657 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027991797/10000000000 : ℝ)^4293 ≤ (1537863228911/12500000000000 : ℝ)^3269 := by
    have hnat : (2027991797 : ℕ)^4293*12500000000000^3269 ≤ 1537863228911^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027991797 10000000000 1537863228911 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539031417/1000000000 : ℝ)^4293 ≤ (44416400290291/100000000000000 : ℝ)^3269 := by
    have hnat : (539031417 : ℕ)^4293*100000000000000^3269 ≤ 44416400290291^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539031417 1000000000 44416400290291 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285038661/10000000000 : ℝ), (-2027991797/10000000000 : ℝ), (539031417/1000000000 : ℝ)] ![(43280693867657/100000000000000 : ℝ), (1537863228911/12500000000000 : ℝ), (44416400290291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285038661/10000000000 : ℝ)|^4293 ≤ (43280693867657/100000000000000 : ℝ)^3269
        have hw : |(5285038661/10000000000 : ℝ)|=(5285038661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027991797/10000000000 : ℝ)|^4293 ≤ (1537863228911/12500000000000 : ℝ)^3269
        have hw : |(-2027991797/10000000000 : ℝ)|=(2027991797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539031417/1000000000 : ℝ)|^4293 ≤ (44416400290291/100000000000000 : ℝ)^3269
        have hw : |(539031417/1000000000 : ℝ)|=(539031417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285038677/10000000000 : ℝ)*x 0 + (539031413/1000000000 : ℝ)*x 1 + (-2027991829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285038677/10000000000 : ℝ)^4293 ≤ (4328069403973/10000000000000 : ℝ)^3269 := by
    have hnat : (5285038677 : ℕ)^4293*10000000000000^3269 ≤ 4328069403973^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285038677 10000000000 4328069403973 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539031413/1000000000 : ℝ)^4293 ≤ (44416399857443/100000000000000 : ℝ)^3269 := by
    have hnat : (539031413 : ℕ)^4293*100000000000000^3269 ≤ 44416399857443^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539031413 1000000000 44416399857443 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027991829/10000000000 : ℝ)^4293 ≤ (12302906086227/100000000000000 : ℝ)^3269 := by
    have hnat : (2027991829 : ℕ)^4293*100000000000000^3269 ≤ 12302906086227^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027991829 10000000000 12302906086227 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285038677/10000000000 : ℝ), (539031413/1000000000 : ℝ), (-2027991829/10000000000 : ℝ)] ![(4328069403973/10000000000000 : ℝ), (44416399857443/100000000000000 : ℝ), (12302906086227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285038677/10000000000 : ℝ)|^4293 ≤ (4328069403973/10000000000000 : ℝ)^3269
        have hw : |(5285038677/10000000000 : ℝ)|=(5285038677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539031413/1000000000 : ℝ)|^4293 ≤ (44416399857443/100000000000000 : ℝ)^3269
        have hw : |(539031413/1000000000 : ℝ)|=(539031413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027991829/10000000000 : ℝ)|^4293 ≤ (12302906086227/100000000000000 : ℝ)^3269
        have hw : |(-2027991829/10000000000 : ℝ)|=(2027991829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (223868981/500000000 : ℝ)*x 0 + (532336383/1250000000 : ℝ)*x 1 + (2129345499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223868981/500000000 : ℝ)^4293 ≤ (1740518669427/5000000000000 : ℝ)^3269 := by
    have hnat : (223868981 : ℕ)^4293*5000000000000^3269 ≤ 1740518669427^3269*500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223868981 500000000 1740518669427 5000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532336383/1250000000 : ℝ)^4293 ≤ (32594813630249/100000000000000 : ℝ)^3269 := by
    have hnat : (532336383 : ℕ)^4293*100000000000000^3269 ≤ 32594813630249^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532336383 1250000000 32594813630249 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129345499/5000000000 : ℝ)^4293 ≤ (32594812966869/100000000000000 : ℝ)^3269 := by
    have hnat : (2129345499 : ℕ)^4293*100000000000000^3269 ≤ 32594812966869^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129345499 5000000000 32594812966869 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223868981/500000000 : ℝ), (532336383/1250000000 : ℝ), (2129345499/5000000000 : ℝ)] ![(1740518669427/5000000000000 : ℝ), (32594813630249/100000000000000 : ℝ), (32594812966869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223868981/500000000 : ℝ)|^4293 ≤ (1740518669427/5000000000000 : ℝ)^3269
        have hw : |(223868981/500000000 : ℝ)|=(223868981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(532336383/1250000000 : ℝ)|^4293 ≤ (32594813630249/100000000000000 : ℝ)^3269
        have hw : |(532336383/1250000000 : ℝ)|=(532336383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2129345499/5000000000 : ℝ)|^4293 ≤ (32594812966869/100000000000000 : ℝ)^3269
        have hw : |(2129345499/5000000000 : ℝ)|=(2129345499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55562403/250000000 : ℝ)*x 0 + (1316181347/2500000000 : ℝ)*x 1 + (658090527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55562403/250000000 : ℝ)^4293 ≤ (6937640793231/50000000000000 : ℝ)^3269 := by
    have hnat : (55562403 : ℕ)^4293*50000000000000^3269 ≤ 6937640793231^3269*250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55562403 250000000 6937640793231 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316181347/2500000000 : ℝ)^4293 ≤ (43062365498603/100000000000000 : ℝ)^3269 := by
    have hnat : (1316181347 : ℕ)^4293*100000000000000^3269 ≤ 43062365498603^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316181347 2500000000 43062365498603 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658090527/1250000000 : ℝ)^4293 ≤ (43062352909473/100000000000000 : ℝ)^3269 := by
    have hnat : (658090527 : ℕ)^4293*100000000000000^3269 ≤ 43062352909473^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658090527 1250000000 43062352909473 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55562403/250000000 : ℝ), (1316181347/2500000000 : ℝ), (658090527/1250000000 : ℝ)] ![(6937640793231/50000000000000 : ℝ), (43062365498603/100000000000000 : ℝ), (43062352909473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55562403/250000000 : ℝ)|^4293 ≤ (6937640793231/50000000000000 : ℝ)^3269
        have hw : |(-55562403/250000000 : ℝ)|=(55562403/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316181347/2500000000 : ℝ)|^4293 ≤ (43062365498603/100000000000000 : ℝ)^3269
        have hw : |(1316181347/2500000000 : ℝ)|=(1316181347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658090527/1250000000 : ℝ)|^4293 ≤ (43062352909473/100000000000000 : ℝ)^3269
        have hw : |(658090527/1250000000 : ℝ)|=(658090527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373283357/10000000000 : ℝ)*x 0 + (-2078322887/10000000000 : ℝ)*x 1 + (658090673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373283357/10000000000 : ℝ)^4293 ≤ (44232197795719/100000000000000 : ℝ)^3269 := by
    have hnat : (5373283357 : ℕ)^4293*100000000000000^3269 ≤ 44232197795719^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373283357 10000000000 44232197795719 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078322887/10000000000 : ℝ)^4293 ≤ (6352718366387/50000000000000 : ℝ)^3269 := by
    have hnat : (2078322887 : ℕ)^4293*50000000000000^3269 ≤ 6352718366387^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078322887 10000000000 6352718366387 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658090673/1250000000 : ℝ)^4293 ≤ (43062365455637/100000000000000 : ℝ)^3269 := by
    have hnat : (658090673 : ℕ)^4293*100000000000000^3269 ≤ 43062365455637^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658090673 1250000000 43062365455637 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373283357/10000000000 : ℝ), (-2078322887/10000000000 : ℝ), (658090673/1250000000 : ℝ)] ![(44232197795719/100000000000000 : ℝ), (6352718366387/50000000000000 : ℝ), (43062365455637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373283357/10000000000 : ℝ)|^4293 ≤ (44232197795719/100000000000000 : ℝ)^3269
        have hw : |(5373283357/10000000000 : ℝ)|=(5373283357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078322887/10000000000 : ℝ)|^4293 ≤ (6352718366387/50000000000000 : ℝ)^3269
        have hw : |(-2078322887/10000000000 : ℝ)|=(2078322887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658090673/1250000000 : ℝ)|^4293 ≤ (43062365455637/100000000000000 : ℝ)^3269
        have hw : |(658090673/1250000000 : ℝ)|=(658090673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167915111/312500000 : ℝ)*x 0 + (1052945101/2000000000 : ℝ)*x 1 + (-2078322463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167915111/312500000 : ℝ)^4293 ≤ (44232199903761/100000000000000 : ℝ)^3269 := by
    have hnat : (167915111 : ℕ)^4293*100000000000000^3269 ≤ 44232199903761^3269*312500000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167915111 312500000 44232199903761 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052945101/2000000000 : ℝ)^4293 ≤ (5382795844421/12500000000000 : ℝ)^3269 := by
    have hnat : (1052945101 : ℕ)^4293*12500000000000^3269 ≤ 5382795844421^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052945101 2000000000 5382795844421 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078322463/10000000000 : ℝ)^4293 ≤ (12705433328783/100000000000000 : ℝ)^3269 := by
    have hnat : (2078322463 : ℕ)^4293*100000000000000^3269 ≤ 12705433328783^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078322463 10000000000 12705433328783 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167915111/312500000 : ℝ), (1052945101/2000000000 : ℝ), (-2078322463/10000000000 : ℝ)] ![(44232199903761/100000000000000 : ℝ), (5382795844421/12500000000000 : ℝ), (12705433328783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167915111/312500000 : ℝ)|^4293 ≤ (44232199903761/100000000000000 : ℝ)^3269
        have hw : |(167915111/312500000 : ℝ)|=(167915111/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052945101/2000000000 : ℝ)|^4293 ≤ (5382795844421/12500000000000 : ℝ)^3269
        have hw : |(1052945101/2000000000 : ℝ)|=(1052945101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078322463/10000000000 : ℝ)|^4293 ≤ (12705433328783/100000000000000 : ℝ)^3269
        have hw : |(-2078322463/10000000000 : ℝ)|=(2078322463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835933879/2000000000 : ℝ)*x 0 + (4407491879/10000000000 : ℝ)*x 1 + (2203746301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835933879/2000000000 : ℝ)^4293 ≤ (6360573686601/20000000000000 : ℝ)^3269 := by
    have hnat : (835933879 : ℕ)^4293*20000000000000^3269 ≤ 6360573686601^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835933879 2000000000 6360573686601 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407491879/10000000000 : ℝ)^4293 ≤ (8524640525339/25000000000000 : ℝ)^3269 := by
    have hnat : (4407491879 : ℕ)^4293*25000000000000^3269 ≤ 8524640525339^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407491879 10000000000 8524640525339 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203746301/5000000000 : ℝ)^4293 ≤ (17049284723491/50000000000000 : ℝ)^3269 := by
    have hnat : (2203746301 : ℕ)^4293*50000000000000^3269 ≤ 17049284723491^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203746301 5000000000 17049284723491 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835933879/2000000000 : ℝ), (4407491879/10000000000 : ℝ), (2203746301/5000000000 : ℝ)] ![(6360573686601/20000000000000 : ℝ), (8524640525339/25000000000000 : ℝ), (17049284723491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835933879/2000000000 : ℝ)|^4293 ≤ (6360573686601/20000000000000 : ℝ)^3269
        have hw : |(835933879/2000000000 : ℝ)|=(835933879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407491879/10000000000 : ℝ)|^4293 ≤ (8524640525339/25000000000000 : ℝ)^3269
        have hw : |(4407491879/10000000000 : ℝ)|=(4407491879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203746301/5000000000 : ℝ)|^4293 ≤ (17049284723491/50000000000000 : ℝ)^3269
        have hw : |(2203746301/5000000000 : ℝ)|=(2203746301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_8 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075698051/5000000000 : ℝ)*x 0 + (5178308141/10000000000 : ℝ)*x 1 + (675542089/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075698051/5000000000 : ℝ)^4293 ≤ (13295293970421/100000000000000 : ℝ)^3269 := by
    have hnat : (1075698051 : ℕ)^4293*100000000000000^3269 ≤ 13295293970421^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075698051 5000000000 13295293970421 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178308141/10000000000 : ℝ)^4293 ≤ (21068251634379/50000000000000 : ℝ)^3269 := by
    have hnat : (5178308141 : ℕ)^4293*50000000000000^3269 ≤ 21068251634379^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178308141 10000000000 21068251634379 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675542089/1250000000 : ℝ)^4293 ≤ (44568202749321/100000000000000 : ℝ)^3269 := by
    have hnat : (675542089 : ℕ)^4293*100000000000000^3269 ≤ 44568202749321^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675542089 1250000000 44568202749321 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075698051/5000000000 : ℝ), (5178308141/10000000000 : ℝ), (675542089/1250000000 : ℝ)] ![(13295293970421/100000000000000 : ℝ), (21068251634379/50000000000000 : ℝ), (44568202749321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075698051/5000000000 : ℝ)|^4293 ≤ (13295293970421/100000000000000 : ℝ)^3269
        have hw : |(-1075698051/5000000000 : ℝ)|=(1075698051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178308141/10000000000 : ℝ)|^4293 ≤ (21068251634379/50000000000000 : ℝ)^3269
        have hw : |(5178308141/10000000000 : ℝ)|=(5178308141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675542089/1250000000 : ℝ)|^4293 ≤ (44568202749321/100000000000000 : ℝ)^3269
        have hw : |(675542089/1250000000 : ℝ)|=(675542089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_9 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131879499/250000000 : ℝ)*x 0 + (-40444769/200000000 : ℝ)*x 1 + (675542183/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131879499/250000000 : ℝ)^4293 ≤ (1349209344403/3125000000000 : ℝ)^3269 := by
    have hnat : (131879499 : ℕ)^4293*3125000000000^3269 ≤ 1349209344403^3269*250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131879499 250000000 1349209344403 3125000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40444769/200000000 : ℝ)^4293 ≤ (3064272517643/25000000000000 : ℝ)^3269 := by
    have hnat : (40444769 : ℕ)^4293*25000000000000^3269 ≤ 3064272517643^3269*200000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40444769 200000000 3064272517643 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675542183/1250000000 : ℝ)^4293 ≤ (22284105446743/50000000000000 : ℝ)^3269 := by
    have hnat : (675542183 : ℕ)^4293*50000000000000^3269 ≤ 22284105446743^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675542183 1250000000 22284105446743 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131879499/250000000 : ℝ), (-40444769/200000000 : ℝ), (675542183/1250000000 : ℝ)] ![(1349209344403/3125000000000 : ℝ), (3064272517643/25000000000000 : ℝ), (22284105446743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131879499/250000000 : ℝ)|^4293 ≤ (1349209344403/3125000000000 : ℝ)^3269
        have hw : |(131879499/250000000 : ℝ)|=(131879499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40444769/200000000 : ℝ)|^4293 ≤ (3064272517643/25000000000000 : ℝ)^3269
        have hw : |(-40444769/200000000 : ℝ)|=(40444769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675542183/1250000000 : ℝ)|^4293 ≤ (22284105446743/50000000000000 : ℝ)^3269
        have hw : |(675542183/1250000000 : ℝ)|=(675542183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_10 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275180729/10000000000 : ℝ)*x 0 + (2702168377/5000000000 : ℝ)*x 1 + (-1011119189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275180729/10000000000 : ℝ)^4293 ≤ (21587353643153/50000000000000 : ℝ)^3269 := by
    have hnat : (5275180729 : ℕ)^4293*50000000000000^3269 ≤ 21587353643153^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275180729 10000000000 21587353643153 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702168377/5000000000 : ℝ)^4293 ≤ (22284101602091/50000000000000 : ℝ)^3269 := by
    have hnat : (2702168377 : ℕ)^4293*50000000000000^3269 ≤ 22284101602091^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702168377 5000000000 22284101602091 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011119189/5000000000 : ℝ)^4293 ≤ (3064272374367/25000000000000 : ℝ)^3269 := by
    have hnat : (1011119189 : ℕ)^4293*25000000000000^3269 ≤ 3064272374367^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011119189 5000000000 3064272374367 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275180729/10000000000 : ℝ), (2702168377/5000000000 : ℝ), (-1011119189/5000000000 : ℝ)] ![(21587353643153/50000000000000 : ℝ), (22284101602091/50000000000000 : ℝ), (3064272374367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275180729/10000000000 : ℝ)|^4293 ≤ (21587353643153/50000000000000 : ℝ)^3269
        have hw : |(5275180729/10000000000 : ℝ)|=(5275180729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702168377/5000000000 : ℝ)|^4293 ≤ (22284101602091/50000000000000 : ℝ)^3269
        have hw : |(2702168377/5000000000 : ℝ)|=(2702168377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011119189/5000000000 : ℝ)|^4293 ≤ (3064272374367/25000000000000 : ℝ)^3269
        have hw : |(-1011119189/5000000000 : ℝ)|=(1011119189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_11 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (451006123/1000000000 : ℝ)*x 0 + (132564457/312500000 : ℝ)*x 1 + (1060515723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451006123/1000000000 : ℝ)^4293 ≤ (8786109325501/25000000000000 : ℝ)^3269 := by
    have hnat : (451006123 : ℕ)^4293*25000000000000^3269 ≤ 8786109325501^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451006123 1000000000 8786109325501 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132564457/312500000 : ℝ)^4293 ≤ (16213889998009/50000000000000 : ℝ)^3269 := by
    have hnat : (132564457 : ℕ)^4293*50000000000000^3269 ≤ 16213889998009^3269*312500000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132564457 312500000 16213889998009 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060515723/2500000000 : ℝ)^4293 ≤ (32427782686443/100000000000000 : ℝ)^3269 := by
    have hnat : (1060515723 : ℕ)^4293*100000000000000^3269 ≤ 32427782686443^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060515723 2500000000 32427782686443 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(451006123/1000000000 : ℝ), (132564457/312500000 : ℝ), (1060515723/2500000000 : ℝ)] ![(8786109325501/25000000000000 : ℝ), (16213889998009/50000000000000 : ℝ), (32427782686443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(451006123/1000000000 : ℝ)|^4293 ≤ (8786109325501/25000000000000 : ℝ)^3269
        have hw : |(451006123/1000000000 : ℝ)|=(451006123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132564457/312500000 : ℝ)|^4293 ≤ (16213889998009/50000000000000 : ℝ)^3269
        have hw : |(132564457/312500000 : ℝ)|=(132564457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060515723/2500000000 : ℝ)|^4293 ≤ (32427782686443/100000000000000 : ℝ)^3269
        have hw : |(1060515723/2500000000 : ℝ)|=(1060515723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_12 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955261407/10000000000 : ℝ)*x 0 + (5474504899/10000000000 : ℝ)*x 1 + (2626831643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955261407/10000000000 : ℝ)^4293 ≤ (11726754422861/100000000000000 : ℝ)^3269 := by
    have hnat : (1955261407 : ℕ)^4293*100000000000000^3269 ≤ 11726754422861^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955261407 10000000000 11726754422861 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474504899/10000000000 : ℝ)^4293 ≤ (45329665386193/100000000000000 : ℝ)^3269 := by
    have hnat : (5474504899 : ℕ)^4293*100000000000000^3269 ≤ 45329665386193^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474504899 10000000000 45329665386193 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626831643/5000000000 : ℝ)^4293 ≤ (8588716035761/20000000000000 : ℝ)^3269 := by
    have hnat : (2626831643 : ℕ)^4293*20000000000000^3269 ≤ 8588716035761^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626831643 5000000000 8588716035761 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955261407/10000000000 : ℝ), (5474504899/10000000000 : ℝ), (2626831643/5000000000 : ℝ)] ![(11726754422861/100000000000000 : ℝ), (45329665386193/100000000000000 : ℝ), (8588716035761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955261407/10000000000 : ℝ)|^4293 ≤ (11726754422861/100000000000000 : ℝ)^3269
        have hw : |(-1955261407/10000000000 : ℝ)|=(1955261407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474504899/10000000000 : ℝ)|^4293 ≤ (45329665386193/100000000000000 : ℝ)^3269
        have hw : |(5474504899/10000000000 : ℝ)|=(5474504899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626831643/5000000000 : ℝ)|^4293 ≤ (8588716035761/20000000000000 : ℝ)^3269
        have hw : |(2626831643/5000000000 : ℝ)|=(2626831643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_13 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538105363/1000000000 : ℝ)*x 0 + (-1041325839/5000000000 : ℝ)*x 1 + (2626831729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538105363/1000000000 : ℝ)^4293 ≤ (346220446487/781250000000 : ℝ)^3269 := by
    have hnat : (538105363 : ℕ)^4293*781250000000^3269 ≤ 346220446487^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538105363 1000000000 346220446487 781250000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041325839/5000000000 : ℝ)^4293 ≤ (12740200813359/100000000000000 : ℝ)^3269 := by
    have hnat : (1041325839 : ℕ)^4293*100000000000000^3269 ≤ 12740200813359^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041325839 5000000000 12740200813359 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626831729/5000000000 : ℝ)^4293 ≤ (42943582025139/100000000000000 : ℝ)^3269 := by
    have hnat : (2626831729 : ℕ)^4293*100000000000000^3269 ≤ 42943582025139^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626831729 5000000000 42943582025139 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538105363/1000000000 : ℝ), (-1041325839/5000000000 : ℝ), (2626831729/5000000000 : ℝ)] ![(346220446487/781250000000 : ℝ), (12740200813359/100000000000000 : ℝ), (42943582025139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538105363/1000000000 : ℝ)|^4293 ≤ (346220446487/781250000000 : ℝ)^3269
        have hw : |(538105363/1000000000 : ℝ)|=(538105363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041325839/5000000000 : ℝ)|^4293 ≤ (12740200813359/100000000000000 : ℝ)^3269
        have hw : |(-1041325839/5000000000 : ℝ)|=(1041325839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626831729/5000000000 : ℝ)|^4293 ≤ (42943582025139/100000000000000 : ℝ)^3269
        have hw : |(2626831729/5000000000 : ℝ)|=(2626831729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_14 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690526789/5000000000 : ℝ)*x 0 + (5253663303/10000000000 : ℝ)*x 1 + (-520662989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690526789/5000000000 : ℝ)^4293 ≤ (44316216587937/100000000000000 : ℝ)^3269 := by
    have hnat : (2690526789 : ℕ)^4293*100000000000000^3269 ≤ 44316216587937^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690526789 5000000000 44316216587937 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253663303/10000000000 : ℝ)^4293 ≤ (42943580361291/100000000000000 : ℝ)^3269 := by
    have hnat : (5253663303 : ℕ)^4293*100000000000000^3269 ≤ 42943580361291^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253663303 10000000000 42943580361291 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520662989/2500000000 : ℝ)^4293 ≤ (3185050761669/25000000000000 : ℝ)^3269 := by
    have hnat : (520662989 : ℕ)^4293*25000000000000^3269 ≤ 3185050761669^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520662989 2500000000 3185050761669 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690526789/5000000000 : ℝ), (5253663303/10000000000 : ℝ), (-520662989/2500000000 : ℝ)] ![(44316216587937/100000000000000 : ℝ), (42943580361291/100000000000000 : ℝ), (3185050761669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690526789/5000000000 : ℝ)|^4293 ≤ (44316216587937/100000000000000 : ℝ)^3269
        have hw : |(2690526789/5000000000 : ℝ)|=(2690526789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253663303/10000000000 : ℝ)|^4293 ≤ (42943580361291/100000000000000 : ℝ)^3269
        have hw : |(5253663303/10000000000 : ℝ)|=(5253663303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520662989/2500000000 : ℝ)|^4293 ≤ (3185050761669/25000000000000 : ℝ)^3269
        have hw : |(-520662989/2500000000 : ℝ)|=(520662989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_box_15 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153001247/10000000000 : ℝ)*x 0 + (4420587247/10000000000 : ℝ)*x 1 + (4420587259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153001247/10000000000 : ℝ)^4293 ≤ (31536656001481/100000000000000 : ℝ)^3269 := by
    have hnat : (4153001247 : ℕ)^4293*100000000000000^3269 ≤ 31536656001481^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153001247 10000000000 31536656001481 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420587247/10000000000 : ℝ)^4293 ≤ (1069739747919/3125000000000 : ℝ)^3269 := by
    have hnat : (4420587247 : ℕ)^4293*3125000000000^3269 ≤ 1069739747919^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420587247 10000000000 1069739747919 3125000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420587259/10000000000 : ℝ)^4293 ≤ (34231672055441/100000000000000 : ℝ)^3269 := by
    have hnat : (4420587259 : ℕ)^4293*100000000000000^3269 ≤ 34231672055441^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420587259 10000000000 34231672055441 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153001247/10000000000 : ℝ), (4420587247/10000000000 : ℝ), (4420587259/10000000000 : ℝ)] ![(31536656001481/100000000000000 : ℝ), (1069739747919/3125000000000 : ℝ), (34231672055441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153001247/10000000000 : ℝ)|^4293 ≤ (31536656001481/100000000000000 : ℝ)^3269
        have hw : |(4153001247/10000000000 : ℝ)|=(4153001247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420587247/10000000000 : ℝ)|^4293 ≤ (1069739747919/3125000000000 : ℝ)^3269
        have hw : |(4420587247/10000000000 : ℝ)|=(4420587247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420587259/10000000000 : ℝ)|^4293 ≤ (34231672055441/100000000000000 : ℝ)^3269
        have hw : |(4420587259/10000000000 : ℝ)|=(4420587259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15713/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14731/25000 : ℝ) ∧ (39951/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84317/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11129/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11129/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11129/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11129/100000 : ℝ) ^ (1073/256 : ℝ) ≤ (10076514070413431/100000000000000000000 : ℝ) := by
    have hpowers : (11129/100000 : ℝ)^1073 ≤ (10076514070413431/100000000000000000000 : ℝ)^256 := by
      have hnat : (11129 : ℕ)^1073*100000000000000000000^256 ≤ 10076514070413431^256*100000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11129 100000 10076514070413431 100000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11129/100000 : ℝ)) (X := (10076514070413431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (147/1000 : ℝ) ^ (1073/256 : ℝ) ≤ (2021941983109173/6250000000000000000 : ℝ) := by
    have hpowers : (147/1000 : ℝ)^1073 ≤ (2021941983109173/6250000000000000000 : ℝ)^256 := by
      have hnat : (147 : ℕ)^1073*6250000000000000000^256 ≤ 2021941983109173^256*1000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 1000 2021941983109173 6250000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/1000 : ℝ)) (X := (2021941983109173/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010076514070413431/50000000000000000000 : ℝ) ≤ (2000096156186711/2000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (50010076514070413431/50000000000000000000 : ℝ)^256 ≤ (2000096156186711/2000000000000000 : ℝ)^1073 := by
      have hnat : (50010076514070413431 : ℕ)^256*2000000000000000^1073 ≤ 2000096156186711^1073*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010076514070413431 50000000000000000000 2000096156186711 2000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000096156186711/2000000000000000 : ℝ)) (X := (50010076514070413431/50000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042427585800160199/100000000000000000000 : ℝ) ≤ (500050604417523/500000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100042427585800160199/100000000000000000000 : ℝ)^256 ≤ (500050604417523/500000000000000 : ℝ)^1073 := by
      have hnat : (100042427585800160199 : ℕ)^256*500000000000000^1073 ≤ 500050604417523^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042427585800160199 100000000000000000000 500050604417523 500000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500050604417523/500000000000000 : ℝ)) (X := (100042427585800160199/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127021941983109173/3125000000000000000 : ℝ) ≤ (2000308679153473/2000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (3127021941983109173/3125000000000000000 : ℝ)^256 ≤ (2000308679153473/2000000000000000 : ℝ)^1073 := by
      have hnat : (3127021941983109173 : ℕ)^256*2000000000000000^1073 ≤ 2000308679153473^1073*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127021941983109173 3125000000000000000 2000308679153473 2000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000308679153473/2000000000000000 : ℝ)) (X := (3127021941983109173/3125000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10076514070413431/100000000000000000000 : ℝ) ≤ ((7139978205645650683/7142000000000000000 : ℝ)+2*(106261483381/71420000000000 : ℝ)*(11129/100000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (7139978205645650683/7142000000000000000 : ℝ)+2*(106261483381/71420000000000 : ℝ)*(11129/100000 : ℝ)=(2000096156186711/2000000000000000 : ℝ) by norm_num, show 1+2*(10076514070413431/100000000000000000000 : ℝ)=(50010076514070413431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2021941983109173/6250000000000000000 : ℝ)+(10076514070413431/100000000000000000000 : ℝ) ≤ ((7139978205645650683/7142000000000000000 : ℝ)+(106261483381/71420000000000 : ℝ)*((147/1000 : ℝ)+(11129/100000 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (7139978205645650683/7142000000000000000 : ℝ)+(106261483381/71420000000000 : ℝ)*((147/1000 : ℝ)+(11129/100000 : ℝ))=(500050604417523/500000000000000 : ℝ) by norm_num, show 1+(2021941983109173/6250000000000000000 : ℝ)+(10076514070413431/100000000000000000000 : ℝ)=(100042427585800160199/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2021941983109173/6250000000000000000 : ℝ) ≤ ((7139978205645650683/7142000000000000000 : ℝ)+2*(106261483381/71420000000000 : ℝ)*(147/1000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (7139978205645650683/7142000000000000000 : ℝ)+2*(106261483381/71420000000000 : ℝ)*(147/1000 : ℝ)=(2000308679153473/2000000000000000 : ℝ) by norm_num, show 1+2*(2021941983109173/6250000000000000000 : ℝ)=(3127021941983109173/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7139978205645650683/7142000000000000000 : ℝ)*(X 1 0+X 2 0)+(106261483381/71420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (7139978205645650683/7142000000000000000 : ℝ)) (alpha := (106261483381/71420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7139978205645650683/7142000000000000000 : ℝ)*(X 0 1+X 2 1)+(106261483381/71420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (7139978205645650683/7142000000000000000 : ℝ)) (alpha := (106261483381/71420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7139978205645650683/7142000000000000000 : ℝ)*(X 0 2+X 1 2)+(106261483381/71420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (11129/100000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (7139978205645650683/7142000000000000000 : ℝ)) (alpha := (106261483381/71420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-941903183/5000000000 : ℝ)*X 0 0+(5390313839/10000000000 : ℝ)*X 0 1+(168447309/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285038661/10000000000 : ℝ)*X 1 0+(-2027991797/10000000000 : ℝ)*X 1 1+(539031417/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285038677/10000000000 : ℝ)*X 2 0+(539031413/1000000000 : ℝ)*X 2 1+(-2027991829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((223868981/500000000 : ℝ)*X 0 0+(532336383/1250000000 : ℝ)*X 0 1+(2129345499/5000000000 : ℝ)*X 0 2+(223868981/500000000 : ℝ)*X 1 0+(532336383/1250000000 : ℝ)*X 1 1+(2129345499/5000000000 : ℝ)*X 1 2+(223868981/500000000 : ℝ)*X 2 0+(532336383/1250000000 : ℝ)*X 2 1+(2129345499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55562403/250000000 : ℝ)*X 0 0+(1316181347/2500000000 : ℝ)*X 0 1+(658090527/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373283357/10000000000 : ℝ)*X 1 0+(-2078322887/10000000000 : ℝ)*X 1 1+(658090673/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((167915111/312500000 : ℝ)*X 2 0+(1052945101/2000000000 : ℝ)*X 2 1+(-2078322463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835933879/2000000000 : ℝ)*X 0 0+(4407491879/10000000000 : ℝ)*X 0 1+(2203746301/5000000000 : ℝ)*X 0 2+(835933879/2000000000 : ℝ)*X 1 0+(4407491879/10000000000 : ℝ)*X 1 1+(2203746301/5000000000 : ℝ)*X 1 2+(835933879/2000000000 : ℝ)*X 2 0+(4407491879/10000000000 : ℝ)*X 2 1+(2203746301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1075698051/5000000000 : ℝ)*X 0 0+(5178308141/10000000000 : ℝ)*X 0 1+(675542089/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((131879499/250000000 : ℝ)*X 1 0+(-40444769/200000000 : ℝ)*X 1 1+(675542183/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275180729/10000000000 : ℝ)*X 2 0+(2702168377/5000000000 : ℝ)*X 2 1+(-1011119189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((451006123/1000000000 : ℝ)*X 0 0+(132564457/312500000 : ℝ)*X 0 1+(1060515723/2500000000 : ℝ)*X 0 2+(451006123/1000000000 : ℝ)*X 1 0+(132564457/312500000 : ℝ)*X 1 1+(1060515723/2500000000 : ℝ)*X 1 2+(451006123/1000000000 : ℝ)*X 2 0+(132564457/312500000 : ℝ)*X 2 1+(1060515723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1955261407/10000000000 : ℝ)*X 0 0+(5474504899/10000000000 : ℝ)*X 0 1+(2626831643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538105363/1000000000 : ℝ)*X 1 0+(-1041325839/5000000000 : ℝ)*X 1 1+(2626831729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690526789/5000000000 : ℝ)*X 2 0+(5253663303/10000000000 : ℝ)*X 2 1+(-520662989/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4153001247/10000000000 : ℝ)*X 0 0+(4420587247/10000000000 : ℝ)*X 0 1+(4420587259/10000000000 : ℝ)*X 0 2+(4153001247/10000000000 : ℝ)*X 1 0+(4420587247/10000000000 : ℝ)*X 1 1+(4420587259/10000000000 : ℝ)*X 1 2+(4153001247/10000000000 : ℝ)*X 2 0+(4420587247/10000000000 : ℝ)*X 2 1+(4420587259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15713/25000 : ℝ) ≤ (-22443491544943624995447500626563/35710000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45889527/50000000000000 : ℝ)*(upper0) + (36368087/25000000000000 : ℝ)*(lower1) + (98541733/50000000000000 : ℝ)*(lower2) + (582124484133213/20000000000000 : ℝ)*(major0) + (582124484133213/20000000000000 : ℝ)*(major1) + (582124484133213/20000000000000 : ℝ)*(major2) + (1304420043/12500000000000 : ℝ)*(sp3) + (197837235567107/5000000000000 : ℝ)*(sp4) + (1978334479739577/50000000000000 : ℝ)*(sp5) + (1978257305676583/50000000000000 : ℝ)*(sp6) + (942712005731901/50000000000000 : ℝ)*(sp7) + (15455913847/100000000000000 : ℝ)*(sp8) + (91207776833/100000000000000 : ℝ)*(sp13) + (245555902821/100000000000000 : ℝ)*(sp14) + (942717223412073/50000000000000 : ℝ)*(f.failure) + (1978380083627993/50000000000000 : ℝ)*(f.sum) + (14276716640569/3571000000000000000000000000 : ℝ)*base65 + (1046250809755905521/142840000000000000000000000000000 : ℝ)*base68 + (1172904280801065521/142840000000000000000000000000000 : ℝ)*base70 + (333952598228185521/142840000000000000000000000000000 : ℝ)*base72 + (3384278440023/3571000000000000000000000000 : ℝ)*base73 + (2210379818223705521/142840000000000000000000000000000 : ℝ)*base76 + (198544151350134479/142840000000000000000000000000000 : ℝ)*base77 + (1731539686078545521/142840000000000000000000000000000 : ℝ)*base80 + (9412699238357/3571000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (842577/2500000000000000000000 : ℝ)*base89 + (842577/2500000000000000000000 : ℝ)*base91 + (842577/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14731/25000 : ℝ) ≤ (13151609185195711555549962617799/22318750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20320033/100000000000000 : ℝ)*(lower0) + (410743/12500000000000 : ℝ)*(lower1) + (341617/4000000000000 : ℝ)*(lower4) + (372376806665749/12500000000000 : ℝ)*(major0) + (372376806665749/12500000000000 : ℝ)*(major1) + (372376806665749/12500000000000 : ℝ)*(major2) + (1002162305123759/25000000000000 : ℝ)*(sp0) + (4008640449687069/100000000000000 : ℝ)*(sp1) + (250540134021137/6250000000000 : ℝ)*(sp2) + (1929735292066493/100000000000000 : ℝ)*(sp3) + (9126571203/100000000000000 : ℝ)*(sp5) + (7431920081/100000000000000 : ℝ)*(sp6) + (972446387/50000000000000 : ℝ)*(sp7) + (88940809/25000000000000 : ℝ)*(sp12) + (482434309239817/25000000000000 : ℝ)*(f.failure) + (125270299258071/3125000000000 : ℝ)*(f.sum) + (128666104569/71420000000000000000000000 : ℝ)*base65 + (500251195609306567/89275000000000000000000000000000 : ℝ)*base67 + (430303861725306567/89275000000000000000000000000000 : ℝ)*base69 + (343879765647206567/89275000000000000000000000000000 : ℝ)*base71 + (4317275585257/892750000000000000000000000 : ℝ)*base73 + (149411571238356567/89275000000000000000000000000000 : ℝ)*base75 + (167837090246193433/89275000000000000000000000000000 : ℝ)*base78 + (1031355089689631567/89275000000000000000000000000000 : ℝ)*base79 + (2401288525209/3571000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7530033/1250000000000000000000 : ℝ)*base89 + (7530033/1250000000000000000000 : ℝ)*base91 + (7530033/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (39951/50000 : ℝ) ≤ (71334392177568218259504622912779/89275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82848207/20000000000000 : ℝ)*(lower3) + (53967453/50000000000000 : ℝ)*(upper4) + (47426989/25000000000000 : ℝ)*(lower5) + (822884761739257/25000000000000 : ℝ)*(major0) + (822884761739257/25000000000000 : ℝ)*(major1) + (822884761739257/25000000000000 : ℝ)*(major2) + (15613709803/50000000000000 : ℝ)*(sp0) + (563872539223/100000000000000 : ℝ)*(sp1) + (328277647081/100000000000000 : ℝ)*(sp2) + (98999527827/50000000000000 : ℝ)*(sp3) + (2212114331593499/50000000000000 : ℝ)*(sp8) + (221184800903369/5000000000000 : ℝ)*(sp9) + (2211965806479761/50000000000000 : ℝ)*(sp10) + (53299637541863/2500000000000 : ℝ)*(sp11) + (1066091750365087/50000000000000 : ℝ)*(f.failure) + (1106064972651651/25000000000000 : ℝ)*(f.sum) + (1008060980899/178550000000000000000000000 : ℝ)*base66 + (1072852388490737469/178550000000000000000000000000000 : ℝ)*base68 + (2622537608946137469/178550000000000000000000000000000 : ℝ)*base70 + (712224560987987469/178550000000000000000000000000000 : ℝ)*base72 + (38859561679787/3571000000000000000000000000 : ℝ)*base74 + (1799467733113437469/178550000000000000000000000000000 : ℝ)*base76 + (1435887384598587469/178550000000000000000000000000000 : ℝ)*base78 + (18683897820037469/178550000000000000000000000000000 : ℝ)*base80 + (16290757625589/3571000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38158263/2500000000000000000000 : ℝ)*base89 + (38158263/2500000000000000000000 : ℝ)*base91 + (38158263/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84317/100000 : ℝ) ≤ (-301086437542285548890263717494747/357100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46559197/100000000000000 : ℝ)*(lower0) + (11743753/50000000000000 : ℝ)*(upper3) + (119102941/100000000000000 : ℝ)*(lower4) + (3327881458568597/100000000000000 : ℝ)*(major0) + (3327881458568597/100000000000000 : ℝ)*(major1) + (3327881458568597/100000000000000 : ℝ)*(major2) + (1235707401/100000000000000 : ℝ)*(sp4) + (122981055021/100000000000000 : ℝ)*(sp6) + (59413605339/100000000000000 : ℝ)*(sp7) + (3519514873/100000000000000 : ℝ)*(sp8) + (283008603368313/6250000000000 : ℝ)*(sp12) + (4528142409115281/100000000000000 : ℝ)*(sp13) + (226400971403013/5000000000000 : ℝ)*(sp14) + (538916466956663/25000000000000 : ℝ)*(sp15) + (2155725281431991/100000000000000 : ℝ)*(f.failure) + (4528142409115281/100000000000000 : ℝ)*(f.sum) + (7750448169423/178550000000000000000000000 : ℝ)*base66 + (7381768009250498249/714200000000000000000000000000000 : ℝ)*base68 + (10811142526348098249/714200000000000000000000000000000 : ℝ)*base70 + (4247134868499301751/714200000000000000000000000000000 : ℝ)*base71 + (143826691/1394921875000000000000000 : ℝ)*base73 + (5296345251443698249/714200000000000000000000000000000 : ℝ)*base76 + (2684465269657098249/714200000000000000000000000000000 : ℝ)*base78 + (4635985750079101751/714200000000000000000000000000000 : ℝ)*base79 + (3088431853529/892750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (29484559/5000000000000000000000 : ℝ)*base89 + (29484559/5000000000000000000000 : ℝ)*base91 + (29484559/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14731/25000 : ℝ) else (39951/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84317/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1333_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1333_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14731/25000 : ℝ) else (39951/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84317/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1333_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15713/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14731/25000 : ℝ) else (39951/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84317/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

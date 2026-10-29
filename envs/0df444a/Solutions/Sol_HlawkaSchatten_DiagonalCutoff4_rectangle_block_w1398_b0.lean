-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:40.566131+00:00
-- url     : https://prove2.me/submissions/23da3d23-1e4a-4e9b-8025-273525d3ce2d

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
theorem support_rectangle_w1398_s0_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-888249759/5000000000 : ℝ)*x 0 + (2986539513/5000000000 : ℝ)*x 1 + (4824093179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888249759/5000000000 : ℝ)^2179 ≤ (10449068791521/100000000000000 : ℝ)^1667 := by
    have hnat : (888249759 : ℕ)^2179*100000000000000^1667 ≤ 10449068791521^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888249759 5000000000 10449068791521 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2986539513/5000000000 : ℝ)^2179 ≤ (50987076838511/100000000000000 : ℝ)^1667 := by
    have hnat : (2986539513 : ℕ)^2179*100000000000000^1667 ≤ 50987076838511^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2986539513 5000000000 50987076838511 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4824093179/10000000000 : ℝ)^2179 ≤ (19281927182239/50000000000000 : ℝ)^1667 := by
    have hnat : (4824093179 : ℕ)^2179*50000000000000^1667 ≤ 19281927182239^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824093179 10000000000 19281927182239 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-888249759/5000000000 : ℝ), (2986539513/5000000000 : ℝ), (4824093179/10000000000 : ℝ)] ![(10449068791521/100000000000000 : ℝ), (50987076838511/100000000000000 : ℝ), (19281927182239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-888249759/5000000000 : ℝ)|^2179 ≤ (10449068791521/100000000000000 : ℝ)^1667
        have hw : |(-888249759/5000000000 : ℝ)|=(888249759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2986539513/5000000000 : ℝ)|^2179 ≤ (50987076838511/100000000000000 : ℝ)^1667
        have hw : |(2986539513/5000000000 : ℝ)|=(2986539513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4824093179/10000000000 : ℝ)|^2179 ≤ (19281927182239/50000000000000 : ℝ)^1667
        have hw : |(4824093179/10000000000 : ℝ)|=(4824093179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1373888121/2500000000 : ℝ)*x 0 + (-606741401/2500000000 : ℝ)*x 1 + (1206023341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373888121/2500000000 : ℝ)^2179 ≤ (45725537587491/100000000000000 : ℝ)^1667 := by
    have hnat : (1373888121 : ℕ)^2179*100000000000000^1667 ≤ 45725537587491^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373888121 2500000000 45725537587491 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606741401/2500000000 : ℝ)^2179 ≤ (1571060609867/10000000000000 : ℝ)^1667 := by
    have hnat : (606741401 : ℕ)^2179*10000000000000^1667 ≤ 1571060609867^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606741401 2500000000 1571060609867 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206023341/2500000000 : ℝ)^2179 ≤ (7712771259519/20000000000000 : ℝ)^1667 := by
    have hnat : (1206023341 : ℕ)^2179*20000000000000^1667 ≤ 7712771259519^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206023341 2500000000 7712771259519 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373888121/2500000000 : ℝ), (-606741401/2500000000 : ℝ), (1206023341/2500000000 : ℝ)] ![(45725537587491/100000000000000 : ℝ), (1571060609867/10000000000000 : ℝ), (7712771259519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373888121/2500000000 : ℝ)|^2179 ≤ (45725537587491/100000000000000 : ℝ)^1667
        have hw : |(1373888121/2500000000 : ℝ)|=(1373888121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-606741401/2500000000 : ℝ)|^2179 ≤ (1571060609867/10000000000000 : ℝ)^1667
        have hw : |(-606741401/2500000000 : ℝ)|=(606741401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206023341/2500000000 : ℝ)|^2179 ≤ (7712771259519/20000000000000 : ℝ)^1667
        have hw : |(1206023341/2500000000 : ℝ)|=(1206023341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1099110499/2000000000 : ℝ)*x 0 + (603011667/1250000000 : ℝ)*x 1 + (-303370703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099110499/2000000000 : ℝ)^2179 ≤ (45725537707127/100000000000000 : ℝ)^1667 := by
    have hnat : (1099110499 : ℕ)^2179*100000000000000^1667 ≤ 45725537707127^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099110499 2000000000 45725537707127 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603011667/1250000000 : ℝ)^2179 ≤ (7712771201003/20000000000000 : ℝ)^1667 := by
    have hnat : (603011667 : ℕ)^2179*20000000000000^1667 ≤ 7712771201003^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603011667 1250000000 7712771201003 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303370703/1250000000 : ℝ)^2179 ≤ (15710606267901/100000000000000 : ℝ)^1667 := by
    have hnat : (303370703 : ℕ)^2179*100000000000000^1667 ≤ 15710606267901^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303370703 1250000000 15710606267901 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099110499/2000000000 : ℝ), (603011667/1250000000 : ℝ), (-303370703/1250000000 : ℝ)] ![(45725537707127/100000000000000 : ℝ), (7712771201003/20000000000000 : ℝ), (15710606267901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099110499/2000000000 : ℝ)|^2179 ≤ (45725537707127/100000000000000 : ℝ)^1667
        have hw : |(1099110499/2000000000 : ℝ)|=(1099110499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603011667/1250000000 : ℝ)|^2179 ≤ (7712771201003/20000000000000 : ℝ)^1667
        have hw : |(603011667/1250000000 : ℝ)|=(603011667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303370703/1250000000 : ℝ)|^2179 ≤ (15710606267901/100000000000000 : ℝ)^1667
        have hw : |(-303370703/1250000000 : ℝ)|=(303370703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2085240241/5000000000 : ℝ)*x 0 + (776063267/2500000000 : ℝ)*x 1 + (347605611/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085240241/5000000000 : ℝ)^2179 ≤ (255047211063/800000000000 : ℝ)^1667 := by
    have hnat : (2085240241 : ℕ)^2179*800000000000^1667 ≤ 255047211063^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085240241 5000000000 255047211063 800000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776063267/2500000000 : ℝ)^2179 ≤ (21672926286987/100000000000000 : ℝ)^1667 := by
    have hnat : (776063267 : ℕ)^2179*100000000000000^1667 ≤ 21672926286987^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776063267 2500000000 21672926286987 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347605611/625000000 : ℝ)^2179 ≤ (5805771539671/12500000000000 : ℝ)^1667 := by
    have hnat : (347605611 : ℕ)^2179*12500000000000^1667 ≤ 5805771539671^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347605611 625000000 5805771539671 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2085240241/5000000000 : ℝ), (776063267/2500000000 : ℝ), (347605611/625000000 : ℝ)] ![(255047211063/800000000000 : ℝ), (21672926286987/100000000000000 : ℝ), (5805771539671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2085240241/5000000000 : ℝ)|^2179 ≤ (255047211063/800000000000 : ℝ)^1667
        have hw : |(2085240241/5000000000 : ℝ)|=(2085240241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776063267/2500000000 : ℝ)|^2179 ≤ (21672926286987/100000000000000 : ℝ)^1667
        have hw : |(776063267/2500000000 : ℝ)|=(776063267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(347605611/625000000 : ℝ)|^2179 ≤ (5805771539671/12500000000000 : ℝ)^1667
        have hw : |(347605611/625000000 : ℝ)|=(347605611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1780669833/10000000000 : ℝ)*x 0 + (2426778983/5000000000 : ℝ)*x 1 + (2971280577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1780669833/10000000000 : ℝ)^2179 ≤ (327535726801/3125000000000 : ℝ)^1667 := by
    have hnat : (1780669833 : ℕ)^2179*3125000000000^1667 ≤ 327535726801^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780669833 10000000000 327535726801 3125000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2426778983/5000000000 : ℝ)^2179 ≤ (38872028564433/100000000000000 : ℝ)^1667 := by
    have hnat : (2426778983 : ℕ)^2179*100000000000000^1667 ≤ 38872028564433^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426778983 5000000000 38872028564433 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2971280577/5000000000 : ℝ)^2179 ≤ (50646828167989/100000000000000 : ℝ)^1667 := by
    have hnat : (2971280577 : ℕ)^2179*100000000000000^1667 ≤ 50646828167989^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2971280577 5000000000 50646828167989 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1780669833/10000000000 : ℝ), (2426778983/5000000000 : ℝ), (2971280577/5000000000 : ℝ)] ![(327535726801/3125000000000 : ℝ), (38872028564433/100000000000000 : ℝ), (50646828167989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1780669833/10000000000 : ℝ)|^2179 ≤ (327535726801/3125000000000 : ℝ)^1667
        have hw : |(-1780669833/10000000000 : ℝ)|=(1780669833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2426778983/5000000000 : ℝ)|^2179 ≤ (38872028564433/100000000000000 : ℝ)^1667
        have hw : |(2426778983/5000000000 : ℝ)|=(2426778983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2971280577/5000000000 : ℝ)|^2179 ≤ (50646828167989/100000000000000 : ℝ)^1667
        have hw : |(2971280577/5000000000 : ℝ)|=(2971280577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2591051039/5000000000 : ℝ)*x 0 + (-1308496687/10000000000 : ℝ)*x 1 + (5942559671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591051039/5000000000 : ℝ)^2179 ≤ (8469343131427/20000000000000 : ℝ)^1667 := by
    have hnat : (2591051039 : ℕ)^2179*20000000000000^1667 ≤ 8469343131427^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591051039 5000000000 8469343131427 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308496687/10000000000 : ℝ)^2179 ≤ (3503236341843/50000000000000 : ℝ)^1667 := by
    have hnat : (1308496687 : ℕ)^2179*50000000000000^1667 ≤ 3503236341843^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308496687 10000000000 3503236341843 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5942559671/10000000000 : ℝ)^2179 ≤ (25323405823399/50000000000000 : ℝ)^1667 := by
    have hnat : (5942559671 : ℕ)^2179*50000000000000^1667 ≤ 25323405823399^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942559671 10000000000 25323405823399 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591051039/5000000000 : ℝ), (-1308496687/10000000000 : ℝ), (5942559671/10000000000 : ℝ)] ![(8469343131427/20000000000000 : ℝ), (3503236341843/50000000000000 : ℝ), (25323405823399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591051039/5000000000 : ℝ)|^2179 ≤ (8469343131427/20000000000000 : ℝ)^1667
        have hw : |(2591051039/5000000000 : ℝ)|=(2591051039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1308496687/10000000000 : ℝ)|^2179 ≤ (3503236341843/50000000000000 : ℝ)^1667
        have hw : |(-1308496687/10000000000 : ℝ)|=(1308496687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5942559671/10000000000 : ℝ)|^2179 ≤ (25323405823399/50000000000000 : ℝ)^1667
        have hw : |(5942559671/10000000000 : ℝ)|=(5942559671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5182097913/10000000000 : ℝ)*x 0 + (297128193/500000000 : ℝ)*x 1 + (-10467971/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182097913/10000000000 : ℝ)^2179 ≤ (4234667116837/10000000000000 : ℝ)^1667 := by
    have hnat : (5182097913 : ℕ)^2179*10000000000000^1667 ≤ 4234667116837^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182097913 10000000000 4234667116837 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297128193/500000000 : ℝ)^2179 ≤ (25323429156937/50000000000000 : ℝ)^1667 := by
    have hnat : (297128193 : ℕ)^2179*50000000000000^1667 ≤ 25323429156937^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297128193 500000000 25323429156937 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10467971/80000000 : ℝ)^2179 ≤ (218952203123/3125000000000 : ℝ)^1667 := by
    have hnat : (10467971 : ℕ)^2179*3125000000000^1667 ≤ 218952203123^1667*80000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10467971 80000000 218952203123 3125000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182097913/10000000000 : ℝ), (297128193/500000000 : ℝ), (-10467971/80000000 : ℝ)] ![(4234667116837/10000000000000 : ℝ), (25323429156937/50000000000000 : ℝ), (218952203123/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182097913/10000000000 : ℝ)|^2179 ≤ (4234667116837/10000000000000 : ℝ)^1667
        have hw : |(5182097913/10000000000 : ℝ)|=(5182097913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297128193/500000000 : ℝ)|^2179 ≤ (25323429156937/50000000000000 : ℝ)^1667
        have hw : |(297128193/500000000 : ℝ)|=(297128193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10467971/80000000 : ℝ)|^2179 ≤ (218952203123/3125000000000 : ℝ)^1667
        have hw : |(-10467971/80000000 : ℝ)|=(10467971/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s0_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089697343/5000000000 : ℝ)*x 0 + (5498671617/10000000000 : ℝ)*x 1 + (3169526881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089697343/5000000000 : ℝ)^2179 ≤ (31970004143573/100000000000000 : ℝ)^1667 := by
    have hnat : (2089697343 : ℕ)^2179*100000000000000^1667 ≤ 31970004143573^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089697343 5000000000 31970004143573 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498671617/10000000000 : ℝ)^2179 ≤ (45759464226011/100000000000000 : ℝ)^1667 := by
    have hnat : (5498671617 : ℕ)^2179*100000000000000^1667 ≤ 45759464226011^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498671617 10000000000 45759464226011 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169526881/10000000000 : ℝ)^2179 ≤ (890821264311/4000000000000 : ℝ)^1667 := by
    have hnat : (3169526881 : ℕ)^2179*4000000000000^1667 ≤ 890821264311^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169526881 10000000000 890821264311 4000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089697343/5000000000 : ℝ), (5498671617/10000000000 : ℝ), (3169526881/10000000000 : ℝ)] ![(31970004143573/100000000000000 : ℝ), (45759464226011/100000000000000 : ℝ), (890821264311/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089697343/5000000000 : ℝ)|^2179 ≤ (31970004143573/100000000000000 : ℝ)^1667
        have hw : |(2089697343/5000000000 : ℝ)|=(2089697343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498671617/10000000000 : ℝ)|^2179 ≤ (45759464226011/100000000000000 : ℝ)^1667
        have hw : |(5498671617/10000000000 : ℝ)|=(5498671617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169526881/10000000000 : ℝ)|^2179 ≤ (890821264311/4000000000000 : ℝ)^1667
        have hw : |(3169526881/10000000000 : ℝ)|=(3169526881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (913/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13237/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4357/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4357 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4357*1^1024 ≤ 0^1024*1^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4357/1024 : ℝ) ≤ (1013402335954636427/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4357 ≤ (1013402335954636427/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4357*50000000000000000000^1024 ≤ 1013402335954636427^1024*5^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1013402335954636427 50000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1013402335954636427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4357 := by
      have hnat : (1 : ℕ)^1024*1^4357 ≤ 1^4357*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51013402335954636427/50000000000000000000 : ℝ) ≤ (125590873229591/125000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (51013402335954636427/50000000000000000000 : ℝ)^1024 ≤ (125590873229591/125000000000000 : ℝ)^4357 := by
      have hnat : (51013402335954636427 : ℕ)^1024*125000000000000^4357 ≤ 125590873229591^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51013402335954636427 50000000000000000000 125590873229591 125000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125590873229591/125000000000000 : ℝ)) (X := (51013402335954636427/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26013402335954636427/25000000000000000000 : ℝ) ≤ (63090873229591/62500000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (26013402335954636427/25000000000000000000 : ℝ)^1024 ≤ (63090873229591/62500000000000 : ℝ)^4357 := by
      have hnat : (26013402335954636427 : ℕ)^1024*62500000000000^4357 ≤ 63090873229591^4357*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26013402335954636427 25000000000000000000 63090873229591 62500000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (63090873229591/62500000000000 : ℝ)) (X := (26013402335954636427/25000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(590873229591/50000000000000 : ℝ)*(0 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(590873229591/50000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1013402335954636427/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(590873229591/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (1 : ℝ)+(590873229591/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(125590873229591/125000000000000 : ℝ) by norm_num, show 1+(1013402335954636427/50000000000000000000 : ℝ)+(0 : ℝ)=(51013402335954636427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1013402335954636427/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(590873229591/50000000000000 : ℝ)*(2/5 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(590873229591/50000000000000 : ℝ)*(2/5 : ℝ)=(63090873229591/62500000000000 : ℝ) by norm_num, show 1+2*(1013402335954636427/50000000000000000000 : ℝ)=(26013402335954636427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(590873229591/50000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (590873229591/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(590873229591/50000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (590873229591/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(590873229591/50000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (590873229591/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-888249759/5000000000 : ℝ)*X 0 0+(2986539513/5000000000 : ℝ)*X 0 1+(4824093179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1373888121/2500000000 : ℝ)*X 1 0+(-606741401/2500000000 : ℝ)*X 1 1+(1206023341/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099110499/2000000000 : ℝ)*X 2 0+(603011667/1250000000 : ℝ)*X 2 1+(-303370703/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2085240241/5000000000 : ℝ)*X 0 0+(776063267/2500000000 : ℝ)*X 0 1+(347605611/625000000 : ℝ)*X 0 2+(2085240241/5000000000 : ℝ)*X 1 0+(776063267/2500000000 : ℝ)*X 1 1+(347605611/625000000 : ℝ)*X 1 2+(2085240241/5000000000 : ℝ)*X 2 0+(776063267/2500000000 : ℝ)*X 2 1+(347605611/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1780669833/10000000000 : ℝ)*X 0 0+(2426778983/5000000000 : ℝ)*X 0 1+(2971280577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591051039/5000000000 : ℝ)*X 1 0+(-1308496687/10000000000 : ℝ)*X 1 1+(5942559671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182097913/10000000000 : ℝ)*X 2 0+(297128193/500000000 : ℝ)*X 2 1+(-10467971/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089697343/5000000000 : ℝ)*X 0 0+(5498671617/10000000000 : ℝ)*X 0 1+(3169526881/10000000000 : ℝ)*X 0 2+(2089697343/5000000000 : ℝ)*X 1 0+(5498671617/10000000000 : ℝ)*X 1 1+(3169526881/10000000000 : ℝ)*X 1 2+(2089697343/5000000000 : ℝ)*X 2 0+(5498671617/10000000000 : ℝ)*X 2 1+(3169526881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9358475450500518494103/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11293853/20000000000000 : ℝ)*(base1) + (347616077/20000000000000 : ℝ)*(base19) + (1739822479/100000000000000 : ℝ)*(base23) + (109557451/50000000000000 : ℝ)*(upper3) + (6698739/3125000000000 : ℝ)*(upper5) + (319319551343737/50000000000000 : ℝ)*(major0) + (319319551343737/50000000000000 : ℝ)*(major1) + (319319551343737/50000000000000 : ℝ)*(major2) + (217584609956063/25000000000000 : ℝ)*(sp0) + (870342629883581/100000000000000 : ℝ)*(sp1) + (870342628141487/100000000000000 : ℝ)*(sp2) + (406930725181543/100000000000000 : ℝ)*(sp3) + (5984608979/100000000000000 : ℝ)*(sp4) + (112248033/4000000000000 : ℝ)*(sp7) + (406933587851633/100000000000000 : ℝ)*(f.failure) + (435172183981983/50000000000000 : ℝ)*(f.sum) + (1916312369683/1250000000000000000000000000 : ℝ)*base66 + (16755347115933/2500000000000000000000000000 : ℝ)*base68 + (7310310754067/2500000000000000000000000000 : ℝ)*base69 + (9568351278433/2500000000000000000000000000 : ℝ)*base72 + (7141114109683/1250000000000000000000000000 : ℝ)*base74 + (4383883270933/2500000000000000000000000000 : ℝ)*base76 + (9319588430933/2500000000000000000000000000 : ℝ)*base78 + (10090135530933/2500000000000000000000000000 : ℝ)*base80 + (760413040317/1250000000000000000000000000 : ℝ)*base81 + (57078769/10000000000000000000000 : ℝ)*base89 + (57078769/10000000000000000000000 : ℝ)*base91 + (57078769/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11624973624294393700113/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12076297/625000000000 : ℝ)*(base19) + (1840799143/100000000000000 : ℝ)*(base23) + (602273877/100000000000000 : ℝ)*(base39) + (65692187/100000000000000 : ℝ)*(upper2) + (218077283/50000000000000 : ℝ)*(upper5) + (168451102172321/25000000000000 : ℝ)*(major0) + (168451102172321/25000000000000 : ℝ)*(major1) + (336901903207703/50000000000000 : ℝ)*(major2) + (2895941587/50000000000000 : ℝ)*(sp1) + (4656387531/100000000000000 : ℝ)*(sp2) + (918267383386099/100000000000000 : ℝ)*(sp4) + (183651931859081/20000000000000 : ℝ)*(sp5) + (918261488473303/100000000000000 : ℝ)*(sp6) + (53667565214911/12500000000000 : ℝ)*(sp7) + (53667565214911/12500000000000 : ℝ)*(f.failure) + (918267985659977/100000000000000 : ℝ)*(f.sum) + (1864178962321/500000000000000000000000000 : ℝ)*base66 + (15398670414473/2500000000000000000000000000 : ℝ)*base67 + (2866395366789/1250000000000000000000000000 : ℝ)*base70 + (4877180304473/2500000000000000000000000000 : ℝ)*base71 + (2577907905679/500000000000000000000000000 : ℝ)*base73 + (5221733923039/1250000000000000000000000000 : ℝ)*base76 + (2871621714289/1250000000000000000000000000 : ℝ)*base78 + (224738735711/1250000000000000000000000000 : ℝ)*base79 + (8831593583/78125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3110977/1250000000000000000000 : ℝ)*base90 + (3110977/1250000000000000000000 : ℝ)*base92 + (9389023/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1398_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (913/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13237/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1398_s1_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953265893/10000000000 : ℝ)*x 0 + (5617911279/10000000000 : ℝ)*x 1 + (1266497349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953265893/10000000000 : ℝ)^2179 ≤ (5914211205433/50000000000000 : ℝ)^1667 := by
    have hnat : (1953265893 : ℕ)^2179*50000000000000^1667 ≤ 5914211205433^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953265893 10000000000 5914211205433 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5617911279/10000000000 : ℝ)^2179 ≤ (47060838550837/100000000000000 : ℝ)^1667 := by
    have hnat : (5617911279 : ℕ)^2179*100000000000000^1667 ≤ 47060838550837^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617911279 10000000000 47060838550837 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266497349/2500000000 : ℝ)^2179 ≤ (41110739023891/100000000000000 : ℝ)^1667 := by
    have hnat : (1266497349 : ℕ)^2179*100000000000000^1667 ≤ 41110739023891^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266497349 2500000000 41110739023891 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953265893/10000000000 : ℝ), (5617911279/10000000000 : ℝ), (1266497349/2500000000 : ℝ)] ![(5914211205433/50000000000000 : ℝ), (47060838550837/100000000000000 : ℝ), (41110739023891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953265893/10000000000 : ℝ)|^2179 ≤ (5914211205433/50000000000000 : ℝ)^1667
        have hw : |(-1953265893/10000000000 : ℝ)|=(1953265893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5617911279/10000000000 : ℝ)|^2179 ≤ (47060838550837/100000000000000 : ℝ)^1667
        have hw : |(5617911279/10000000000 : ℝ)|=(5617911279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1266497349/2500000000 : ℝ)|^2179 ≤ (41110739023891/100000000000000 : ℝ)^1667
        have hw : |(1266497349/2500000000 : ℝ)|=(1266497349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5399945971/10000000000 : ℝ)*x 0 + (-2246428053/10000000000 : ℝ)*x 1 + (5065990751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399945971/10000000000 : ℝ)^2179 ≤ (44688510686913/100000000000000 : ℝ)^1667 := by
    have hnat : (5399945971 : ℕ)^2179*100000000000000^1667 ≤ 44688510686913^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399945971 10000000000 44688510686913 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246428053/10000000000 : ℝ)^2179 ≤ (3550183973529/25000000000000 : ℝ)^1667 := by
    have hnat : (2246428053 : ℕ)^2179*25000000000000^1667 ≤ 3550183973529^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246428053 10000000000 3550183973529 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5065990751/10000000000 : ℝ)^2179 ≤ (41110753397041/100000000000000 : ℝ)^1667 := by
    have hnat : (5065990751 : ℕ)^2179*100000000000000^1667 ≤ 41110753397041^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065990751 10000000000 41110753397041 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399945971/10000000000 : ℝ), (-2246428053/10000000000 : ℝ), (5065990751/10000000000 : ℝ)] ![(44688510686913/100000000000000 : ℝ), (3550183973529/25000000000000 : ℝ), (41110753397041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399945971/10000000000 : ℝ)|^2179 ≤ (44688510686913/100000000000000 : ℝ)^1667
        have hw : |(5399945971/10000000000 : ℝ)|=(5399945971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246428053/10000000000 : ℝ)|^2179 ≤ (3550183973529/25000000000000 : ℝ)^1667
        have hw : |(-2246428053/10000000000 : ℝ)|=(2246428053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5065990751/10000000000 : ℝ)|^2179 ≤ (41110753397041/100000000000000 : ℝ)^1667
        have hw : |(5065990751/10000000000 : ℝ)|=(5065990751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5399946891/10000000000 : ℝ)*x 0 + (253299479/500000000 : ℝ)*x 1 + (-1123214177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399946891/10000000000 : ℝ)^2179 ≤ (139651626997/312500000000 : ℝ)^1667 := by
    have hnat : (5399946891 : ℕ)^2179*312500000000^1667 ≤ 139651626997^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399946891 10000000000 139651626997 312500000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253299479/500000000 : ℝ)^2179 ≤ (4111074097567/10000000000000 : ℝ)^1667 := by
    have hnat : (253299479 : ℕ)^2179*10000000000000^1667 ≤ 4111074097567^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253299479 500000000 4111074097567 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123214177/5000000000 : ℝ)^2179 ≤ (3550184595323/25000000000000 : ℝ)^1667 := by
    have hnat : (1123214177 : ℕ)^2179*25000000000000^1667 ≤ 3550184595323^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123214177 5000000000 3550184595323 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399946891/10000000000 : ℝ), (253299479/500000000 : ℝ), (-1123214177/5000000000 : ℝ)] ![(139651626997/312500000000 : ℝ), (4111074097567/10000000000000 : ℝ), (3550184595323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399946891/10000000000 : ℝ)|^2179 ≤ (139651626997/312500000000 : ℝ)^1667
        have hw : |(5399946891/10000000000 : ℝ)|=(5399946891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(253299479/500000000 : ℝ)|^2179 ≤ (4111074097567/10000000000000 : ℝ)^1667
        have hw : |(253299479/500000000 : ℝ)|=(253299479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123214177/5000000000 : ℝ)|^2179 ≤ (3550184595323/25000000000000 : ℝ)^1667
        have hw : |(-1123214177/5000000000 : ℝ)|=(1123214177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2141127319/5000000000 : ℝ)*x 0 + (1864413759/5000000000 : ℝ)*x 1 + (4909267871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141127319/5000000000 : ℝ)^2179 ≤ (33002352778277/100000000000000 : ℝ)^1667 := by
    have hnat : (2141127319 : ℕ)^2179*100000000000000^1667 ≤ 33002352778277^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141127319 5000000000 33002352778277 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864413759/5000000000 : ℝ)^2179 ≤ (27541375172441/100000000000000 : ℝ)^1667 := by
    have hnat : (1864413759 : ℕ)^2179*100000000000000^1667 ≤ 27541375172441^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864413759 5000000000 27541375172441 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4909267871/10000000000 : ℝ)^2179 ≤ (7891254407799/20000000000000 : ℝ)^1667 := by
    have hnat : (4909267871 : ℕ)^2179*20000000000000^1667 ≤ 7891254407799^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909267871 10000000000 7891254407799 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141127319/5000000000 : ℝ), (1864413759/5000000000 : ℝ), (4909267871/10000000000 : ℝ)] ![(33002352778277/100000000000000 : ℝ), (27541375172441/100000000000000 : ℝ), (7891254407799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141127319/5000000000 : ℝ)|^2179 ≤ (33002352778277/100000000000000 : ℝ)^1667
        have hw : |(2141127319/5000000000 : ℝ)|=(2141127319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1864413759/5000000000 : ℝ)|^2179 ≤ (27541375172441/100000000000000 : ℝ)^1667
        have hw : |(1864413759/5000000000 : ℝ)|=(1864413759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4909267871/10000000000 : ℝ)|^2179 ≤ (7891254407799/20000000000000 : ℝ)^1667
        have hw : |(4909267871/10000000000 : ℝ)|=(4909267871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953708759/10000000000 : ℝ)*x 0 + (5072620923/10000000000 : ℝ)*x 1 + (1402791093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953708759/10000000000 : ℝ)^2179 ≤ (5915964054629/50000000000000 : ℝ)^1667 := by
    have hnat : (1953708759 : ℕ)^2179*50000000000000^1667 ≤ 5915964054629^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953708759 10000000000 5915964054629 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072620923/10000000000 : ℝ)^2179 ≤ (8236219403613/20000000000000 : ℝ)^1667 := by
    have hnat : (5072620923 : ℕ)^2179*20000000000000^1667 ≤ 8236219403613^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072620923 10000000000 8236219403613 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1402791093/2500000000 : ℝ)^2179 ≤ (23493487429363/50000000000000 : ℝ)^1667 := by
    have hnat : (1402791093 : ℕ)^2179*50000000000000^1667 ≤ 23493487429363^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402791093 2500000000 23493487429363 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953708759/10000000000 : ℝ), (5072620923/10000000000 : ℝ), (1402791093/2500000000 : ℝ)] ![(5915964054629/50000000000000 : ℝ), (8236219403613/20000000000000 : ℝ), (23493487429363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953708759/10000000000 : ℝ)|^2179 ≤ (5915964054629/50000000000000 : ℝ)^1667
        have hw : |(-1953708759/10000000000 : ℝ)|=(1953708759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072620923/10000000000 : ℝ)|^2179 ≤ (8236219403613/20000000000000 : ℝ)^1667
        have hw : |(5072620923/10000000000 : ℝ)|=(5072620923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1402791093/2500000000 : ℝ)|^2179 ≤ (23493487429363/50000000000000 : ℝ)^1667
        have hw : |(1402791093/2500000000 : ℝ)|=(1402791093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5256082369/10000000000 : ℝ)*x 0 + (-340250873/2000000000 : ℝ)*x 1 + (1122232867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256082369/10000000000 : ℝ)^2179 ≤ (43138668668537/100000000000000 : ℝ)^1667 := by
    have hnat : (5256082369 : ℕ)^2179*100000000000000^1667 ≤ 43138668668537^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256082369 10000000000 43138668668537 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340250873/2000000000 : ℝ)^2179 ≤ (9874356868177/100000000000000 : ℝ)^1667 := by
    have hnat : (340250873 : ℕ)^2179*100000000000000^1667 ≤ 9874356868177^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340250873 2000000000 9874356868177 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122232867/2000000000 : ℝ)^2179 ≤ (46986974453733/100000000000000 : ℝ)^1667 := by
    have hnat : (1122232867 : ℕ)^2179*100000000000000^1667 ≤ 46986974453733^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122232867 2000000000 46986974453733 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256082369/10000000000 : ℝ), (-340250873/2000000000 : ℝ), (1122232867/2000000000 : ℝ)] ![(43138668668537/100000000000000 : ℝ), (9874356868177/100000000000000 : ℝ), (46986974453733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256082369/10000000000 : ℝ)|^2179 ≤ (43138668668537/100000000000000 : ℝ)^1667
        have hw : |(5256082369/10000000000 : ℝ)|=(5256082369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-340250873/2000000000 : ℝ)|^2179 ≤ (9874356868177/100000000000000 : ℝ)^1667
        have hw : |(-340250873/2000000000 : ℝ)|=(340250873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122232867/2000000000 : ℝ)|^2179 ≤ (46986974453733/100000000000000 : ℝ)^1667
        have hw : |(1122232867/2000000000 : ℝ)|=(1122232867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (657010359/1250000000 : ℝ)*x 0 + (2805582377/5000000000 : ℝ)*x 1 + (-1701253049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657010359/1250000000 : ℝ)^2179 ≤ (43138674064813/100000000000000 : ℝ)^1667 := by
    have hnat : (657010359 : ℕ)^2179*100000000000000^1667 ≤ 43138674064813^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657010359 1250000000 43138674064813 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2805582377/5000000000 : ℝ)^2179 ≤ (5873372380001/12500000000000 : ℝ)^1667 := by
    have hnat : (2805582377 : ℕ)^2179*12500000000000^1667 ≤ 5873372380001^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805582377 5000000000 5873372380001 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701253049/10000000000 : ℝ)^2179 ≤ (987434688389/10000000000000 : ℝ)^1667 := by
    have hnat : (1701253049 : ℕ)^2179*10000000000000^1667 ≤ 987434688389^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701253049 10000000000 987434688389 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657010359/1250000000 : ℝ), (2805582377/5000000000 : ℝ), (-1701253049/10000000000 : ℝ)] ![(43138674064813/100000000000000 : ℝ), (5873372380001/12500000000000 : ℝ), (987434688389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657010359/1250000000 : ℝ)|^2179 ≤ (43138674064813/100000000000000 : ℝ)^1667
        have hw : |(657010359/1250000000 : ℝ)|=(657010359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2805582377/5000000000 : ℝ)|^2179 ≤ (5873372380001/12500000000000 : ℝ)^1667
        have hw : |(2805582377/5000000000 : ℝ)|=(2805582377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1701253049/10000000000 : ℝ)|^2179 ≤ (987434688389/10000000000000 : ℝ)^1667
        have hw : |(-1701253049/10000000000 : ℝ)|=(1701253049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s1_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267700213/625000000 : ℝ)*x 0 + (4895084501/10000000000 : ℝ)*x 1 + (935813909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267700213/625000000 : ℝ)^2179 ≤ (3301191083853/10000000000000 : ℝ)^1667 := by
    have hnat : (267700213 : ℕ)^2179*10000000000000^1667 ≤ 3301191083853^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267700213 625000000 3301191083853 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4895084501/10000000000 : ℝ)^2179 ≤ (19653666675419/50000000000000 : ℝ)^1667 := by
    have hnat : (4895084501 : ℕ)^2179*50000000000000^1667 ≤ 19653666675419^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895084501 10000000000 19653666675419 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935813909/2500000000 : ℝ)^2179 ≤ (2768075579459/10000000000000 : ℝ)^1667 := by
    have hnat : (935813909 : ℕ)^2179*10000000000000^1667 ≤ 2768075579459^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935813909 2500000000 2768075579459 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267700213/625000000 : ℝ), (4895084501/10000000000 : ℝ), (935813909/2500000000 : ℝ)] ![(3301191083853/10000000000000 : ℝ), (19653666675419/50000000000000 : ℝ), (2768075579459/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267700213/625000000 : ℝ)|^2179 ≤ (3301191083853/10000000000000 : ℝ)^1667
        have hw : |(267700213/625000000 : ℝ)|=(267700213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4895084501/10000000000 : ℝ)|^2179 ≤ (19653666675419/50000000000000 : ℝ)^1667
        have hw : |(4895084501/10000000000 : ℝ)|=(4895084501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935813909/2500000000 : ℝ)|^2179 ≤ (2768075579459/10000000000000 : ℝ)^1667
        have hw : |(935813909/2500000000 : ℝ)|=(935813909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13237/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13237/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (913/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13237/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (913/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13237/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (913/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13237/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (913/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13237/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (913/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13237/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (913/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (913/50000 : ℝ) ^ (4357/1024 : ℝ) ≤ (801529509167/20000000000000000000 : ℝ) := by
    have hpowers : (913/50000 : ℝ)^4357 ≤ (801529509167/20000000000000000000 : ℝ)^1024 := by
      have hnat : (913 : ℕ)^4357*20000000000000000000^1024 ≤ 801529509167^1024*50000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        913 50000 801529509167 20000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (913/50000 : ℝ)) (X := (801529509167/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13237/50000 : ℝ) ^ (4357/1024 : ℝ) ≤ (175039026675043269/50000000000000000000 : ℝ) := by
    have hpowers : (13237/50000 : ℝ)^4357 ≤ (175039026675043269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (13237 : ℕ)^4357*50000000000000000000^1024 ≤ 175039026675043269^1024*50000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13237 50000 175039026675043269 50000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13237/50000 : ℝ)) (X := (175039026675043269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000801529509167/10000000000000000000 : ℝ) ≤ (5000000094189373/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (10000000801529509167/10000000000000000000 : ℝ)^1024 ≤ (5000000094189373/5000000000000000 : ℝ)^4357 := by
      have hnat : (10000000801529509167 : ℕ)^1024*5000000000000000^4357 ≤ 5000000094189373^4357*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000801529509167 10000000000000000000 5000000094189373 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000094189373/5000000000000000 : ℝ)) (X := (10000000801529509167/10000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100350082060997632373/100000000000000000000 : ℝ) ≤ (10008216777572519/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (100350082060997632373/100000000000000000000 : ℝ)^1024 ≤ (10008216777572519/10000000000000000 : ℝ)^4357 := by
      have hnat : (100350082060997632373 : ℕ)^1024*10000000000000000^4357 ≤ 10008216777572519^4357*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100350082060997632373 100000000000000000000 10008216777572519 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008216777572519/10000000000000000 : ℝ)) (X := (100350082060997632373/100000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25175039026675043269/25000000000000000000 : ℝ) ≤ (2504108341691573/2500000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (25175039026675043269/25000000000000000000 : ℝ)^1024 ≤ (2504108341691573/2500000000000000 : ℝ)^4357 := by
      have hnat : (25175039026675043269 : ℕ)^1024*2500000000000000^4357 ≤ 2504108341691573^4357*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25175039026675043269 25000000000000000000 2504108341691573 2500000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504108341691573/2500000000000000 : ℝ)) (X := (25175039026675043269/25000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(801529509167/20000000000000000000 : ℝ) ≤ ((20537499804951972701/20540000000000000000 : ℝ)+2*(2738863064591/821600000000000 : ℝ)*(913/50000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (20537499804951972701/20540000000000000000 : ℝ)+2*(2738863064591/821600000000000 : ℝ)*(913/50000 : ℝ)=(5000000094189373/5000000000000000 : ℝ) by norm_num, show 1+2*(801529509167/20000000000000000000 : ℝ)=(10000000801529509167/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(175039026675043269/50000000000000000000 : ℝ)+(801529509167/20000000000000000000 : ℝ) ≤ ((20537499804951972701/20540000000000000000 : ℝ)+(2738863064591/821600000000000 : ℝ)*((13237/50000 : ℝ)+(913/50000 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (20537499804951972701/20540000000000000000 : ℝ)+(2738863064591/821600000000000 : ℝ)*((13237/50000 : ℝ)+(913/50000 : ℝ))=(10008216777572519/10000000000000000 : ℝ) by norm_num, show 1+(175039026675043269/50000000000000000000 : ℝ)+(801529509167/20000000000000000000 : ℝ)=(100350082060997632373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(175039026675043269/50000000000000000000 : ℝ) ≤ ((20537499804951972701/20540000000000000000 : ℝ)+2*(2738863064591/821600000000000 : ℝ)*(13237/50000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (20537499804951972701/20540000000000000000 : ℝ)+2*(2738863064591/821600000000000 : ℝ)*(13237/50000 : ℝ)=(2504108341691573/2500000000000000 : ℝ) by norm_num, show 1+2*(175039026675043269/50000000000000000000 : ℝ)=(25175039026675043269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20537499804951972701/20540000000000000000 : ℝ)*(X 1 0+X 2 0)+(2738863064591/821600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (913/50000 : ℝ)) (hi := (13237/50000 : ℝ)) (c := (20537499804951972701/20540000000000000000 : ℝ)) (alpha := (2738863064591/821600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20537499804951972701/20540000000000000000 : ℝ)*(X 0 1+X 2 1)+(2738863064591/821600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (913/50000 : ℝ)) (hi := (13237/50000 : ℝ)) (c := (20537499804951972701/20540000000000000000 : ℝ)) (alpha := (2738863064591/821600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20537499804951972701/20540000000000000000 : ℝ)*(X 0 2+X 1 2)+(2738863064591/821600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (913/50000 : ℝ)) (hi := (13237/50000 : ℝ)) (c := (20537499804951972701/20540000000000000000 : ℝ)) (alpha := (2738863064591/821600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1953265893/10000000000 : ℝ)*X 0 0+(5617911279/10000000000 : ℝ)*X 0 1+(1266497349/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5399945971/10000000000 : ℝ)*X 1 0+(-2246428053/10000000000 : ℝ)*X 1 1+(5065990751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5399946891/10000000000 : ℝ)*X 2 0+(253299479/500000000 : ℝ)*X 2 1+(-1123214177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2141127319/5000000000 : ℝ)*X 0 0+(1864413759/5000000000 : ℝ)*X 0 1+(4909267871/10000000000 : ℝ)*X 0 2+(2141127319/5000000000 : ℝ)*X 1 0+(1864413759/5000000000 : ℝ)*X 1 1+(4909267871/10000000000 : ℝ)*X 1 2+(2141127319/5000000000 : ℝ)*X 2 0+(1864413759/5000000000 : ℝ)*X 2 1+(4909267871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1953708759/10000000000 : ℝ)*X 0 0+(5072620923/10000000000 : ℝ)*X 0 1+(1402791093/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256082369/10000000000 : ℝ)*X 1 0+(-340250873/2000000000 : ℝ)*X 1 1+(1122232867/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657010359/1250000000 : ℝ)*X 2 0+(2805582377/5000000000 : ℝ)*X 2 1+(-1701253049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267700213/625000000 : ℝ)*X 0 0+(4895084501/10000000000 : ℝ)*X 0 1+(935813909/2500000000 : ℝ)*X 0 2+(267700213/625000000 : ℝ)*X 1 0+(4895084501/10000000000 : ℝ)*X 1 1+(935813909/2500000000 : ℝ)*X 1 2+(267700213/625000000 : ℝ)*X 2 0+(4895084501/10000000000 : ℝ)*X 2 1+(935813909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119279644559817130786500369/64187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38384499/20000000000000 : ℝ)*(base19) + (555500531/100000000000000 : ℝ)*(base23) + (30270459/100000000000000 : ℝ)*(upper2) + (18344103/100000000000000 : ℝ)*(upper3) + (315769/50000000000000 : ℝ)*(upper4) + (83093951084341/6250000000000 : ℝ)*(major0) + (83093951084341/6250000000000 : ℝ)*(major1) + (83093951084341/6250000000000 : ℝ)*(major2) + (1811856108407117/100000000000000 : ℝ)*(sp0) + (226482727529923/12500000000000 : ℝ)*(sp1) + (1811861456661347/100000000000000 : ℝ)*(sp2) + (211785678223013/25000000000000 : ℝ)*(sp3) + (5903754761/100000000000000 : ℝ)*(sp4) + (1647701631/100000000000000 : ℝ)*(sp7) + (847144360593683/100000000000000 : ℝ)*(f.failure) + (905931006080939/50000000000000 : ℝ)*(f.sum) + (17024659829689/2567500000000000000000000000 : ℝ)*base66 + (1133244413662524959/128375000000000000000000000000000 : ℝ)*base68 + (1473677572639149959/128375000000000000000000000000000 : ℝ)*base70 + (1825515892303149959/128375000000000000000000000000000 : ℝ)*base72 + (3547857012463/5135000000000000000000000000 : ℝ)*base74 + (2350277397129149959/128375000000000000000000000000000 : ℝ)*base76 + (1066331857484524959/128375000000000000000000000000000 : ℝ)*base78 + (1295398369759774959/128375000000000000000000000000000 : ℝ)*base80 + (3869041945611/641875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (129654419/10000000000000000000000 : ℝ)*base89 + (129654419/10000000000000000000000 : ℝ)*base91 + (129654419/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815052295878377394169671381/256750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181704391/100000000000000 : ℝ)*(base1) + (492397203/50000000000000 : ℝ)*(base19) + (632945767/50000000000000 : ℝ)*(base23) + (18335357/25000000000000 : ℝ)*(upper3) + (184131273/100000000000000 : ℝ)*(upper5) + (681261739833273/50000000000000 : ℝ)*(major0) + (681261739833273/50000000000000 : ℝ)*(major1) + (681261739833273/50000000000000 : ℝ)*(major2) + (2293223199/50000000000000 : ℝ)*(sp1) + (8364087413/100000000000000 : ℝ)*(sp2) + (1856862538249789/100000000000000 : ℝ)*(sp4) + (928428392652297/50000000000000 : ℝ)*(sp5) + (464213181641613/25000000000000 : ℝ)*(sp6) + (217046078816677/25000000000000 : ℝ)*(sp7) + (868184496971099/100000000000000 : ℝ)*(f.failure) + (928431178272699/50000000000000 : ℝ)*(f.sum) + (1491693390677/20540000000000000000000000000 : ℝ)*base66 + (879417129188944627/1027000000000000000000000000000000 : ℝ)*base68 + (3546279322104055373/1027000000000000000000000000000000 : ℝ)*base69 + (7302097696880055373/1027000000000000000000000000000000 : ℝ)*base71 + (98680766017817/20540000000000000000000000000 : ℝ)*base74 + (4659134077844055373/1027000000000000000000000000000000 : ℝ)*base75 + (418191171839055373/1027000000000000000000000000000000 : ℝ)*base77 + (1290989109084055373/1027000000000000000000000000000000 : ℝ)*base79 + (23366935630177/20540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15602907/10000000000000000000000 : ℝ)*base89 + (15602907/10000000000000000000000 : ℝ)*base91 + (15602907/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1398_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13237/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (913/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1398_s2_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-397755491/2000000000 : ℝ)*x 0 + (546536879/1000000000 : ℝ)*x 1 + (5195713109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397755491/2000000000 : ℝ)^2179 ≤ (12110301383147/100000000000000 : ℝ)^1667 := by
    have hnat : (397755491 : ℕ)^2179*100000000000000^1667 ≤ 12110301383147^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397755491 2000000000 12110301383147 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546536879/1000000000 : ℝ)^2179 ≤ (11349384263791/25000000000000 : ℝ)^1667 := by
    have hnat : (546536879 : ℕ)^2179*25000000000000^1667 ≤ 11349384263791^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546536879 1000000000 11349384263791 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195713109/10000000000 : ℝ)^2179 ≤ (21246080774157/50000000000000 : ℝ)^1667 := by
    have hnat : (5195713109 : ℕ)^2179*50000000000000^1667 ≤ 21246080774157^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195713109 10000000000 21246080774157 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397755491/2000000000 : ℝ), (546536879/1000000000 : ℝ), (5195713109/10000000000 : ℝ)] ![(12110301383147/100000000000000 : ℝ), (11349384263791/25000000000000 : ℝ), (21246080774157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397755491/2000000000 : ℝ)|^2179 ≤ (12110301383147/100000000000000 : ℝ)^1667
        have hw : |(-397755491/2000000000 : ℝ)|=(397755491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546536879/1000000000 : ℝ)|^2179 ≤ (11349384263791/25000000000000 : ℝ)^1667
        have hw : |(546536879/1000000000 : ℝ)|=(546536879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195713109/10000000000 : ℝ)|^2179 ≤ (21246080774157/50000000000000 : ℝ)^1667
        have hw : |(5195713109/10000000000 : ℝ)|=(5195713109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362141819/10000000000 : ℝ)*x 0 + (-2127711327/10000000000 : ℝ)*x 1 + (81183017/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362141819/10000000000 : ℝ)^2179 ≤ (22140001763531/50000000000000 : ℝ)^1667 := by
    have hnat : (5362141819 : ℕ)^2179*50000000000000^1667 ≤ 22140001763531^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362141819 10000000000 22140001763531 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127711327/10000000000 : ℝ)^2179 ≤ (103342462009/781250000000 : ℝ)^1667 := by
    have hnat : (2127711327 : ℕ)^2179*781250000000^1667 ≤ 103342462009^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127711327 10000000000 103342462009 781250000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81183017/156250000 : ℝ)^2179 ≤ (2124608066191/5000000000000 : ℝ)^1667 := by
    have hnat : (81183017 : ℕ)^2179*5000000000000^1667 ≤ 2124608066191^1667*156250000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81183017 156250000 2124608066191 5000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362141819/10000000000 : ℝ), (-2127711327/10000000000 : ℝ), (81183017/156250000 : ℝ)] ![(22140001763531/50000000000000 : ℝ), (103342462009/781250000000 : ℝ), (2124608066191/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362141819/10000000000 : ℝ)|^2179 ≤ (22140001763531/50000000000000 : ℝ)^1667
        have hw : |(5362141819/10000000000 : ℝ)|=(5362141819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127711327/10000000000 : ℝ)|^2179 ≤ (103342462009/781250000000 : ℝ)^1667
        have hw : |(-2127711327/10000000000 : ℝ)|=(2127711327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81183017/156250000 : ℝ)|^2179 ≤ (2124608066191/5000000000000 : ℝ)^1667
        have hw : |(81183017/156250000 : ℝ)|=(81183017/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362141637/10000000000 : ℝ)*x 0 + (1298928323/2500000000 : ℝ)*x 1 + (-21277113/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362141637/10000000000 : ℝ)^2179 ≤ (8856000312503/20000000000000 : ℝ)^1667 := by
    have hnat : (5362141637 : ℕ)^2179*20000000000000^1667 ≤ 8856000312503^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362141637 10000000000 8856000312503 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298928323/2500000000 : ℝ)^2179 ≤ (21246081752309/50000000000000 : ℝ)^1667 := by
    have hnat : (1298928323 : ℕ)^2179*50000000000000^1667 ≤ 21246081752309^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298928323 2500000000 21246081752309 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21277113/100000000 : ℝ)^2179 ≤ (13227834917739/100000000000000 : ℝ)^1667 := by
    have hnat : (21277113 : ℕ)^2179*100000000000000^1667 ≤ 13227834917739^1667*100000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21277113 100000000 13227834917739 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362141637/10000000000 : ℝ), (1298928323/2500000000 : ℝ), (-21277113/100000000 : ℝ)] ![(8856000312503/20000000000000 : ℝ), (21246081752309/50000000000000 : ℝ), (13227834917739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362141637/10000000000 : ℝ)|^2179 ≤ (8856000312503/20000000000000 : ℝ)^1667
        have hw : |(5362141637/10000000000 : ℝ)|=(5362141637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298928323/2500000000 : ℝ)|^2179 ≤ (21246081752309/50000000000000 : ℝ)^1667
        have hw : |(1298928323/2500000000 : ℝ)|=(1298928323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21277113/100000000 : ℝ)|^2179 ≤ (13227834917739/100000000000000 : ℝ)^1667
        have hw : |(-21277113/100000000 : ℝ)|=(21277113/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076810757/2500000000 : ℝ)*x 0 + (2013828117/5000000000 : ℝ)*x 1 + (230219637/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076810757/2500000000 : ℝ)^2179 ≤ (6650861303303/20000000000000 : ℝ)^1667 := by
    have hnat : (1076810757 : ℕ)^2179*20000000000000^1667 ≤ 6650861303303^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076810757 2500000000 6650861303303 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013828117/5000000000 : ℝ)^2179 ≤ (6092264471197/20000000000000 : ℝ)^1667 := by
    have hnat : (2013828117 : ℕ)^2179*20000000000000^1667 ≤ 6092264471197^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013828117 5000000000 6092264471197 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230219637/500000000 : ℝ)^2179 ≤ (7256874221653/20000000000000 : ℝ)^1667 := by
    have hnat : (230219637 : ℕ)^2179*20000000000000^1667 ≤ 7256874221653^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230219637 500000000 7256874221653 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076810757/2500000000 : ℝ), (2013828117/5000000000 : ℝ), (230219637/500000000 : ℝ)] ![(6650861303303/20000000000000 : ℝ), (6092264471197/20000000000000 : ℝ), (7256874221653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076810757/2500000000 : ℝ)|^2179 ≤ (6650861303303/20000000000000 : ℝ)^1667
        have hw : |(1076810757/2500000000 : ℝ)|=(1076810757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013828117/5000000000 : ℝ)|^2179 ≤ (6092264471197/20000000000000 : ℝ)^1667
        have hw : |(2013828117/5000000000 : ℝ)|=(2013828117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230219637/500000000 : ℝ)|^2179 ≤ (7256874221653/20000000000000 : ℝ)^1667
        have hw : |(230219637/500000000 : ℝ)|=(230219637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1988828871/10000000000 : ℝ)*x 0 + (162415801/312500000 : ℝ)*x 1 + (2731881493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1988828871/10000000000 : ℝ)^2179 ≤ (2422142126953/20000000000000 : ℝ)^1667 := by
    have hnat : (1988828871 : ℕ)^2179*20000000000000^1667 ≤ 2422142126953^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988828871 10000000000 2422142126953 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162415801/312500000 : ℝ)^2179 ≤ (10627296679463/25000000000000 : ℝ)^1667 := by
    have hnat : (162415801 : ℕ)^2179*25000000000000^1667 ≤ 10627296679463^1667*312500000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162415801 312500000 10627296679463 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731881493/5000000000 : ℝ)^2179 ≤ (11345025659959/25000000000000 : ℝ)^1667 := by
    have hnat : (2731881493 : ℕ)^2179*25000000000000^1667 ≤ 11345025659959^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731881493 5000000000 11345025659959 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1988828871/10000000000 : ℝ), (162415801/312500000 : ℝ), (2731881493/5000000000 : ℝ)] ![(2422142126953/20000000000000 : ℝ), (10627296679463/25000000000000 : ℝ), (11345025659959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1988828871/10000000000 : ℝ)|^2179 ≤ (2422142126953/20000000000000 : ℝ)^1667
        have hw : |(-1988828871/10000000000 : ℝ)|=(1988828871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162415801/312500000 : ℝ)|^2179 ≤ (10627296679463/25000000000000 : ℝ)^1667
        have hw : |(162415801/312500000 : ℝ)|=(162415801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731881493/5000000000 : ℝ)|^2179 ≤ (11345025659959/25000000000000 : ℝ)^1667
        have hw : |(2731881493/5000000000 : ℝ)|=(2731881493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292232233/10000000000 : ℝ)*x 0 + (-929831021/5000000000 : ℝ)*x 1 + (5463762683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292232233/10000000000 : ℝ)^2179 ≤ (21763450013007/50000000000000 : ℝ)^1667 := by
    have hnat : (5292232233 : ℕ)^2179*50000000000000^1667 ≤ 21763450013007^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292232233 10000000000 21763450013007 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929831021/5000000000 : ℝ)^2179 ≤ (2773250151201/25000000000000 : ℝ)^1667 := by
    have hnat : (929831021 : ℕ)^2179*25000000000000^1667 ≤ 2773250151201^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929831021 5000000000 2773250151201 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463762683/10000000000 : ℝ)^2179 ≤ (11345024837569/25000000000000 : ℝ)^1667 := by
    have hnat : (5463762683 : ℕ)^2179*25000000000000^1667 ≤ 11345024837569^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463762683 10000000000 11345024837569 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292232233/10000000000 : ℝ), (-929831021/5000000000 : ℝ), (5463762683/10000000000 : ℝ)] ![(21763450013007/50000000000000 : ℝ), (2773250151201/25000000000000 : ℝ), (11345024837569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292232233/10000000000 : ℝ)|^2179 ≤ (21763450013007/50000000000000 : ℝ)^1667
        have hw : |(5292232233/10000000000 : ℝ)|=(5292232233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-929831021/5000000000 : ℝ)|^2179 ≤ (2773250151201/25000000000000 : ℝ)^1667
        have hw : |(-929831021/5000000000 : ℝ)|=(929831021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463762683/10000000000 : ℝ)|^2179 ≤ (11345024837569/25000000000000 : ℝ)^1667
        have hw : |(5463762683/10000000000 : ℝ)|=(5463762683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292233649/10000000000 : ℝ)*x 0 + (546376267/1000000000 : ℝ)*x 1 + (-464915027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292233649/10000000000 : ℝ)^2179 ≤ (2720432203071/6250000000000 : ℝ)^1667 := by
    have hnat : (5292233649 : ℕ)^2179*6250000000000^1667 ≤ 2720432203071^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292233649 10000000000 2720432203071 6250000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546376267/1000000000 : ℝ)^2179 ≤ (2269004960457/5000000000000 : ℝ)^1667 := by
    have hnat : (546376267 : ℕ)^2179*5000000000000^1667 ≤ 2269004960457^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546376267 1000000000 2269004960457 5000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464915027/2500000000 : ℝ)^2179 ≤ (2773246381273/25000000000000 : ℝ)^1667 := by
    have hnat : (464915027 : ℕ)^2179*25000000000000^1667 ≤ 2773246381273^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464915027 2500000000 2773246381273 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292233649/10000000000 : ℝ), (546376267/1000000000 : ℝ), (-464915027/2500000000 : ℝ)] ![(2720432203071/6250000000000 : ℝ), (2269004960457/5000000000000 : ℝ), (2773246381273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292233649/10000000000 : ℝ)|^2179 ≤ (2720432203071/6250000000000 : ℝ)^1667
        have hw : |(5292233649/10000000000 : ℝ)|=(5292233649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546376267/1000000000 : ℝ)|^2179 ≤ (2269004960457/5000000000000 : ℝ)^1667
        have hw : |(546376267/1000000000 : ℝ)|=(546376267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464915027/2500000000 : ℝ)|^2179 ≤ (2773246381273/25000000000000 : ℝ)^1667
        have hw : |(-464915027/2500000000 : ℝ)|=(464915027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_s2_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307354323/10000000000 : ℝ)*x 0 + (4600987187/10000000000 : ℝ)*x 1 + (4031090217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307354323/10000000000 : ℝ)^2179 ≤ (33255429691769/100000000000000 : ℝ)^1667 := by
    have hnat : (4307354323 : ℕ)^2179*100000000000000^1667 ≤ 33255429691769^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307354323 10000000000 33255429691769 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4600987187/10000000000 : ℝ)^2179 ≤ (36249295341531/100000000000000 : ℝ)^1667 := by
    have hnat : (4600987187 : ℕ)^2179*100000000000000^1667 ≤ 36249295341531^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4600987187 10000000000 36249295341531 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031090217/10000000000 : ℝ)^2179 ≤ (30495274951269/100000000000000 : ℝ)^1667 := by
    have hnat : (4031090217 : ℕ)^2179*100000000000000^1667 ≤ 30495274951269^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031090217 10000000000 30495274951269 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307354323/10000000000 : ℝ), (4600987187/10000000000 : ℝ), (4031090217/10000000000 : ℝ)] ![(33255429691769/100000000000000 : ℝ), (36249295341531/100000000000000 : ℝ), (30495274951269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307354323/10000000000 : ℝ)|^2179 ≤ (33255429691769/100000000000000 : ℝ)^1667
        have hw : |(4307354323/10000000000 : ℝ)|=(4307354323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4600987187/10000000000 : ℝ)|^2179 ≤ (36249295341531/100000000000000 : ℝ)^1667
        have hw : |(4600987187/10000000000 : ℝ)|=(4600987187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031090217/10000000000 : ℝ)|^2179 ≤ (30495274951269/100000000000000 : ℝ)^1667
        have hw : |(4031090217/10000000000 : ℝ)|=(4031090217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2549/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15899/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7391/100000 : ℝ) ^ (4357/1024 : ℝ) ≤ (1536259917492397/100000000000000000000 : ℝ) := by
    have hpowers : (7391/100000 : ℝ)^4357 ≤ (1536259917492397/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7391 : ℕ)^4357*100000000000000000000^1024 ≤ 1536259917492397^1024*100000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7391 100000 1536259917492397 100000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7391/100000 : ℝ)) (X := (1536259917492397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19057/100000 : ℝ) ^ (4357/1024 : ℝ) ≤ (17288065779522493/20000000000000000000 : ℝ) := by
    have hpowers : (19057/100000 : ℝ)^4357 ≤ (17288065779522493/20000000000000000000 : ℝ)^1024 := by
      have hnat : (19057 : ℕ)^4357*20000000000000000000^1024 ≤ 17288065779522493^1024*100000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19057 100000 17288065779522493 20000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19057/100000 : ℝ)) (X := (17288065779522493/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001536259917492397/50000000000000000000 : ℝ) ≤ (5000036105386009/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50001536259917492397/50000000000000000000 : ℝ)^1024 ≤ (5000036105386009/5000000000000000 : ℝ)^4357 := by
      have hnat : (50001536259917492397 : ℕ)^1024*5000000000000000^4357 ≤ 5000036105386009^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001536259917492397 50000000000000000000 5000036105386009 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000036105386009/5000000000000000 : ℝ)) (X := (50001536259917492397/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50043988294407552431/50000000000000000000 : ℝ) ≤ (500103348322263/500000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50043988294407552431/50000000000000000000 : ℝ)^1024 ≤ (500103348322263/500000000000000 : ℝ)^4357 := by
      have hnat : (50043988294407552431 : ℕ)^1024*500000000000000^4357 ≤ 500103348322263^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043988294407552431 50000000000000000000 500103348322263 500000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500103348322263/500000000000000 : ℝ)) (X := (50043988294407552431/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10017288065779522493/10000000000000000000 : ℝ) ≤ (5002030861059251/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (10017288065779522493/10000000000000000000 : ℝ)^1024 ≤ (5002030861059251/5000000000000000 : ℝ)^4357 := by
      have hnat : (10017288065779522493 : ℕ)^1024*5000000000000000^4357 ≤ 5002030861059251^4357*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10017288065779522493 10000000000000000000 5002030861059251 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002030861059251/5000000000000000 : ℝ)) (X := (10017288065779522493/10000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1536259917492397/100000000000000000000 : ℝ) ≤ ((767311552187529597/767500000000000000 : ℝ)+2*(997377836621/583300000000000 : ℝ)*(7391/100000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (767311552187529597/767500000000000000 : ℝ)+2*(997377836621/583300000000000 : ℝ)*(7391/100000 : ℝ)=(5000036105386009/5000000000000000 : ℝ) by norm_num, show 1+2*(1536259917492397/100000000000000000000 : ℝ)=(50001536259917492397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17288065779522493/20000000000000000000 : ℝ)+(1536259917492397/100000000000000000000 : ℝ) ≤ ((767311552187529597/767500000000000000 : ℝ)+(997377836621/583300000000000 : ℝ)*((19057/100000 : ℝ)+(7391/100000 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (767311552187529597/767500000000000000 : ℝ)+(997377836621/583300000000000 : ℝ)*((19057/100000 : ℝ)+(7391/100000 : ℝ))=(500103348322263/500000000000000 : ℝ) by norm_num, show 1+(17288065779522493/20000000000000000000 : ℝ)+(1536259917492397/100000000000000000000 : ℝ)=(50043988294407552431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17288065779522493/20000000000000000000 : ℝ) ≤ ((767311552187529597/767500000000000000 : ℝ)+2*(997377836621/583300000000000 : ℝ)*(19057/100000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (767311552187529597/767500000000000000 : ℝ)+2*(997377836621/583300000000000 : ℝ)*(19057/100000 : ℝ)=(5002030861059251/5000000000000000 : ℝ) by norm_num, show 1+2*(17288065779522493/20000000000000000000 : ℝ)=(10017288065779522493/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (767311552187529597/767500000000000000 : ℝ)*(X 1 0+X 2 0)+(997377836621/583300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (7391/100000 : ℝ)) (hi := (19057/100000 : ℝ)) (c := (767311552187529597/767500000000000000 : ℝ)) (alpha := (997377836621/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (767311552187529597/767500000000000000 : ℝ)*(X 0 1+X 2 1)+(997377836621/583300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (7391/100000 : ℝ)) (hi := (19057/100000 : ℝ)) (c := (767311552187529597/767500000000000000 : ℝ)) (alpha := (997377836621/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (767311552187529597/767500000000000000 : ℝ)*(X 0 2+X 1 2)+(997377836621/583300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (7391/100000 : ℝ)) (hi := (19057/100000 : ℝ)) (c := (767311552187529597/767500000000000000 : ℝ)) (alpha := (997377836621/583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397755491/2000000000 : ℝ)*X 0 0+(546536879/1000000000 : ℝ)*X 0 1+(5195713109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362141819/10000000000 : ℝ)*X 1 0+(-2127711327/10000000000 : ℝ)*X 1 1+(81183017/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362141637/10000000000 : ℝ)*X 2 0+(1298928323/2500000000 : ℝ)*X 2 1+(-21277113/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076810757/2500000000 : ℝ)*X 0 0+(2013828117/5000000000 : ℝ)*X 0 1+(230219637/500000000 : ℝ)*X 0 2+(1076810757/2500000000 : ℝ)*X 1 0+(2013828117/5000000000 : ℝ)*X 1 1+(230219637/500000000 : ℝ)*X 1 2+(1076810757/2500000000 : ℝ)*X 2 0+(2013828117/5000000000 : ℝ)*X 2 1+(230219637/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1988828871/10000000000 : ℝ)*X 0 0+(162415801/312500000 : ℝ)*X 0 1+(2731881493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292232233/10000000000 : ℝ)*X 1 0+(-929831021/5000000000 : ℝ)*X 1 1+(5463762683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292233649/10000000000 : ℝ)*X 2 0+(546376267/1000000000 : ℝ)*X 2 1+(-464915027/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307354323/10000000000 : ℝ)*X 0 0+(4600987187/10000000000 : ℝ)*X 0 1+(4031090217/10000000000 : ℝ)*X 0 2+(4307354323/10000000000 : ℝ)*X 1 0+(4600987187/10000000000 : ℝ)*X 1 1+(4031090217/10000000000 : ℝ)*X 1 2+(4307354323/10000000000 : ℝ)*X 2 0+(4600987187/10000000000 : ℝ)*X 2 1+(4031090217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (179523783325143186622798743/45570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (595476897/100000000000000 : ℝ)*(base19) + (2820491/781250000000 : ℝ)*(base23) + (29111941/50000000000000 : ℝ)*(lower2) + (66533527/50000000000000 : ℝ)*(upper3) + (10857447/25000000000000 : ℝ)*(upper5) + (10629582919731/390625000000 : ℝ)*(major0) + (10629582919731/390625000000 : ℝ)*(major1) + (10629582919731/390625000000 : ℝ)*(major2) + (23177751310213/625000000000 : ℝ)*(sp0) + (927111258039053/25000000000000 : ℝ)*(sp1) + (185422263330513/5000000000000 : ℝ)*(sp2) + (216737115310579/12500000000000 : ℝ)*(sp3) + (541799903/10000000000000 : ℝ)*(sp4) + (117920881/3125000000000 : ℝ)*(sp7) + (216737586994103/12500000000000 : ℝ)*(f.failure) + (3708445627633109/100000000000000 : ℝ)*(f.sum) + (54847542663287/14582500000000000000000000000 : ℝ)*base66 + (4801272760782087/356018066406250000000000000000 : ℝ)*base68 + (353338361969100443/22785156250000000000000000000000 : ℝ)*base70 + (287476995065850443/22785156250000000000000000000000 : ℝ)*base72 + (43220704016941/7291250000000000000000000000 : ℝ)*base74 + (6888162883435267/5696289062500000000000000000000 : ℝ)*base76 + (216650840500756693/22785156250000000000000000000000 : ℝ)*base78 + (32983150761002233/5696289062500000000000000000000 : ℝ)*base79 + (9153840718519/1822812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (19399479/1250000000000000000000 : ℝ)*base89 + (19399479/1250000000000000000000 : ℝ)*base91 + (19399479/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2808413417481656641082178951/729125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572853801/100000000000000 : ℝ)*(base19) + (2270822271/100000000000000 : ℝ)*(base23) + (17361037/20000000000000 : ℝ)*(lower2) + (146145769/100000000000000 : ℝ)*(upper3) + (204069793/100000000000000 : ℝ)*(lower4) + (2753827707872381/100000000000000 : ℝ)*(major0) + (2753827707872381/100000000000000 : ℝ)*(major1) + (2753827707872381/100000000000000 : ℝ)*(major2) + (35750233787/100000000000000 : ℝ)*(sp2) + (297739279/100000000000000 : ℝ)*(sp3) + (117279610221721/3125000000000 : ℝ)*(sp4) + (469118369280159/12500000000000 : ℝ)*(sp5) + (750581901207803/20000000000000 : ℝ)*(sp6) + (1754707462518453/100000000000000 : ℝ)*(sp7) + (1754707760257733/100000000000000 : ℝ)*(f.failure) + (117279610221721/3125000000000 : ℝ)*(f.sum) + (114025023184733/14582500000000000000000000000 : ℝ)*base65 + (13727711632922623683/1458250000000000000000000000000000 : ℝ)*base67 + (4273452164693623683/1458250000000000000000000000000000 : ℝ)*base69 + (14255135858923123683/1458250000000000000000000000000000 : ℝ)*base71 + (10092261689757/3645625000000000000000000000 : ℝ)*base73 + (1611239566324376317/1458250000000000000000000000000000 : ℝ)*base76 + (195224347770376317/1458250000000000000000000000000000 : ℝ)*base78 + (1130004574285123683/1458250000000000000000000000000000 : ℝ)*base79 + (5006909190291/7291250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (40576069/10000000000000000000000 : ℝ)*base89 + (40576069/10000000000000000000000 : ℝ)*base91 + (40576069/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1398_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1398_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1398_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1398_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1398_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1398_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2549/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

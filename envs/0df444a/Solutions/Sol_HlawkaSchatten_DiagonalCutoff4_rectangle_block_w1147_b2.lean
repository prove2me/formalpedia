-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:21.560837+00:00
-- url     : https://prove2.me/submissions/69d7370b-dedf-4fe0-b544-3fcbdb26b4a1

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
theorem support_rectangle_w1147_s6_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164465693/10000000000 : ℝ)*x 0 + (5393279863/10000000000 : ℝ)*x 1 + (263275231/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164465693/10000000000 : ℝ)^2085 ≤ (822038651407/6250000000000 : ℝ)^1573 := by
    have hnat : (2164465693 : ℕ)^2085*6250000000000^1573 ≤ 822038651407^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164465693 10000000000 822038651407 6250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393279863/10000000000 : ℝ)^2085 ≤ (8822731250861/20000000000000 : ℝ)^1573 := by
    have hnat : (5393279863 : ℕ)^2085*20000000000000^1573 ≤ 8822731250861^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393279863 10000000000 8822731250861 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263275231/500000000 : ℝ)^2085 ≤ (5341715663883/12500000000000 : ℝ)^1573 := by
    have hnat : (263275231 : ℕ)^2085*12500000000000^1573 ≤ 5341715663883^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263275231 500000000 5341715663883 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164465693/10000000000 : ℝ), (5393279863/10000000000 : ℝ), (263275231/500000000 : ℝ)] ![(822038651407/6250000000000 : ℝ), (8822731250861/20000000000000 : ℝ), (5341715663883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164465693/10000000000 : ℝ)|^2085 ≤ (822038651407/6250000000000 : ℝ)^1573
        have hw : |(-2164465693/10000000000 : ℝ)|=(2164465693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393279863/10000000000 : ℝ)|^2085 ≤ (8822731250861/20000000000000 : ℝ)^1573
        have hw : |(5393279863/10000000000 : ℝ)|=(5393279863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263275231/500000000 : ℝ)|^2085 ≤ (5341715663883/12500000000000 : ℝ)^1573
        have hw : |(263275231/500000000 : ℝ)|=(263275231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672412163/5000000000 : ℝ)*x 0 + (-557319853/2500000000 : ℝ)*x 1 + (5265504727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672412163/5000000000 : ℝ)^2085 ≤ (43589085501181/100000000000000 : ℝ)^1573 := by
    have hnat : (2672412163 : ℕ)^2085*100000000000000^1573 ≤ 43589085501181^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672412163 5000000000 43589085501181 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557319853/2500000000 : ℝ)^2085 ≤ (53426515697/390625000000 : ℝ)^1573 := by
    have hnat : (557319853 : ℕ)^2085*390625000000^1573 ≤ 53426515697^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557319853 2500000000 53426515697 390625000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265504727/10000000000 : ℝ)^2085 ≤ (10683431615527/25000000000000 : ℝ)^1573 := by
    have hnat : (5265504727 : ℕ)^2085*25000000000000^1573 ≤ 10683431615527^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265504727 10000000000 10683431615527 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672412163/5000000000 : ℝ), (-557319853/2500000000 : ℝ), (5265504727/10000000000 : ℝ)] ![(43589085501181/100000000000000 : ℝ), (53426515697/390625000000 : ℝ), (10683431615527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672412163/5000000000 : ℝ)|^2085 ≤ (43589085501181/100000000000000 : ℝ)^1573
        have hw : |(2672412163/5000000000 : ℝ)|=(2672412163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557319853/2500000000 : ℝ)|^2085 ≤ (53426515697/390625000000 : ℝ)^1573
        have hw : |(-557319853/2500000000 : ℝ)|=(557319853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265504727/10000000000 : ℝ)|^2085 ≤ (10683431615527/25000000000000 : ℝ)^1573
        have hw : |(5265504727/10000000000 : ℝ)|=(5265504727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672412383/5000000000 : ℝ)*x 0 + (329094021/625000000 : ℝ)*x 1 + (-1114639673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672412383/5000000000 : ℝ)^2085 ≤ (43589090257537/100000000000000 : ℝ)^1573 := by
    have hnat : (2672412383 : ℕ)^2085*100000000000000^1573 ≤ 43589090257537^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672412383 5000000000 43589090257537 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329094021/625000000 : ℝ)^2085 ≤ (42733722255957/100000000000000 : ℝ)^1573 := by
    have hnat : (329094021 : ℕ)^2085*100000000000000^1573 ≤ 42733722255957^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329094021 625000000 42733722255957 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114639673/5000000000 : ℝ)^2085 ≤ (2735437496341/20000000000000 : ℝ)^1573 := by
    have hnat : (1114639673 : ℕ)^2085*20000000000000^1573 ≤ 2735437496341^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114639673 5000000000 2735437496341 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672412383/5000000000 : ℝ), (329094021/625000000 : ℝ), (-1114639673/5000000000 : ℝ)] ![(43589090257537/100000000000000 : ℝ), (42733722255957/100000000000000 : ℝ), (2735437496341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672412383/5000000000 : ℝ)|^2085 ≤ (43589090257537/100000000000000 : ℝ)^1573
        have hw : |(2672412383/5000000000 : ℝ)|=(2672412383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329094021/625000000 : ℝ)|^2085 ≤ (42733722255957/100000000000000 : ℝ)^1573
        have hw : |(329094021/625000000 : ℝ)|=(329094021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114639673/5000000000 : ℝ)|^2085 ≤ (2735437496341/20000000000000 : ℝ)^1573
        have hw : |(-1114639673/5000000000 : ℝ)|=(1114639673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181976549/5000000000 : ℝ)*x 0 + (4238567833/10000000000 : ℝ)*x 1 + (2246511787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181976549/5000000000 : ℝ)^2085 ≤ (33316829882243/100000000000000 : ℝ)^1573 := by
    have hnat : (2181976549 : ℕ)^2085*100000000000000^1573 ≤ 33316829882243^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181976549 5000000000 33316829882243 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238567833/10000000000 : ℝ)^2085 ≤ (32053960146833/100000000000000 : ℝ)^1573 := by
    have hnat : (4238567833 : ℕ)^2085*100000000000000^1573 ≤ 32053960146833^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238567833 10000000000 32053960146833 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246511787/5000000000 : ℝ)^2085 ≤ (34629209952377/100000000000000 : ℝ)^1573 := by
    have hnat : (2246511787 : ℕ)^2085*100000000000000^1573 ≤ 34629209952377^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246511787 5000000000 34629209952377 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181976549/5000000000 : ℝ), (4238567833/10000000000 : ℝ), (2246511787/5000000000 : ℝ)] ![(33316829882243/100000000000000 : ℝ), (32053960146833/100000000000000 : ℝ), (34629209952377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181976549/5000000000 : ℝ)|^2085 ≤ (33316829882243/100000000000000 : ℝ)^1573
        have hw : |(2181976549/5000000000 : ℝ)|=(2181976549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238567833/10000000000 : ℝ)|^2085 ≤ (32053960146833/100000000000000 : ℝ)^1573
        have hw : |(4238567833/10000000000 : ℝ)|=(4238567833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246511787/5000000000 : ℝ)|^2085 ≤ (34629209952377/100000000000000 : ℝ)^1573
        have hw : |(2246511787/5000000000 : ℝ)|=(2246511787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-432894169/2000000000 : ℝ)*x 0 + (5265827079/10000000000 : ℝ)*x 1 + (5392956077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432894169/2000000000 : ℝ)^2085 ≤ (13152659919337/100000000000000 : ℝ)^1573 := by
    have hnat : (432894169 : ℕ)^2085*100000000000000^1573 ≤ 13152659919337^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432894169 2000000000 13152659919337 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265827079/10000000000 : ℝ)^2085 ≤ (42737194172273/100000000000000 : ℝ)^1573 := by
    have hnat : (5265827079 : ℕ)^2085*100000000000000^1573 ≤ 42737194172273^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265827079 10000000000 42737194172273 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392956077/10000000000 : ℝ)^2085 ≤ (22055072948767/50000000000000 : ℝ)^1573 := by
    have hnat : (5392956077 : ℕ)^2085*50000000000000^1573 ≤ 22055072948767^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392956077 10000000000 22055072948767 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432894169/2000000000 : ℝ), (5265827079/10000000000 : ℝ), (5392956077/10000000000 : ℝ)] ![(13152659919337/100000000000000 : ℝ), (42737194172273/100000000000000 : ℝ), (22055072948767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432894169/2000000000 : ℝ)|^2085 ≤ (13152659919337/100000000000000 : ℝ)^1573
        have hw : |(-432894169/2000000000 : ℝ)|=(432894169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265827079/10000000000 : ℝ)|^2085 ≤ (42737194172273/100000000000000 : ℝ)^1573
        have hw : |(5265827079/10000000000 : ℝ)|=(5265827079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392956077/10000000000 : ℝ)|^2085 ≤ (22055072948767/50000000000000 : ℝ)^1573
        have hw : |(5392956077/10000000000 : ℝ)|=(5392956077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312440279/10000000000 : ℝ)*x 0 + (-2101827649/10000000000 : ℝ)*x 1 + (674119503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312440279/10000000000 : ℝ)^2085 ≤ (43239362869823/100000000000000 : ℝ)^1573 := by
    have hnat : (5312440279 : ℕ)^2085*100000000000000^1573 ≤ 43239362869823^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312440279 10000000000 43239362869823 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101827649/10000000000 : ℝ)^2085 ≤ (1581311475081/12500000000000 : ℝ)^1573 := by
    have hnat : (2101827649 : ℕ)^2085*12500000000000^1573 ≤ 1581311475081^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101827649 10000000000 1581311475081 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674119503/1250000000 : ℝ)^2085 ≤ (8822029064587/20000000000000 : ℝ)^1573 := by
    have hnat : (674119503 : ℕ)^2085*20000000000000^1573 ≤ 8822029064587^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674119503 1250000000 8822029064587 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312440279/10000000000 : ℝ), (-2101827649/10000000000 : ℝ), (674119503/1250000000 : ℝ)] ![(43239362869823/100000000000000 : ℝ), (1581311475081/12500000000000 : ℝ), (8822029064587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312440279/10000000000 : ℝ)|^2085 ≤ (43239362869823/100000000000000 : ℝ)^1573
        have hw : |(5312440279/10000000000 : ℝ)|=(5312440279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101827649/10000000000 : ℝ)|^2085 ≤ (1581311475081/12500000000000 : ℝ)^1573
        have hw : |(-2101827649/10000000000 : ℝ)|=(2101827649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674119503/1250000000 : ℝ)|^2085 ≤ (8822029064587/20000000000000 : ℝ)^1573
        have hw : |(674119503/1250000000 : ℝ)|=(674119503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531244029/1000000000 : ℝ)*x 0 + (1078591199/2000000000 : ℝ)*x 1 + (-262728459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531244029/1000000000 : ℝ)^2085 ≤ (43239362988497/100000000000000 : ℝ)^1573 := by
    have hnat : (531244029 : ℕ)^2085*100000000000000^1573 ≤ 43239362988497^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531244029 1000000000 43239362988497 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078591199/2000000000 : ℝ)^2085 ≤ (44110145008531/100000000000000 : ℝ)^1573 := by
    have hnat : (1078591199 : ℕ)^2085*100000000000000^1573 ≤ 44110145008531^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078591199 2000000000 44110145008531 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262728459/1250000000 : ℝ)^2085 ≤ (12650491984139/100000000000000 : ℝ)^1573 := by
    have hnat : (262728459 : ℕ)^2085*100000000000000^1573 ≤ 12650491984139^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262728459 1250000000 12650491984139 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531244029/1000000000 : ℝ), (1078591199/2000000000 : ℝ), (-262728459/1250000000 : ℝ)] ![(43239362988497/100000000000000 : ℝ), (44110145008531/100000000000000 : ℝ), (12650491984139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531244029/1000000000 : ℝ)|^2085 ≤ (43239362988497/100000000000000 : ℝ)^1573
        have hw : |(531244029/1000000000 : ℝ)|=(531244029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078591199/2000000000 : ℝ)|^2085 ≤ (44110145008531/100000000000000 : ℝ)^1573
        have hw : |(1078591199/2000000000 : ℝ)|=(1078591199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262728459/1250000000 : ℝ)|^2085 ≤ (12650491984139/100000000000000 : ℝ)^1573
        have hw : |(-262728459/1250000000 : ℝ)|=(262728459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s6_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68186913/156250000 : ℝ)*x 0 + (4492381029/10000000000 : ℝ)*x 1 + (2119606617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68186913/156250000 : ℝ)^2085 ≤ (16658462169049/50000000000000 : ℝ)^1573 := by
    have hnat : (68186913 : ℕ)^2085*50000000000000^1573 ≤ 16658462169049^1573*156250000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68186913 156250000 16658462169049 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492381029/10000000000 : ℝ)^2085 ≤ (34622645860321/100000000000000 : ℝ)^1573 := by
    have hnat : (4492381029 : ℕ)^2085*100000000000000^1573 ≤ 34622645860321^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492381029 10000000000 34622645860321 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119606617/5000000000 : ℝ)^2085 ≤ (6412085957879/20000000000000 : ℝ)^1573 := by
    have hnat : (2119606617 : ℕ)^2085*20000000000000^1573 ≤ 6412085957879^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119606617 5000000000 6412085957879 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68186913/156250000 : ℝ), (4492381029/10000000000 : ℝ), (2119606617/5000000000 : ℝ)] ![(16658462169049/50000000000000 : ℝ), (34622645860321/100000000000000 : ℝ), (6412085957879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68186913/156250000 : ℝ)|^2085 ≤ (16658462169049/50000000000000 : ℝ)^1573
        have hw : |(68186913/156250000 : ℝ)|=(68186913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492381029/10000000000 : ℝ)|^2085 ≤ (34622645860321/100000000000000 : ℝ)^1573
        have hw : |(4492381029/10000000000 : ℝ)|=(4492381029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119606617/5000000000 : ℝ)|^2085 ≤ (6412085957879/20000000000000 : ℝ)^1573
        have hw : |(2119606617/5000000000 : ℝ)|=(2119606617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11323/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (14058594327070673/100000000000000000000 : ℝ) := by
    have hpowers : (11323/100000 : ℝ)^8339 ≤ (14058594327070673/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11323 : ℕ)^8339*100000000000000000000^2048 ≤ 14058594327070673^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11323 100000 14058594327070673 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11323/100000 : ℝ)) (X := (14058594327070673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14091/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (34251576351255781/100000000000000000000 : ℝ) := by
    have hpowers : (14091/100000 : ℝ)^8339 ≤ (34251576351255781/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14091 : ℕ)^8339*100000000000000000000^2048 ≤ 34251576351255781^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14091 100000 34251576351255781 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14091/100000 : ℝ)) (X := (34251576351255781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014058594327070673/50000000000000000000 : ℝ) ≤ (5000345232618209/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50014058594327070673/50000000000000000000 : ℝ)^2048 ≤ (5000345232618209/5000000000000000 : ℝ)^8339 := by
      have hnat : (50014058594327070673 : ℕ)^2048*5000000000000000^8339 ≤ 5000345232618209^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014058594327070673 50000000000000000000 5000345232618209 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000345232618209/5000000000000000 : ℝ)) (X := (50014058594327070673/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024155085339163227/50000000000000000000 : ℝ) ≤ (2000237249562723/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50024155085339163227/50000000000000000000 : ℝ)^2048 ≤ (2000237249562723/2000000000000000 : ℝ)^8339 := by
      have hnat : (50024155085339163227 : ℕ)^2048*2000000000000000^8339 ≤ 2000237249562723^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024155085339163227 50000000000000000000 2000237249562723 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000237249562723/2000000000000000 : ℝ)) (X := (50024155085339163227/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034251576351255781/50000000000000000000 : ℝ) ≤ (2500420507597703/2500000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50034251576351255781/50000000000000000000 : ℝ)^2048 ≤ (2500420507597703/2500000000000000 : ℝ)^8339 := by
      have hnat : (50034251576351255781 : ℕ)^2048*2500000000000000^8339 ≤ 2500420507597703^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034251576351255781 50000000000000000000 2500420507597703 2500000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500420507597703/2500000000000000 : ℝ)) (X := (50034251576351255781/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14058594327070673/100000000000000000000 : ℝ) ≤ ((13835341857765600881/13840000000000000000 : ℝ)+2*(495782577197/276800000000000 : ℝ)*(11323/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (13835341857765600881/13840000000000000000 : ℝ)+2*(495782577197/276800000000000 : ℝ)*(11323/100000 : ℝ)=(5000345232618209/5000000000000000 : ℝ) by norm_num, show 1+2*(14058594327070673/100000000000000000000 : ℝ)=(50014058594327070673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34251576351255781/100000000000000000000 : ℝ)+(14058594327070673/100000000000000000000 : ℝ) ≤ ((13835341857765600881/13840000000000000000 : ℝ)+(495782577197/276800000000000 : ℝ)*((14091/100000 : ℝ)+(11323/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (13835341857765600881/13840000000000000000 : ℝ)+(495782577197/276800000000000 : ℝ)*((14091/100000 : ℝ)+(11323/100000 : ℝ))=(2000237249562723/2000000000000000 : ℝ) by norm_num, show 1+(34251576351255781/100000000000000000000 : ℝ)+(14058594327070673/100000000000000000000 : ℝ)=(50024155085339163227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34251576351255781/100000000000000000000 : ℝ) ≤ ((13835341857765600881/13840000000000000000 : ℝ)+2*(495782577197/276800000000000 : ℝ)*(14091/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (13835341857765600881/13840000000000000000 : ℝ)+2*(495782577197/276800000000000 : ℝ)*(14091/100000 : ℝ)=(2500420507597703/2500000000000000 : ℝ) by norm_num, show 1+2*(34251576351255781/100000000000000000000 : ℝ)=(50034251576351255781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13835341857765600881/13840000000000000000 : ℝ)*(X 1 0+X 2 0)+(495782577197/276800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13835341857765600881/13840000000000000000 : ℝ)) (alpha := (495782577197/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13835341857765600881/13840000000000000000 : ℝ)*(X 0 1+X 2 1)+(495782577197/276800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13835341857765600881/13840000000000000000 : ℝ)) (alpha := (495782577197/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13835341857765600881/13840000000000000000 : ℝ)*(X 0 2+X 1 2)+(495782577197/276800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13835341857765600881/13840000000000000000 : ℝ)) (alpha := (495782577197/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164465693/10000000000 : ℝ)*X 0 0+(5393279863/10000000000 : ℝ)*X 0 1+(263275231/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672412163/5000000000 : ℝ)*X 1 0+(-557319853/2500000000 : ℝ)*X 1 1+(5265504727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672412383/5000000000 : ℝ)*X 2 0+(329094021/625000000 : ℝ)*X 2 1+(-1114639673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181976549/5000000000 : ℝ)*X 0 0+(4238567833/10000000000 : ℝ)*X 0 1+(2246511787/5000000000 : ℝ)*X 0 2+(2181976549/5000000000 : ℝ)*X 1 0+(4238567833/10000000000 : ℝ)*X 1 1+(2246511787/5000000000 : ℝ)*X 1 2+(2181976549/5000000000 : ℝ)*X 2 0+(4238567833/10000000000 : ℝ)*X 2 1+(2246511787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432894169/2000000000 : ℝ)*X 0 0+(5265827079/10000000000 : ℝ)*X 0 1+(5392956077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312440279/10000000000 : ℝ)*X 1 0+(-2101827649/10000000000 : ℝ)*X 1 1+(674119503/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531244029/1000000000 : ℝ)*X 2 0+(1078591199/2000000000 : ℝ)*X 2 1+(-262728459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68186913/156250000 : ℝ)*X 0 0+(4492381029/10000000000 : ℝ)*X 0 1+(2119606617/5000000000 : ℝ)*X 0 2+(68186913/156250000 : ℝ)*X 1 0+(4492381029/10000000000 : ℝ)*X 1 1+(2119606617/5000000000 : ℝ)*X 1 2+(68186913/156250000 : ℝ)*X 2 0+(4492381029/10000000000 : ℝ)*X 2 1+(2119606617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3845098606685593166243854149/692000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431265197/100000000000000 : ℝ)*(base19) + (405830357/100000000000000 : ℝ)*(base23) + (373057093/100000000000000 : ℝ)*(lower2) + (16844459/6250000000000 : ℝ)*(upper3) + (755401/5000000000000 : ℝ)*(lower4) + (1469526377139557/25000000000000 : ℝ)*(major0) + (1469526377139557/25000000000000 : ℝ)*(major1) + (5878105508558229/100000000000000 : ℝ)*(major2) + (3913119923723209/50000000000000 : ℝ)*(sp0) + (7826240860789471/100000000000000 : ℝ)*(sp1) + (7826240886224311/100000000000000 : ℝ)*(sp2) + (785991360288609/20000000000000 : ℝ)*(sp3) + (5778433/400000000000 : ℝ)*(sp4) + (12738402037/100000000000000 : ℝ)*(sp7) + (3929969539845083/100000000000000 : ℝ)*(f.failure) + (1956560323013667/25000000000000 : ℝ)*(f.sum) + (39106457618571/27680000000000000000000000000 : ℝ)*base66 + (1518530683868562217/346000000000000000000000000000000 : ℝ)*base67 + (284361095675999749/1384000000000000000000000000000000 : ℝ)*base69 + (137804225160562217/346000000000000000000000000000000 : ℝ)*base71 + (9187169544949/27680000000000000000000000000 : ℝ)*base73 + (16063285573987999749/1384000000000000000000000000000000 : ℝ)*base75 + (3846913736334400283/346000000000000000000000000000000 : ℝ)*base78 + (14428018617501599717/346000000000000000000000000000000 : ℝ)*base79 + (9095412090009/3460000000000000000000000000 : ℝ)*base81 + (13472871/5000000000000000000000 : ℝ)*base89 + (13472871/5000000000000000000000 : ℝ)*base91 + (36527129/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22026305293885829213667/6920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682013629/100000000000000 : ℝ)*(base19) + (138898127/20000000000000 : ℝ)*(base23) + (7910431/20000000000000 : ℝ)*(upper3) + (7103157/100000000000000 : ℝ)*(lower4) + (42190681/50000000000000 : ℝ)*(upper5) + (2953994159173397/50000000000000 : ℝ)*(major0) + (2953994159173397/50000000000000 : ℝ)*(major1) + (2953994159173397/50000000000000 : ℝ)*(major2) + (18278713549/100000000000000 : ℝ)*(sp1) + (1546000603/10000000000000 : ℝ)*(sp2) + (7866028014178323/100000000000000 : ℝ)*(sp4) + (1573201810690229/20000000000000 : ℝ)*(sp5) + (7866011859681659/100000000000000 : ℝ)*(sp6) + (3949948516415521/100000000000000 : ℝ)*(sp7) + (3949948516415521/100000000000000 : ℝ)*(f.failure) + (7866028014178323/100000000000000 : ℝ)*(f.sum) + (19690140599831/6920000000000000000000000000 : ℝ)*base66 + (12129984363806587243/692000000000000000000000000000000 : ℝ)*base68 + (1482787638165412757/692000000000000000000000000000000 : ℝ)*base69 + (959811602693412757/692000000000000000000000000000000 : ℝ)*base71 + (29222272298511/6920000000000000000000000000 : ℝ)*base74 + (3578596323621412757/692000000000000000000000000000000 : ℝ)*base75 + (535820218718587243/692000000000000000000000000000000 : ℝ)*base78 + (17706489385262587243/692000000000000000000000000000000 : ℝ)*base80 + (1253470881089/6920000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5328123/5000000000000000000000 : ℝ)*base90 + (5328123/5000000000000000000000 : ℝ)*base92 + (5328123/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s7_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164494993/10000000000 : ℝ)*x 0 + (5392964057/10000000000 : ℝ)*x 1 + (1316450239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164494993/10000000000 : ℝ)^2085 ≤ (6576427210013/50000000000000 : ℝ)^1573 := by
    have hnat : (2164494993 : ℕ)^2085*50000000000000^1573 ≤ 6576427210013^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164494993 10000000000 6576427210013 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392964057/10000000000 : ℝ)^2085 ≤ (44110232412639/100000000000000 : ℝ)^1573 := by
    have hnat : (5392964057 : ℕ)^2085*100000000000000^1573 ≤ 44110232412639^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392964057 10000000000 44110232412639 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316450239/2500000000 : ℝ)^2085 ≤ (42736913150837/100000000000000 : ℝ)^1573 := by
    have hnat : (1316450239 : ℕ)^2085*100000000000000^1573 ≤ 42736913150837^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316450239 2500000000 42736913150837 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164494993/10000000000 : ℝ), (5392964057/10000000000 : ℝ), (1316450239/2500000000 : ℝ)] ![(6576427210013/50000000000000 : ℝ), (44110232412639/100000000000000 : ℝ), (42736913150837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164494993/10000000000 : ℝ)|^2085 ≤ (6576427210013/50000000000000 : ℝ)^1573
        have hw : |(-2164494993/10000000000 : ℝ)|=(2164494993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392964057/10000000000 : ℝ)|^2085 ≤ (44110232412639/100000000000000 : ℝ)^1573
        have hw : |(5392964057/10000000000 : ℝ)|=(5392964057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316450239/2500000000 : ℝ)|^2085 ≤ (42736913150837/100000000000000 : ℝ)^1573
        have hw : |(1316450239/2500000000 : ℝ)|=(1316450239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267237237/500000000 : ℝ)*x 0 + (-2228993341/10000000000 : ℝ)*x 1 + (2632900477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267237237/500000000 : ℝ)^2085 ≤ (43588225186599/100000000000000 : ℝ)^1573 := by
    have hnat : (267237237 : ℕ)^2085*100000000000000^1573 ≤ 43588225186599^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267237237 500000000 43588225186599 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228993341/10000000000 : ℝ)^2085 ≤ (6837430835937/50000000000000 : ℝ)^1573 := by
    have hnat : (2228993341 : ℕ)^2085*50000000000000^1573 ≤ 6837430835937^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228993341 10000000000 6837430835937 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632900477/5000000000 : ℝ)^2085 ≤ (42736913129321/100000000000000 : ℝ)^1573 := by
    have hnat : (2632900477 : ℕ)^2085*100000000000000^1573 ≤ 42736913129321^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632900477 5000000000 42736913129321 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267237237/500000000 : ℝ), (-2228993341/10000000000 : ℝ), (2632900477/5000000000 : ℝ)] ![(43588225186599/100000000000000 : ℝ), (6837430835937/50000000000000 : ℝ), (42736913129321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267237237/500000000 : ℝ)|^2085 ≤ (43588225186599/100000000000000 : ℝ)^1573
        have hw : |(267237237/500000000 : ℝ)|=(267237237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228993341/10000000000 : ℝ)|^2085 ≤ (6837430835937/50000000000000 : ℝ)^1573
        have hw : |(-2228993341/10000000000 : ℝ)|=(2228993341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632900477/5000000000 : ℝ)|^2085 ≤ (42736913129321/100000000000000 : ℝ)^1573
        have hw : |(2632900477/5000000000 : ℝ)|=(2632900477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344744739/10000000000 : ℝ)*x 0 + (2632900477/5000000000 : ℝ)*x 1 + (-1114496671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344744739/10000000000 : ℝ)^2085 ≤ (4358822517579/10000000000000 : ℝ)^1573 := by
    have hnat : (5344744739 : ℕ)^2085*10000000000000^1573 ≤ 4358822517579^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344744739 10000000000 4358822517579 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632900477/5000000000 : ℝ)^2085 ≤ (42736913129321/100000000000000 : ℝ)^1573 := by
    have hnat : (2632900477 : ℕ)^2085*100000000000000^1573 ≤ 42736913129321^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632900477 5000000000 42736913129321 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114496671/5000000000 : ℝ)^2085 ≤ (6837430840003/50000000000000 : ℝ)^1573 := by
    have hnat : (1114496671 : ℕ)^2085*50000000000000^1573 ≤ 6837430840003^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114496671 5000000000 6837430840003 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344744739/10000000000 : ℝ), (2632900477/5000000000 : ℝ), (-1114496671/5000000000 : ℝ)] ![(4358822517579/10000000000000 : ℝ), (42736913129321/100000000000000 : ℝ), (6837430840003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344744739/10000000000 : ℝ)|^2085 ≤ (4358822517579/10000000000000 : ℝ)^1573
        have hw : |(5344744739/10000000000 : ℝ)|=(5344744739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632900477/5000000000 : ℝ)|^2085 ≤ (42736913129321/100000000000000 : ℝ)^1573
        have hw : |(2632900477/5000000000 : ℝ)|=(2632900477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114496671/5000000000 : ℝ)|^2085 ≤ (6837430840003/50000000000000 : ℝ)^1573
        have hw : |(-1114496671/5000000000 : ℝ)|=(1114496671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181984099/5000000000 : ℝ)*x 0 + (4239176003/10000000000 : ℝ)*x 1 + (1123102963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181984099/5000000000 : ℝ)^2085 ≤ (33316982687441/100000000000000 : ℝ)^1573 := by
    have hnat : (2181984099 : ℕ)^2085*100000000000000^1573 ≤ 33316982687441^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181984099 5000000000 33316982687441 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239176003/10000000000 : ℝ)^2085 ≤ (32060056568891/100000000000000 : ℝ)^1573 := by
    have hnat : (4239176003 : ℕ)^2085*100000000000000^1573 ≤ 32060056568891^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239176003 10000000000 32060056568891 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123102963/2500000000 : ℝ)^2085 ≤ (8655740183507/25000000000000 : ℝ)^1573 := by
    have hnat : (1123102963 : ℕ)^2085*25000000000000^1573 ≤ 8655740183507^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123102963 2500000000 8655740183507 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181984099/5000000000 : ℝ), (4239176003/10000000000 : ℝ), (1123102963/2500000000 : ℝ)] ![(33316982687441/100000000000000 : ℝ), (32060056568891/100000000000000 : ℝ), (8655740183507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181984099/5000000000 : ℝ)|^2085 ≤ (33316982687441/100000000000000 : ℝ)^1573
        have hw : |(2181984099/5000000000 : ℝ)|=(2181984099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239176003/10000000000 : ℝ)|^2085 ≤ (32060056568891/100000000000000 : ℝ)^1573
        have hw : |(4239176003/10000000000 : ℝ)|=(4239176003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123102963/2500000000 : ℝ)|^2085 ≤ (8655740183507/25000000000000 : ℝ)^1573
        have hw : |(1123102963/2500000000 : ℝ)|=(1123102963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-54112491/250000000 : ℝ)*x 0 + (5266120839/10000000000 : ℝ)*x 1 + (5392643191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54112491/250000000 : ℝ)^2085 ≤ (822055740593/6250000000000 : ℝ)^1573 := by
    have hnat : (54112491 : ℕ)^2085*6250000000000^1573 ≤ 822055740593^1573*250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54112491 250000000 822055740593 6250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266120839/10000000000 : ℝ)^2085 ≤ (5342544295427/12500000000000 : ℝ)^1573 := by
    have hnat : (5266120839 : ℕ)^2085*12500000000000^1573 ≤ 5342544295427^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266120839 10000000000 5342544295427 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392643191/10000000000 : ℝ)^2085 ≤ (1764270151173/4000000000000 : ℝ)^1573 := by
    have hnat : (5392643191 : ℕ)^2085*4000000000000^1573 ≤ 1764270151173^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392643191 10000000000 1764270151173 4000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54112491/250000000 : ℝ), (5266120839/10000000000 : ℝ), (5392643191/10000000000 : ℝ)] ![(822055740593/6250000000000 : ℝ), (5342544295427/12500000000000 : ℝ), (1764270151173/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54112491/250000000 : ℝ)|^2085 ≤ (822055740593/6250000000000 : ℝ)^1573
        have hw : |(-54112491/250000000 : ℝ)|=(54112491/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266120839/10000000000 : ℝ)|^2085 ≤ (5342544295427/12500000000000 : ℝ)^1573
        have hw : |(5266120839/10000000000 : ℝ)|=(5266120839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392643191/10000000000 : ℝ)|^2085 ≤ (1764270151173/4000000000000 : ℝ)^1573
        have hw : |(5392643191/10000000000 : ℝ)|=(5392643191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656257547/5000000000 : ℝ)*x 0 + (-420430231/2000000000 : ℝ)*x 1 + (5392643507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656257547/5000000000 : ℝ)^2085 ≤ (43240170016081/100000000000000 : ℝ)^1573 := by
    have hnat : (2656257547 : ℕ)^2085*100000000000000^1573 ≤ 43240170016081^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656257547 5000000000 43240170016081 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420430231/2000000000 : ℝ)^2085 ≤ (1265307275821/10000000000000 : ℝ)^1573 := by
    have hnat : (420430231 : ℕ)^2085*10000000000000^1573 ≤ 1265307275821^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420430231 2000000000 1265307275821 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392643507/10000000000 : ℝ)^2085 ≤ (44106757205171/100000000000000 : ℝ)^1573 := by
    have hnat : (5392643507 : ℕ)^2085*100000000000000^1573 ≤ 44106757205171^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392643507 10000000000 44106757205171 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656257547/5000000000 : ℝ), (-420430231/2000000000 : ℝ), (5392643507/10000000000 : ℝ)] ![(43240170016081/100000000000000 : ℝ), (1265307275821/10000000000000 : ℝ), (44106757205171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656257547/5000000000 : ℝ)|^2085 ≤ (43240170016081/100000000000000 : ℝ)^1573
        have hw : |(2656257547/5000000000 : ℝ)|=(2656257547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420430231/2000000000 : ℝ)|^2085 ≤ (1265307275821/10000000000000 : ℝ)^1573
        have hw : |(-420430231/2000000000 : ℝ)|=(420430231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392643507/10000000000 : ℝ)|^2085 ≤ (44106757205171/100000000000000 : ℝ)^1573
        have hw : |(5392643507/10000000000 : ℝ)|=(5392643507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656257531/5000000000 : ℝ)*x 0 + (1078528721/2000000000 : ℝ)*x 1 + (-420430213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656257531/5000000000 : ℝ)^2085 ≤ (21620084835423/50000000000000 : ℝ)^1573 := by
    have hnat : (2656257531 : ℕ)^2085*50000000000000^1573 ≤ 21620084835423^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656257531 5000000000 21620084835423 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078528721/2000000000 : ℝ)^2085 ≤ (44106758267617/100000000000000 : ℝ)^1573 := by
    have hnat : (1078528721 : ℕ)^2085*100000000000000^1573 ≤ 44106758267617^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078528721 2000000000 44106758267617 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420430213/2000000000 : ℝ)^2085 ≤ (3163268010041/25000000000000 : ℝ)^1573 := by
    have hnat : (420430213 : ℕ)^2085*25000000000000^1573 ≤ 3163268010041^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420430213 2000000000 3163268010041 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656257531/5000000000 : ℝ), (1078528721/2000000000 : ℝ), (-420430213/2000000000 : ℝ)] ![(21620084835423/50000000000000 : ℝ), (44106758267617/100000000000000 : ℝ), (3163268010041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656257531/5000000000 : ℝ)|^2085 ≤ (21620084835423/50000000000000 : ℝ)^1573
        have hw : |(2656257531/5000000000 : ℝ)|=(2656257531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078528721/2000000000 : ℝ)|^2085 ≤ (44106758267617/100000000000000 : ℝ)^1573
        have hw : |(1078528721/2000000000 : ℝ)|=(1078528721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420430213/2000000000 : ℝ)|^2085 ≤ (3163268010041/25000000000000 : ℝ)^1573
        have hw : |(-420430213/2000000000 : ℝ)|=(420430213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s7_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174559117/400000000 : ℝ)*x 0 + (4491775219/10000000000 : ℝ)*x 1 + (4239814923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174559117/400000000 : ℝ)^2085 ≤ (3331708112039/10000000000000 : ℝ)^1573 := by
    have hnat : (174559117 : ℕ)^2085*10000000000000^1573 ≤ 3331708112039^1573*400000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174559117 400000000 3331708112039 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491775219/10000000000 : ℝ)^2085 ≤ (17308228662231/50000000000000 : ℝ)^1573 := by
    have hnat : (4491775219 : ℕ)^2085*50000000000000^1573 ≤ 17308228662231^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491775219 10000000000 17308228662231 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239814923/10000000000 : ℝ)^2085 ≤ (16033230770981/50000000000000 : ℝ)^1573 := by
    have hnat : (4239814923 : ℕ)^2085*50000000000000^1573 ≤ 16033230770981^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239814923 10000000000 16033230770981 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174559117/400000000 : ℝ), (4491775219/10000000000 : ℝ), (4239814923/10000000000 : ℝ)] ![(3331708112039/10000000000000 : ℝ), (17308228662231/50000000000000 : ℝ), (16033230770981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174559117/400000000 : ℝ)|^2085 ≤ (3331708112039/10000000000000 : ℝ)^1573
        have hw : |(174559117/400000000 : ℝ)|=(174559117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491775219/10000000000 : ℝ)|^2085 ≤ (17308228662231/50000000000000 : ℝ)^1573
        have hw : |(4491775219/10000000000 : ℝ)|=(4491775219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239814923/10000000000 : ℝ)|^2085 ≤ (16033230770981/50000000000000 : ℝ)^1573
        have hw : |(4239814923/10000000000 : ℝ)|=(4239814923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11353/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (14210877731903533/100000000000000000000 : ℝ) := by
    have hpowers : (11353/100000 : ℝ)^8339 ≤ (14210877731903533/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11353 : ℕ)^8339*100000000000000000000^2048 ≤ 14210877731903533^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11353 100000 14210877731903533 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11353/100000 : ℝ)) (X := (14210877731903533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (33935961308665753/100000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^8339 ≤ (33935961308665753/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14059 : ℕ)^8339*100000000000000000000^2048 ≤ 33935961308665753^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 33935961308665753 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (33935961308665753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014210877731903533/50000000000000000000 : ℝ) ≤ (5000348971794569/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50014210877731903533/50000000000000000000 : ℝ)^2048 ≤ (5000348971794569/5000000000000000 : ℝ)^8339 := by
      have hnat : (50014210877731903533 : ℕ)^2048*5000000000000000^8339 ≤ 5000348971794569^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014210877731903533 50000000000000000000 5000348971794569 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348971794569/5000000000000000 : ℝ)) (X := (50014210877731903533/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024073419520284643/50000000000000000000 : ℝ) ≤ (1250147779745229/1250000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50024073419520284643/50000000000000000000 : ℝ)^2048 ≤ (1250147779745229/1250000000000000 : ℝ)^8339 := by
      have hnat : (50024073419520284643 : ℕ)^2048*1250000000000000^8339 ≤ 1250147779745229^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024073419520284643 50000000000000000000 1250147779745229 1250000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250147779745229/1250000000000000 : ℝ)) (X := (50024073419520284643/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033935961308665753/50000000000000000000 : ℝ) ≤ (5000833266167263/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50033935961308665753/50000000000000000000 : ℝ)^2048 ≤ (5000833266167263/5000000000000000 : ℝ)^8339 := by
      have hnat : (50033935961308665753 : ℕ)^2048*5000000000000000^8339 ≤ 5000833266167263^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033935961308665753 50000000000000000000 5000833266167263 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000833266167263/5000000000000000 : ℝ)) (X := (50033935961308665753/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14210877731903533/100000000000000000000 : ℝ) ≤ ((307396502810520653/307500000000000000 : ℝ)+2*(22013380577/12300000000000 : ℝ)*(11353/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (307396502810520653/307500000000000000 : ℝ)+2*(22013380577/12300000000000 : ℝ)*(11353/100000 : ℝ)=(5000348971794569/5000000000000000 : ℝ) by norm_num, show 1+2*(14210877731903533/100000000000000000000 : ℝ)=(50014210877731903533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33935961308665753/100000000000000000000 : ℝ)+(14210877731903533/100000000000000000000 : ℝ) ≤ ((307396502810520653/307500000000000000 : ℝ)+(22013380577/12300000000000 : ℝ)*((14059/100000 : ℝ)+(11353/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (307396502810520653/307500000000000000 : ℝ)+(22013380577/12300000000000 : ℝ)*((14059/100000 : ℝ)+(11353/100000 : ℝ))=(1250147779745229/1250000000000000 : ℝ) by norm_num, show 1+(33935961308665753/100000000000000000000 : ℝ)+(14210877731903533/100000000000000000000 : ℝ)=(50024073419520284643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33935961308665753/100000000000000000000 : ℝ) ≤ ((307396502810520653/307500000000000000 : ℝ)+2*(22013380577/12300000000000 : ℝ)*(14059/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (307396502810520653/307500000000000000 : ℝ)+2*(22013380577/12300000000000 : ℝ)*(14059/100000 : ℝ)=(5000833266167263/5000000000000000 : ℝ) by norm_num, show 1+2*(33935961308665753/100000000000000000000 : ℝ)=(50033935961308665753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (307396502810520653/307500000000000000 : ℝ)*(X 1 0+X 2 0)+(22013380577/12300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (307396502810520653/307500000000000000 : ℝ)) (alpha := (22013380577/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (307396502810520653/307500000000000000 : ℝ)*(X 0 1+X 2 1)+(22013380577/12300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (307396502810520653/307500000000000000 : ℝ)) (alpha := (22013380577/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (307396502810520653/307500000000000000 : ℝ)*(X 0 2+X 1 2)+(22013380577/12300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (307396502810520653/307500000000000000 : ℝ)) (alpha := (22013380577/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164494993/10000000000 : ℝ)*X 0 0+(5392964057/10000000000 : ℝ)*X 0 1+(1316450239/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267237237/500000000 : ℝ)*X 1 0+(-2228993341/10000000000 : ℝ)*X 1 1+(2632900477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344744739/10000000000 : ℝ)*X 2 0+(2632900477/5000000000 : ℝ)*X 2 1+(-1114496671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181984099/5000000000 : ℝ)*X 0 0+(4239176003/10000000000 : ℝ)*X 0 1+(1123102963/2500000000 : ℝ)*X 0 2+(2181984099/5000000000 : ℝ)*X 1 0+(4239176003/10000000000 : ℝ)*X 1 1+(1123102963/2500000000 : ℝ)*X 1 2+(2181984099/5000000000 : ℝ)*X 2 0+(4239176003/10000000000 : ℝ)*X 2 1+(1123102963/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54112491/250000000 : ℝ)*X 0 0+(5266120839/10000000000 : ℝ)*X 0 1+(5392643191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656257547/5000000000 : ℝ)*X 1 0+(-420430231/2000000000 : ℝ)*X 1 1+(5392643507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656257531/5000000000 : ℝ)*X 2 0+(1078528721/2000000000 : ℝ)*X 2 1+(-420430213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174559117/400000000 : ℝ)*X 0 0+(4491775219/10000000000 : ℝ)*X 0 1+(4239814923/10000000000 : ℝ)*X 0 2+(174559117/400000000 : ℝ)*X 1 0+(4491775219/10000000000 : ℝ)*X 1 1+(4239814923/10000000000 : ℝ)*X 1 2+(174559117/400000000 : ℝ)*X 2 0+(4491775219/10000000000 : ℝ)*X 2 1+(4239814923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9208528661111868550888001/1281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (709314017/50000000000000 : ℝ)*(base19) + (1317068693/100000000000000 : ℝ)*(base23) + (53494477/100000000000000 : ℝ)*(lower2) + (18292649/10000000000000 : ℝ)*(upper3) + (4271673/4000000000000 : ℝ)*(upper5) + (5906461660239267/100000000000000 : ℝ)*(major0) + (5906461660239267/100000000000000 : ℝ)*(major1) + (1476615415059817/25000000000000 : ℝ)*(major2) + (7863956851247001/100000000000000 : ℝ)*(sp0) + (7863993835242341/100000000000000 : ℝ)*(sp1) + (7863993936801683/100000000000000 : ℝ)*(sp2) + (1974453404702087/50000000000000 : ℝ)*(sp3) + (307220987/800000000000 : ℝ)*(sp4) + (10508816249/50000000000000 : ℝ)*(sp7) + (7712749662181/195312500000 : ℝ)*(f.failure) + (62911962030963/800000000000 : ℝ)*(f.sum) + (5675041697/1968000000000000000000000 : ℝ)*base65 + (145583615413518649/30750000000000000000000000000000 : ℝ)*base68 + (2489916322543249/7687500000000000000000000000000 : ℝ)*base70 + (289693606924481351/30750000000000000000000000000000 : ℝ)*base71 + (894253983599/246000000000000000000000000 : ℝ)*base74 + (84514547582480749/7687500000000000000000000000000 : ℝ)*base76 + (147471606984102117/10250000000000000000000000000000 : ℝ)*base77 + (35100863367647883/10250000000000000000000000000000 : ℝ)*base80 + (913001707427/205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (94687/39062500000000000000 : ℝ)*base90 + (94687/39062500000000000000 : ℝ)*base92 + (7583/610351562500000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6530642393477881330581183/512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48908859/10000000000000 : ℝ)*(base19) + (564863339/50000000000000 : ℝ)*(base23) + (59263151/25000000000000 : ℝ)*(upper3) + (140625259/50000000000000 : ℝ)*(lower4) + (100118271/100000000000000 : ℝ)*(upper5) + (593630394569489/10000000000000 : ℝ)*(major0) + (593630394569489/10000000000000 : ℝ)*(major1) + (593630394569489/10000000000000 : ℝ)*(major2) + (18767025469/100000000000000 : ℝ)*(sp1) + (11237067237/25000000000000 : ℝ)*(sp2) + (7903727756685767/100000000000000 : ℝ)*(sp4) + (7903708500571707/100000000000000 : ℝ)*(sp5) + (395184083934507/5000000000000 : ℝ)*(sp6) + (396887970994677/10000000000000 : ℝ)*(sp7) + (396887970994677/10000000000000 : ℝ)*(f.failure) + (7903727756685767/100000000000000 : ℝ)*(f.sum) + (176796535199/30750000000000000000000000 : ℝ)*base65 + (5257782992256317/3075000000000000000000000000000 : ℝ)*base67 + (14737158704543683/3075000000000000000000000000000 : ℝ)*base70 + (46306604895381317/3075000000000000000000000000000 : ℝ)*base71 + (233479210481/61500000000000000000000000 : ℝ)*base74 + (4313107808106317/3075000000000000000000000000000 : ℝ)*base75 + (9690143661668683/3075000000000000000000000000000 : ℝ)*base78 + (47996800311831317/3075000000000000000000000000000 : ℝ)*base79 + (25571816711/30750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6945751/500000000000000000000 : ℝ)*base90 + (6945751/500000000000000000000 : ℝ)*base92 + (6945751/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s8_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-541124831/2500000000 : ℝ)*x 0 + (2696452091/5000000000 : ℝ)*x 1 + (1053171611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541124831/2500000000 : ℝ)^2085 ≤ (13152889304251/100000000000000 : ℝ)^1573 := by
    have hnat : (541124831 : ℕ)^2085*100000000000000^1573 ≤ 13152889304251^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541124831 2500000000 13152889304251 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696452091/5000000000 : ℝ)^2085 ≤ (1764383331173/4000000000000 : ℝ)^1573 := by
    have hnat : (2696452091 : ℕ)^2085*4000000000000^1573 ≤ 1764383331173^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696452091 5000000000 1764383331173 4000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053171611/2000000000 : ℝ)^2085 ≤ (42737527401051/100000000000000 : ℝ)^1573 := by
    have hnat : (1053171611 : ℕ)^2085*100000000000000^1573 ≤ 42737527401051^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053171611 2000000000 42737527401051 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541124831/2500000000 : ℝ), (2696452091/5000000000 : ℝ), (1053171611/2000000000 : ℝ)] ![(13152889304251/100000000000000 : ℝ), (1764383331173/4000000000000 : ℝ), (42737527401051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541124831/2500000000 : ℝ)|^2085 ≤ (13152889304251/100000000000000 : ℝ)^1573
        have hw : |(-541124831/2500000000 : ℝ)|=(541124831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696452091/5000000000 : ℝ)|^2085 ≤ (1764383331173/4000000000000 : ℝ)^1573
        have hw : |(2696452091/5000000000 : ℝ)|=(2696452091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053171611/2000000000 : ℝ)|^2085 ≤ (42737527401051/100000000000000 : ℝ)^1573
        have hw : |(1053171611/2000000000 : ℝ)|=(1053171611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267236497/500000000 : ℝ)*x 0 + (-2228937503/10000000000 : ℝ)*x 1 + (1053171607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267236497/500000000 : ℝ)^2085 ≤ (43588065200933/100000000000000 : ℝ)^1573 := by
    have hnat : (267236497 : ℕ)^2085*100000000000000^1573 ≤ 43588065200933^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267236497 500000000 43588065200933 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228937503/10000000000 : ℝ)^2085 ≤ (13674407605239/100000000000000 : ℝ)^1573 := by
    have hnat : (2228937503 : ℕ)^2085*100000000000000^1573 ≤ 13674407605239^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228937503 10000000000 13674407605239 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053171607/2000000000 : ℝ)^2085 ≤ (21368763592949/50000000000000 : ℝ)^1573 := by
    have hnat : (1053171607 : ℕ)^2085*50000000000000^1573 ≤ 21368763592949^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053171607 2000000000 21368763592949 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267236497/500000000 : ℝ), (-2228937503/10000000000 : ℝ), (1053171607/2000000000 : ℝ)] ![(43588065200933/100000000000000 : ℝ), (13674407605239/100000000000000 : ℝ), (21368763592949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267236497/500000000 : ℝ)|^2085 ≤ (43588065200933/100000000000000 : ℝ)^1573
        have hw : |(267236497/500000000 : ℝ)|=(267236497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228937503/10000000000 : ℝ)|^2085 ≤ (13674407605239/100000000000000 : ℝ)^1573
        have hw : |(-2228937503/10000000000 : ℝ)|=(2228937503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053171607/2000000000 : ℝ)|^2085 ≤ (21368763592949/50000000000000 : ℝ)^1573
        have hw : |(1053171607/2000000000 : ℝ)|=(1053171607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068945983/2000000000 : ℝ)*x 0 + (5265858059/10000000000 : ℝ)*x 1 + (-2228937503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068945983/2000000000 : ℝ)^2085 ≤ (43588064930687/100000000000000 : ℝ)^1573 := by
    have hnat : (1068945983 : ℕ)^2085*100000000000000^1573 ≤ 43588064930687^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068945983 2000000000 43588064930687 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265858059/10000000000 : ℝ)^2085 ≤ (42737527444081/100000000000000 : ℝ)^1573 := by
    have hnat : (5265858059 : ℕ)^2085*100000000000000^1573 ≤ 42737527444081^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265858059 10000000000 42737527444081 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228937503/10000000000 : ℝ)^2085 ≤ (13674407605239/100000000000000 : ℝ)^1573 := by
    have hnat : (2228937503 : ℕ)^2085*100000000000000^1573 ≤ 13674407605239^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228937503 10000000000 13674407605239 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068945983/2000000000 : ℝ), (5265858059/10000000000 : ℝ), (-2228937503/10000000000 : ℝ)] ![(43588064930687/100000000000000 : ℝ), (42737527444081/100000000000000 : ℝ), (13674407605239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068945983/2000000000 : ℝ)|^2085 ≤ (43588064930687/100000000000000 : ℝ)^1573
        have hw : |(1068945983/2000000000 : ℝ)|=(1068945983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265858059/10000000000 : ℝ)|^2085 ≤ (42737527444081/100000000000000 : ℝ)^1573
        have hw : |(5265858059/10000000000 : ℝ)|=(5265858059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228937503/10000000000 : ℝ)|^2085 ≤ (13674407605239/100000000000000 : ℝ)^1573
        have hw : |(-2228937503/10000000000 : ℝ)|=(2228937503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363971137/10000000000 : ℝ)*x 0 + (847858423/2000000000 : ℝ)*x 1 + (4492294999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363971137/10000000000 : ℝ)^2085 ≤ (33317012428817/100000000000000 : ℝ)^1573 := by
    have hnat : (4363971137 : ℕ)^2085*100000000000000^1573 ≤ 33317012428817^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363971137 10000000000 33317012428817 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847858423/2000000000 : ℝ)^2085 ≤ (8015305132999/25000000000000 : ℝ)^1573 := by
    have hnat : (847858423 : ℕ)^2085*25000000000000^1573 ≤ 8015305132999^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847858423 2000000000 8015305132999 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492294999/10000000000 : ℝ)^2085 ≤ (4327720877601/12500000000000 : ℝ)^1573 := by
    have hnat : (4492294999 : ℕ)^2085*12500000000000^1573 ≤ 4327720877601^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492294999 10000000000 4327720877601 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363971137/10000000000 : ℝ), (847858423/2000000000 : ℝ), (4492294999/10000000000 : ℝ)] ![(33317012428817/100000000000000 : ℝ), (8015305132999/25000000000000 : ℝ), (4327720877601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363971137/10000000000 : ℝ)|^2085 ≤ (33317012428817/100000000000000 : ℝ)^1573
        have hw : |(4363971137/10000000000 : ℝ)|=(4363971137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847858423/2000000000 : ℝ)|^2085 ≤ (8015305132999/25000000000000 : ℝ)^1573
        have hw : |(847858423/2000000000 : ℝ)|=(847858423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492294999/10000000000 : ℝ)|^2085 ≤ (4327720877601/12500000000000 : ℝ)^1573
        have hw : |(4492294999/10000000000 : ℝ)|=(4492294999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164504157/10000000000 : ℝ)*x 0 + (5266177143/10000000000 : ℝ)*x 1 + (1348145991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164504157/10000000000 : ℝ)^2085 ≤ (2630585646377/20000000000000 : ℝ)^1573 := by
    have hnat : (2164504157 : ℕ)^2085*20000000000000^1573 ≤ 2630585646377^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164504157 10000000000 2630585646377 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266177143/10000000000 : ℝ)^2085 ≤ (42740960073271/100000000000000 : ℝ)^1573 := by
    have hnat : (5266177143 : ℕ)^2085*100000000000000^1573 ≤ 42740960073271^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266177143 10000000000 42740960073271 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348145991/2500000000 : ℝ)^2085 ≤ (11026527920927/25000000000000 : ℝ)^1573 := by
    have hnat : (1348145991 : ℕ)^2085*25000000000000^1573 ≤ 11026527920927^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348145991 2500000000 11026527920927 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164504157/10000000000 : ℝ), (5266177143/10000000000 : ℝ), (1348145991/2500000000 : ℝ)] ![(2630585646377/20000000000000 : ℝ), (42740960073271/100000000000000 : ℝ), (11026527920927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164504157/10000000000 : ℝ)|^2085 ≤ (2630585646377/20000000000000 : ℝ)^1573
        have hw : |(-2164504157/10000000000 : ℝ)|=(2164504157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266177143/10000000000 : ℝ)|^2085 ≤ (42740960073271/100000000000000 : ℝ)^1573
        have hw : |(5266177143/10000000000 : ℝ)|=(5266177143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348145991/2500000000 : ℝ)|^2085 ≤ (11026527920927/25000000000000 : ℝ)^1573
        have hw : |(1348145991/2500000000 : ℝ)|=(1348145991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656265127/5000000000 : ℝ)*x 0 + (-525552891/2500000000 : ℝ)*x 1 + (1078516793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656265127/5000000000 : ℝ)^2085 ≤ (4324033357113/10000000000000 : ℝ)^1573 := by
    have hnat : (2656265127 : ℕ)^2085*10000000000000^1573 ≤ 4324033357113^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656265127 5000000000 4324033357113 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525552891/2500000000 : ℝ)^2085 ≤ (12653554720521/100000000000000 : ℝ)^1573 := by
    have hnat : (525552891 : ℕ)^2085*100000000000000^1573 ≤ 12653554720521^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525552891 2500000000 12653554720521 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078516793/2000000000 : ℝ)^2085 ≤ (882122233891/2000000000000 : ℝ)^1573 := by
    have hnat : (1078516793 : ℕ)^2085*2000000000000^1573 ≤ 882122233891^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078516793 2000000000 882122233891 2000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656265127/5000000000 : ℝ), (-525552891/2500000000 : ℝ), (1078516793/2000000000 : ℝ)] ![(4324033357113/10000000000000 : ℝ), (12653554720521/100000000000000 : ℝ), (882122233891/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656265127/5000000000 : ℝ)|^2085 ≤ (4324033357113/10000000000000 : ℝ)^1573
        have hw : |(2656265127/5000000000 : ℝ)|=(2656265127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525552891/2500000000 : ℝ)|^2085 ≤ (12653554720521/100000000000000 : ℝ)^1573
        have hw : |(-525552891/2500000000 : ℝ)|=(525552891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078516793/2000000000 : ℝ)|^2085 ≤ (882122233891/2000000000000 : ℝ)^1573
        have hw : |(1078516793/2000000000 : ℝ)|=(1078516793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328132561/2500000000 : ℝ)*x 0 + (1078516793/2000000000 : ℝ)*x 1 + (-1051105789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328132561/2500000000 : ℝ)^2085 ≤ (10810083365811/25000000000000 : ℝ)^1573 := by
    have hnat : (1328132561 : ℕ)^2085*25000000000000^1573 ≤ 10810083365811^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328132561 2500000000 10810083365811 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078516793/2000000000 : ℝ)^2085 ≤ (882122233891/2000000000000 : ℝ)^1573 := by
    have hnat : (1078516793 : ℕ)^2085*2000000000000^1573 ≤ 882122233891^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078516793 2000000000 882122233891 2000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051105789/5000000000 : ℝ)^2085 ≤ (6326777416109/50000000000000 : ℝ)^1573 := by
    have hnat : (1051105789 : ℕ)^2085*50000000000000^1573 ≤ 6326777416109^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051105789 5000000000 6326777416109 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328132561/2500000000 : ℝ), (1078516793/2000000000 : ℝ), (-1051105789/5000000000 : ℝ)] ![(10810083365811/25000000000000 : ℝ), (882122233891/2000000000000 : ℝ), (6326777416109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328132561/2500000000 : ℝ)|^2085 ≤ (10810083365811/25000000000000 : ℝ)^1573
        have hw : |(1328132561/2500000000 : ℝ)|=(1328132561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078516793/2000000000 : ℝ)|^2085 ≤ (882122233891/2000000000000 : ℝ)^1573
        have hw : |(1078516793/2000000000 : ℝ)|=(1078516793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051105789/5000000000 : ℝ)|^2085 ≤ (6326777416109/50000000000000 : ℝ)^1573
        have hw : |(-1051105789/5000000000 : ℝ)|=(1051105789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s8_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1090995209/2500000000 : ℝ)*x 0 + (2245829791/5000000000 : ℝ)*x 1 + (4239929813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090995209/2500000000 : ℝ)^2085 ≤ (33317110578439/100000000000000 : ℝ)^1573 := by
    have hnat : (1090995209 : ℕ)^2085*100000000000000^1573 ≤ 33317110578439^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090995209 2500000000 33317110578439 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245829791/5000000000 : ℝ)^2085 ≤ (6923055217549/20000000000000 : ℝ)^1573 := by
    have hnat : (2245829791 : ℕ)^2085*20000000000000^1573 ≤ 6923055217549^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245829791 5000000000 6923055217549 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239929813/10000000000 : ℝ)^2085 ≤ (8016903327897/25000000000000 : ℝ)^1573 := by
    have hnat : (4239929813 : ℕ)^2085*25000000000000^1573 ≤ 8016903327897^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239929813 10000000000 8016903327897 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090995209/2500000000 : ℝ), (2245829791/5000000000 : ℝ), (4239929813/10000000000 : ℝ)] ![(33317110578439/100000000000000 : ℝ), (6923055217549/20000000000000 : ℝ), (8016903327897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090995209/2500000000 : ℝ)|^2085 ≤ (33317110578439/100000000000000 : ℝ)^1573
        have hw : |(1090995209/2500000000 : ℝ)|=(1090995209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245829791/5000000000 : ℝ)|^2085 ≤ (6923055217549/20000000000000 : ℝ)^1573
        have hw : |(2245829791/5000000000 : ℝ)|=(2245829791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239929813/10000000000 : ℝ)|^2085 ≤ (8016903327897/25000000000000 : ℝ)^1573
        have hw : |(4239929813/10000000000 : ℝ)|=(4239929813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (71/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11359/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (1780185391340957/12500000000000000000 : ℝ) := by
    have hpowers : (11359/100000 : ℝ)^8339 ≤ (1780185391340957/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11359 : ℕ)^8339*12500000000000000000^2048 ≤ 1780185391340957^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359 100000 1780185391340957 12500000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11359/100000 : ℝ)) (X := (1780185391340957/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (271016228891667/800000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^8339 ≤ (271016228891667/800000000000000000 : ℝ)^2048 := by
      have hnat : (14053 : ℕ)^8339*800000000000000000^2048 ≤ 271016228891667^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 271016228891667 800000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (271016228891667/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251780185391340957/6250000000000000000 : ℝ) ≤ (2000139889312173/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (6251780185391340957/6250000000000000000 : ℝ)^2048 ≤ (2000139889312173/2000000000000000 : ℝ)^8339 := by
      have hnat : (6251780185391340957 : ℕ)^2048*2000000000000000^8339 ≤ 2000139889312173^8339*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251780185391340957 6250000000000000000 2000139889312173 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000139889312173/2000000000000000 : ℝ)) (X := (6251780185391340957/6250000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048118511742186031/100000000000000000000 : ℝ) ≤ (2000236308503147/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (100048118511742186031/100000000000000000000 : ℝ)^2048 ≤ (2000236308503147/2000000000000000 : ℝ)^8339 := by
      have hnat : (100048118511742186031 : ℕ)^2048*2000000000000000^8339 ≤ 2000236308503147^8339*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048118511742186031 100000000000000000000 2000236308503147 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000236308503147/2000000000000000 : ℝ)) (X := (100048118511742186031/100000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (400271016228891667/400000000000000000 : ℝ) ≤ (2000332727694121/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (400271016228891667/400000000000000000 : ℝ)^2048 ≤ (2000332727694121/2000000000000000 : ℝ)^8339 := by
      have hnat : (400271016228891667 : ℕ)^2048*2000000000000000^8339 ≤ 2000332727694121^8339*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400271016228891667 400000000000000000 2000332727694121 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000332727694121/2000000000000000 : ℝ)) (X := (400271016228891667/400000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1780185391340957/12500000000000000000 : ℝ) ≤ ((538618641062644673/538800000000000000 : ℝ)+2*(48209595487/26940000000000 : ℝ)*(11359/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (538618641062644673/538800000000000000 : ℝ)+2*(48209595487/26940000000000 : ℝ)*(11359/100000 : ℝ)=(2000139889312173/2000000000000000 : ℝ) by norm_num, show 1+2*(1780185391340957/12500000000000000000 : ℝ)=(6251780185391340957/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(271016228891667/800000000000000000 : ℝ)+(1780185391340957/12500000000000000000 : ℝ) ≤ ((538618641062644673/538800000000000000 : ℝ)+(48209595487/26940000000000 : ℝ)*((14053/100000 : ℝ)+(11359/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (538618641062644673/538800000000000000 : ℝ)+(48209595487/26940000000000 : ℝ)*((14053/100000 : ℝ)+(11359/100000 : ℝ))=(2000236308503147/2000000000000000 : ℝ) by norm_num, show 1+(271016228891667/800000000000000000 : ℝ)+(1780185391340957/12500000000000000000 : ℝ)=(100048118511742186031/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(271016228891667/800000000000000000 : ℝ) ≤ ((538618641062644673/538800000000000000 : ℝ)+2*(48209595487/26940000000000 : ℝ)*(14053/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (538618641062644673/538800000000000000 : ℝ)+2*(48209595487/26940000000000 : ℝ)*(14053/100000 : ℝ)=(2000332727694121/2000000000000000 : ℝ) by norm_num, show 1+2*(271016228891667/800000000000000000 : ℝ)=(400271016228891667/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (538618641062644673/538800000000000000 : ℝ)*(X 1 0+X 2 0)+(48209595487/26940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (538618641062644673/538800000000000000 : ℝ)) (alpha := (48209595487/26940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (538618641062644673/538800000000000000 : ℝ)*(X 0 1+X 2 1)+(48209595487/26940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (538618641062644673/538800000000000000 : ℝ)) (alpha := (48209595487/26940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (538618641062644673/538800000000000000 : ℝ)*(X 0 2+X 1 2)+(48209595487/26940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (538618641062644673/538800000000000000 : ℝ)) (alpha := (48209595487/26940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541124831/2500000000 : ℝ)*X 0 0+(2696452091/5000000000 : ℝ)*X 0 1+(1053171611/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267236497/500000000 : ℝ)*X 1 0+(-2228937503/10000000000 : ℝ)*X 1 1+(1053171607/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068945983/2000000000 : ℝ)*X 2 0+(5265858059/10000000000 : ℝ)*X 2 1+(-2228937503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363971137/10000000000 : ℝ)*X 0 0+(847858423/2000000000 : ℝ)*X 0 1+(4492294999/10000000000 : ℝ)*X 0 2+(4363971137/10000000000 : ℝ)*X 1 0+(847858423/2000000000 : ℝ)*X 1 1+(4492294999/10000000000 : ℝ)*X 1 2+(4363971137/10000000000 : ℝ)*X 2 0+(847858423/2000000000 : ℝ)*X 2 1+(4492294999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164504157/10000000000 : ℝ)*X 0 0+(5266177143/10000000000 : ℝ)*X 0 1+(1348145991/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656265127/5000000000 : ℝ)*X 1 0+(-525552891/2500000000 : ℝ)*X 1 1+(1078516793/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328132561/2500000000 : ℝ)*X 2 0+(1078516793/2000000000 : ℝ)*X 2 1+(-1051105789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090995209/2500000000 : ℝ)*X 0 0+(2245829791/5000000000 : ℝ)*X 0 1+(4239929813/10000000000 : ℝ)*X 0 2+(1090995209/2500000000 : ℝ)*X 1 0+(2245829791/5000000000 : ℝ)*X 1 1+(4239929813/10000000000 : ℝ)*X 1 2+(1090995209/2500000000 : ℝ)*X 2 0+(2245829791/5000000000 : ℝ)*X 2 1+(4239929813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41430095524265910596398619/4490000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1807706661/100000000000000 : ℝ)*(base19) + (839468833/50000000000000 : ℝ)*(base23) + (49145413/100000000000000 : ℝ)*(lower2) + (1730531/781250000000 : ℝ)*(upper3) + (145659559/100000000000000 : ℝ)*(upper5) + (5911915791780203/100000000000000 : ℝ)*(major0) + (5911915791780203/100000000000000 : ℝ)*(major1) + (5911915791780203/100000000000000 : ℝ)*(major2) + (7686726688813/97656250000 : ℝ)*(sp0) + (393562756559611/5000000000000 : ℝ)*(sp1) + (1574251051992243/20000000000000 : ℝ)*(sp2) + (3952548228268779/100000000000000 : ℝ)*(sp3) + (48809554369/100000000000000 : ℝ)*(sp4) + (652720491/2500000000000 : ℝ)*(sp7) + (1976287168544209/50000000000000 : ℝ)*(f.failure) + (7871256938898881/100000000000000 : ℝ)*(f.sum) + (4928310741013/1347000000000000000000000000 : ℝ)*base66 + (92493493480051381/53880000000000000000000000000000 : ℝ)*base68 + (417332856165931381/53880000000000000000000000000000 : ℝ)*base70 + (531567677512411381/53880000000000000000000000000000 : ℝ)*base72 + (175476064337/673500000000000000000000000 : ℝ)*base74 + (426799832083051381/53880000000000000000000000000000 : ℝ)*base76 + (69340851871411381/53880000000000000000000000000000 : ℝ)*base78 + (968509056252028619/53880000000000000000000000000000 : ℝ)*base79 + (3577254188551/1347000000000000000000000000 : ℝ)*base82 + (42273867/2500000000000000000000 : ℝ)*base90 + (42273867/2500000000000000000000 : ℝ)*base92 + (42273867/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5029669583090002396703997/2245000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97823111/25000000000000 : ℝ)*(base19) + (216339697/50000000000000 : ℝ)*(base23) + (29557127/20000000000000 : ℝ)*(lower1) + (16645079/50000000000000 : ℝ)*(upper3) + (28217639/100000000000000 : ℝ)*(lower4) + (33595763/100000000000000 : ℝ)*(upper5) + (1485432569705211/25000000000000 : ℝ)*(major0) + (1485432569705211/25000000000000 : ℝ)*(major1) + (1485432569705211/25000000000000 : ℝ)*(major2) + (521829989/100000000000000 : ℝ)*(sp2) + (1977738212090123/25000000000000 : ℝ)*(sp4) + (494434528566753/6250000000000 : ℝ)*(sp5) + (7910951893851109/100000000000000 : ℝ)*(sp6) + (3972507634601577/100000000000000 : ℝ)*(sp7) + (3972507634601577/100000000000000 : ℝ)*(f.failure) + (1977738212090123/25000000000000 : ℝ)*(f.sum) + (654629112699/112250000000000000000000000 : ℝ)*base66 + (252347872121577001/4490000000000000000000000000000 : ℝ)*base67 + (14808596838267001/4490000000000000000000000000000 : ℝ)*base69 + (883574488922517001/4490000000000000000000000000000 : ℝ)*base71 + (1589252156759/224500000000000000000000000 : ℝ)*base73 + (450841670305412999/4490000000000000000000000000000 : ℝ)*base76 + (4382482270407001/4490000000000000000000000000000 : ℝ)*base77 + (50726069046622999/4490000000000000000000000000000 : ℝ)*base80 + (511418823273/112250000000000000000000000 : ℝ)*base82 + (22850451/5000000000000000000000 : ℝ)*base90 + (22850451/5000000000000000000000 : ℝ)*base92 + (22850451/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1147_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1147_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1147_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1147_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

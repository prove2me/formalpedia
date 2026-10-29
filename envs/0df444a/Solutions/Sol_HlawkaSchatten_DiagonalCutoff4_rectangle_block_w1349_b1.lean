-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:18.817992+00:00
-- url     : https://prove2.me/submissions/7405fe40-3d34-4b68-8003-fab1abfeff4e

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
theorem support_rectangle_w1349_s3_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036251639/10000000000 : ℝ)*x 0 + (1356569661/2500000000 : ℝ)*x 1 + (5231996521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036251639/10000000000 : ℝ)^4309 ≤ (12398822067419/100000000000000 : ℝ)^3285 := by
    have hnat : (2036251639 : ℕ)^4309*100000000000000^3285 ≤ 12398822067419^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036251639 10000000000 12398822067419 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356569661/2500000000 : ℝ)^4309 ≤ (44847795436323/100000000000000 : ℝ)^3285 := by
    have hnat : (1356569661 : ℕ)^4309*100000000000000^3285 ≤ 44847795436323^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356569661 2500000000 44847795436323 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231996521/10000000000 : ℝ)^4309 ≤ (267208640497/625000000000 : ℝ)^3285 := by
    have hnat : (5231996521 : ℕ)^4309*625000000000^3285 ≤ 267208640497^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231996521 10000000000 267208640497 625000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036251639/10000000000 : ℝ), (1356569661/2500000000 : ℝ), (5231996521/10000000000 : ℝ)] ![(12398822067419/100000000000000 : ℝ), (44847795436323/100000000000000 : ℝ), (267208640497/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036251639/10000000000 : ℝ)|^4309 ≤ (12398822067419/100000000000000 : ℝ)^3285
        have hw : |(-2036251639/10000000000 : ℝ)|=(2036251639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356569661/2500000000 : ℝ)|^4309 ≤ (44847795436323/100000000000000 : ℝ)^3285
        have hw : |(1356569661/2500000000 : ℝ)|=(1356569661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231996521/10000000000 : ℝ)|^4309 ≤ (267208640497/625000000000 : ℝ)^3285
        have hw : |(5231996521/10000000000 : ℝ)|=(5231996521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334527019/625000000 : ℝ)*x 0 + (-266940909/1250000000 : ℝ)*x 1 + (5231996441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334527019/625000000 : ℝ)^4309 ≤ (44048910846713/100000000000000 : ℝ)^3285 := by
    have hnat : (334527019 : ℕ)^4309*100000000000000^3285 ≤ 44048910846713^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334527019 625000000 44048910846713 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266940909/1250000000 : ℝ)^4309 ≤ (6598853758659/50000000000000 : ℝ)^3285 := by
    have hnat : (266940909 : ℕ)^4309*50000000000000^3285 ≤ 6598853758659^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266940909 1250000000 6598853758659 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231996441/10000000000 : ℝ)^4309 ≤ (2137669081101/5000000000000 : ℝ)^3285 := by
    have hnat : (5231996441 : ℕ)^4309*5000000000000^3285 ≤ 2137669081101^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231996441 10000000000 2137669081101 5000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334527019/625000000 : ℝ), (-266940909/1250000000 : ℝ), (5231996441/10000000000 : ℝ)] ![(44048910846713/100000000000000 : ℝ), (6598853758659/50000000000000 : ℝ), (2137669081101/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334527019/625000000 : ℝ)|^4309 ≤ (44048910846713/100000000000000 : ℝ)^3285
        have hw : |(334527019/625000000 : ℝ)|=(334527019/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266940909/1250000000 : ℝ)|^4309 ≤ (6598853758659/50000000000000 : ℝ)^3285
        have hw : |(-266940909/1250000000 : ℝ)|=(266940909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231996441/10000000000 : ℝ)|^4309 ≤ (2137669081101/5000000000000 : ℝ)^3285
        have hw : |(5231996441/10000000000 : ℝ)|=(5231996441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167263511/312500000 : ℝ)*x 0 + (5231996589/10000000000 : ℝ)*x 1 + (-2135527011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167263511/312500000 : ℝ)^4309 ≤ (11012227841219/25000000000000 : ℝ)^3285 := by
    have hnat : (167263511 : ℕ)^4309*25000000000000^3285 ≤ 11012227841219^3285*312500000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167263511 312500000 11012227841219 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231996589/10000000000 : ℝ)^4309 ≤ (8550676641679/20000000000000 : ℝ)^3285 := by
    have hnat : (5231996589 : ℕ)^4309*20000000000000^3285 ≤ 8550676641679^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231996589 10000000000 8550676641679 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135527011/10000000000 : ℝ)^4309 ≤ (3299426350379/25000000000000 : ℝ)^3285 := by
    have hnat : (2135527011 : ℕ)^4309*25000000000000^3285 ≤ 3299426350379^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135527011 10000000000 3299426350379 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167263511/312500000 : ℝ), (5231996589/10000000000 : ℝ), (-2135527011/10000000000 : ℝ)] ![(11012227841219/25000000000000 : ℝ), (8550676641679/20000000000000 : ℝ), (3299426350379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167263511/312500000 : ℝ)|^4309 ≤ (11012227841219/25000000000000 : ℝ)^3285
        have hw : |(167263511/312500000 : ℝ)|=(167263511/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231996589/10000000000 : ℝ)|^4309 ≤ (8550676641679/20000000000000 : ℝ)^3285
        have hw : |(5231996589/10000000000 : ℝ)|=(5231996589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135527011/10000000000 : ℝ)|^4309 ≤ (3299426350379/25000000000000 : ℝ)^3285
        have hw : |(-2135527011/10000000000 : ℝ)|=(2135527011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540471211/1250000000 : ℝ)*x 0 + (41242467/100000000 : ℝ)*x 1 + (4532255833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540471211/1250000000 : ℝ)^4309 ≤ (16646527552997/50000000000000 : ℝ)^3285 := by
    have hnat : (540471211 : ℕ)^4309*50000000000000^3285 ≤ 16646527552997^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540471211 1250000000 16646527552997 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41242467/100000000 : ℝ)^4309 ≤ (3911559148527/12500000000000 : ℝ)^3285 := by
    have hnat : (41242467 : ℕ)^4309*12500000000000^3285 ≤ 3911559148527^3285*100000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41242467 100000000 3911559148527 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532255833/10000000000 : ℝ)^4309 ≤ (2213404480729/6250000000000 : ℝ)^3285 := by
    have hnat : (4532255833 : ℕ)^4309*6250000000000^3285 ≤ 2213404480729^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532255833 10000000000 2213404480729 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540471211/1250000000 : ℝ), (41242467/100000000 : ℝ), (4532255833/10000000000 : ℝ)] ![(16646527552997/50000000000000 : ℝ), (3911559148527/12500000000000 : ℝ), (2213404480729/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540471211/1250000000 : ℝ)|^4309 ≤ (16646527552997/50000000000000 : ℝ)^3285
        have hw : |(540471211/1250000000 : ℝ)|=(540471211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41242467/100000000 : ℝ)|^4309 ≤ (3911559148527/12500000000000 : ℝ)^3285
        have hw : |(41242467/100000000 : ℝ)|=(41242467/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532255833/10000000000 : ℝ)|^4309 ≤ (2213404480729/6250000000000 : ℝ)^3285
        have hw : |(4532255833/10000000000 : ℝ)|=(4532255833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036270957/10000000000 : ℝ)*x 0 + (13082007/25000000 : ℝ)*x 1 + (2712733603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036270957/10000000000 : ℝ)^4309 ≤ (12398976362793/100000000000000 : ℝ)^3285 := by
    have hnat : (2036270957 : ℕ)^4309*100000000000000^3285 ≤ 12398976362793^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036270957 10000000000 12398976362793 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13082007/25000000 : ℝ)^4309 ≤ (21381012495181/50000000000000 : ℝ)^3285 := by
    have hnat : (13082007 : ℕ)^4309*50000000000000^3285 ≤ 21381012495181^3285*25000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13082007 25000000 21381012495181 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712733603/5000000000 : ℝ)^4309 ≤ (44838998623571/100000000000000 : ℝ)^3285 := by
    have hnat : (2712733603 : ℕ)^4309*100000000000000^3285 ≤ 44838998623571^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712733603 5000000000 44838998623571 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036270957/10000000000 : ℝ), (13082007/25000000 : ℝ), (2712733603/5000000000 : ℝ)] ![(12398976362793/100000000000000 : ℝ), (21381012495181/50000000000000 : ℝ), (44838998623571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036270957/10000000000 : ℝ)|^4309 ≤ (12398976362793/100000000000000 : ℝ)^3285
        have hw : |(-2036270957/10000000000 : ℝ)|=(2036270957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13082007/25000000 : ℝ)|^4309 ≤ (21381012495181/50000000000000 : ℝ)^3285
        have hw : |(13082007/25000000 : ℝ)|=(13082007/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712733603/5000000000 : ℝ)|^4309 ≤ (44838998623571/100000000000000 : ℝ)^3285
        have hw : |(2712733603/5000000000 : ℝ)|=(2712733603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651174193/5000000000 : ℝ)*x 0 + (-971028101/5000000000 : ℝ)*x 1 + (5425467587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651174193/5000000000 : ℝ)^4309 ≤ (21754521044519/50000000000000 : ℝ)^3285 := by
    have hnat : (2651174193 : ℕ)^4309*50000000000000^3285 ≤ 21754521044519^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651174193 5000000000 21754521044519 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971028101/5000000000 : ℝ)^4309 ≤ (11651955135101/100000000000000 : ℝ)^3285 := by
    have hnat : (971028101 : ℕ)^4309*100000000000000^3285 ≤ 11651955135101^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971028101 5000000000 11651955135101 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425467587/10000000000 : ℝ)^4309 ≤ (22419501376951/50000000000000 : ℝ)^3285 := by
    have hnat : (5425467587 : ℕ)^4309*50000000000000^3285 ≤ 22419501376951^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425467587 10000000000 22419501376951 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651174193/5000000000 : ℝ), (-971028101/5000000000 : ℝ), (5425467587/10000000000 : ℝ)] ![(21754521044519/50000000000000 : ℝ), (11651955135101/100000000000000 : ℝ), (22419501376951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651174193/5000000000 : ℝ)|^4309 ≤ (21754521044519/50000000000000 : ℝ)^3285
        have hw : |(2651174193/5000000000 : ℝ)|=(2651174193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971028101/5000000000 : ℝ)|^4309 ≤ (11651955135101/100000000000000 : ℝ)^3285
        have hw : |(-971028101/5000000000 : ℝ)|=(971028101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425467587/10000000000 : ℝ)|^4309 ≤ (22419501376951/50000000000000 : ℝ)^3285
        have hw : |(5425467587/10000000000 : ℝ)|=(5425467587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651174689/5000000000 : ℝ)*x 0 + (2712733467/5000000000 : ℝ)*x 1 + (-971027873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651174689/5000000000 : ℝ)^4309 ≤ (21754526383201/50000000000000 : ℝ)^3285 := by
    have hnat : (2651174689 : ℕ)^4309*50000000000000^3285 ≤ 21754526383201^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651174689 5000000000 21754526383201 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712733467/5000000000 : ℝ)^4309 ≤ (44838995674883/100000000000000 : ℝ)^3285 := by
    have hnat : (2712733467 : ℕ)^4309*100000000000000^3285 ≤ 44838995674883^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712733467 5000000000 44838995674883 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971027873/5000000000 : ℝ)^4309 ≤ (11651951546353/100000000000000 : ℝ)^3285 := by
    have hnat : (971027873 : ℕ)^4309*100000000000000^3285 ≤ 11651951546353^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971027873 5000000000 11651951546353 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651174689/5000000000 : ℝ), (2712733467/5000000000 : ℝ), (-971027873/5000000000 : ℝ)] ![(21754526383201/50000000000000 : ℝ), (44838995674883/100000000000000 : ℝ), (11651951546353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651174689/5000000000 : ℝ)|^4309 ≤ (21754526383201/50000000000000 : ℝ)^3285
        have hw : |(2651174689/5000000000 : ℝ)|=(2651174689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712733467/5000000000 : ℝ)|^4309 ≤ (44838995674883/100000000000000 : ℝ)^3285
        have hw : |(2712733467/5000000000 : ℝ)|=(2712733467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971027873/5000000000 : ℝ)|^4309 ≤ (11651951546353/100000000000000 : ℝ)^3285
        have hw : |(-971027873/5000000000 : ℝ)|=(971027873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s3_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (432381031/1000000000 : ℝ)*x 0 + (906112459/2000000000 : ℝ)*x 1 + (2062974671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432381031/1000000000 : ℝ)^4309 ≤ (33293465399039/100000000000000 : ℝ)^3285 := by
    have hnat : (432381031 : ℕ)^4309*100000000000000^3285 ≤ 33293465399039^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432381031 1000000000 33293465399039 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906112459/2000000000 : ℝ)^4309 ≤ (35397114593443/100000000000000 : ℝ)^3285 := by
    have hnat : (906112459 : ℕ)^4309*100000000000000^3285 ≤ 35397114593443^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906112459 2000000000 35397114593443 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062974671/5000000000 : ℝ)^4309 ≤ (31309419986363/100000000000000 : ℝ)^3285 := by
    have hnat : (2062974671 : ℕ)^4309*100000000000000^3285 ≤ 31309419986363^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062974671 5000000000 31309419986363 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432381031/1000000000 : ℝ), (906112459/2000000000 : ℝ), (2062974671/5000000000 : ℝ)] ![(33293465399039/100000000000000 : ℝ), (35397114593443/100000000000000 : ℝ), (31309419986363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432381031/1000000000 : ℝ)|^4309 ≤ (33293465399039/100000000000000 : ℝ)^3285
        have hw : |(432381031/1000000000 : ℝ)|=(432381031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906112459/2000000000 : ℝ)|^4309 ≤ (35397114593443/100000000000000 : ℝ)^3285
        have hw : |(906112459/2000000000 : ℝ)|=(906112459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062974671/5000000000 : ℝ)|^4309 ≤ (31309419986363/100000000000000 : ℝ)^3285
        have hw : |(2062974671/5000000000 : ℝ)|=(2062974671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4019/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4019/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4019/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4019/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4019/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4019/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9897/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (742954371825999/12500000000000000000 : ℝ) := by
    have hpowers : (9897/100000 : ℝ)^1077 ≤ (742954371825999/12500000000000000000 : ℝ)^256 := by
      have hnat : (9897 : ℕ)^1077*12500000000000000000^256 ≤ 742954371825999^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9897 100000 742954371825999 12500000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9897/100000 : ℝ)) (X := (742954371825999/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4019/25000 : ℝ) ^ (1077/256 : ℝ) ≤ (2287367957218151/5000000000000000000 : ℝ) := by
    have hpowers : (4019/25000 : ℝ)^1077 ≤ (2287367957218151/5000000000000000000 : ℝ)^256 := by
      have hnat : (4019 : ℕ)^1077*5000000000000000000^256 ≤ 2287367957218151^256*25000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4019 25000 2287367957218151 5000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4019/25000 : ℝ)) (X := (2287367957218151/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250742954371825999/6250000000000000000 : ℝ) ≤ (1250035318050563/1250000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (6250742954371825999/6250000000000000000 : ℝ)^256 ≤ (1250035318050563/1250000000000000 : ℝ)^1077 := by
      have hnat : (6250742954371825999 : ℕ)^256*1250000000000000^1077 ≤ 1250035318050563^1077*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250742954371825999 6250000000000000000 1250035318050563 1250000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035318050563/1250000000000000 : ℝ)) (X := (6250742954371825999/6250000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012922748529742753/25000000000000000000 : ℝ) ≤ (10001228439009173/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (25012922748529742753/25000000000000000000 : ℝ)^256 ≤ (10001228439009173/10000000000000000 : ℝ)^1077 := by
      have hnat : (25012922748529742753 : ℕ)^256*10000000000000000^1077 ≤ 10001228439009173^1077*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012922748529742753 25000000000000000000 10001228439009173 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228439009173/10000000000000000 : ℝ)) (X := (25012922748529742753/25000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502287367957218151/2500000000000000000 : ℝ) ≤ (5001087166806921/5000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (2502287367957218151/2500000000000000000 : ℝ)^256 ≤ (5001087166806921/5000000000000000 : ℝ)^1077 := by
      have hnat : (2502287367957218151 : ℕ)^256*5000000000000000^1077 ≤ 5001087166806921^1077*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502287367957218151 2500000000000000000 5001087166806921 5000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001087166806921/5000000000000000 : ℝ)) (X := (2502287367957218151/2500000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742954371825999/12500000000000000000 : ℝ) ≤ ((6177302280407061203/6179000000000000000 : ℝ)+2*(945894604669/617900000000000 : ℝ)*(9897/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (6177302280407061203/6179000000000000000 : ℝ)+2*(945894604669/617900000000000 : ℝ)*(9897/100000 : ℝ)=(1250035318050563/1250000000000000 : ℝ) by norm_num, show 1+2*(742954371825999/12500000000000000000 : ℝ)=(6250742954371825999/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2287367957218151/5000000000000000000 : ℝ)+(742954371825999/12500000000000000000 : ℝ) ≤ ((6177302280407061203/6179000000000000000 : ℝ)+(945894604669/617900000000000 : ℝ)*((4019/25000 : ℝ)+(9897/100000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (6177302280407061203/6179000000000000000 : ℝ)+(945894604669/617900000000000 : ℝ)*((4019/25000 : ℝ)+(9897/100000 : ℝ))=(10001228439009173/10000000000000000 : ℝ) by norm_num, show 1+(2287367957218151/5000000000000000000 : ℝ)+(742954371825999/12500000000000000000 : ℝ)=(25012922748529742753/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2287367957218151/5000000000000000000 : ℝ) ≤ ((6177302280407061203/6179000000000000000 : ℝ)+2*(945894604669/617900000000000 : ℝ)*(4019/25000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (6177302280407061203/6179000000000000000 : ℝ)+2*(945894604669/617900000000000 : ℝ)*(4019/25000 : ℝ)=(5001087166806921/5000000000000000 : ℝ) by norm_num, show 1+2*(2287367957218151/5000000000000000000 : ℝ)=(2502287367957218151/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6177302280407061203/6179000000000000000 : ℝ)*(X 1 0+X 2 0)+(945894604669/617900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (9897/100000 : ℝ)) (hi := (4019/25000 : ℝ)) (c := (6177302280407061203/6179000000000000000 : ℝ)) (alpha := (945894604669/617900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6177302280407061203/6179000000000000000 : ℝ)*(X 0 1+X 2 1)+(945894604669/617900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (9897/100000 : ℝ)) (hi := (4019/25000 : ℝ)) (c := (6177302280407061203/6179000000000000000 : ℝ)) (alpha := (945894604669/617900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6177302280407061203/6179000000000000000 : ℝ)*(X 0 2+X 1 2)+(945894604669/617900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (9897/100000 : ℝ)) (hi := (4019/25000 : ℝ)) (c := (6177302280407061203/6179000000000000000 : ℝ)) (alpha := (945894604669/617900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2036251639/10000000000 : ℝ)*X 0 0+(1356569661/2500000000 : ℝ)*X 0 1+(5231996521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334527019/625000000 : ℝ)*X 1 0+(-266940909/1250000000 : ℝ)*X 1 1+(5231996441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167263511/312500000 : ℝ)*X 2 0+(5231996589/10000000000 : ℝ)*X 2 1+(-2135527011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540471211/1250000000 : ℝ)*X 0 0+(41242467/100000000 : ℝ)*X 0 1+(4532255833/10000000000 : ℝ)*X 0 2+(540471211/1250000000 : ℝ)*X 1 0+(41242467/100000000 : ℝ)*X 1 1+(4532255833/10000000000 : ℝ)*X 1 2+(540471211/1250000000 : ℝ)*X 2 0+(41242467/100000000 : ℝ)*X 2 1+(4532255833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2036270957/10000000000 : ℝ)*X 0 0+(13082007/25000000 : ℝ)*X 0 1+(2712733603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651174193/5000000000 : ℝ)*X 1 0+(-971028101/5000000000 : ℝ)*X 1 1+(5425467587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651174689/5000000000 : ℝ)*X 2 0+(2712733467/5000000000 : ℝ)*X 2 1+(-971027873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432381031/1000000000 : ℝ)*X 0 0+(906112459/2000000000 : ℝ)*X 0 1+(2062974671/5000000000 : ℝ)*X 0 2+(432381031/1000000000 : ℝ)*X 1 0+(906112459/2000000000 : ℝ)*X 1 1+(2062974671/5000000000 : ℝ)*X 1 2+(432381031/1000000000 : ℝ)*X 2 0+(906112459/2000000000 : ℝ)*X 2 1+(2062974671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (905085453693346708510181181/77237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1319596133/100000000000000 : ℝ)*(base19) + (184194349/20000000000000 : ℝ)*(base23) + (238067533/100000000000000 : ℝ)*(lower2) + (20818199/12500000000000 : ℝ)*(upper3) + (58780497/50000000000000 : ℝ)*(upper5) + (949766754644309/25000000000000 : ℝ)*(major0) + (949766754644309/25000000000000 : ℝ)*(major1) + (949766754644309/25000000000000 : ℝ)*(major2) + (643396528583011/12500000000000 : ℝ)*(sp0) + (643399086660763/12500000000000 : ℝ)*(sp1) + (1286798272977623/25000000000000 : ℝ)*(sp2) + (612732835817813/25000000000000 : ℝ)*(sp3) + (21784218149/100000000000000 : ℝ)*(sp4) + (8290393887/100000000000000 : ℝ)*(sp7) + (2450939633665139/100000000000000 : ℝ)*(f.failure) + (5147194012882237/100000000000000 : ℝ)*(f.sum) + (104735896156411/30895000000000000000000000000 : ℝ)*base66 + (741061386602778727/154475000000000000000000000000000 : ℝ)*base67 + (568242742287846273/154475000000000000000000000000000 : ℝ)*base70 + (1315815722884096273/154475000000000000000000000000000 : ℝ)*base72 + (141917881359469/30895000000000000000000000000 : ℝ)*base73 + (2125288384128796273/154475000000000000000000000000000 : ℝ)*base76 + (243588769199103727/154475000000000000000000000000000 : ℝ)*base77 + (1788491132471321273/154475000000000000000000000000000 : ℝ)*base80 + (41756135815987/15447500000000000000000000000 : ℝ)*base81 + (1315849/312500000000000000000 : ℝ)*base89 + (1315849/312500000000000000000 : ℝ)*base91 + (1315849/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2022675470828984735085787137/308950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130258751/10000000000000 : ℝ)*(base19) + (2921349593/100000000000000 : ℝ)*(base23) + (78463461/25000000000000 : ℝ)*(upper3) + (27158869/12500000000000 : ℝ)*(lower4) + (130911073/50000000000000 : ℝ)*(upper5) + (3830937446985469/100000000000000 : ℝ)*(major0) + (3830937446985469/100000000000000 : ℝ)*(major1) + (3830937446985469/100000000000000 : ℝ)*(major2) + (4959626239/20000000000000 : ℝ)*(sp1) + (3124403099/6250000000000 : ℝ)*(sp2) + (2595187036941399/50000000000000 : ℝ)*(sp4) + (5190347973164093/100000000000000 : ℝ)*(sp5) + (5190321162083621/100000000000000 : ℝ)*(sp6) + (154468787616061/6250000000000 : ℝ)*(sp7) + (154468787616061/6250000000000 : ℝ)*(f.failure) + (2595187036941399/50000000000000 : ℝ)*(f.sum) + (42852288572531/30895000000000000000000000000 : ℝ)*base65 + (8665785044954269207/617900000000000000000000000000000 : ℝ)*base67 + (8698856375260269207/617900000000000000000000000000000 : ℝ)*base69 + (2688285066172069207/617900000000000000000000000000000 : ℝ)*base71 + (32576913725631/30895000000000000000000000000 : ℝ)*base73 + (4708267739716069207/617900000000000000000000000000000 : ℝ)*base75 + (1056996856280869207/617900000000000000000000000000000 : ℝ)*base77 + (6134420156593269207/617900000000000000000000000000000 : ℝ)*base79 + (112083805703471/30895000000000000000000000000 : ℝ)*base81 + (161423/39062500000000000000 : ℝ)*base90 + (161423/39062500000000000000 : ℝ)*base92 + (161423/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_s4_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-254706871/1250000000 : ℝ)*x 0 + (5414782651/10000000000 : ℝ)*x 1 + (2621285469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254706871/1250000000 : ℝ)^4309 ≤ (12410031825511/100000000000000 : ℝ)^3285 := by
    have hnat : (254706871 : ℕ)^4309*100000000000000^3285 ≤ 12410031825511^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254706871 1250000000 12410031825511 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414782651/10000000000 : ℝ)^4309 ≤ (11180801363743/25000000000000 : ℝ)^3285 := by
    have hnat : (5414782651 : ℕ)^4309*25000000000000^3285 ≤ 11180801363743^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414782651 10000000000 11180801363743 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621285469/5000000000 : ℝ)^4309 ≤ (5358345337867/12500000000000 : ℝ)^3285 := by
    have hnat : (2621285469 : ℕ)^4309*12500000000000^3285 ≤ 5358345337867^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621285469 5000000000 5358345337867 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254706871/1250000000 : ℝ), (5414782651/10000000000 : ℝ), (2621285469/5000000000 : ℝ)] ![(12410031825511/100000000000000 : ℝ), (11180801363743/25000000000000 : ℝ), (5358345337867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254706871/1250000000 : ℝ)|^4309 ≤ (12410031825511/100000000000000 : ℝ)^3285
        have hw : |(-254706871/1250000000 : ℝ)|=(254706871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414782651/10000000000 : ℝ)|^4309 ≤ (11180801363743/25000000000000 : ℝ)^3285
        have hw : |(5414782651/10000000000 : ℝ)|=(5414782651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621285469/5000000000 : ℝ)|^4309 ≤ (5358345337867/12500000000000 : ℝ)^3285
        have hw : |(2621285469/5000000000 : ℝ)|=(2621285469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8358593/15625000 : ℝ)*x 0 + (-1062719403/5000000000 : ℝ)*x 1 + (262128537/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8358593/15625000 : ℝ)^4309 ≤ (880345079357/2000000000000 : ℝ)^3285 := by
    have hnat : (8358593 : ℕ)^4309*2000000000000^3285 ≤ 880345079357^3285*15625000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8358593 15625000 880345079357 2000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062719403/5000000000 : ℝ)^4309 ≤ (3278996360067/25000000000000 : ℝ)^3285 := by
    have hnat : (1062719403 : ℕ)^4309*25000000000000^3285 ≤ 3278996360067^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062719403 5000000000 3278996360067 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262128537/500000000 : ℝ)^4309 ≤ (42866760579287/100000000000000 : ℝ)^3285 := by
    have hnat : (262128537 : ℕ)^4309*100000000000000^3285 ≤ 42866760579287^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262128537 500000000 42866760579287 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8358593/15625000 : ℝ), (-1062719403/5000000000 : ℝ), (262128537/500000000 : ℝ)] ![(880345079357/2000000000000 : ℝ), (3278996360067/25000000000000 : ℝ), (42866760579287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8358593/15625000 : ℝ)|^4309 ≤ (880345079357/2000000000000 : ℝ)^3285
        have hw : |(8358593/15625000 : ℝ)|=(8358593/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062719403/5000000000 : ℝ)|^4309 ≤ (3278996360067/25000000000000 : ℝ)^3285
        have hw : |(-1062719403/5000000000 : ℝ)|=(1062719403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262128537/500000000 : ℝ)|^4309 ≤ (42866760579287/100000000000000 : ℝ)^3285
        have hw : |(262128537/500000000 : ℝ)|=(262128537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349499937/10000000000 : ℝ)*x 0 + (5242570299/10000000000 : ℝ)*x 1 + (-1062719417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349499937/10000000000 : ℝ)^4309 ≤ (22008629234311/50000000000000 : ℝ)^3285 := by
    have hnat : (5349499937 : ℕ)^4309*50000000000000^3285 ≤ 22008629234311^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349499937 10000000000 22008629234311 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242570299/10000000000 : ℝ)^4309 ≤ (42866755849343/100000000000000 : ℝ)^3285 := by
    have hnat : (5242570299 : ℕ)^4309*100000000000000^3285 ≤ 42866755849343^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242570299 10000000000 42866755849343 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062719417/5000000000 : ℝ)^4309 ≤ (3278996416729/25000000000000 : ℝ)^3285 := by
    have hnat : (1062719417 : ℕ)^4309*25000000000000^3285 ≤ 3278996416729^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062719417 5000000000 3278996416729 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349499937/10000000000 : ℝ), (5242570299/10000000000 : ℝ), (-1062719417/5000000000 : ℝ)] ![(22008629234311/50000000000000 : ℝ), (42866755849343/100000000000000 : ℝ), (3278996416729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349499937/10000000000 : ℝ)|^4309 ≤ (22008629234311/50000000000000 : ℝ)^3285
        have hw : |(5349499937/10000000000 : ℝ)|=(5349499937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242570299/10000000000 : ℝ)|^4309 ≤ (42866755849343/100000000000000 : ℝ)^3285
        have hw : |(5242570299/10000000000 : ℝ)|=(5242570299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1062719417/5000000000 : ℝ)|^4309 ≤ (3278996416729/25000000000000 : ℝ)^3285
        have hw : |(-1062719417/5000000000 : ℝ)|=(1062719417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324623281/10000000000 : ℝ)*x 0 + (165892611/400000000 : ℝ)*x 1 + (2254488203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324623281/10000000000 : ℝ)^4309 ≤ (16650838437911/50000000000000 : ℝ)^3285 := by
    have hnat : (4324623281 : ℕ)^4309*50000000000000^3285 ≤ 16650838437911^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324623281 10000000000 16650838437911 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165892611/400000000 : ℝ)^4309 ≤ (31522265293859/100000000000000 : ℝ)^3285 := by
    have hnat : (165892611 : ℕ)^4309*100000000000000^3285 ≤ 31522265293859^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165892611 400000000 31522265293859 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254488203/5000000000 : ℝ)^4309 ≤ (35176057814949/100000000000000 : ℝ)^3285 := by
    have hnat : (2254488203 : ℕ)^4309*100000000000000^3285 ≤ 35176057814949^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254488203 5000000000 35176057814949 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324623281/10000000000 : ℝ), (165892611/400000000 : ℝ), (2254488203/5000000000 : ℝ)] ![(16650838437911/50000000000000 : ℝ), (31522265293859/100000000000000 : ℝ), (35176057814949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324623281/10000000000 : ℝ)|^4309 ≤ (16650838437911/50000000000000 : ℝ)^3285
        have hw : |(4324623281/10000000000 : ℝ)|=(4324623281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165892611/400000000 : ℝ)|^4309 ≤ (31522265293859/100000000000000 : ℝ)^3285
        have hw : |(165892611/400000000 : ℝ)|=(165892611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254488203/5000000000 : ℝ)|^4309 ≤ (35176057814949/100000000000000 : ℝ)^3285
        have hw : |(2254488203/5000000000 : ℝ)|=(2254488203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-509417111/2500000000 : ℝ)*x 0 + (5243204581/10000000000 : ℝ)*x 1 + (27070727/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509417111/2500000000 : ℝ)^4309 ≤ (6205069741571/50000000000000 : ℝ)^3285 := by
    have hnat : (509417111 : ℕ)^4309*50000000000000^3285 ≤ 6205069741571^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509417111 2500000000 6205069741571 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243204581/10000000000 : ℝ)^4309 ≤ (42873558968081/100000000000000 : ℝ)^3285 := by
    have hnat : (5243204581 : ℕ)^4309*100000000000000^3285 ≤ 42873558968081^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243204581 10000000000 42873558968081 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27070727/50000000 : ℝ)^4309 ≤ (2794768846111/6250000000000 : ℝ)^3285 := by
    have hnat : (27070727 : ℕ)^4309*6250000000000^3285 ≤ 2794768846111^3285*50000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27070727 50000000 2794768846111 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509417111/2500000000 : ℝ), (5243204581/10000000000 : ℝ), (27070727/50000000 : ℝ)] ![(6205069741571/50000000000000 : ℝ), (42873558968081/100000000000000 : ℝ), (2794768846111/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509417111/2500000000 : ℝ)|^4309 ≤ (6205069741571/50000000000000 : ℝ)^3285
        have hw : |(-509417111/2500000000 : ℝ)|=(509417111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243204581/10000000000 : ℝ)|^4309 ≤ (42873558968081/100000000000000 : ℝ)^3285
        have hw : |(5243204581/10000000000 : ℝ)|=(5243204581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27070727/50000000 : ℝ)|^4309 ≤ (2794768846111/6250000000000 : ℝ)^3285
        have hw : |(27070727/50000000 : ℝ)|=(27070727/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652553131/5000000000 : ℝ)*x 0 + (-488465933/2500000000 : ℝ)*x 1 + (5414145453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652553131/5000000000 : ℝ)^4309 ≤ (21769364408039/50000000000000 : ℝ)^3285 := by
    have hnat : (2652553131 : ℕ)^4309*50000000000000^3285 ≤ 21769364408039^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652553131 5000000000 21769364408039 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488465933/2500000000 : ℝ)^4309 ≤ (11744969058707/100000000000000 : ℝ)^3285 := by
    have hnat : (488465933 : ℕ)^4309*100000000000000^3285 ≤ 11744969058707^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488465933 2500000000 11744969058707 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414145453/10000000000 : ℝ)^4309 ≤ (22358151055981/50000000000000 : ℝ)^3285 := by
    have hnat : (5414145453 : ℕ)^4309*50000000000000^3285 ≤ 22358151055981^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414145453 10000000000 22358151055981 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652553131/5000000000 : ℝ), (-488465933/2500000000 : ℝ), (5414145453/10000000000 : ℝ)] ![(21769364408039/50000000000000 : ℝ), (11744969058707/100000000000000 : ℝ), (22358151055981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652553131/5000000000 : ℝ)|^4309 ≤ (21769364408039/50000000000000 : ℝ)^3285
        have hw : |(2652553131/5000000000 : ℝ)|=(2652553131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488465933/2500000000 : ℝ)|^4309 ≤ (11744969058707/100000000000000 : ℝ)^3285
        have hw : |(-488465933/2500000000 : ℝ)|=(488465933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414145453/10000000000 : ℝ)|^4309 ≤ (22358151055981/50000000000000 : ℝ)^3285
        have hw : |(5414145453/10000000000 : ℝ)|=(5414145453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305106357/10000000000 : ℝ)*x 0 + (5414145397/10000000000 : ℝ)*x 1 + (-976931839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305106357/10000000000 : ℝ)^4309 ≤ (21769364919387/50000000000000 : ℝ)^3285 := by
    have hnat : (5305106357 : ℕ)^4309*50000000000000^3285 ≤ 21769364919387^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305106357 10000000000 21769364919387 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414145397/10000000000 : ℝ)^4309 ≤ (1788652060211/4000000000000 : ℝ)^3285 := by
    have hnat : (5414145397 : ℕ)^4309*4000000000000^3285 ≤ 1788652060211^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414145397 10000000000 1788652060211 4000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976931839/5000000000 : ℝ)^4309 ≤ (293624215823/2500000000000 : ℝ)^3285 := by
    have hnat : (976931839 : ℕ)^4309*2500000000000^3285 ≤ 293624215823^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976931839 5000000000 293624215823 2500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305106357/10000000000 : ℝ), (5414145397/10000000000 : ℝ), (-976931839/5000000000 : ℝ)] ![(21769364919387/50000000000000 : ℝ), (1788652060211/4000000000000 : ℝ), (293624215823/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305106357/10000000000 : ℝ)|^4309 ≤ (21769364919387/50000000000000 : ℝ)^3285
        have hw : |(5305106357/10000000000 : ℝ)|=(5305106357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414145397/10000000000 : ℝ)|^4309 ≤ (1788652060211/4000000000000 : ℝ)^3285
        have hw : |(5414145397/10000000000 : ℝ)|=(5414145397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976931839/5000000000 : ℝ)|^4309 ≤ (293624215823/2500000000000 : ℝ)^3285
        have hw : |(-976931839/5000000000 : ℝ)|=(976931839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s4_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540581399/1250000000 : ℝ)*x 0 + (4507644893/10000000000 : ℝ)*x 1 + (207432677/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540581399/1250000000 : ℝ)^4309 ≤ (4162744850199/12500000000000 : ℝ)^3285 := by
    have hnat : (540581399 : ℕ)^4309*12500000000000^3285 ≤ 4162744850199^3285*1250000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540581399 1250000000 4162744850199 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507644893/10000000000 : ℝ)^4309 ≤ (7032486567801/20000000000000 : ℝ)^3285 := by
    have hnat : (4507644893 : ℕ)^4309*20000000000000^3285 ≤ 7032486567801^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507644893 10000000000 7032486567801 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207432677/500000000 : ℝ)^4309 ≤ (31535608354153/100000000000000 : ℝ)^3285 := by
    have hnat : (207432677 : ℕ)^4309*100000000000000^3285 ≤ 31535608354153^3285*500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207432677 500000000 31535608354153 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540581399/1250000000 : ℝ), (4507644893/10000000000 : ℝ), (207432677/500000000 : ℝ)] ![(4162744850199/12500000000000 : ℝ), (7032486567801/20000000000000 : ℝ), (31535608354153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540581399/1250000000 : ℝ)|^4309 ≤ (4162744850199/12500000000000 : ℝ)^3285
        have hw : |(540581399/1250000000 : ℝ)|=(540581399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507644893/10000000000 : ℝ)|^4309 ≤ (7032486567801/20000000000000 : ℝ)^3285
        have hw : |(4507644893/10000000000 : ℝ)|=(4507644893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207432677/500000000 : ℝ)|^4309 ≤ (31535608354153/100000000000000 : ℝ)^3285
        have hw : |(207432677/500000000 : ℝ)|=(207432677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11117/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10891/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (277820307797087/3125000000000000000 : ℝ) := by
    have hpowers : (10891/100000 : ℝ)^1077 ≤ (277820307797087/3125000000000000000 : ℝ)^256 := by
      have hnat : (10891 : ℕ)^1077*3125000000000000000^256 ≤ 277820307797087^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10891 100000 277820307797087 3125000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10891/100000 : ℝ)) (X := (277820307797087/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15003/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (4276274488814877/12500000000000000000 : ℝ) := by
    have hpowers : (15003/100000 : ℝ)^1077 ≤ (4276274488814877/12500000000000000000 : ℝ)^256 := by
      have hnat : (15003 : ℕ)^1077*12500000000000000000^256 ≤ 4276274488814877^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15003 100000 4276274488814877 12500000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15003/100000 : ℝ)) (X := (4276274488814877/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562777820307797087/1562500000000000000 : ℝ) ≤ (10000422609050729/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (1562777820307797087/1562500000000000000 : ℝ)^256 ≤ (10000422609050729/10000000000000000 : ℝ)^1077 := by
      have hnat : (1562777820307797087 : ℕ)^256*10000000000000000^1077 ≤ 10000422609050729^1077*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562777820307797087 1562500000000000000 10000422609050729 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000422609050729/10000000000000000 : ℝ)) (X := (1562777820307797087/1562500000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (500215502228800129/500000000000000000 : ℝ) ≤ (10001024317732373/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (500215502228800129/500000000000000000 : ℝ)^256 ≤ (10001024317732373/10000000000000000 : ℝ)^1077 := by
      have hnat : (500215502228800129 : ℕ)^256*10000000000000000^1077 ≤ 10001024317732373^1077*500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500215502228800129 500000000000000000 10001024317732373 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001024317732373/10000000000000000 : ℝ)) (X := (500215502228800129/500000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254276274488814877/6250000000000000000 : ℝ) ≤ (10001626026414017/10000000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (6254276274488814877/6250000000000000000 : ℝ)^256 ≤ (10001626026414017/10000000000000000 : ℝ)^1077 := by
      have hnat : (6254276274488814877 : ℕ)^256*10000000000000000^1077 ≤ 10001626026414017^1077*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254276274488814877 6250000000000000000 10001626026414017 10000000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001626026414017/10000000000000000 : ℝ)) (X := (6254276274488814877/6250000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(277820307797087/3125000000000000000 : ℝ) ≤ ((1027715783747825701/1028000000000000000 : ℝ)+2*(150427170411/102800000000000 : ℝ)*(10891/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1027715783747825701/1028000000000000000 : ℝ)+2*(150427170411/102800000000000 : ℝ)*(10891/100000 : ℝ)=(10000422609050729/10000000000000000 : ℝ) by norm_num, show 1+2*(277820307797087/3125000000000000000 : ℝ)=(1562777820307797087/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4276274488814877/12500000000000000000 : ℝ)+(277820307797087/3125000000000000000 : ℝ) ≤ ((1027715783747825701/1028000000000000000 : ℝ)+(150427170411/102800000000000 : ℝ)*((15003/100000 : ℝ)+(10891/100000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (1027715783747825701/1028000000000000000 : ℝ)+(150427170411/102800000000000 : ℝ)*((15003/100000 : ℝ)+(10891/100000 : ℝ))=(10001024317732373/10000000000000000 : ℝ) by norm_num, show 1+(4276274488814877/12500000000000000000 : ℝ)+(277820307797087/3125000000000000000 : ℝ)=(500215502228800129/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4276274488814877/12500000000000000000 : ℝ) ≤ ((1027715783747825701/1028000000000000000 : ℝ)+2*(150427170411/102800000000000 : ℝ)*(15003/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (1027715783747825701/1028000000000000000 : ℝ)+2*(150427170411/102800000000000 : ℝ)*(15003/100000 : ℝ)=(10001626026414017/10000000000000000 : ℝ) by norm_num, show 1+2*(4276274488814877/12500000000000000000 : ℝ)=(6254276274488814877/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1027715783747825701/1028000000000000000 : ℝ)*(X 1 0+X 2 0)+(150427170411/102800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15003/100000 : ℝ)) (c := (1027715783747825701/1028000000000000000 : ℝ)) (alpha := (150427170411/102800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1027715783747825701/1028000000000000000 : ℝ)*(X 0 1+X 2 1)+(150427170411/102800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15003/100000 : ℝ)) (c := (1027715783747825701/1028000000000000000 : ℝ)) (alpha := (150427170411/102800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1027715783747825701/1028000000000000000 : ℝ)*(X 0 2+X 1 2)+(150427170411/102800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15003/100000 : ℝ)) (c := (1027715783747825701/1028000000000000000 : ℝ)) (alpha := (150427170411/102800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-254706871/1250000000 : ℝ)*X 0 0+(5414782651/10000000000 : ℝ)*X 0 1+(2621285469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8358593/15625000 : ℝ)*X 1 0+(-1062719403/5000000000 : ℝ)*X 1 1+(262128537/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349499937/10000000000 : ℝ)*X 2 0+(5242570299/10000000000 : ℝ)*X 2 1+(-1062719417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324623281/10000000000 : ℝ)*X 0 0+(165892611/400000000 : ℝ)*X 0 1+(2254488203/5000000000 : ℝ)*X 0 2+(4324623281/10000000000 : ℝ)*X 1 0+(165892611/400000000 : ℝ)*X 1 1+(2254488203/5000000000 : ℝ)*X 1 2+(4324623281/10000000000 : ℝ)*X 2 0+(165892611/400000000 : ℝ)*X 2 1+(2254488203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-509417111/2500000000 : ℝ)*X 0 0+(5243204581/10000000000 : ℝ)*X 0 1+(27070727/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652553131/5000000000 : ℝ)*X 1 0+(-488465933/2500000000 : ℝ)*X 1 1+(5414145453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305106357/10000000000 : ℝ)*X 2 0+(5414145397/10000000000 : ℝ)*X 2 1+(-976931839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540581399/1250000000 : ℝ)*X 0 0+(4507644893/10000000000 : ℝ)*X 0 1+(207432677/500000000 : ℝ)*X 0 2+(540581399/1250000000 : ℝ)*X 1 0+(4507644893/10000000000 : ℝ)*X 1 1+(207432677/500000000 : ℝ)*X 1 2+(540581399/1250000000 : ℝ)*X 2 0+(4507644893/10000000000 : ℝ)*X 2 1+(207432677/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544241733241543969713522897/51400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (237993751/50000000000000 : ℝ)*(base19) + (146531793/20000000000000 : ℝ)*(base23) + (69818779/50000000000000 : ℝ)*(lower2) + (13934121/12500000000000 : ℝ)*(upper3) + (8700063/25000000000000 : ℝ)*(lower4) + (12342817/100000000000000 : ℝ)*(upper5) + (2142957590096069/50000000000000 : ℝ)*(major0) + (2142957590096069/50000000000000 : ℝ)*(major1) + (4285915180192139/100000000000000 : ℝ)*(major2) + (725850491073779/12500000000000 : ℝ)*(sp0) + (580680345260273/10000000000000 : ℝ)*(sp1) + (5806803195931267/100000000000000 : ℝ)*(sp2) + (1382510379909863/50000000000000 : ℝ)*(sp3) + (2659514479/50000000000000 : ℝ)*(sp7) + (691256519712171/25000000000000 : ℝ)*(f.failure) + (725850491073779/12500000000000 : ℝ)*(f.sum) + (15913799814633/10280000000000000000000000000 : ℝ)*base66 + (300336477993485631/51400000000000000000000000000000 : ℝ)*base68 + (1326520673411944439/102800000000000000000000000000000 : ℝ)*base69 + (352895926605885631/51400000000000000000000000000000 : ℝ)*base72 + (53349441626073/10280000000000000000000000000 : ℝ)*base74 + (139361335776744439/102800000000000000000000000000000 : ℝ)*base75 + (589427088218540631/51400000000000000000000000000000 : ℝ)*base78 + (372355532783059369/51400000000000000000000000000000 : ℝ)*base79 + (18622592581499/2570000000000000000000000000 : ℝ)*base81 + (115139/78125000000000000000 : ℝ)*base90 + (115139/78125000000000000000 : ℝ)*base92 + (896389/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68698876467180949223527119/6425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1580098493/100000000000000 : ℝ)*(base19) + (373066473/20000000000000 : ℝ)*(base23) + (57408679/25000000000000 : ℝ)*(upper3) + (67305899/100000000000000 : ℝ)*(lower4) + (4511869/2500000000000 : ℝ)*(upper5) + (1079444893948727/25000000000000 : ℝ)*(major0) + (1079444893948727/25000000000000 : ℝ)*(major1) + (1079444893948727/25000000000000 : ℝ)*(major2) + (6131210483/20000000000000 : ℝ)*(sp1) + (1158185169/3125000000000 : ℝ)*(sp2) + (1169995128030829/20000000000000 : ℝ)*(sp4) + (5849943404003237/100000000000000 : ℝ)*(sp5) + (1462484178224093/25000000000000 : ℝ)*(sp6) + (139279157751063/5000000000000 : ℝ)*(sp7) + (139279157751063/5000000000000 : ℝ)*(f.failure) + (1169995128030829/20000000000000 : ℝ)*(f.sum) + (346702137897/1285000000000000000000000000 : ℝ)*base65 + (235139953572302627/25700000000000000000000000000000 : ℝ)*base67 + (118228598214802627/25700000000000000000000000000000 : ℝ)*base69 + (124170196275002627/25700000000000000000000000000000 : ℝ)*base71 + (3344007472087/1285000000000000000000000000 : ℝ)*base73 + (214418978132897373/25700000000000000000000000000000 : ℝ)*base76 + (6982688480802627/25700000000000000000000000000000 : ℝ)*base77 + (231903849895602627/25700000000000000000000000000000 : ℝ)*base79 + (4986903479877/1285000000000000000000000000 : ℝ)*base81 + (68867/15625000000000000000 : ℝ)*base90 + (68867/15625000000000000000 : ℝ)*base92 + (68867/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1349_s5_0 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037893727/10000000000 : ℝ)*x 0 + (1082542533/2000000000 : ℝ)*x 1 + (5244483809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037893727/10000000000 : ℝ)^4309 ≤ (12411939266233/100000000000000 : ℝ)^3285 := by
    have hnat : (2037893727 : ℕ)^4309*100000000000000^3285 ≤ 12411939266233^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037893727 10000000000 12411939266233 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082542533/2000000000 : ℝ)^4309 ≤ (44700780346969/100000000000000 : ℝ)^3285 := by
    have hnat : (1082542533 : ℕ)^4309*100000000000000^3285 ≤ 44700780346969^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082542533 2000000000 44700780346969 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244483809/10000000000 : ℝ)^4309 ≤ (670113755701/1562500000000 : ℝ)^3285 := by
    have hnat : (5244483809 : ℕ)^4309*1562500000000^3285 ≤ 670113755701^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244483809 10000000000 670113755701 1562500000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037893727/10000000000 : ℝ), (1082542533/2000000000 : ℝ), (5244483809/10000000000 : ℝ)] ![(12411939266233/100000000000000 : ℝ), (44700780346969/100000000000000 : ℝ), (670113755701/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037893727/10000000000 : ℝ)|^4309 ≤ (12411939266233/100000000000000 : ℝ)^3285
        have hw : |(-2037893727/10000000000 : ℝ)|=(2037893727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082542533/2000000000 : ℝ)|^4309 ≤ (44700780346969/100000000000000 : ℝ)^3285
        have hw : |(1082542533/2000000000 : ℝ)|=(1082542533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244483809/10000000000 : ℝ)|^4309 ≤ (670113755701/1562500000000 : ℝ)^3285
        have hw : |(5244483809/10000000000 : ℝ)|=(5244483809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_1 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674485359/5000000000 : ℝ)*x 0 + (-132725539/625000000 : ℝ)*x 1 + (5244483821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674485359/5000000000 : ℝ)^4309 ≤ (22005773290499/50000000000000 : ℝ)^3285 := by
    have hnat : (2674485359 : ℕ)^4309*50000000000000^3285 ≤ 22005773290499^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674485359 5000000000 22005773290499 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132725539/625000000 : ℝ)^4309 ≤ (818823306517/6250000000000 : ℝ)^3285 := by
    have hnat : (132725539 : ℕ)^4309*6250000000000^3285 ≤ 818823306517^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132725539 625000000 818823306517 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244483821/10000000000 : ℝ)^4309 ≤ (2680455030849/6250000000000 : ℝ)^3285 := by
    have hnat : (5244483821 : ℕ)^4309*6250000000000^3285 ≤ 2680455030849^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244483821 10000000000 2680455030849 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674485359/5000000000 : ℝ), (-132725539/625000000 : ℝ), (5244483821/10000000000 : ℝ)] ![(22005773290499/50000000000000 : ℝ), (818823306517/6250000000000 : ℝ), (2680455030849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674485359/5000000000 : ℝ)|^4309 ≤ (22005773290499/50000000000000 : ℝ)^3285
        have hw : |(2674485359/5000000000 : ℝ)|=(2674485359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132725539/625000000 : ℝ)|^4309 ≤ (818823306517/6250000000000 : ℝ)^3285
        have hw : |(-132725539/625000000 : ℝ)|=(132725539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244483821/10000000000 : ℝ)|^4309 ≤ (2680455030849/6250000000000 : ℝ)^3285
        have hw : |(5244483821/10000000000 : ℝ)|=(5244483821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_2 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337242689/2500000000 : ℝ)*x 0 + (327780239/625000000 : ℝ)*x 1 + (-2123608571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337242689/2500000000 : ℝ)^4309 ≤ (5501443373891/12500000000000 : ℝ)^3285 := by
    have hnat : (1337242689 : ℕ)^4309*12500000000000^3285 ≤ 5501443373891^3285*2500000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337242689 2500000000 5501443373891 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327780239/625000000 : ℝ)^4309 ≤ (10721820131441/25000000000000 : ℝ)^3285 := by
    have hnat : (327780239 : ℕ)^4309*25000000000000^3285 ≤ 10721820131441^3285*625000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327780239 625000000 10721820131441 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123608571/10000000000 : ℝ)^4309 ≤ (818823279711/6250000000000 : ℝ)^3285 := by
    have hnat : (2123608571 : ℕ)^4309*6250000000000^3285 ≤ 818823279711^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123608571 10000000000 818823279711 6250000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337242689/2500000000 : ℝ), (327780239/625000000 : ℝ), (-2123608571/10000000000 : ℝ)] ![(5501443373891/12500000000000 : ℝ), (10721820131441/25000000000000 : ℝ), (818823279711/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337242689/2500000000 : ℝ)|^4309 ≤ (5501443373891/12500000000000 : ℝ)^3285
        have hw : |(1337242689/2500000000 : ℝ)|=(1337242689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327780239/625000000 : ℝ)|^4309 ≤ (10721820131441/25000000000000 : ℝ)^3285
        have hw : |(327780239/625000000 : ℝ)|=(327780239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123608571/10000000000 : ℝ)|^4309 ≤ (818823279711/6250000000000 : ℝ)^3285
        have hw : |(-2123608571/10000000000 : ℝ)|=(2123608571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_3 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324766877/10000000000 : ℝ)*x 0 + (830296009/2000000000 : ℝ)*x 1 + (4504775793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324766877/10000000000 : ℝ)^4309 ≤ (8325781832097/25000000000000 : ℝ)^3285 := by
    have hnat : (4324766877 : ℕ)^4309*25000000000000^3285 ≤ 8325781832097^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324766877 10000000000 8325781832097 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830296009/2000000000 : ℝ)^4309 ≤ (31563794197331/100000000000000 : ℝ)^3285 := by
    have hnat : (830296009 : ℕ)^4309*100000000000000^3285 ≤ 31563794197331^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830296009 2000000000 31563794197331 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504775793/10000000000 : ℝ)^4309 ≤ (35133078457551/100000000000000 : ℝ)^3285 := by
    have hnat : (4504775793 : ℕ)^4309*100000000000000^3285 ≤ 35133078457551^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504775793 10000000000 35133078457551 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324766877/10000000000 : ℝ), (830296009/2000000000 : ℝ), (4504775793/10000000000 : ℝ)] ![(8325781832097/25000000000000 : ℝ), (31563794197331/100000000000000 : ℝ), (35133078457551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324766877/10000000000 : ℝ)|^4309 ≤ (8325781832097/25000000000000 : ℝ)^3285
        have hw : |(4324766877/10000000000 : ℝ)|=(4324766877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830296009/2000000000 : ℝ)|^4309 ≤ (31563794197331/100000000000000 : ℝ)^3285
        have hw : |(830296009/2000000000 : ℝ)|=(830296009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504775793/10000000000 : ℝ)|^4309 ≤ (35133078457551/100000000000000 : ℝ)^3285
        have hw : |(4504775793/10000000000 : ℝ)|=(4504775793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_4 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018952983/5000000000 : ℝ)*x 0 + (5245088961/10000000000 : ℝ)*x 1 + (5412104393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018952983/5000000000 : ℝ)^4309 ≤ (3103009261307/25000000000000 : ℝ)^3285 := by
    have hnat : (1018952983 : ℕ)^4309*25000000000000^3285 ≤ 3103009261307^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018952983 5000000000 3103009261307 25000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245088961/10000000000 : ℝ)^4309 ≤ (1715750871067/4000000000000 : ℝ)^3285 := by
    have hnat : (5245088961 : ℕ)^4309*4000000000000^3285 ≤ 1715750871067^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245088961 10000000000 1715750871067 4000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412104393/10000000000 : ℝ)^4309 ≤ (44694191165471/100000000000000 : ℝ)^3285 := by
    have hnat : (5412104393 : ℕ)^4309*100000000000000^3285 ≤ 44694191165471^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412104393 10000000000 44694191165471 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018952983/5000000000 : ℝ), (5245088961/10000000000 : ℝ), (5412104393/10000000000 : ℝ)] ![(3103009261307/25000000000000 : ℝ), (1715750871067/4000000000000 : ℝ), (44694191165471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018952983/5000000000 : ℝ)|^4309 ≤ (3103009261307/25000000000000 : ℝ)^3285
        have hw : |(-1018952983/5000000000 : ℝ)|=(1018952983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245088961/10000000000 : ℝ)|^4309 ≤ (1715750871067/4000000000000 : ℝ)^3285
        have hw : |(5245088961/10000000000 : ℝ)|=(5245088961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412104393/10000000000 : ℝ)|^4309 ≤ (44694191165471/100000000000000 : ℝ)^3285
        have hw : |(5412104393/10000000000 : ℝ)|=(5412104393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_5 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652801997/5000000000 : ℝ)*x 0 + (-1955987991/10000000000 : ℝ)*x 1 + (5412104409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652801997/5000000000 : ℝ)^4309 ≤ (8708817417457/20000000000000 : ℝ)^3285 := by
    have hnat : (2652801997 : ℕ)^4309*20000000000000^3285 ≤ 8708817417457^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652801997 5000000000 8708817417457 20000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955987991/10000000000 : ℝ)^4309 ≤ (1470215195483/12500000000000 : ℝ)^3285 := by
    have hnat : (1955987991 : ℕ)^4309*12500000000000^3285 ≤ 1470215195483^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955987991 10000000000 1470215195483 12500000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412104409/10000000000 : ℝ)^4309 ≤ (4469419133879/10000000000000 : ℝ)^3285 := by
    have hnat : (5412104409 : ℕ)^4309*10000000000000^3285 ≤ 4469419133879^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412104409 10000000000 4469419133879 10000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652801997/5000000000 : ℝ), (-1955987991/10000000000 : ℝ), (5412104409/10000000000 : ℝ)] ![(8708817417457/20000000000000 : ℝ), (1470215195483/12500000000000 : ℝ), (4469419133879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652801997/5000000000 : ℝ)|^4309 ≤ (8708817417457/20000000000000 : ℝ)^3285
        have hw : |(2652801997/5000000000 : ℝ)|=(2652801997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955987991/10000000000 : ℝ)|^4309 ≤ (1470215195483/12500000000000 : ℝ)^3285
        have hw : |(-1955987991/10000000000 : ℝ)|=(1955987991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412104409/10000000000 : ℝ)|^4309 ≤ (4469419133879/10000000000000 : ℝ)^3285
        have hw : |(5412104409/10000000000 : ℝ)|=(5412104409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_6 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652801987/5000000000 : ℝ)*x 0 + (216484177/400000000 : ℝ)*x 1 + (-391197599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652801987/5000000000 : ℝ)^4309 ≤ (21772043435987/50000000000000 : ℝ)^3285 := by
    have hnat : (2652801987 : ℕ)^4309*50000000000000^3285 ≤ 21772043435987^3285*5000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652801987 5000000000 21772043435987 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216484177/400000000 : ℝ)^4309 ≤ (44694191512109/100000000000000 : ℝ)^3285 := by
    have hnat : (216484177 : ℕ)^4309*100000000000000^3285 ≤ 44694191512109^3285*400000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216484177 400000000 44694191512109 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391197599/2000000000 : ℝ)^4309 ≤ (5880860797707/50000000000000 : ℝ)^3285 := by
    have hnat : (391197599 : ℕ)^4309*50000000000000^3285 ≤ 5880860797707^3285*2000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391197599 2000000000 5880860797707 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652801987/5000000000 : ℝ), (216484177/400000000 : ℝ), (-391197599/2000000000 : ℝ)] ![(21772043435987/50000000000000 : ℝ), (44694191512109/100000000000000 : ℝ), (5880860797707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652801987/5000000000 : ℝ)|^4309 ≤ (21772043435987/50000000000000 : ℝ)^3285
        have hw : |(2652801987/5000000000 : ℝ)|=(2652801987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216484177/400000000 : ℝ)|^4309 ≤ (44694191512109/100000000000000 : ℝ)^3285
        have hw : |(216484177/400000000 : ℝ)|=(216484177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391197599/2000000000 : ℝ)|^4309 ≤ (5880860797707/50000000000000 : ℝ)^3285
        have hw : |(-391197599/2000000000 : ℝ)|=(391197599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1349_s5_7 (p : ℝ) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324792541/10000000000 : ℝ)*x 0 + (35183633/78125000 : ℝ)*x 1 + (415275747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324792541/10000000000 : ℝ)^4309 ≤ (16651693280067/50000000000000 : ℝ)^3285 := by
    have hnat : (4324792541 : ℕ)^4309*50000000000000^3285 ≤ 16651693280067^3285*10000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324792541 10000000000 16651693280067 50000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35183633/78125000 : ℝ)^4309 ≤ (35120078807521/100000000000000 : ℝ)^3285 := by
    have hnat : (35183633 : ℕ)^4309*100000000000000^3285 ≤ 35120078807521^3285*78125000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35183633 78125000 35120078807521 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415275747/1000000000 : ℝ)^4309 ≤ (31576534613249/100000000000000 : ℝ)^3285 := by
    have hnat : (415275747 : ℕ)^4309*100000000000000^3285 ≤ 31576534613249^3285*1000000000^4309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415275747 1000000000 31576534613249 100000000000000 4309 3285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4309/1024 : ℝ)) 4309 3285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324792541/10000000000 : ℝ), (35183633/78125000 : ℝ), (415275747/1000000000 : ℝ)] ![(16651693280067/50000000000000 : ℝ), (35120078807521/100000000000000 : ℝ), (31576534613249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324792541/10000000000 : ℝ)|^4309 ≤ (16651693280067/50000000000000 : ℝ)^3285
        have hw : |(4324792541/10000000000 : ℝ)|=(4324792541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35183633/78125000 : ℝ)|^4309 ≤ (35120078807521/100000000000000 : ℝ)^3285
        have hw : |(35183633/78125000 : ℝ)|=(35183633/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415275747/1000000000 : ℝ)|^4309 ≤ (31576534613249/100000000000000 : ℝ)^3285
        have hw : |(415275747/1000000000 : ℝ)|=(415275747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1349_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11117/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (9692594504074737/100000000000000000000 : ℝ) := by
    have hpowers : (11117/100000 : ℝ)^1077 ≤ (9692594504074737/100000000000000000000 : ℝ)^256 := by
      have hnat : (11117 : ℕ)^1077*100000000000000000000^256 ≤ 9692594504074737^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11117 100000 9692594504074737 100000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11117/100000 : ℝ)) (X := (9692594504074737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (1077/256 : ℝ) ≤ (31966247819043957/100000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^1077 ≤ (31966247819043957/100000000000000000000 : ℝ)^256 := by
      have hnat : (14763 : ℕ)^1077*100000000000000000000^256 ≤ 31966247819043957^256*100000^1077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 31966247819043957 100000000000000000000 1077 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (31966247819043957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009692594504074737/50000000000000000000 : ℝ) ≤ (2500115186670289/2500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50009692594504074737/50000000000000000000 : ℝ)^256 ≤ (2500115186670289/2500000000000000 : ℝ)^1077 := by
      have hnat : (50009692594504074737 : ℕ)^256*2500000000000000^1077 ≤ 2500115186670289^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009692594504074737 50000000000000000000 2500115186670289 2500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500115186670289/2500000000000000 : ℝ)) (X := (50009692594504074737/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020829421161559347/50000000000000000000 : ℝ) ≤ (1250123757784113/1250000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50020829421161559347/50000000000000000000 : ℝ)^256 ≤ (1250123757784113/1250000000000000 : ℝ)^1077 := by
      have hnat : (50020829421161559347 : ℕ)^256*1250000000000000^1077 ≤ 1250123757784113^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020829421161559347 50000000000000000000 1250123757784113 1250000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250123757784113/1250000000000000 : ℝ)) (X := (50020829421161559347/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031966247819043957/50000000000000000000 : ℝ) ≤ (2500379844466163/2500000000000000 : ℝ) ^ (1077/256 : ℝ) := by
    have hpowers : (50031966247819043957/50000000000000000000 : ℝ)^256 ≤ (2500379844466163/2500000000000000 : ℝ)^1077 := by
      have hnat : (50031966247819043957 : ℕ)^256*2500000000000000^1077 ≤ 2500379844466163^1077*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031966247819043957 50000000000000000000 2500379844466163 2500000000000000 256 1077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500379844466163/2500000000000000 : ℝ)) (X := (50031966247819043957/50000000000000000000 : ℝ)) (by norm_num) 1077 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9692594504074737/100000000000000000000 : ℝ) ≤ ((2278119442470785609/2278750000000000000 : ℝ)+2*(132328897937/91150000000000 : ℝ)*(11117/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (2278119442470785609/2278750000000000000 : ℝ)+2*(132328897937/91150000000000 : ℝ)*(11117/100000 : ℝ)=(2500115186670289/2500000000000000 : ℝ) by norm_num, show 1+2*(9692594504074737/100000000000000000000 : ℝ)=(50009692594504074737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31966247819043957/100000000000000000000 : ℝ)+(9692594504074737/100000000000000000000 : ℝ) ≤ ((2278119442470785609/2278750000000000000 : ℝ)+(132328897937/91150000000000 : ℝ)*((14763/100000 : ℝ)+(11117/100000 : ℝ)))^(1077/256 : ℝ) := by
    rw [show (2278119442470785609/2278750000000000000 : ℝ)+(132328897937/91150000000000 : ℝ)*((14763/100000 : ℝ)+(11117/100000 : ℝ))=(1250123757784113/1250000000000000 : ℝ) by norm_num, show 1+(31966247819043957/100000000000000000000 : ℝ)+(9692594504074737/100000000000000000000 : ℝ)=(50020829421161559347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31966247819043957/100000000000000000000 : ℝ) ≤ ((2278119442470785609/2278750000000000000 : ℝ)+2*(132328897937/91150000000000 : ℝ)*(14763/100000 : ℝ))^(1077/256 : ℝ) := by
    rw [show (2278119442470785609/2278750000000000000 : ℝ)+2*(132328897937/91150000000000 : ℝ)*(14763/100000 : ℝ)=(2500379844466163/2500000000000000 : ℝ) by norm_num, show 1+2*(31966247819043957/100000000000000000000 : ℝ)=(50031966247819043957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2278119442470785609/2278750000000000000 : ℝ)*(X 1 0+X 2 0)+(132328897937/91150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2278119442470785609/2278750000000000000 : ℝ)) (alpha := (132328897937/91150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2278119442470785609/2278750000000000000 : ℝ)*(X 0 1+X 2 1)+(132328897937/91150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2278119442470785609/2278750000000000000 : ℝ)) (alpha := (132328897937/91150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2278119442470785609/2278750000000000000 : ℝ)*(X 0 2+X 1 2)+(132328897937/91150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1077/256 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2278119442470785609/2278750000000000000 : ℝ)) (alpha := (132328897937/91150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037893727/10000000000 : ℝ)*X 0 0+(1082542533/2000000000 : ℝ)*X 0 1+(5244483809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674485359/5000000000 : ℝ)*X 1 0+(-132725539/625000000 : ℝ)*X 1 1+(5244483821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337242689/2500000000 : ℝ)*X 2 0+(327780239/625000000 : ℝ)*X 2 1+(-2123608571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324766877/10000000000 : ℝ)*X 0 0+(830296009/2000000000 : ℝ)*X 0 1+(4504775793/10000000000 : ℝ)*X 0 2+(4324766877/10000000000 : ℝ)*X 1 0+(830296009/2000000000 : ℝ)*X 1 1+(4504775793/10000000000 : ℝ)*X 1 2+(4324766877/10000000000 : ℝ)*X 2 0+(830296009/2000000000 : ℝ)*X 2 1+(4504775793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1018952983/5000000000 : ℝ)*X 0 0+(5245088961/10000000000 : ℝ)*X 0 1+(5412104393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652801997/5000000000 : ℝ)*X 1 0+(-1955987991/10000000000 : ℝ)*X 1 1+(5412104409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652801987/5000000000 : ℝ)*X 2 0+(216484177/400000000 : ℝ)*X 2 1+(-391197599/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324792541/10000000000 : ℝ)*X 0 0+(35183633/78125000 : ℝ)*X 0 1+(415275747/1000000000 : ℝ)*X 0 2+(4324792541/10000000000 : ℝ)*X 1 0+(35183633/78125000 : ℝ)*X 1 1+(415275747/1000000000 : ℝ)*X 1 2+(4324792541/10000000000 : ℝ)*X 2 0+(35183633/78125000 : ℝ)*X 2 1+(415275747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1349_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20966798657712891893866749/3560546875000000000000000000000 : ℝ) := by norm_num
    linear_combination (56623779/5000000000000 : ℝ)*(base19) + (1126670829/100000000000000 : ℝ)*(base23) + (12846699/50000000000000 : ℝ)*(lower2) + (62709209/50000000000000 : ℝ)*(upper3) + (10196153/6250000000000 : ℝ)*(upper5) + (548427724764073/12500000000000 : ℝ)*(major0) + (548427724764073/12500000000000 : ℝ)*(major1) + (877484359622517/20000000000000 : ℝ)*(major2) + (5944306014357191/100000000000000 : ℝ)*(sp0) + (2972164977151013/50000000000000 : ℝ)*(sp1) + (743041245013347/12500000000000 : ℝ)*(sp2) + (88453159558171/3125000000000 : ℝ)*(sp3) + (5014484083/20000000000000 : ℝ)*(sp4) + (11207297893/100000000000000 : ℝ)*(sp7) + (707628078289841/25000000000000 : ℝ)*(f.failure) + (2972165543388803/50000000000000 : ℝ)*(f.sum) + (45973101579297/9115000000000000000000000000 : ℝ)*base66 + (86367456833769417/7121093750000000000000000000000 : ℝ)*base68 + (63583533459502147/45575000000000000000000000000000 : ℝ)*base70 + (580376201655843293/28484375000000000000000000000000 : ℝ)*base72 + (26804466172833/9115000000000000000000000000 : ℝ)*base73 + (674826365904597853/45575000000000000000000000000000 : ℝ)*base75 + (237120082247541959/14242187500000000000000000000000 : ℝ)*base78 + (274571031939150457/28484375000000000000000000000000 : ℝ)*base79 + (3713595658117/4557500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (38669/78125000000000000000 : ℝ)*base90 + (38669/78125000000000000000 : ℝ)*base92 + (819919/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (351482867030808383787189063/113937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4541949/781250000000 : ℝ)*(base19) + (285757103/50000000000000 : ℝ)*(base23) + (4574711/100000000000000 : ℝ)*(upper2) + (80557201/100000000000000 : ℝ)*(upper3) + (1523391/2500000000000 : ℝ)*(upper5) + (4419261686571569/100000000000000 : ℝ)*(major0) + (4419261686571569/100000000000000 : ℝ)*(major1) + (4419261686571569/100000000000000 : ℝ)*(major2) + (11678099781/100000000000000 : ℝ)*(sp1) + (12178793271/100000000000000 : ℝ)*(sp2) + (748433711447789/12500000000000 : ℝ)*(sp4) + (5987457432113059/100000000000000 : ℝ)*(sp5) + (2993728470637417/50000000000000 : ℝ)*(sp6) + (114042143149267/4000000000000 : ℝ)*(sp7) + (114042143149267/4000000000000 : ℝ)*(f.failure) + (748433711447789/12500000000000 : ℝ)*(f.sum) + (24482460860739/9115000000000000000000000000 : ℝ)*base66 + (367360885395575521/227875000000000000000000000000000 : ℝ)*base67 + (2259414816527174479/227875000000000000000000000000000 : ℝ)*base70 + (1661344964127049479/227875000000000000000000000000000 : ℝ)*base72 + (73845723743801/9115000000000000000000000000 : ℝ)*base73 + (67764045810674479/227875000000000000000000000000000 : ℝ)*base76 + (2505394599442549479/227875000000000000000000000000000 : ℝ)*base78 + (244757089044825521/227875000000000000000000000000000 : ℝ)*base79 + (14037931147221/9115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (47103/12500000000000000000 : ℝ)*base90 + (47103/12500000000000000000 : ℝ)*base92 + (47103/12500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1349_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1349_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1349_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1349_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1349_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1349_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1077/256 : ℝ) ≤ p) (hpb : p ≤ (4309/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4843891/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4019/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1349_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

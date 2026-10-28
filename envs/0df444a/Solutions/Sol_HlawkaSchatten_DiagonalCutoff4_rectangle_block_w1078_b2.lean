-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:22.456548+00:00
-- url     : https://prove2.me/submissions/98359139-b8a7-4aa2-b9a9-49cd4e5543fa

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
theorem support_rectangle_w1078_s6_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098913061/5000000000 : ℝ)*x 0 + (1348667763/2500000000 : ℝ)*x 1 + (5264178269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098913061/5000000000 : ℝ)^8271 ≤ (13348799335373/100000000000000 : ℝ)^6223 := by
    have hnat : (1098913061 : ℕ)^8271*100000000000000^6223 ≤ 13348799335373^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098913061 5000000000 13348799335373 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348667763/2500000000 : ℝ)^8271 ≤ (22015278437051/50000000000000 : ℝ)^6223 := by
    have hnat : (1348667763 : ℕ)^8271*50000000000000^6223 ≤ 22015278437051^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348667763 2500000000 22015278437051 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264178269/10000000000 : ℝ)^8271 ≤ (21310321890737/50000000000000 : ℝ)^6223 := by
    have hnat : (5264178269 : ℕ)^8271*50000000000000^6223 ≤ 21310321890737^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264178269 10000000000 21310321890737 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098913061/5000000000 : ℝ), (1348667763/2500000000 : ℝ), (5264178269/10000000000 : ℝ)] ![(13348799335373/100000000000000 : ℝ), (22015278437051/50000000000000 : ℝ), (21310321890737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098913061/5000000000 : ℝ)|^8271 ≤ (13348799335373/100000000000000 : ℝ)^6223
        have hw : |(-1098913061/5000000000 : ℝ)|=(1098913061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348667763/2500000000 : ℝ)|^8271 ≤ (22015278437051/50000000000000 : ℝ)^6223
        have hw : |(1348667763/2500000000 : ℝ)|=(1348667763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264178269/10000000000 : ℝ)|^8271 ≤ (21310321890737/50000000000000 : ℝ)^6223
        have hw : |(5264178269/10000000000 : ℝ)|=(5264178269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336270387/2500000000 : ℝ)*x 0 + (-2264038317/10000000000 : ℝ)*x 1 + (5264178267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336270387/2500000000 : ℝ)^8271 ≤ (8698685618509/20000000000000 : ℝ)^6223 := by
    have hnat : (1336270387 : ℕ)^8271*20000000000000^6223 ≤ 8698685618509^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336270387 2500000000 8698685618509 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264038317/10000000000 : ℝ)^8271 ≤ (13885928126139/100000000000000 : ℝ)^6223 := by
    have hnat : (2264038317 : ℕ)^8271*100000000000000^6223 ≤ 13885928126139^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264038317 10000000000 13885928126139 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264178267/10000000000 : ℝ)^8271 ≤ (2663790234997/6250000000000 : ℝ)^6223 := by
    have hnat : (5264178267 : ℕ)^8271*6250000000000^6223 ≤ 2663790234997^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264178267 10000000000 2663790234997 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336270387/2500000000 : ℝ), (-2264038317/10000000000 : ℝ), (5264178267/10000000000 : ℝ)] ![(8698685618509/20000000000000 : ℝ), (13885928126139/100000000000000 : ℝ), (2663790234997/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336270387/2500000000 : ℝ)|^8271 ≤ (8698685618509/20000000000000 : ℝ)^6223
        have hw : |(1336270387/2500000000 : ℝ)|=(1336270387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264038317/10000000000 : ℝ)|^8271 ≤ (13885928126139/100000000000000 : ℝ)^6223
        have hw : |(-2264038317/10000000000 : ℝ)|=(2264038317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264178267/10000000000 : ℝ)|^8271 ≤ (2663790234997/6250000000000 : ℝ)^6223
        have hw : |(5264178267/10000000000 : ℝ)|=(5264178267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345081543/10000000000 : ℝ)*x 0 + (5264178273/10000000000 : ℝ)*x 1 + (-566009579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345081543/10000000000 : ℝ)^8271 ≤ (43493428038469/100000000000000 : ℝ)^6223 := by
    have hnat : (5345081543 : ℕ)^8271*100000000000000^6223 ≤ 43493428038469^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345081543 10000000000 43493428038469 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264178273/10000000000 : ℝ)^8271 ≤ (42620643824517/100000000000000 : ℝ)^6223 := by
    have hnat : (5264178273 : ℕ)^8271*100000000000000^6223 ≤ 42620643824517^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264178273 10000000000 42620643824517 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566009579/2500000000 : ℝ)^8271 ≤ (3471482029497/25000000000000 : ℝ)^6223 := by
    have hnat : (566009579 : ℕ)^8271*25000000000000^6223 ≤ 3471482029497^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566009579 2500000000 3471482029497 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345081543/10000000000 : ℝ), (5264178273/10000000000 : ℝ), (-566009579/2500000000 : ℝ)] ![(43493428038469/100000000000000 : ℝ), (42620643824517/100000000000000 : ℝ), (3471482029497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345081543/10000000000 : ℝ)|^8271 ≤ (43493428038469/100000000000000 : ℝ)^6223
        have hw : |(5345081543/10000000000 : ℝ)|=(5345081543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264178273/10000000000 : ℝ)|^8271 ≤ (42620643824517/100000000000000 : ℝ)^6223
        have hw : |(5264178273/10000000000 : ℝ)|=(5264178273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566009579/2500000000 : ℝ)|^8271 ≤ (3471482029497/25000000000000 : ℝ)^6223
        have hw : |(-566009579/2500000000 : ℝ)|=(566009579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093435807/2500000000 : ℝ)*x 0 + (1061865511/2500000000 : ℝ)*x 1 + (4503819143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093435807/2500000000 : ℝ)^8271 ≤ (4164544374593/12500000000000 : ℝ)^6223 := by
    have hnat : (1093435807 : ℕ)^8271*12500000000000^6223 ≤ 4164544374593^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093435807 2500000000 4164544374593 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061865511/2500000000 : ℝ)^8271 ≤ (16021983944513/50000000000000 : ℝ)^6223 := by
    have hnat : (1061865511 : ℕ)^8271*50000000000000^6223 ≤ 16021983944513^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061865511 2500000000 16021983944513 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503819143/10000000000 : ℝ)^8271 ≤ (17319838551301/50000000000000 : ℝ)^6223 := by
    have hnat : (4503819143 : ℕ)^8271*50000000000000^6223 ≤ 17319838551301^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503819143 10000000000 17319838551301 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093435807/2500000000 : ℝ), (1061865511/2500000000 : ℝ), (4503819143/10000000000 : ℝ)] ![(4164544374593/12500000000000 : ℝ), (16021983944513/50000000000000 : ℝ), (17319838551301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093435807/2500000000 : ℝ)|^8271 ≤ (4164544374593/12500000000000 : ℝ)^6223
        have hw : |(1093435807/2500000000 : ℝ)|=(1093435807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061865511/2500000000 : ℝ)|^8271 ≤ (16021983944513/50000000000000 : ℝ)^6223
        have hw : |(1061865511/2500000000 : ℝ)|=(1061865511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503819143/10000000000 : ℝ)|^8271 ≤ (17319838551301/50000000000000 : ℝ)^6223
        have hw : |(4503819143/10000000000 : ℝ)|=(4503819143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-27472891/125000000 : ℝ)*x 0 + (526450781/1000000000 : ℝ)*x 1 + (5394340311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27472891/125000000 : ℝ)^8271 ≤ (3337210243313/25000000000000 : ℝ)^6223 := by
    have hnat : (27472891 : ℕ)^8271*25000000000000^6223 ≤ 3337210243313^6223*125000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27472891 125000000 3337210243313 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526450781/1000000000 : ℝ)^8271 ≤ (10656047491981/25000000000000 : ℝ)^6223 := by
    have hnat : (526450781 : ℕ)^8271*25000000000000^6223 ≤ 10656047491981^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526450781 1000000000 10656047491981 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394340311/10000000000 : ℝ)^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223 := by
    have hnat : (5394340311 : ℕ)^8271*10000000000000^6223 ≤ 4402696905049^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394340311 10000000000 4402696905049 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27472891/125000000 : ℝ), (526450781/1000000000 : ℝ), (5394340311/10000000000 : ℝ)] ![(3337210243313/25000000000000 : ℝ), (10656047491981/25000000000000 : ℝ), (4402696905049/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27472891/125000000 : ℝ)|^8271 ≤ (3337210243313/25000000000000 : ℝ)^6223
        have hw : |(-27472891/125000000 : ℝ)|=(27472891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526450781/1000000000 : ℝ)|^8271 ≤ (10656047491981/25000000000000 : ℝ)^6223
        have hw : |(526450781/1000000000 : ℝ)|=(526450781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394340311/10000000000 : ℝ)|^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223
        have hw : |(5394340311/10000000000 : ℝ)|=(5394340311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328045453/2500000000 : ℝ)*x 0 + (-533469073/2500000000 : ℝ)*x 1 + (5394340311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328045453/2500000000 : ℝ)^8271 ≤ (8627595500717/20000000000000 : ℝ)^6223 := by
    have hnat : (1328045453 : ℕ)^8271*20000000000000^6223 ≤ 8627595500717^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328045453 2500000000 8627595500717 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533469073/2500000000 : ℝ)^8271 ≤ (12835053438383/100000000000000 : ℝ)^6223 := by
    have hnat : (533469073 : ℕ)^8271*100000000000000^6223 ≤ 12835053438383^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533469073 2500000000 12835053438383 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394340311/10000000000 : ℝ)^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223 := by
    have hnat : (5394340311 : ℕ)^8271*10000000000000^6223 ≤ 4402696905049^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394340311 10000000000 4402696905049 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328045453/2500000000 : ℝ), (-533469073/2500000000 : ℝ), (5394340311/10000000000 : ℝ)] ![(8627595500717/20000000000000 : ℝ), (12835053438383/100000000000000 : ℝ), (4402696905049/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328045453/2500000000 : ℝ)|^8271 ≤ (8627595500717/20000000000000 : ℝ)^6223
        have hw : |(1328045453/2500000000 : ℝ)|=(1328045453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533469073/2500000000 : ℝ)|^8271 ≤ (12835053438383/100000000000000 : ℝ)^6223
        have hw : |(-533469073/2500000000 : ℝ)|=(533469073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394340311/10000000000 : ℝ)|^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223
        have hw : |(5394340311/10000000000 : ℝ)|=(5394340311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312181811/10000000000 : ℝ)*x 0 + (5394340311/10000000000 : ℝ)*x 1 + (-533469073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312181811/10000000000 : ℝ)^8271 ≤ (5392247186599/12500000000000 : ℝ)^6223 := by
    have hnat : (5312181811 : ℕ)^8271*12500000000000^6223 ≤ 5392247186599^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312181811 10000000000 5392247186599 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394340311/10000000000 : ℝ)^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223 := by
    have hnat : (5394340311 : ℕ)^8271*10000000000000^6223 ≤ 4402696905049^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394340311 10000000000 4402696905049 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533469073/2500000000 : ℝ)^8271 ≤ (12835053438383/100000000000000 : ℝ)^6223 := by
    have hnat : (533469073 : ℕ)^8271*100000000000000^6223 ≤ 12835053438383^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533469073 2500000000 12835053438383 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312181811/10000000000 : ℝ), (5394340311/10000000000 : ℝ), (-533469073/2500000000 : ℝ)] ![(5392247186599/12500000000000 : ℝ), (4402696905049/10000000000000 : ℝ), (12835053438383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312181811/10000000000 : ℝ)|^8271 ≤ (5392247186599/12500000000000 : ℝ)^6223
        have hw : |(5312181811/10000000000 : ℝ)|=(5312181811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394340311/10000000000 : ℝ)|^8271 ≤ (4402696905049/10000000000000 : ℝ)^6223
        have hw : |(5394340311/10000000000 : ℝ)|=(5394340311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533469073/2500000000 : ℝ)|^8271 ≤ (12835053438383/100000000000000 : ℝ)^6223
        have hw : |(-533469073/2500000000 : ℝ)|=(533469073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s6_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8542487/19531250 : ℝ)*x 0 + (4503171741/10000000000 : ℝ)*x 1 + (4248111807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8542487/19531250 : ℝ)^8271 ≤ (4164557176699/12500000000000 : ℝ)^6223 := by
    have hnat : (8542487 : ℕ)^8271*12500000000000^6223 ≤ 4164557176699^6223*19531250^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8542487 19531250 4164557176699 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503171741/10000000000 : ℝ)^8271 ≤ (6926611856747/20000000000000 : ℝ)^6223 := by
    have hnat : (4503171741 : ℕ)^8271*20000000000000^6223 ≤ 6926611856747^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503171741 10000000000 6926611856747 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248111807/10000000000 : ℝ)^8271 ≤ (1282019331457/4000000000000 : ℝ)^6223 := by
    have hnat : (4248111807 : ℕ)^8271*4000000000000^6223 ≤ 1282019331457^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248111807 10000000000 1282019331457 4000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8542487/19531250 : ℝ), (4503171741/10000000000 : ℝ), (4248111807/10000000000 : ℝ)] ![(4164557176699/12500000000000 : ℝ), (6926611856747/20000000000000 : ℝ), (1282019331457/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8542487/19531250 : ℝ)|^8271 ≤ (4164557176699/12500000000000 : ℝ)^6223
        have hw : |(8542487/19531250 : ℝ)|=(8542487/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503171741/10000000000 : ℝ)|^8271 ≤ (6926611856747/20000000000000 : ℝ)^6223
        have hw : |(4503171741/10000000000 : ℝ)|=(4503171741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248111807/10000000000 : ℝ)|^8271 ≤ (1282019331457/4000000000000 : ℝ)^6223
        have hw : |(4248111807/10000000000 : ℝ)|=(4248111807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5609/50000 : ℝ) ^ (4135/1024 : ℝ) ≤ (14570581396116737/100000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^4135 ≤ (14570581396116737/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5609 : ℕ)^4135*100000000000000000000^1024 ≤ 14570581396116737^1024*50000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 14570581396116737 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (14570581396116737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14063/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (9074143997305893/25000000000000000000 : ℝ) := by
    have hpowers : (14063/100000 : ℝ)^4135 ≤ (9074143997305893/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14063 : ℕ)^4135*25000000000000000000^1024 ≤ 9074143997305893^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14063 100000 9074143997305893 25000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14063/100000 : ℝ)) (X := (9074143997305893/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014570581396116737/50000000000000000000 : ℝ) ≤ (10000721578719409/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50014570581396116737/50000000000000000000 : ℝ)^1024 ≤ (10000721578719409/10000000000000000 : ℝ)^4135 := by
      have hnat : (50014570581396116737 : ℕ)^1024*10000000000000000^4135 ≤ 10000721578719409^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014570581396116737 50000000000000000000 10000721578719409 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000721578719409/10000000000000000 : ℝ)) (X := (50014570581396116737/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050867157385340309/100000000000000000000 : ℝ) ≤ (10001259443893827/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (100050867157385340309/100000000000000000000 : ℝ)^1024 ≤ (10001259443893827/10000000000000000 : ℝ)^4135 := by
      have hnat : (100050867157385340309 : ℕ)^1024*10000000000000000^4135 ≤ 10001259443893827^4135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050867157385340309 100000000000000000000 10001259443893827 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259443893827/10000000000000000 : ℝ)) (X := (100050867157385340309/100000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509074143997305893/12500000000000000000 : ℝ) ≤ (2000359461813649/2000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (12509074143997305893/12500000000000000000 : ℝ)^1024 ≤ (2000359461813649/2000000000000000 : ℝ)^4135 := by
      have hnat : (12509074143997305893 : ℕ)^1024*2000000000000000^4135 ≤ 2000359461813649^4135*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509074143997305893 12500000000000000000 2000359461813649 2000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000359461813649/2000000000000000 : ℝ)) (X := (12509074143997305893/12500000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14570581396116737/100000000000000000000 : ℝ) ≤ ((28439985348403476357/28450000000000000000 : ℝ)+2*(268932587209/142250000000000 : ℝ)*(5609/50000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (28439985348403476357/28450000000000000000 : ℝ)+2*(268932587209/142250000000000 : ℝ)*(5609/50000 : ℝ)=(10000721578719409/10000000000000000 : ℝ) by norm_num, show 1+2*(14570581396116737/100000000000000000000 : ℝ)=(50014570581396116737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9074143997305893/25000000000000000000 : ℝ)+(14570581396116737/100000000000000000000 : ℝ) ≤ ((28439985348403476357/28450000000000000000 : ℝ)+(268932587209/142250000000000 : ℝ)*((14063/100000 : ℝ)+(5609/50000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (28439985348403476357/28450000000000000000 : ℝ)+(268932587209/142250000000000 : ℝ)*((14063/100000 : ℝ)+(5609/50000 : ℝ))=(10001259443893827/10000000000000000 : ℝ) by norm_num, show 1+(9074143997305893/25000000000000000000 : ℝ)+(14570581396116737/100000000000000000000 : ℝ)=(100050867157385340309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9074143997305893/25000000000000000000 : ℝ) ≤ ((28439985348403476357/28450000000000000000 : ℝ)+2*(268932587209/142250000000000 : ℝ)*(14063/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (28439985348403476357/28450000000000000000 : ℝ)+2*(268932587209/142250000000000 : ℝ)*(14063/100000 : ℝ)=(2000359461813649/2000000000000000 : ℝ) by norm_num, show 1+2*(9074143997305893/25000000000000000000 : ℝ)=(12509074143997305893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28439985348403476357/28450000000000000000 : ℝ)*(X 1 0+X 2 0)+(268932587209/142250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (28439985348403476357/28450000000000000000 : ℝ)) (alpha := (268932587209/142250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28439985348403476357/28450000000000000000 : ℝ)*(X 0 1+X 2 1)+(268932587209/142250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (28439985348403476357/28450000000000000000 : ℝ)) (alpha := (268932587209/142250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28439985348403476357/28450000000000000000 : ℝ)*(X 0 2+X 1 2)+(268932587209/142250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (28439985348403476357/28450000000000000000 : ℝ)) (alpha := (268932587209/142250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098913061/5000000000 : ℝ)*X 0 0+(1348667763/2500000000 : ℝ)*X 0 1+(5264178269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336270387/2500000000 : ℝ)*X 1 0+(-2264038317/10000000000 : ℝ)*X 1 1+(5264178267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345081543/10000000000 : ℝ)*X 2 0+(5264178273/10000000000 : ℝ)*X 2 1+(-566009579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093435807/2500000000 : ℝ)*X 0 0+(1061865511/2500000000 : ℝ)*X 0 1+(4503819143/10000000000 : ℝ)*X 0 2+(1093435807/2500000000 : ℝ)*X 1 0+(1061865511/2500000000 : ℝ)*X 1 1+(4503819143/10000000000 : ℝ)*X 1 2+(1093435807/2500000000 : ℝ)*X 2 0+(1061865511/2500000000 : ℝ)*X 2 1+(4503819143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-27472891/125000000 : ℝ)*X 0 0+(526450781/1000000000 : ℝ)*X 0 1+(5394340311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328045453/2500000000 : ℝ)*X 1 0+(-533469073/2500000000 : ℝ)*X 1 1+(5394340311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312181811/10000000000 : ℝ)*X 2 0+(5394340311/10000000000 : ℝ)*X 2 1+(-533469073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8542487/19531250 : ℝ)*X 0 0+(4503171741/10000000000 : ℝ)*X 0 1+(4248111807/10000000000 : ℝ)*X 0 2+(8542487/19531250 : ℝ)*X 1 0+(4503171741/10000000000 : ℝ)*X 1 1+(4248111807/10000000000 : ℝ)*X 1 2+(8542487/19531250 : ℝ)*X 2 0+(4503171741/10000000000 : ℝ)*X 2 1+(4248111807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14699705824195167938255256843/1422500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2131814477/100000000000000 : ℝ)*(base19) + (123142517/6250000000000 : ℝ)*(base23) + (82509661/100000000000000 : ℝ)*(lower2) + (266788553/100000000000000 : ℝ)*(upper3) + (6089051/4000000000000 : ℝ)*(upper5) + (5782122474777467/100000000000000 : ℝ)*(major0) + (5782122474777467/100000000000000 : ℝ)*(major1) + (5782122474777467/100000000000000 : ℝ)*(major2) + (957914872311007/12500000000000 : ℝ)*(sp0) + (7663373796310339/100000000000000 : ℝ)*(sp1) + (119740218091321/1562500000000 : ℝ)*(sp2) + (1950418534187621/50000000000000 : ℝ)*(sp3) + (1423740919/2500000000000 : ℝ)*(sp4) + (31608597789/100000000000000 : ℝ)*(sp7) + (3900868676973031/100000000000000 : ℝ)*(f.failure) + (478960995507801/6250000000000 : ℝ)*(f.sum) + (29596056479103/7112500000000000000000000000 : ℝ)*base65 + (21975678850086447719/2845000000000000000000000000000000 : ℝ)*base67 + (28627590579406447719/2845000000000000000000000000000000 : ℝ)*base69 + (53337546151111447719/2845000000000000000000000000000000 : ℝ)*base71 + (2911369750139/3556250000000000000000000000 : ℝ)*base73 + (77219254848798552281/2845000000000000000000000000000000 : ℝ)*base76 + (58870917211447719/2845000000000000000000000000000000 : ℝ)*base77 + (7391384139913552281/2845000000000000000000000000000000 : ℝ)*base80 + (9947460793581/14225000000000000000000000000 : ℝ)*base81 + (5284483/2000000000000000000000 : ℝ)*base90 + (5284483/2000000000000000000000 : ℝ)*base92 + (5284483/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (385410777070716039112765371/177812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406495553/100000000000000 : ℝ)*(base19) + (110002393/25000000000000 : ℝ)*(base23) + (21920309/50000000000000 : ℝ)*(upper3) + (400771/2500000000000 : ℝ)*(lower4) + (44619691/100000000000000 : ℝ)*(upper5) + (726429898309267/12500000000000 : ℝ)*(major0) + (726429898309267/12500000000000 : ℝ)*(major1) + (726429898309267/12500000000000 : ℝ)*(major2) + (2753825063/25000000000000 : ℝ)*(sp1) + (5894073307/50000000000000 : ℝ)*(sp2) + (7702231308258791/100000000000000 : ℝ)*(sp4) + (3851109943231493/50000000000000 : ℝ)*(sp5) + (3851109540051303/50000000000000 : ℝ)*(sp6) + (490080874054883/12500000000000 : ℝ)*(sp7) + (490080874054883/12500000000000 : ℝ)*(f.failure) + (7702231308258791/100000000000000 : ℝ)*(f.sum) + (1480855552293/222265625000000000000000000 : ℝ)*base66 + (4127153237484649681/355625000000000000000000000000000 : ℝ)*base68 + (777167343131524681/355625000000000000000000000000000 : ℝ)*base70 + (2517965265665899681/355625000000000000000000000000000 : ℝ)*base72 + (11706135857613/3556250000000000000000000000 : ℝ)*base74 + (2959221150382149681/355625000000000000000000000000000 : ℝ)*base76 + (4790723437953399681/355625000000000000000000000000000 : ℝ)*base78 + (3130909053160899681/355625000000000000000000000000000 : ℝ)*base80 + (204393971081/1778125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1384081/250000000000000000000 : ℝ)*base89 + (1384081/250000000000000000000 : ℝ)*base91 + (1384081/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s7_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197868069/10000000000 : ℝ)*x 0 + (1348558393/2500000000 : ℝ)*x 1 + (5264587809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197868069/10000000000 : ℝ)^8271 ≤ (6674568976423/50000000000000 : ℝ)^6223 := by
    have hnat : (2197868069 : ℕ)^8271*50000000000000^6223 ≤ 6674568976423^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197868069 10000000000 6674568976423 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348558393/2500000000 : ℝ)^8271 ≤ (44025811178941/100000000000000 : ℝ)^6223 := by
    have hnat : (1348558393 : ℕ)^8271*100000000000000^6223 ≤ 44025811178941^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348558393 2500000000 44025811178941 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264587809/10000000000 : ℝ)^8271 ≤ (42625050847151/100000000000000 : ℝ)^6223 := by
    have hnat : (5264587809 : ℕ)^8271*100000000000000^6223 ≤ 42625050847151^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264587809 10000000000 42625050847151 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197868069/10000000000 : ℝ), (1348558393/2500000000 : ℝ), (5264587809/10000000000 : ℝ)] ![(6674568976423/50000000000000 : ℝ), (44025811178941/100000000000000 : ℝ), (42625050847151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197868069/10000000000 : ℝ)|^8271 ≤ (6674568976423/50000000000000 : ℝ)^6223
        have hw : |(-2197868069/10000000000 : ℝ)|=(2197868069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348558393/2500000000 : ℝ)|^8271 ≤ (44025811178941/100000000000000 : ℝ)^6223
        have hw : |(1348558393/2500000000 : ℝ)|=(1348558393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264587809/10000000000 : ℝ)|^8271 ≤ (42625050847151/100000000000000 : ℝ)^6223
        have hw : |(5264587809/10000000000 : ℝ)|=(5264587809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344970999/10000000000 : ℝ)*x 0 + (-2263644267/10000000000 : ℝ)*x 1 + (1052917573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344970999/10000000000 : ℝ)^8271 ≤ (1739689300257/4000000000000 : ℝ)^6223 := by
    have hnat : (5344970999 : ℕ)^8271*4000000000000^6223 ≤ 1739689300257^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344970999 10000000000 1739689300257 4000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263644267/10000000000 : ℝ)^8271 ≤ (6941358016043/50000000000000 : ℝ)^6223 := by
    have hnat : (2263644267 : ℕ)^8271*50000000000000^6223 ≤ 6941358016043^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263644267 10000000000 6941358016043 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052917573/2000000000 : ℝ)^8271 ≤ (1705002057991/4000000000000 : ℝ)^6223 := by
    have hnat : (1052917573 : ℕ)^8271*4000000000000^6223 ≤ 1705002057991^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052917573 2000000000 1705002057991 4000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344970999/10000000000 : ℝ), (-2263644267/10000000000 : ℝ), (1052917573/2000000000 : ℝ)] ![(1739689300257/4000000000000 : ℝ), (6941358016043/50000000000000 : ℝ), (1705002057991/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344970999/10000000000 : ℝ)|^8271 ≤ (1739689300257/4000000000000 : ℝ)^6223
        have hw : |(5344970999/10000000000 : ℝ)|=(5344970999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263644267/10000000000 : ℝ)|^8271 ≤ (6941358016043/50000000000000 : ℝ)^6223
        have hw : |(-2263644267/10000000000 : ℝ)|=(2263644267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052917573/2000000000 : ℝ)|^8271 ≤ (1705002057991/4000000000000 : ℝ)^6223
        have hw : |(1052917573/2000000000 : ℝ)|=(1052917573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344971041/10000000000 : ℝ)*x 0 + (5264587833/10000000000 : ℝ)*x 1 + (-1131822127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344971041/10000000000 : ℝ)^8271 ≤ (43492232960653/100000000000000 : ℝ)^6223 := by
    have hnat : (5344971041 : ℕ)^8271*100000000000000^6223 ≤ 43492232960653^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344971041 10000000000 43492232960653 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264587833/10000000000 : ℝ)^8271 ≤ (42625051105419/100000000000000 : ℝ)^6223 := by
    have hnat : (5264587833 : ℕ)^8271*100000000000000^6223 ≤ 42625051105419^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264587833 10000000000 42625051105419 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131822127/5000000000 : ℝ)^8271 ≤ (347067898153/2500000000000 : ℝ)^6223 := by
    have hnat : (1131822127 : ℕ)^8271*2500000000000^6223 ≤ 347067898153^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131822127 5000000000 347067898153 2500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344971041/10000000000 : ℝ), (5264587833/10000000000 : ℝ), (-1131822127/5000000000 : ℝ)] ![(43492232960653/100000000000000 : ℝ), (42625051105419/100000000000000 : ℝ), (347067898153/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344971041/10000000000 : ℝ)|^8271 ≤ (43492232960653/100000000000000 : ℝ)^6223
        have hw : |(5344971041/10000000000 : ℝ)|=(5344971041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264587833/10000000000 : ℝ)|^8271 ≤ (42625051105419/100000000000000 : ℝ)^6223
        have hw : |(5264587833/10000000000 : ℝ)|=(5264587833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1131822127/5000000000 : ℝ)|^8271 ≤ (347067898153/2500000000000 : ℝ)^6223
        have hw : |(-1131822127/5000000000 : ℝ)|=(1131822127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186882499/5000000000 : ℝ)*x 0 + (4248291119/10000000000 : ℝ)*x 1 + (1125746073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186882499/5000000000 : ℝ)^8271 ≤ (33316575401623/100000000000000 : ℝ)^6223 := by
    have hnat : (2186882499 : ℕ)^8271*100000000000000^6223 ≤ 33316575401623^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186882499 5000000000 33316575401623 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248291119/10000000000 : ℝ)^8271 ≤ (6410456273471/20000000000000 : ℝ)^6223 := by
    have hnat : (4248291119 : ℕ)^8271*20000000000000^6223 ≤ 6410456273471^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248291119 10000000000 6410456273471 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125746073/2500000000 : ℝ)^8271 ≤ (34631143216613/100000000000000 : ℝ)^6223 := by
    have hnat : (1125746073 : ℕ)^8271*100000000000000^6223 ≤ 34631143216613^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125746073 2500000000 34631143216613 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186882499/5000000000 : ℝ), (4248291119/10000000000 : ℝ), (1125746073/2500000000 : ℝ)] ![(33316575401623/100000000000000 : ℝ), (6410456273471/20000000000000 : ℝ), (34631143216613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186882499/5000000000 : ℝ)|^8271 ≤ (33316575401623/100000000000000 : ℝ)^6223
        have hw : |(2186882499/5000000000 : ℝ)|=(2186882499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248291119/10000000000 : ℝ)|^8271 ≤ (6410456273471/20000000000000 : ℝ)^6223
        have hw : |(4248291119/10000000000 : ℝ)|=(4248291119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125746073/2500000000 : ℝ)|^8271 ≤ (34631143216613/100000000000000 : ℝ)^6223
        have hw : |(1125746073/2500000000 : ℝ)|=(1125746073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197873089/10000000000 : ℝ)*x 0 + (52649131/100000000 : ℝ)*x 1 + (5393907133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197873089/10000000000 : ℝ)^8271 ≤ (834323654811/6250000000000 : ℝ)^6223 := by
    have hnat : (2197873089 : ℕ)^8271*6250000000000^6223 ≤ 834323654811^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197873089 10000000000 834323654811 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52649131/100000000 : ℝ)^8271 ≤ (42628551388559/100000000000000 : ℝ)^6223 := by
    have hnat : (52649131 : ℕ)^8271*100000000000000^6223 ≤ 42628551388559^6223*100000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52649131 100000000 42628551388559 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393907133/10000000000 : ℝ)^8271 ≤ (22011135058381/50000000000000 : ℝ)^6223 := by
    have hnat : (5393907133 : ℕ)^8271*50000000000000^6223 ≤ 22011135058381^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393907133 10000000000 22011135058381 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197873089/10000000000 : ℝ), (52649131/100000000 : ℝ), (5393907133/10000000000 : ℝ)] ![(834323654811/6250000000000 : ℝ), (42628551388559/100000000000000 : ℝ), (22011135058381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197873089/10000000000 : ℝ)|^8271 ≤ (834323654811/6250000000000 : ℝ)^6223
        have hw : |(-2197873089/10000000000 : ℝ)|=(2197873089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52649131/100000000 : ℝ)|^8271 ≤ (42628551388559/100000000000000 : ℝ)^6223
        have hw : |(52649131/100000000 : ℝ)|=(52649131/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393907133/10000000000 : ℝ)|^8271 ≤ (22011135058381/50000000000000 : ℝ)^6223
        have hw : |(5393907133/10000000000 : ℝ)|=(5393907133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328071213/2500000000 : ℝ)*x 0 + (-2134324941/10000000000 : ℝ)*x 1 + (5393907133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328071213/2500000000 : ℝ)^8271 ≤ (2156954481263/5000000000000 : ℝ)^6223 := by
    have hnat : (1328071213 : ℕ)^8271*5000000000000^6223 ≤ 2156954481263^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328071213 2500000000 2156954481263 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134324941/10000000000 : ℝ)^8271 ≤ (6419320124271/50000000000000 : ℝ)^6223 := by
    have hnat : (2134324941 : ℕ)^8271*50000000000000^6223 ≤ 6419320124271^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134324941 10000000000 6419320124271 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393907133/10000000000 : ℝ)^8271 ≤ (22011135058381/50000000000000 : ℝ)^6223 := by
    have hnat : (5393907133 : ℕ)^8271*50000000000000^6223 ≤ 22011135058381^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393907133 10000000000 22011135058381 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328071213/2500000000 : ℝ), (-2134324941/10000000000 : ℝ), (5393907133/10000000000 : ℝ)] ![(2156954481263/5000000000000 : ℝ), (6419320124271/50000000000000 : ℝ), (22011135058381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328071213/2500000000 : ℝ)|^8271 ≤ (2156954481263/5000000000000 : ℝ)^6223
        have hw : |(1328071213/2500000000 : ℝ)|=(1328071213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134324941/10000000000 : ℝ)|^8271 ≤ (6419320124271/50000000000000 : ℝ)^6223
        have hw : |(-2134324941/10000000000 : ℝ)|=(2134324941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393907133/10000000000 : ℝ)|^8271 ≤ (22011135058381/50000000000000 : ℝ)^6223
        have hw : |(5393907133/10000000000 : ℝ)|=(5393907133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656142427/5000000000 : ℝ)*x 0 + (5393907131/10000000000 : ℝ)*x 1 + (-106716247/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656142427/5000000000 : ℝ)^8271 ≤ (43139089646847/100000000000000 : ℝ)^6223 := by
    have hnat : (2656142427 : ℕ)^8271*100000000000000^6223 ≤ 43139089646847^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656142427 5000000000 43139089646847 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393907131/10000000000 : ℝ)^8271 ≤ (44022270095067/100000000000000 : ℝ)^6223 := by
    have hnat : (5393907131 : ℕ)^8271*100000000000000^6223 ≤ 44022270095067^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393907131 10000000000 44022270095067 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106716247/500000000 : ℝ)^8271 ≤ (12838640240547/100000000000000 : ℝ)^6223 := by
    have hnat : (106716247 : ℕ)^8271*100000000000000^6223 ≤ 12838640240547^6223*500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106716247 500000000 12838640240547 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656142427/5000000000 : ℝ), (5393907131/10000000000 : ℝ), (-106716247/500000000 : ℝ)] ![(43139089646847/100000000000000 : ℝ), (44022270095067/100000000000000 : ℝ), (12838640240547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656142427/5000000000 : ℝ)|^8271 ≤ (43139089646847/100000000000000 : ℝ)^6223
        have hw : |(2656142427/5000000000 : ℝ)|=(2656142427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393907131/10000000000 : ℝ)|^8271 ≤ (44022270095067/100000000000000 : ℝ)^6223
        have hw : |(5393907131/10000000000 : ℝ)|=(5393907131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106716247/500000000 : ℝ)|^8271 ≤ (12838640240547/100000000000000 : ℝ)^6223
        have hw : |(-106716247/500000000 : ℝ)|=(106716247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s7_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273360927/625000000 : ℝ)*x 0 + (1125586319/2500000000 : ℝ)*x 1 + (2124466269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273360927/625000000 : ℝ)^8271 ≤ (6663334992719/20000000000000 : ℝ)^6223 := by
    have hnat : (273360927 : ℕ)^8271*20000000000000^6223 ≤ 6663334992719^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273360927 625000000 6663334992719 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125586319/2500000000 : ℝ)^8271 ≤ (34624611516953/100000000000000 : ℝ)^6223 := by
    have hnat : (1125586319 : ℕ)^8271*100000000000000^6223 ≤ 34624611516953^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125586319 2500000000 34624611516953 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124466269/5000000000 : ℝ)^8271 ≤ (16029356753809/50000000000000 : ℝ)^6223 := by
    have hnat : (2124466269 : ℕ)^8271*50000000000000^6223 ≤ 16029356753809^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124466269 5000000000 16029356753809 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273360927/625000000 : ℝ), (1125586319/2500000000 : ℝ), (2124466269/5000000000 : ℝ)] ![(6663334992719/20000000000000 : ℝ), (34624611516953/100000000000000 : ℝ), (16029356753809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273360927/625000000 : ℝ)|^8271 ≤ (6663334992719/20000000000000 : ℝ)^6223
        have hw : |(273360927/625000000 : ℝ)|=(273360927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125586319/2500000000 : ℝ)|^8271 ≤ (34624611516953/100000000000000 : ℝ)^6223
        have hw : |(1125586319/2500000000 : ℝ)|=(1125586319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124466269/5000000000 : ℝ)|^8271 ≤ (16029356753809/50000000000000 : ℝ)^6223
        have hw : |(2124466269/5000000000 : ℝ)|=(2124466269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3503/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (738810759631303/5000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^4135 ≤ (738810759631303/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11257 : ℕ)^4135*5000000000000000000^1024 ≤ 738810759631303^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 738810759631303 5000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (738810759631303/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14021/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (35860821581141301/100000000000000000000 : ℝ) := by
    have hpowers : (14021/100000 : ℝ)^4135 ≤ (35860821581141301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14021 : ℕ)^4135*100000000000000000000^1024 ≤ 35860821581141301^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14021 100000 35860821581141301 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14021/100000 : ℝ)) (X := (35860821581141301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500738810759631303/2500000000000000000 : ℝ) ≤ (10000731761187483/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (2500738810759631303/2500000000000000000 : ℝ)^1024 ≤ (10000731761187483/10000000000000000 : ℝ)^4135 := by
      have hnat : (2500738810759631303 : ℕ)^1024*10000000000000000^4135 ≤ 10000731761187483^4135*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500738810759631303 2500000000000000000 10000731761187483 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000731761187483/10000000000000000 : ℝ)) (X := (2500738810759631303/2500000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050637036773767361/100000000000000000000 : ℝ) ≤ (2500313436828543/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (100050637036773767361/100000000000000000000 : ℝ)^1024 ≤ (2500313436828543/2500000000000000 : ℝ)^4135 := by
      have hnat : (100050637036773767361 : ℕ)^1024*2500000000000000^4135 ≤ 2500313436828543^4135*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050637036773767361 100000000000000000000 2500313436828543 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500313436828543/2500000000000000 : ℝ)) (X := (100050637036773767361/100000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035860821581141301/50000000000000000000 : ℝ) ≤ (10001775733440861/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50035860821581141301/50000000000000000000 : ℝ)^1024 ≤ (10001775733440861/10000000000000000 : ℝ)^4135 := by
      have hnat : (50035860821581141301 : ℕ)^1024*10000000000000000^4135 ≤ 10001775733440861^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035860821581141301 50000000000000000000 10001775733440861 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001775733440861/10000000000000000 : ℝ)) (X := (50035860821581141301/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(738810759631303/5000000000000000000 : ℝ) ≤ ((13815135296132963433/13820000000000000000 : ℝ)+2*(521986126689/276400000000000 : ℝ)*(11257/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (13815135296132963433/13820000000000000000 : ℝ)+2*(521986126689/276400000000000 : ℝ)*(11257/100000 : ℝ)=(10000731761187483/10000000000000000 : ℝ) by norm_num, show 1+2*(738810759631303/5000000000000000000 : ℝ)=(2500738810759631303/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35860821581141301/100000000000000000000 : ℝ)+(738810759631303/5000000000000000000 : ℝ) ≤ ((13815135296132963433/13820000000000000000 : ℝ)+(521986126689/276400000000000 : ℝ)*((14021/100000 : ℝ)+(11257/100000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (13815135296132963433/13820000000000000000 : ℝ)+(521986126689/276400000000000 : ℝ)*((14021/100000 : ℝ)+(11257/100000 : ℝ))=(2500313436828543/2500000000000000 : ℝ) by norm_num, show 1+(35860821581141301/100000000000000000000 : ℝ)+(738810759631303/5000000000000000000 : ℝ)=(100050637036773767361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35860821581141301/100000000000000000000 : ℝ) ≤ ((13815135296132963433/13820000000000000000 : ℝ)+2*(521986126689/276400000000000 : ℝ)*(14021/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (13815135296132963433/13820000000000000000 : ℝ)+2*(521986126689/276400000000000 : ℝ)*(14021/100000 : ℝ)=(10001775733440861/10000000000000000 : ℝ) by norm_num, show 1+2*(35860821581141301/100000000000000000000 : ℝ)=(50035860821581141301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13815135296132963433/13820000000000000000 : ℝ)*(X 1 0+X 2 0)+(521986126689/276400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (13815135296132963433/13820000000000000000 : ℝ)) (alpha := (521986126689/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13815135296132963433/13820000000000000000 : ℝ)*(X 0 1+X 2 1)+(521986126689/276400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (13815135296132963433/13820000000000000000 : ℝ)) (alpha := (521986126689/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13815135296132963433/13820000000000000000 : ℝ)*(X 0 2+X 1 2)+(521986126689/276400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (13815135296132963433/13820000000000000000 : ℝ)) (alpha := (521986126689/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2197868069/10000000000 : ℝ)*X 0 0+(1348558393/2500000000 : ℝ)*X 0 1+(5264587809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344970999/10000000000 : ℝ)*X 1 0+(-2263644267/10000000000 : ℝ)*X 1 1+(1052917573/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344971041/10000000000 : ℝ)*X 2 0+(5264587833/10000000000 : ℝ)*X 2 1+(-1131822127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186882499/5000000000 : ℝ)*X 0 0+(4248291119/10000000000 : ℝ)*X 0 1+(1125746073/2500000000 : ℝ)*X 0 2+(2186882499/5000000000 : ℝ)*X 1 0+(4248291119/10000000000 : ℝ)*X 1 1+(1125746073/2500000000 : ℝ)*X 1 2+(2186882499/5000000000 : ℝ)*X 2 0+(4248291119/10000000000 : ℝ)*X 2 1+(1125746073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2197873089/10000000000 : ℝ)*X 0 0+(52649131/100000000 : ℝ)*X 0 1+(5393907133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328071213/2500000000 : ℝ)*X 1 0+(-2134324941/10000000000 : ℝ)*X 1 1+(5393907133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656142427/5000000000 : ℝ)*X 2 0+(5393907131/10000000000 : ℝ)*X 2 1+(-106716247/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273360927/625000000 : ℝ)*X 0 0+(1125586319/2500000000 : ℝ)*X 0 1+(2124466269/5000000000 : ℝ)*X 0 2+(273360927/625000000 : ℝ)*X 1 0+(1125586319/2500000000 : ℝ)*X 1 1+(2124466269/5000000000 : ℝ)*X 1 2+(273360927/625000000 : ℝ)*X 2 0+(1125586319/2500000000 : ℝ)*X 2 1+(2124466269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2742248497068488015099658117/345500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1596900717/100000000000000 : ℝ)*(base19) + (1524718567/100000000000000 : ℝ)*(base23) + (35488743/50000000000000 : ℝ)*(lower2) + (22556691/10000000000000 : ℝ)*(upper3) + (159055033/100000000000000 : ℝ)*(upper5) + (5819877464228217/100000000000000 : ℝ)*(major0) + (5819877464228217/100000000000000 : ℝ)*(major1) + (5819877464228217/100000000000000 : ℝ)*(major2) + (3856685236633521/50000000000000 : ℝ)*(sp0) + (7713413249202459/100000000000000 : ℝ)*(sp1) + (241044166293269/3125000000000 : ℝ)*(sp2) + (1963157560614289/50000000000000 : ℝ)*(sp3) + (22186418067/50000000000000 : ℝ)*(sp4) + (4939311311/20000000000000 : ℝ)*(sp7) + (3926339817785133/100000000000000 : ℝ)*(f.failure) + (964176855762897/12500000000000 : ℝ)*(f.sum) + (56595985883913/13820000000000000000000000000 : ℝ)*base65 + (2845472642151438961/1382000000000000000000000000000000 : ℝ)*base67 + (4260439174191438961/1382000000000000000000000000000000 : ℝ)*base69 + (13061699293213438961/1382000000000000000000000000000000 : ℝ)*base71 + (70959485668867/13820000000000000000000000000 : ℝ)*base74 + (14981822099421438961/1382000000000000000000000000000000 : ℝ)*base75 + (23359464458379438961/1382000000000000000000000000000000 : ℝ)*base77 + (15760096283128561039/1382000000000000000000000000000000 : ℝ)*base80 + (151517793124367/13820000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12179169/2000000000000000000000 : ℝ)*base90 + (12179169/2000000000000000000000 : ℝ)*base92 + (12179169/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1300918445756615883322245141/345500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343766697/50000000000000 : ℝ)*(base19) + (755517863/100000000000000 : ℝ)*(base23) + (18592051/25000000000000 : ℝ)*(upper3) + (1840631/6250000000000 : ℝ)*(lower4) + (18959221/25000000000000 : ℝ)*(upper5) + (2924606842089147/50000000000000 : ℝ)*(major0) + (2924606842089147/50000000000000 : ℝ)*(major1) + (2924606842089147/50000000000000 : ℝ)*(major2) + (18737815777/100000000000000 : ℝ)*(sp1) + (20302592059/100000000000000 : ℝ)*(sp2) + (7752295948487347/100000000000000 : ℝ)*(sp4) + (310091060925527/4000000000000 : ℝ)*(sp5) + (484517180648589/6250000000000 : ℝ)*(sp6) + (1973065647179263/50000000000000 : ℝ)*(sp7) + (1973065647179263/50000000000000 : ℝ)*(f.failure) + (7752295948487347/100000000000000 : ℝ)*(f.sum) + (49771344848693/6910000000000000000000000000 : ℝ)*base65 + (5886565577775311651/691000000000000000000000000000000 : ℝ)*base67 + (4538496260042311651/691000000000000000000000000000000 : ℝ)*base69 + (7775811348186311651/691000000000000000000000000000000 : ℝ)*base71 + (22171341345937/6910000000000000000000000000 : ℝ)*base74 + (7072184419803311651/691000000000000000000000000000000 : ℝ)*base75 + (4165182122514311651/691000000000000000000000000000000 : ℝ)*base77 + (9780846030994311651/691000000000000000000000000000000 : ℝ)*base79 + (16144018540063/6910000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4331259/1000000000000000000000 : ℝ)*base90 + (4331259/1000000000000000000000 : ℝ)*base92 + (4331259/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1078_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s8_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-439574991/2000000000 : ℝ)*x 0 + (5394138831/10000000000 : ℝ)*x 1 + (5264678147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439574991/2000000000 : ℝ)^8271 ≤ (834324596271/6250000000000 : ℝ)^6223 := by
    have hnat : (439574991 : ℕ)^8271*6250000000000^6223 ≤ 834324596271^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439574991 2000000000 834324596271 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394138831/10000000000 : ℝ)^8271 ≤ (4402478346429/10000000000000 : ℝ)^6223 := by
    have hnat : (5394138831 : ℕ)^8271*10000000000000^6223 ≤ 4402478346429^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394138831 10000000000 4402478346429 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264678147/10000000000 : ℝ)^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223 := by
    have hnat : (5264678147 : ℕ)^8271*12500000000000^6223 ≤ 5328252873853^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264678147 10000000000 5328252873853 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439574991/2000000000 : ℝ), (5394138831/10000000000 : ℝ), (5264678147/10000000000 : ℝ)] ![(834324596271/6250000000000 : ℝ), (4402478346429/10000000000000 : ℝ), (5328252873853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439574991/2000000000 : ℝ)|^8271 ≤ (834324596271/6250000000000 : ℝ)^6223
        have hw : |(-439574991/2000000000 : ℝ)|=(439574991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394138831/10000000000 : ℝ)|^8271 ≤ (4402478346429/10000000000000 : ℝ)^6223
        have hw : |(5394138831/10000000000 : ℝ)|=(5394138831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264678147/10000000000 : ℝ)|^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223
        have hw : |(5264678147/10000000000 : ℝ)|=(5264678147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66811847/125000000 : ℝ)*x 0 + (-226355591/1000000000 : ℝ)*x 1 + (5264678147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66811847/125000000 : ℝ)^8271 ≤ (1359124411811/3125000000000 : ℝ)^6223 := by
    have hnat : (66811847 : ℕ)^8271*3125000000000^6223 ≤ 1359124411811^6223*125000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66811847 125000000 1359124411811 3125000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226355591/1000000000 : ℝ)^8271 ≤ (1388199581627/10000000000000 : ℝ)^6223 := by
    have hnat : (226355591 : ℕ)^8271*10000000000000^6223 ≤ 1388199581627^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226355591 1000000000 1388199581627 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264678147/10000000000 : ℝ)^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223 := by
    have hnat : (5264678147 : ℕ)^8271*12500000000000^6223 ≤ 5328252873853^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264678147 10000000000 5328252873853 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66811847/125000000 : ℝ), (-226355591/1000000000 : ℝ), (5264678147/10000000000 : ℝ)] ![(1359124411811/3125000000000 : ℝ), (1388199581627/10000000000000 : ℝ), (5328252873853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66811847/125000000 : ℝ)|^8271 ≤ (1359124411811/3125000000000 : ℝ)^6223
        have hw : |(66811847/125000000 : ℝ)|=(66811847/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226355591/1000000000 : ℝ)|^8271 ≤ (1388199581627/10000000000000 : ℝ)^6223
        have hw : |(-226355591/1000000000 : ℝ)|=(226355591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264678147/10000000000 : ℝ)|^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223
        have hw : |(5264678147/10000000000 : ℝ)|=(5264678147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66811847/125000000 : ℝ)*x 0 + (5264678147/10000000000 : ℝ)*x 1 + (-226355591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66811847/125000000 : ℝ)^8271 ≤ (1359124411811/3125000000000 : ℝ)^6223 := by
    have hnat : (66811847 : ℕ)^8271*3125000000000^6223 ≤ 1359124411811^6223*125000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66811847 125000000 1359124411811 3125000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264678147/10000000000 : ℝ)^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223 := by
    have hnat : (5264678147 : ℕ)^8271*12500000000000^6223 ≤ 5328252873853^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264678147 10000000000 5328252873853 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226355591/1000000000 : ℝ)^8271 ≤ (1388199581627/10000000000000 : ℝ)^6223 := by
    have hnat : (226355591 : ℕ)^8271*10000000000000^6223 ≤ 1388199581627^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226355591 1000000000 1388199581627 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66811847/125000000 : ℝ), (5264678147/10000000000 : ℝ), (-226355591/1000000000 : ℝ)] ![(1359124411811/3125000000000 : ℝ), (5328252873853/12500000000000 : ℝ), (1388199581627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66811847/125000000 : ℝ)|^8271 ≤ (1359124411811/3125000000000 : ℝ)^6223
        have hw : |(66811847/125000000 : ℝ)|=(66811847/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264678147/10000000000 : ℝ)|^8271 ≤ (5328252873853/12500000000000 : ℝ)^6223
        have hw : |(5264678147/10000000000 : ℝ)|=(5264678147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226355591/1000000000 : ℝ)|^8271 ≤ (1388199581627/10000000000000 : ℝ)^6223
        have hw : |(-226355591/1000000000 : ℝ)|=(226355591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546721203/1250000000 : ℝ)*x 0 + (424847239/1000000000 : ℝ)*x 1 + (2251400939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546721203/1250000000 : ℝ)^8271 ≤ (832915555911/2500000000000 : ℝ)^6223 := by
    have hnat : (546721203 : ℕ)^8271*2500000000000^6223 ≤ 832915555911^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546721203 1250000000 832915555911 2500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424847239/1000000000 : ℝ)^8271 ≤ (32054099117871/100000000000000 : ℝ)^6223 := by
    have hnat : (424847239 : ℕ)^8271*100000000000000^6223 ≤ 32054099117871^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424847239 1000000000 32054099117871 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251400939/5000000000 : ℝ)^8271 ≤ (865731966037/2500000000000 : ℝ)^6223 := by
    have hnat : (2251400939 : ℕ)^8271*2500000000000^6223 ≤ 865731966037^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251400939 5000000000 865731966037 2500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546721203/1250000000 : ℝ), (424847239/1000000000 : ℝ), (2251400939/5000000000 : ℝ)] ![(832915555911/2500000000000 : ℝ), (32054099117871/100000000000000 : ℝ), (865731966037/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546721203/1250000000 : ℝ)|^8271 ≤ (832915555911/2500000000000 : ℝ)^6223
        have hw : |(546721203/1250000000 : ℝ)|=(546721203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424847239/1000000000 : ℝ)|^8271 ≤ (32054099117871/100000000000000 : ℝ)^6223
        have hw : |(424847239/1000000000 : ℝ)|=(424847239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251400939/5000000000 : ℝ)|^8271 ≤ (865731966037/2500000000000 : ℝ)^6223
        have hw : |(2251400939/5000000000 : ℝ)|=(2251400939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197880031/10000000000 : ℝ)*x 0 + (105300047/200000000 : ℝ)*x 1 + (337113339/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197880031/10000000000 : ℝ)^8271 ≤ (1334923451657/10000000000000 : ℝ)^6223 := by
    have hnat : (2197880031 : ℕ)^8271*10000000000000^6223 ≤ 1334923451657^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197880031 10000000000 1334923451657 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105300047/200000000 : ℝ)^8271 ≤ (21314755921781/50000000000000 : ℝ)^6223 := by
    have hnat : (105300047 : ℕ)^8271*50000000000000^6223 ≤ 21314755921781^6223*200000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105300047 200000000 21314755921781 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337113339/625000000 : ℝ)^8271 ≤ (44021253617071/100000000000000 : ℝ)^6223 := by
    have hnat : (337113339 : ℕ)^8271*100000000000000^6223 ≤ 44021253617071^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337113339 625000000 44021253617071 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197880031/10000000000 : ℝ), (105300047/200000000 : ℝ), (337113339/625000000 : ℝ)] ![(1334923451657/10000000000000 : ℝ), (21314755921781/50000000000000 : ℝ), (44021253617071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197880031/10000000000 : ℝ)|^8271 ≤ (1334923451657/10000000000000 : ℝ)^6223
        have hw : |(-2197880031/10000000000 : ℝ)|=(2197880031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105300047/200000000 : ℝ)|^8271 ≤ (21314755921781/50000000000000 : ℝ)^6223
        have hw : |(105300047/200000000 : ℝ)|=(105300047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337113339/625000000 : ℝ)|^8271 ≤ (44021253617071/100000000000000 : ℝ)^6223
        have hw : |(337113339/625000000 : ℝ)|=(337113339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062461721/2000000000 : ℝ)*x 0 + (-1067209839/5000000000 : ℝ)*x 1 + (5393813673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062461721/2000000000 : ℝ)^8271 ≤ (21569672997461/50000000000000 : ℝ)^6223 := by
    have hnat : (1062461721 : ℕ)^8271*50000000000000^6223 ≤ 21569672997461^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062461721 2000000000 21569672997461 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067209839/5000000000 : ℝ)^8271 ≤ (12839397673323/100000000000000 : ℝ)^6223 := by
    have hnat : (1067209839 : ℕ)^8271*100000000000000^6223 ≤ 12839397673323^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067209839 5000000000 12839397673323 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393813673/10000000000 : ℝ)^8271 ≤ (44021256318067/100000000000000 : ℝ)^6223 := by
    have hnat : (5393813673 : ℕ)^8271*100000000000000^6223 ≤ 44021256318067^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393813673 10000000000 44021256318067 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062461721/2000000000 : ℝ), (-1067209839/5000000000 : ℝ), (5393813673/10000000000 : ℝ)] ![(21569672997461/50000000000000 : ℝ), (12839397673323/100000000000000 : ℝ), (44021256318067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062461721/2000000000 : ℝ)|^8271 ≤ (21569672997461/50000000000000 : ℝ)^6223
        have hw : |(1062461721/2000000000 : ℝ)|=(1062461721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067209839/5000000000 : ℝ)|^8271 ≤ (12839397673323/100000000000000 : ℝ)^6223
        have hw : |(-1067209839/5000000000 : ℝ)|=(1067209839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393813673/10000000000 : ℝ)|^8271 ≤ (44021256318067/100000000000000 : ℝ)^6223
        have hw : |(5393813673/10000000000 : ℝ)|=(5393813673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656153603/5000000000 : ℝ)*x 0 + (2696906799/5000000000 : ℝ)*x 1 + (-533605417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656153603/5000000000 : ℝ)^8271 ≤ (674052045239/1562500000000 : ℝ)^6223 := by
    have hnat : (2656153603 : ℕ)^8271*1562500000000^6223 ≤ 674052045239^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656153603 5000000000 674052045239 1562500000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696906799/5000000000 : ℝ)^8271 ≤ (22010627752257/50000000000000 : ℝ)^6223 := by
    have hnat : (2696906799 : ℕ)^8271*50000000000000^6223 ≤ 22010627752257^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696906799 5000000000 22010627752257 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533605417/2500000000 : ℝ)^8271 ≤ (12839413583543/100000000000000 : ℝ)^6223 := by
    have hnat : (533605417 : ℕ)^8271*100000000000000^6223 ≤ 12839413583543^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533605417 2500000000 12839413583543 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656153603/5000000000 : ℝ), (2696906799/5000000000 : ℝ), (-533605417/2500000000 : ℝ)] ![(674052045239/1562500000000 : ℝ), (22010627752257/50000000000000 : ℝ), (12839413583543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656153603/5000000000 : ℝ)|^8271 ≤ (674052045239/1562500000000 : ℝ)^6223
        have hw : |(2656153603/5000000000 : ℝ)|=(2656153603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696906799/5000000000 : ℝ)|^8271 ≤ (22010627752257/50000000000000 : ℝ)^6223
        have hw : |(2696906799/5000000000 : ℝ)|=(2696906799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533605417/2500000000 : ℝ)|^8271 ≤ (12839413583543/100000000000000 : ℝ)^6223
        have hw : |(-533605417/2500000000 : ℝ)|=(533605417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s8_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373778439/10000000000 : ℝ)*x 0 + (4502164761/10000000000 : ℝ)*x 1 + (2124556441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373778439/10000000000 : ℝ)^8271 ≤ (1665835574091/5000000000000 : ℝ)^6223 := by
    have hnat : (4373778439 : ℕ)^8271*5000000000000^6223 ≤ 1665835574091^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373778439 10000000000 1665835574091 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502164761/10000000000 : ℝ)^8271 ≤ (34622766438817/100000000000000 : ℝ)^6223 := by
    have hnat : (4502164761 : ℕ)^8271*100000000000000^6223 ≤ 34622766438817^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502164761 10000000000 34622766438817 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124556441/5000000000 : ℝ)^8271 ≤ (16030261026073/50000000000000 : ℝ)^6223 := by
    have hnat : (2124556441 : ℕ)^8271*50000000000000^6223 ≤ 16030261026073^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124556441 5000000000 16030261026073 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373778439/10000000000 : ℝ), (4502164761/10000000000 : ℝ), (2124556441/5000000000 : ℝ)] ![(1665835574091/5000000000000 : ℝ), (34622766438817/100000000000000 : ℝ), (16030261026073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373778439/10000000000 : ℝ)|^8271 ≤ (1665835574091/5000000000000 : ℝ)^6223
        have hw : |(4373778439/10000000000 : ℝ)|=(4373778439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502164761/10000000000 : ℝ)|^8271 ≤ (34622766438817/100000000000000 : ℝ)^6223
        have hw : |(4502164761/10000000000 : ℝ)|=(4502164761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124556441/5000000000 : ℝ)|^8271 ≤ (16030261026073/50000000000000 : ℝ)^6223
        have hw : |(2124556441/5000000000 : ℝ)|=(2124556441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2817/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (5633/50000 : ℝ) ^ (4135/1024 : ℝ) ≤ (14823977578774623/100000000000000000000 : ℝ) := by
    have hpowers : (5633/50000 : ℝ)^4135 ≤ (14823977578774623/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5633 : ℕ)^4135*100000000000000000000^1024 ≤ 14823977578774623^1024*50000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5633 50000 14823977578774623 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5633/50000 : ℝ)) (X := (14823977578774623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3503/25000 : ℝ) ^ (4135/1024 : ℝ) ≤ (2235497503323247/6250000000000000000 : ℝ) := by
    have hpowers : (3503/25000 : ℝ)^4135 ≤ (2235497503323247/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3503 : ℕ)^4135*6250000000000000000^1024 ≤ 2235497503323247^1024*25000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3503 25000 2235497503323247 6250000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3503/25000 : ℝ)) (X := (2235497503323247/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014823977578774623/50000000000000000000 : ℝ) ≤ (2500183531564033/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50014823977578774623/50000000000000000000 : ℝ)^1024 ≤ (2500183531564033/2500000000000000 : ℝ)^4135 := by
      have hnat : (50014823977578774623 : ℕ)^1024*2500000000000000^4135 ≤ 2500183531564033^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014823977578774623 50000000000000000000 2500183531564033 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500183531564033/2500000000000000 : ℝ)) (X := (50014823977578774623/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002023677505277863/4000000000000000000 : ℝ) ≤ (312539144715461/312500000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (4002023677505277863/4000000000000000000 : ℝ)^1024 ≤ (312539144715461/312500000000000 : ℝ)^4135 := by
      have hnat : (4002023677505277863 : ℕ)^1024*312500000000000^4135 ≤ 312539144715461^4135*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002023677505277863 4000000000000000000 312539144715461 312500000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312539144715461/312500000000000 : ℝ)) (X := (4002023677505277863/4000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127235497503323247/3125000000000000000 : ℝ) ≤ (2500442783883343/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (3127235497503323247/3125000000000000000 : ℝ)^1024 ≤ (2500442783883343/2500000000000000 : ℝ)^4135 := by
      have hnat : (3127235497503323247 : ℕ)^1024*2500000000000000^4135 ≤ 2500442783883343^4135*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127235497503323247 3125000000000000000 2500442783883343 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500442783883343/2500000000000000 : ℝ)) (X := (3127235497503323247/3125000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14823977578774623/100000000000000000000 : ℝ) ≤ ((3431291620522744079/3432500000000000000 : ℝ)+2*(25925231931/13730000000000 : ℝ)*(5633/50000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (3431291620522744079/3432500000000000000 : ℝ)+2*(25925231931/13730000000000 : ℝ)*(5633/50000 : ℝ)=(2500183531564033/2500000000000000 : ℝ) by norm_num, show 1+2*(14823977578774623/100000000000000000000 : ℝ)=(50014823977578774623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2235497503323247/6250000000000000000 : ℝ)+(14823977578774623/100000000000000000000 : ℝ) ≤ ((3431291620522744079/3432500000000000000 : ℝ)+(25925231931/13730000000000 : ℝ)*((3503/25000 : ℝ)+(5633/50000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (3431291620522744079/3432500000000000000 : ℝ)+(25925231931/13730000000000 : ℝ)*((3503/25000 : ℝ)+(5633/50000 : ℝ))=(312539144715461/312500000000000 : ℝ) by norm_num, show 1+(2235497503323247/6250000000000000000 : ℝ)+(14823977578774623/100000000000000000000 : ℝ)=(4002023677505277863/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2235497503323247/6250000000000000000 : ℝ) ≤ ((3431291620522744079/3432500000000000000 : ℝ)+2*(25925231931/13730000000000 : ℝ)*(3503/25000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (3431291620522744079/3432500000000000000 : ℝ)+2*(25925231931/13730000000000 : ℝ)*(3503/25000 : ℝ)=(2500442783883343/2500000000000000 : ℝ) by norm_num, show 1+2*(2235497503323247/6250000000000000000 : ℝ)=(3127235497503323247/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3431291620522744079/3432500000000000000 : ℝ)*(X 1 0+X 2 0)+(25925231931/13730000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3431291620522744079/3432500000000000000 : ℝ)) (alpha := (25925231931/13730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3431291620522744079/3432500000000000000 : ℝ)*(X 0 1+X 2 1)+(25925231931/13730000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3431291620522744079/3432500000000000000 : ℝ)) (alpha := (25925231931/13730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3431291620522744079/3432500000000000000 : ℝ)*(X 0 2+X 1 2)+(25925231931/13730000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (3431291620522744079/3432500000000000000 : ℝ)) (alpha := (25925231931/13730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-439574991/2000000000 : ℝ)*X 0 0+(5394138831/10000000000 : ℝ)*X 0 1+(5264678147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66811847/125000000 : ℝ)*X 1 0+(-226355591/1000000000 : ℝ)*X 1 1+(5264678147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66811847/125000000 : ℝ)*X 2 0+(5264678147/10000000000 : ℝ)*X 2 1+(-226355591/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546721203/1250000000 : ℝ)*X 0 0+(424847239/1000000000 : ℝ)*X 0 1+(2251400939/5000000000 : ℝ)*X 0 2+(546721203/1250000000 : ℝ)*X 1 0+(424847239/1000000000 : ℝ)*X 1 1+(2251400939/5000000000 : ℝ)*X 1 2+(546721203/1250000000 : ℝ)*X 2 0+(424847239/1000000000 : ℝ)*X 2 1+(2251400939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2197880031/10000000000 : ℝ)*X 0 0+(105300047/200000000 : ℝ)*X 0 1+(337113339/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062461721/2000000000 : ℝ)*X 1 0+(-1067209839/5000000000 : ℝ)*X 1 1+(5393813673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656153603/5000000000 : ℝ)*X 2 0+(2696906799/5000000000 : ℝ)*X 2 1+(-533605417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373778439/10000000000 : ℝ)*X 0 0+(4502164761/10000000000 : ℝ)*X 0 1+(2124556441/5000000000 : ℝ)*X 0 2+(4373778439/10000000000 : ℝ)*X 1 0+(4502164761/10000000000 : ℝ)*X 1 1+(2124556441/5000000000 : ℝ)*X 1 2+(4373778439/10000000000 : ℝ)*X 2 0+(4502164761/10000000000 : ℝ)*X 2 1+(2124556441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1252806569680313358136508529/171625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1461756051/100000000000000 : ℝ)*(base19) + (68068223/5000000000000 : ℝ)*(base23) + (53658781/100000000000000 : ℝ)*(lower2) + (46160293/25000000000000 : ℝ)*(upper3) + (54979533/50000000000000 : ℝ)*(upper5) + (5828191045466517/100000000000000 : ℝ)*(major0) + (5828191045466517/100000000000000 : ℝ)*(major1) + (5828191045466517/100000000000000 : ℝ)*(major2) + (1544878805314953/20000000000000 : ℝ)*(sp0) + (1931107967089909/25000000000000 : ℝ)*(sp1) + (7724431968751227/100000000000000 : ℝ)*(sp2) + (1965963445504553/50000000000000 : ℝ)*(sp3) + (19651770461/50000000000000 : ℝ)*(sp4) + (10813242883/50000000000000 : ℝ)*(sp7) + (491493564686859/12500000000000 : ℝ)*(f.failure) + (7724433330115687/100000000000000 : ℝ)*(f.sum) + (7176839837699/1373000000000000000000000000 : ℝ)*base66 + (1778864563133002843/343250000000000000000000000000000 : ℝ)*base67 + (2587700791511502843/343250000000000000000000000000000 : ℝ)*base69 + (1842618279412247157/343250000000000000000000000000000 : ℝ)*base72 + (1533981921021/343250000000000000000000000 : ℝ)*base74 + (162410351152747157/343250000000000000000000000000000 : ℝ)*base76 + (1649810003832247157/343250000000000000000000000000000 : ℝ)*base78 + (1037148123577497157/343250000000000000000000000000000 : ℝ)*base80 + (328310371461/85812500000000000000000000 : ℝ)*base82 + (1420713/250000000000000000000 : ℝ)*base89 + (1420713/250000000000000000000 : ℝ)*base91 + (1420713/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (232707922957641761452585773/42906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137456603/100000000000000 : ℝ)*(base8) + (63385101/25000000000000 : ℝ)*(upper1) + (915949809/100000000000000 : ℝ)*(upper2) + (14221343/50000000000000 : ℝ)*(upper3) + (195717931/50000000000000 : ℝ)*(lower4) + (2928766255663021/50000000000000 : ℝ)*(major0) + (2928766255663021/50000000000000 : ℝ)*(major1) + (2928766255663021/50000000000000 : ℝ)*(major2) + (5931871957/20000000000000 : ℝ)*(sp0) + (67801087437/100000000000000 : ℝ)*(sp1) + (7763291511863237/100000000000000 : ℝ)*(sp4) + (1940813376898047/25000000000000 : ℝ)*(sp5) + (62106570469437/800000000000 : ℝ)*(sp6) + (987935883296139/25000000000000 : ℝ)*(sp7) + (987935883296139/25000000000000 : ℝ)*(f.failure) + (62106570469437/800000000000 : ℝ)*(f.sum) + (5347671475039/686500000000000000000000000 : ℝ)*base65 + (777492604388127659/171625000000000000000000000000000 : ℝ)*base67 + (1137130582387877659/171625000000000000000000000000000 : ℝ)*base69 + (714728047320752659/171625000000000000000000000000000 : ℝ)*base71 + (1633120425041/686500000000000000000000000 : ℝ)*base74 + (282159062267122341/171625000000000000000000000000000 : ℝ)*base76 + (1206878371574502659/171625000000000000000000000000000 : ℝ)*base77 + (400154023832502659/171625000000000000000000000000000 : ℝ)*base79 + (767780060689/171625000000000000000000000 : ℝ)*base82 + (2569673/500000000000000000000 : ℝ)*base89 + (2569673/500000000000000000000 : ℝ)*base91 + (2569673/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1078_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1078_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1078_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1078_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:08.022476+00:00
-- url     : https://prove2.me/submissions/c96f6180-1196-4e73-bba8-06d4a11d3779

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
theorem support_rectangle_w1543_s3_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1822828299/10000000000 : ℝ)*x 0 + (2715762803/5000000000 : ℝ)*x 1 + (208679483/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822828299/10000000000 : ℝ)^4583 ≤ (5584915395487/50000000000000 : ℝ)^3559 := by
    have hnat : (1822828299 : ℕ)^4583*50000000000000^3559 ≤ 5584915395487^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822828299 10000000000 5584915395487 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715762803/5000000000 : ℝ)^4583 ≤ (9113458066087/20000000000000 : ℝ)^3559 := by
    have hnat : (2715762803 : ℕ)^4583*20000000000000^3559 ≤ 9113458066087^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715762803 5000000000 9113458066087 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208679483/400000000 : ℝ)^4583 ≤ (2703929928413/6250000000000 : ℝ)^3559 := by
    have hnat : (208679483 : ℕ)^4583*6250000000000^3559 ≤ 2703929928413^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208679483 400000000 2703929928413 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1822828299/10000000000 : ℝ), (2715762803/5000000000 : ℝ), (208679483/400000000 : ℝ)] ![(5584915395487/50000000000000 : ℝ), (9113458066087/20000000000000 : ℝ), (2703929928413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1822828299/10000000000 : ℝ)|^4583 ≤ (5584915395487/50000000000000 : ℝ)^3559
        have hw : |(-1822828299/10000000000 : ℝ)|=(1822828299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715762803/5000000000 : ℝ)|^4583 ≤ (9113458066087/20000000000000 : ℝ)^3559
        have hw : |(2715762803/5000000000 : ℝ)|=(2715762803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208679483/400000000 : ℝ)|^4583 ≤ (2703929928413/6250000000000 : ℝ)^3559
        have hw : |(208679483/400000000 : ℝ)|=(208679483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675209821/5000000000 : ℝ)*x 0 + (-1932690327/10000000000 : ℝ)*x 1 + (5216987303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675209821/5000000000 : ℝ)^4583 ≤ (8938594737583/20000000000000 : ℝ)^3559 := by
    have hnat : (2675209821 : ℕ)^4583*20000000000000^3559 ≤ 8938594737583^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675209821 5000000000 8938594737583 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932690327/10000000000 : ℝ)^4583 ≤ (3011036252007/25000000000000 : ℝ)^3559 := by
    have hnat : (1932690327 : ℕ)^4583*25000000000000^3559 ≤ 3011036252007^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932690327 10000000000 3011036252007 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216987303/10000000000 : ℝ)^4583 ≤ (43262881289347/100000000000000 : ℝ)^3559 := by
    have hnat : (5216987303 : ℕ)^4583*100000000000000^3559 ≤ 43262881289347^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216987303 10000000000 43262881289347 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675209821/5000000000 : ℝ), (-1932690327/10000000000 : ℝ), (5216987303/10000000000 : ℝ)] ![(8938594737583/20000000000000 : ℝ), (3011036252007/25000000000000 : ℝ), (43262881289347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675209821/5000000000 : ℝ)|^4583 ≤ (8938594737583/20000000000000 : ℝ)^3559
        have hw : |(2675209821/5000000000 : ℝ)|=(2675209821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1932690327/10000000000 : ℝ)|^4583 ≤ (3011036252007/25000000000000 : ℝ)^3559
        have hw : |(-1932690327/10000000000 : ℝ)|=(1932690327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216987303/10000000000 : ℝ)|^4583 ≤ (43262881289347/100000000000000 : ℝ)^3559
        have hw : |(5216987303/10000000000 : ℝ)|=(5216987303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350419273/10000000000 : ℝ)*x 0 + (81515429/156250000 : ℝ)*x 1 + (-1932690619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350419273/10000000000 : ℝ)^4583 ≤ (22346484859373/50000000000000 : ℝ)^3559 := by
    have hnat : (5350419273 : ℕ)^4583*50000000000000^3559 ≤ 22346484859373^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350419273 10000000000 22346484859373 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81515429/156250000 : ℝ)^4583 ≤ (2703930182699/6250000000000 : ℝ)^3559 := by
    have hnat : (81515429 : ℕ)^4583*6250000000000^3559 ≤ 2703930182699^3559*156250000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81515429 156250000 2703930182699 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932690619/10000000000 : ℝ)^4583 ≤ (12044147351277/100000000000000 : ℝ)^3559 := by
    have hnat : (1932690619 : ℕ)^4583*100000000000000^3559 ≤ 12044147351277^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932690619 10000000000 12044147351277 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350419273/10000000000 : ℝ), (81515429/156250000 : ℝ), (-1932690619/10000000000 : ℝ)] ![(22346484859373/50000000000000 : ℝ), (2703930182699/6250000000000 : ℝ), (12044147351277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350419273/10000000000 : ℝ)|^4583 ≤ (22346484859373/50000000000000 : ℝ)^3559
        have hw : |(5350419273/10000000000 : ℝ)|=(5350419273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81515429/156250000 : ℝ)|^4583 ≤ (2703930182699/6250000000000 : ℝ)^3559
        have hw : |(81515429/156250000 : ℝ)|=(81515429/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932690619/10000000000 : ℝ)|^4583 ≤ (12044147351277/100000000000000 : ℝ)^3559
        have hw : |(-1932690619/10000000000 : ℝ)|=(1932690619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255333871/10000000000 : ℝ)*x 0 + (32102209/80000000 : ℝ)*x 1 + (1127476783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255333871/10000000000 : ℝ)^4583 ≤ (4159872013911/12500000000000 : ℝ)^3559 := by
    have hnat : (4255333871 : ℕ)^4583*12500000000000^3559 ≤ 4159872013911^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255333871 10000000000 4159872013911 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32102209/80000000 : ℝ)^4583 ≤ (30856566752683/100000000000000 : ℝ)^3559 := by
    have hnat : (32102209 : ℕ)^4583*100000000000000^3559 ≤ 30856566752683^3559*80000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32102209 80000000 30856566752683 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127476783/2500000000 : ℝ)^4583 ≤ (35864457122801/100000000000000 : ℝ)^3559 := by
    have hnat : (1127476783 : ℕ)^4583*100000000000000^3559 ≤ 35864457122801^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127476783 2500000000 35864457122801 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255333871/10000000000 : ℝ), (32102209/80000000 : ℝ), (1127476783/2500000000 : ℝ)] ![(4159872013911/12500000000000 : ℝ), (30856566752683/100000000000000 : ℝ), (35864457122801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255333871/10000000000 : ℝ)|^4583 ≤ (4159872013911/12500000000000 : ℝ)^3559
        have hw : |(4255333871/10000000000 : ℝ)|=(4255333871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32102209/80000000 : ℝ)|^4583 ≤ (30856566752683/100000000000000 : ℝ)^3559
        have hw : |(32102209/80000000 : ℝ)|=(32102209/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127476783/2500000000 : ℝ)|^4583 ≤ (35864457122801/100000000000000 : ℝ)^3559
        have hw : |(1127476783/2500000000 : ℝ)|=(1127476783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364571599/2000000000 : ℝ)*x 0 + (1304530261/2500000000 : ℝ)*x 1 + (5430382951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364571599/2000000000 : ℝ)^4583 ≤ (5585032558809/50000000000000 : ℝ)^3559 := by
    have hnat : (364571599 : ℕ)^4583*50000000000000^3559 ≤ 5585032558809^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364571599 2000000000 5585032558809 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304530261/2500000000 : ℝ)^4583 ≤ (676171695687/1562500000000 : ℝ)^3559 := by
    have hnat : (1304530261 : ℕ)^4583*1562500000000^3559 ≤ 676171695687^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304530261 2500000000 676171695687 1562500000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430382951/10000000000 : ℝ)^4583 ≤ (45554946350087/100000000000000 : ℝ)^3559 := by
    have hnat : (5430382951 : ℕ)^4583*100000000000000^3559 ≤ 45554946350087^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430382951 10000000000 45554946350087 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364571599/2000000000 : ℝ), (1304530261/2500000000 : ℝ), (5430382951/10000000000 : ℝ)] ![(5585032558809/50000000000000 : ℝ), (676171695687/1562500000000 : ℝ), (45554946350087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364571599/2000000000 : ℝ)|^4583 ≤ (5585032558809/50000000000000 : ℝ)^3559
        have hw : |(-364571599/2000000000 : ℝ)|=(364571599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304530261/2500000000 : ℝ)|^4583 ≤ (676171695687/1562500000000 : ℝ)^3559
        have hw : |(1304530261/2500000000 : ℝ)|=(1304530261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430382951/10000000000 : ℝ)|^4583 ≤ (45554946350087/100000000000000 : ℝ)^3559
        have hw : |(5430382951/10000000000 : ℝ)|=(5430382951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646925613/5000000000 : ℝ)*x 0 + (-68771793/400000000 : ℝ)*x 1 + (1086076591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646925613/5000000000 : ℝ)^4583 ≤ (44085420139237/100000000000000 : ℝ)^3559 := by
    have hnat : (2646925613 : ℕ)^4583*100000000000000^3559 ≤ 44085420139237^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646925613 5000000000 44085420139237 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68771793/400000000 : ℝ)^4583 ≤ (10359633450659/100000000000000 : ℝ)^3559 := by
    have hnat : (68771793 : ℕ)^4583*100000000000000^3559 ≤ 10359633450659^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68771793 400000000 10359633450659 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086076591/2000000000 : ℝ)^4583 ≤ (22777473196649/50000000000000 : ℝ)^3559 := by
    have hnat : (1086076591 : ℕ)^4583*50000000000000^3559 ≤ 22777473196649^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086076591 2000000000 22777473196649 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646925613/5000000000 : ℝ), (-68771793/400000000 : ℝ), (1086076591/2000000000 : ℝ)] ![(44085420139237/100000000000000 : ℝ), (10359633450659/100000000000000 : ℝ), (22777473196649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646925613/5000000000 : ℝ)|^4583 ≤ (44085420139237/100000000000000 : ℝ)^3559
        have hw : |(2646925613/5000000000 : ℝ)|=(2646925613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68771793/400000000 : ℝ)|^4583 ≤ (10359633450659/100000000000000 : ℝ)^3559
        have hw : |(-68771793/400000000 : ℝ)|=(68771793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086076591/2000000000 : ℝ)|^4583 ≤ (22777473196649/50000000000000 : ℝ)^3559
        have hw : |(1086076591/2000000000 : ℝ)|=(1086076591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82716433/156250000 : ℝ)*x 0 + (1357595683/2500000000 : ℝ)*x 1 + (-343858893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82716433/156250000 : ℝ)^4583 ≤ (44085425350961/100000000000000 : ℝ)^3559 := by
    have hnat : (82716433 : ℕ)^4583*100000000000000^3559 ≤ 44085425350961^3559*156250000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82716433 156250000 44085425350961 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357595683/2500000000 : ℝ)^4583 ≤ (1822197759373/4000000000000 : ℝ)^3559 := by
    have hnat : (1357595683 : ℕ)^4583*4000000000000^3559 ≤ 1822197759373^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357595683 2500000000 1822197759373 4000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343858893/2000000000 : ℝ)^4583 ≤ (5179815328677/50000000000000 : ℝ)^3559 := by
    have hnat : (343858893 : ℕ)^4583*50000000000000^3559 ≤ 5179815328677^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343858893 2000000000 5179815328677 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82716433/156250000 : ℝ), (1357595683/2500000000 : ℝ), (-343858893/2000000000 : ℝ)] ![(44085425350961/100000000000000 : ℝ), (1822197759373/4000000000000 : ℝ), (5179815328677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82716433/156250000 : ℝ)|^4583 ≤ (44085425350961/100000000000000 : ℝ)^3559
        have hw : |(82716433/156250000 : ℝ)|=(82716433/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357595683/2500000000 : ℝ)|^4583 ≤ (1822197759373/4000000000000 : ℝ)^3559
        have hw : |(1357595683/2500000000 : ℝ)|=(1357595683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343858893/2000000000 : ℝ)|^4583 ≤ (5179815328677/50000000000000 : ℝ)^3559
        have hw : |(-343858893/2000000000 : ℝ)|=(343858893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s3_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851080373/2000000000 : ℝ)*x 0 + (4507279303/10000000000 : ℝ)*x 1 + (31370501/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851080373/2000000000 : ℝ)^4583 ≤ (16639830428857/50000000000000 : ℝ)^3559 := by
    have hnat : (851080373 : ℕ)^4583*50000000000000^3559 ≤ 16639830428857^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851080373 2000000000 16639830428857 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507279303/10000000000 : ℝ)^4583 ≤ (716750985179/2000000000000 : ℝ)^3559 := by
    have hnat : (4507279303 : ℕ)^4583*2000000000000^3559 ≤ 716750985179^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507279303 10000000000 716750985179 2000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31370501/78125000 : ℝ)^4583 ≤ (15441394932473/50000000000000 : ℝ)^3559 := by
    have hnat : (31370501 : ℕ)^4583*50000000000000^3559 ≤ 15441394932473^3559*78125000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31370501 78125000 15441394932473 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851080373/2000000000 : ℝ), (4507279303/10000000000 : ℝ), (31370501/78125000 : ℝ)] ![(16639830428857/50000000000000 : ℝ), (716750985179/2000000000000 : ℝ), (15441394932473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851080373/2000000000 : ℝ)|^4583 ≤ (16639830428857/50000000000000 : ℝ)^3559
        have hw : |(851080373/2000000000 : ℝ)|=(851080373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507279303/10000000000 : ℝ)|^4583 ≤ (716750985179/2000000000000 : ℝ)^3559
        have hw : |(4507279303/10000000000 : ℝ)|=(4507279303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31370501/78125000 : ℝ)|^4583 ≤ (15441394932473/50000000000000 : ℝ)^3559
        have hw : |(31370501/78125000 : ℝ)|=(31370501/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5493/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15533/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1589/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10657/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1589/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10657/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1589/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10657/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1589/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10657/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1589/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10657/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1589/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10657/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10657/100000 : ℝ) ^ (4581/1024 : ℝ) ≤ (4466793517340699/100000000000000000000 : ℝ) := by
    have hpowers : (10657/100000 : ℝ)^4581 ≤ (4466793517340699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10657 : ℕ)^4581*100000000000000000000^1024 ≤ 4466793517340699^1024*100000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10657 100000 4466793517340699 100000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10657/100000 : ℝ)) (X := (4466793517340699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1589/10000 : ℝ) ^ (4581/1024 : ℝ) ≤ (26676058025749771/100000000000000000000 : ℝ) := by
    have hpowers : (1589/10000 : ℝ)^4581 ≤ (26676058025749771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1589 : ℕ)^4581*100000000000000000000^1024 ≤ 26676058025749771^1024*10000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1589 10000 26676058025749771 100000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1589/10000 : ℝ)) (X := (26676058025749771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004466793517340699/50000000000000000000 : ℝ) ≤ (10000199687314089/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50004466793517340699/50000000000000000000 : ℝ)^1024 ≤ (10000199687314089/10000000000000000 : ℝ)^4581 := by
      have hnat : (50004466793517340699 : ℕ)^1024*10000000000000000^4581 ≤ 10000199687314089^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004466793517340699 50000000000000000000 10000199687314089 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000199687314089/10000000000000000 : ℝ)) (X := (50004466793517340699/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003114285154309047/10000000000000000000 : ℝ) ≤ (10000696058173509/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (10003114285154309047/10000000000000000000 : ℝ)^1024 ≤ (10000696058173509/10000000000000000 : ℝ)^4581 := by
      have hnat : (10003114285154309047 : ℕ)^1024*10000000000000000^4581 ≤ 10000696058173509^4581*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003114285154309047 10000000000000000000 10000696058173509 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696058173509/10000000000000000 : ℝ)) (X := (10003114285154309047/10000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026676058025749771/50000000000000000000 : ℝ) ≤ (10001192429032929/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50026676058025749771/50000000000000000000 : ℝ)^1024 ≤ (10001192429032929/10000000000000000 : ℝ)^4581 := by
      have hnat : (50026676058025749771 : ℕ)^1024*10000000000000000^4581 ≤ 10001192429032929^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026676058025749771 50000000000000000000 10001192429032929 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001192429032929/10000000000000000 : ℝ)) (X := (50026676058025749771/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4466793517340699/100000000000000000000 : ℝ) ≤ ((52320465315216949857/52330000000000000000 : ℝ)+2*(24818542971/26165000000000 : ℝ)*(10657/100000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (52320465315216949857/52330000000000000000 : ℝ)+2*(24818542971/26165000000000 : ℝ)*(10657/100000 : ℝ)=(10000199687314089/10000000000000000 : ℝ) by norm_num, show 1+2*(4466793517340699/100000000000000000000 : ℝ)=(50004466793517340699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26676058025749771/100000000000000000000 : ℝ)+(4466793517340699/100000000000000000000 : ℝ) ≤ ((52320465315216949857/52330000000000000000 : ℝ)+(24818542971/26165000000000 : ℝ)*((1589/10000 : ℝ)+(10657/100000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (52320465315216949857/52330000000000000000 : ℝ)+(24818542971/26165000000000 : ℝ)*((1589/10000 : ℝ)+(10657/100000 : ℝ))=(10000696058173509/10000000000000000 : ℝ) by norm_num, show 1+(26676058025749771/100000000000000000000 : ℝ)+(4466793517340699/100000000000000000000 : ℝ)=(10003114285154309047/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26676058025749771/100000000000000000000 : ℝ) ≤ ((52320465315216949857/52330000000000000000 : ℝ)+2*(24818542971/26165000000000 : ℝ)*(1589/10000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (52320465315216949857/52330000000000000000 : ℝ)+2*(24818542971/26165000000000 : ℝ)*(1589/10000 : ℝ)=(10001192429032929/10000000000000000 : ℝ) by norm_num, show 1+2*(26676058025749771/100000000000000000000 : ℝ)=(50026676058025749771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52320465315216949857/52330000000000000000 : ℝ)*(X 1 0+X 2 0)+(24818542971/26165000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (10657/100000 : ℝ)) (hi := (1589/10000 : ℝ)) (c := (52320465315216949857/52330000000000000000 : ℝ)) (alpha := (24818542971/26165000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52320465315216949857/52330000000000000000 : ℝ)*(X 0 1+X 2 1)+(24818542971/26165000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (10657/100000 : ℝ)) (hi := (1589/10000 : ℝ)) (c := (52320465315216949857/52330000000000000000 : ℝ)) (alpha := (24818542971/26165000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52320465315216949857/52330000000000000000 : ℝ)*(X 0 2+X 1 2)+(24818542971/26165000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (10657/100000 : ℝ)) (hi := (1589/10000 : ℝ)) (c := (52320465315216949857/52330000000000000000 : ℝ)) (alpha := (24818542971/26165000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1822828299/10000000000 : ℝ)*X 0 0+(2715762803/5000000000 : ℝ)*X 0 1+(208679483/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675209821/5000000000 : ℝ)*X 1 0+(-1932690327/10000000000 : ℝ)*X 1 1+(5216987303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350419273/10000000000 : ℝ)*X 2 0+(81515429/156250000 : ℝ)*X 2 1+(-1932690619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255333871/10000000000 : ℝ)*X 0 0+(32102209/80000000 : ℝ)*X 0 1+(1127476783/2500000000 : ℝ)*X 0 2+(4255333871/10000000000 : ℝ)*X 1 0+(32102209/80000000 : ℝ)*X 1 1+(1127476783/2500000000 : ℝ)*X 1 2+(4255333871/10000000000 : ℝ)*X 2 0+(32102209/80000000 : ℝ)*X 2 1+(1127476783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-364571599/2000000000 : ℝ)*X 0 0+(1304530261/2500000000 : ℝ)*X 0 1+(5430382951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646925613/5000000000 : ℝ)*X 1 0+(-68771793/400000000 : ℝ)*X 1 1+(1086076591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82716433/156250000 : ℝ)*X 2 0+(1357595683/2500000000 : ℝ)*X 2 1+(-343858893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851080373/2000000000 : ℝ)*X 0 0+(4507279303/10000000000 : ℝ)*X 0 1+(31370501/78125000 : ℝ)*X 0 2+(851080373/2000000000 : ℝ)*X 1 0+(4507279303/10000000000 : ℝ)*X 1 1+(31370501/78125000 : ℝ)*X 1 2+(851080373/2000000000 : ℝ)*X 2 0+(4507279303/10000000000 : ℝ)*X 2 1+(31370501/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4044916629567288340606384293/523300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1006407383/100000000000000 : ℝ)*(base19) + (311936031/50000000000000 : ℝ)*(base23) + (69161231/100000000000000 : ℝ)*(lower2) + (47290443/12500000000000 : ℝ)*(upper3) + (36487013/100000000000000 : ℝ)*(lower4) + (834094988828771/25000000000000 : ℝ)*(major0) + (834094988828771/25000000000000 : ℝ)*(major1) + (667275991063017/20000000000000 : ℝ)*(major2) + (932237900689127/20000000000000 : ℝ)*(sp0) + (1165299576482789/25000000000000 : ℝ)*(sp1) + (4661198688466477/100000000000000 : ℝ)*(sp2) + (251443690105579/12500000000000 : ℝ)*(sp3) + (9808892903/100000000000000 : ℝ)*(sp4) + (432791703/4000000000000 : ℝ)*(sp7) + (251445042579651/12500000000000 : ℝ)*(f.failure) + (4661199312338539/100000000000000 : ℝ)*(f.sum) + (16816376499397/5233000000000000000000000000 : ℝ)*base65 + (7687699055694314253/1308250000000000000000000000000000 : ℝ)*base68 + (11182196047508538569/1046600000000000000000000000000000 : ℝ)*base69 + (1528683789291685747/1308250000000000000000000000000000 : ℝ)*base71 + (19864548155569/5233000000000000000000000000 : ℝ)*base73 + (4852518445834538569/1046600000000000000000000000000000 : ℝ)*base75 + (2571973306286935747/1308250000000000000000000000000000 : ℝ)*base77 + (27543032026932314253/1308250000000000000000000000000000 : ℝ)*base80 + (33987824110943/5233000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11016347/1250000000000000000000 : ℝ)*base89 + (11016347/1250000000000000000000 : ℝ)*base91 + (1483653/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14957818144871199902291380923/1308250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (883493721/50000000000000 : ℝ)*(base19) + (75300951/3125000000000 : ℝ)*(base23) + (3751977/10000000000000 : ℝ)*(upper2) + (327848919/100000000000000 : ℝ)*(upper3) + (108335183/50000000000000 : ℝ)*(upper5) + (1686070342377171/50000000000000 : ℝ)*(major0) + (1686070342377171/50000000000000 : ℝ)*(major1) + (1686070342377171/50000000000000 : ℝ)*(major2) + (22562837339/100000000000000 : ℝ)*(sp1) + (35596021631/100000000000000 : ℝ)*(sp2) + (58889498680851/1250000000000 : ℝ)*(sp4) + (47111355646433/1000000000000 : ℝ)*(sp5) + (4711121888816017/100000000000000 : ℝ)*(sp6) + (406624218785083/20000000000000 : ℝ)*(sp7) + (406624218785083/20000000000000 : ℝ)*(f.failure) + (58889498680851/1250000000000 : ℝ)*(f.sum) + (35777926209047/5233000000000000000000000000 : ℝ)*base66 + (3597528536501985453/2616500000000000000000000000000000 : ℝ)*base68 + (9423573790429485453/2616500000000000000000000000000000 : ℝ)*base70 + (9583390167743985453/2616500000000000000000000000000000 : ℝ)*base72 + (137317781251/654125000000000000000000000 : ℝ)*base74 + (18179832689889985453/2616500000000000000000000000000000 : ℝ)*base76 + (30728548387472485453/2616500000000000000000000000000000 : ℝ)*base78 + (23585504912891985453/2616500000000000000000000000000000 : ℝ)*base80 + (1995117952653/523300000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5549651/2000000000000000000000 : ℝ)*base89 + (5549651/2000000000000000000000 : ℝ)*base91 + (5549651/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1543_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1543_s4_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823135513/10000000000 : ℝ)*x 0 + (2714740651/5000000000 : ℝ)*x 1 + (5218828001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823135513/10000000000 : ℝ)^4583 ≤ (5586127511637/50000000000000 : ℝ)^3559 := by
    have hnat : (1823135513 : ℕ)^4583*50000000000000^3559 ≤ 5586127511637^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823135513 10000000000 5586127511637 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714740651/5000000000 : ℝ)^4583 ≤ (227726032297/500000000000 : ℝ)^3559 := by
    have hnat : (2714740651 : ℕ)^4583*500000000000^3559 ≤ 227726032297^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714740651 5000000000 227726032297 500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218828001/10000000000 : ℝ)^4583 ≤ (2164126925497/5000000000000 : ℝ)^3559 := by
    have hnat : (5218828001 : ℕ)^4583*5000000000000^3559 ≤ 2164126925497^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218828001 10000000000 2164126925497 5000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823135513/10000000000 : ℝ), (2714740651/5000000000 : ℝ), (5218828001/10000000000 : ℝ)] ![(5586127511637/50000000000000 : ℝ), (227726032297/500000000000 : ℝ), (2164126925497/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823135513/10000000000 : ℝ)|^4583 ≤ (5586127511637/50000000000000 : ℝ)^3559
        have hw : |(-1823135513/10000000000 : ℝ)|=(1823135513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714740651/5000000000 : ℝ)|^4583 ≤ (227726032297/500000000000 : ℝ)^3559
        have hw : |(2714740651/5000000000 : ℝ)|=(2714740651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218828001/10000000000 : ℝ)|^4583 ≤ (2164126925497/5000000000000 : ℝ)^3559
        have hw : |(5218828001/10000000000 : ℝ)|=(5218828001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349881413/10000000000 : ℝ)*x 0 + (-482740501/2500000000 : ℝ)*x 1 + (5218827991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349881413/10000000000 : ℝ)^4583 ≤ (22343592140443/50000000000000 : ℝ)^3559 := by
    have hnat : (5349881413 : ℕ)^4583*50000000000000^3559 ≤ 22343592140443^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349881413 10000000000 22343592140443 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482740501/2500000000 : ℝ)^4583 ≤ (1203027730303/10000000000000 : ℝ)^3559 := by
    have hnat : (482740501 : ℕ)^4583*10000000000000^3559 ≤ 1203027730303^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482740501 2500000000 1203027730303 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218827991/10000000000 : ℝ)^4583 ≤ (43282538403143/100000000000000 : ℝ)^3559 := by
    have hnat : (5218827991 : ℕ)^4583*100000000000000^3559 ≤ 43282538403143^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218827991 10000000000 43282538403143 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349881413/10000000000 : ℝ), (-482740501/2500000000 : ℝ), (5218827991/10000000000 : ℝ)] ![(22343592140443/50000000000000 : ℝ), (1203027730303/10000000000000 : ℝ), (43282538403143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349881413/10000000000 : ℝ)|^4583 ≤ (22343592140443/50000000000000 : ℝ)^3559
        have hw : |(5349881413/10000000000 : ℝ)|=(5349881413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482740501/2500000000 : ℝ)|^4583 ≤ (1203027730303/10000000000000 : ℝ)^3559
        have hw : |(-482740501/2500000000 : ℝ)|=(482740501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218827991/10000000000 : ℝ)|^4583 ≤ (43282538403143/100000000000000 : ℝ)^3559
        have hw : |(5218827991/10000000000 : ℝ)|=(5218827991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349881417/10000000000 : ℝ)*x 0 + (104376559/200000000 : ℝ)*x 1 + (-1930962053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349881417/10000000000 : ℝ)^4583 ≤ (44687184323911/100000000000000 : ℝ)^3559 := by
    have hnat : (5349881417 : ℕ)^4583*100000000000000^3559 ≤ 44687184323911^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349881417 10000000000 44687184323911 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104376559/200000000 : ℝ)^4583 ≤ (5410317245659/12500000000000 : ℝ)^3559 := by
    have hnat : (104376559 : ℕ)^4583*12500000000000^3559 ≤ 5410317245659^3559*200000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104376559 200000000 5410317245659 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930962053/10000000000 : ℝ)^4583 ≤ (2406055539229/20000000000000 : ℝ)^3559 := by
    have hnat : (1930962053 : ℕ)^4583*20000000000000^3559 ≤ 2406055539229^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930962053 10000000000 2406055539229 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349881417/10000000000 : ℝ), (104376559/200000000 : ℝ), (-1930962053/10000000000 : ℝ)] ![(44687184323911/100000000000000 : ℝ), (5410317245659/12500000000000 : ℝ), (2406055539229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349881417/10000000000 : ℝ)|^4583 ≤ (44687184323911/100000000000000 : ℝ)^3559
        have hw : |(5349881417/10000000000 : ℝ)|=(5349881417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104376559/200000000 : ℝ)|^4583 ≤ (5410317245659/12500000000000 : ℝ)^3559
        have hw : |(104376559/200000000 : ℝ)|=(104376559/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930962053/10000000000 : ℝ)|^4583 ≤ (2406055539229/20000000000000 : ℝ)^3559
        have hw : |(-1930962053/10000000000 : ℝ)|=(1930962053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255527191/10000000000 : ℝ)*x 0 + (2008628157/5000000000 : ℝ)*x 1 + (4505383529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255527191/10000000000 : ℝ)^4583 ≤ (33280922985129/100000000000000 : ℝ)^3559 := by
    have hnat : (4255527191 : ℕ)^4583*100000000000000^3559 ≤ 33280922985129^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255527191 10000000000 33280922985129 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008628157/5000000000 : ℝ)^4583 ≤ (30900936873147/100000000000000 : ℝ)^3559 := by
    have hnat : (2008628157 : ℕ)^4583*100000000000000^3559 ≤ 30900936873147^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008628157 5000000000 30900936873147 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505383529/10000000000 : ℝ)^4583 ≤ (4477267516603/12500000000000 : ℝ)^3559 := by
    have hnat : (4505383529 : ℕ)^4583*12500000000000^3559 ≤ 4477267516603^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505383529 10000000000 4477267516603 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255527191/10000000000 : ℝ), (2008628157/5000000000 : ℝ), (4505383529/10000000000 : ℝ)] ![(33280922985129/100000000000000 : ℝ), (30900936873147/100000000000000 : ℝ), (4477267516603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255527191/10000000000 : ℝ)|^4583 ≤ (33280922985129/100000000000000 : ℝ)^3559
        have hw : |(4255527191/10000000000 : ℝ)|=(4255527191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008628157/5000000000 : ℝ)|^4583 ≤ (30900936873147/100000000000000 : ℝ)^3559
        have hw : |(2008628157/5000000000 : ℝ)|=(2008628157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505383529/10000000000 : ℝ)|^4583 ≤ (4477267516603/12500000000000 : ℝ)^3559
        have hw : |(4505383529/10000000000 : ℝ)|=(4505383529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455790817/2500000000 : ℝ)*x 0 + (163122549/312500000 : ℝ)*x 1 + (2714189887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455790817/2500000000 : ℝ)^4583 ≤ (5586237022183/50000000000000 : ℝ)^3559 := by
    have hnat : (455790817 : ℕ)^4583*50000000000000^3559 ≤ 5586237022183^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455790817 2500000000 5586237022183 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163122549/312500000 : ℝ)^4583 ≤ (21647108949109/50000000000000 : ℝ)^3559 := by
    have hnat : (163122549 : ℕ)^4583*50000000000000^3559 ≤ 21647108949109^3559*312500000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163122549 312500000 21647108949109 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714189887/5000000000 : ℝ)^4583 ≤ (11383327011409/25000000000000 : ℝ)^3559 := by
    have hnat : (2714189887 : ℕ)^4583*25000000000000^3559 ≤ 11383327011409^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714189887 5000000000 11383327011409 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455790817/2500000000 : ℝ), (163122549/312500000 : ℝ), (2714189887/5000000000 : ℝ)] ![(5586237022183/50000000000000 : ℝ), (21647108949109/50000000000000 : ℝ), (11383327011409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455790817/2500000000 : ℝ)|^4583 ≤ (5586237022183/50000000000000 : ℝ)^3559
        have hw : |(-455790817/2500000000 : ℝ)|=(455790817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163122549/312500000 : ℝ)|^4583 ≤ (21647108949109/50000000000000 : ℝ)^3559
        have hw : |(163122549/312500000 : ℝ)|=(163122549/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714189887/5000000000 : ℝ)|^4583 ≤ (11383327011409/25000000000000 : ℝ)^3559
        have hw : |(2714189887/5000000000 : ℝ)|=(2714189887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647169047/5000000000 : ℝ)*x 0 + (-1721410331/10000000000 : ℝ)*x 1 + (5428379751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647169047/5000000000 : ℝ)^4583 ≤ (22045320620139/50000000000000 : ℝ)^3559 := by
    have hnat : (2647169047 : ℕ)^4583*50000000000000^3559 ≤ 22045320620139^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647169047 5000000000 22045320620139 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721410331/10000000000 : ℝ)^4583 ≤ (10376050950117/100000000000000 : ℝ)^3559 := by
    have hnat : (1721410331 : ℕ)^4583*100000000000000^3559 ≤ 10376050950117^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721410331 10000000000 10376050950117 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428379751/10000000000 : ℝ)^4583 ≤ (11383326949301/25000000000000 : ℝ)^3559 := by
    have hnat : (5428379751 : ℕ)^4583*25000000000000^3559 ≤ 11383326949301^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428379751 10000000000 11383326949301 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647169047/5000000000 : ℝ), (-1721410331/10000000000 : ℝ), (5428379751/10000000000 : ℝ)] ![(22045320620139/50000000000000 : ℝ), (10376050950117/100000000000000 : ℝ), (11383326949301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647169047/5000000000 : ℝ)|^4583 ≤ (22045320620139/50000000000000 : ℝ)^3559
        have hw : |(2647169047/5000000000 : ℝ)|=(2647169047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1721410331/10000000000 : ℝ)|^4583 ≤ (10376050950117/100000000000000 : ℝ)^3559
        have hw : |(-1721410331/10000000000 : ℝ)|=(1721410331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428379751/10000000000 : ℝ)|^4583 ≤ (11383326949301/25000000000000 : ℝ)^3559
        have hw : |(5428379751/10000000000 : ℝ)|=(5428379751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294337993/10000000000 : ℝ)*x 0 + (542837973/1000000000 : ℝ)*x 1 + (-1721410499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294337993/10000000000 : ℝ)^4583 ≤ (8818128031431/20000000000000 : ℝ)^3559 := by
    have hnat : (5294337993 : ℕ)^4583*20000000000000^3559 ≤ 8818128031431^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294337993 10000000000 8818128031431 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542837973/1000000000 : ℝ)^4583 ≤ (22766653785187/50000000000000 : ℝ)^3559 := by
    have hnat : (542837973 : ℕ)^4583*50000000000000^3559 ≤ 22766653785187^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542837973 1000000000 22766653785187 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1721410499/10000000000 : ℝ)^4583 ≤ (10376052254121/100000000000000 : ℝ)^3559 := by
    have hnat : (1721410499 : ℕ)^4583*100000000000000^3559 ≤ 10376052254121^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721410499 10000000000 10376052254121 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294337993/10000000000 : ℝ), (542837973/1000000000 : ℝ), (-1721410499/10000000000 : ℝ)] ![(8818128031431/20000000000000 : ℝ), (22766653785187/50000000000000 : ℝ), (10376052254121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294337993/10000000000 : ℝ)|^4583 ≤ (8818128031431/20000000000000 : ℝ)^3559
        have hw : |(5294337993/10000000000 : ℝ)|=(5294337993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542837973/1000000000 : ℝ)|^4583 ≤ (22766653785187/50000000000000 : ℝ)^3559
        have hw : |(542837973/1000000000 : ℝ)|=(542837973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1721410499/10000000000 : ℝ)|^4583 ≤ (10376052254121/100000000000000 : ℝ)^3559
        have hw : |(-1721410499/10000000000 : ℝ)|=(1721410499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s4_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531948999/1250000000 : ℝ)*x 0 + (2251424719/5000000000 : ℝ)*x 1 + (100495227/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531948999/1250000000 : ℝ)^4583 ≤ (6656315116861/20000000000000 : ℝ)^3559 := by
    have hnat : (531948999 : ℕ)^4583*20000000000000^3559 ≤ 6656315116861^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531948999 1250000000 6656315116861 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251424719/5000000000 : ℝ)^4583 ≤ (35792199522333/100000000000000 : ℝ)^3559 := by
    have hnat : (2251424719 : ℕ)^4583*100000000000000^3559 ≤ 35792199522333^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251424719 5000000000 35792199522333 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100495227/250000000 : ℝ)^4583 ≤ (30926224884321/100000000000000 : ℝ)^3559 := by
    have hnat : (100495227 : ℕ)^4583*100000000000000^3559 ≤ 30926224884321^3559*250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100495227 250000000 30926224884321 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531948999/1250000000 : ℝ), (2251424719/5000000000 : ℝ), (100495227/250000000 : ℝ)] ![(6656315116861/20000000000000 : ℝ), (35792199522333/100000000000000 : ℝ), (30926224884321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531948999/1250000000 : ℝ)|^4583 ≤ (6656315116861/20000000000000 : ℝ)^3559
        have hw : |(531948999/1250000000 : ℝ)|=(531948999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251424719/5000000000 : ℝ)|^4583 ≤ (35792199522333/100000000000000 : ℝ)^3559
        have hw : |(2251424719/5000000000 : ℝ)|=(2251424719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100495227/250000000 : ℝ)|^4583 ≤ (30926224884321/100000000000000 : ℝ)^3559
        have hw : |(100495227/250000000 : ℝ)|=(100495227/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (441/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15533/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15533/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15533/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5493/50000 : ℝ) ^ (4581/1024 : ℝ) ≤ (1279406482894987/25000000000000000000 : ℝ) := by
    have hpowers : (5493/50000 : ℝ)^4581 ≤ (1279406482894987/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5493 : ℕ)^4581*25000000000000000000^1024 ≤ 1279406482894987^1024*50000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5493 50000 1279406482894987 25000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5493/50000 : ℝ)) (X := (1279406482894987/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15533/100000 : ℝ) ^ (4581/1024 : ℝ) ≤ (2409757619399843/10000000000000000000 : ℝ) := by
    have hpowers : (15533/100000 : ℝ)^4581 ≤ (2409757619399843/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15533 : ℕ)^4581*10000000000000000000^1024 ≤ 2409757619399843^1024*100000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15533 100000 2409757619399843 10000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15533/100000 : ℝ)) (X := (2409757619399843/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501279406482894987/12500000000000000000 : ℝ) ≤ (10000228781520553/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (12501279406482894987/12500000000000000000 : ℝ)^1024 ≤ (10000228781520553/10000000000000000 : ℝ)^4581 := by
      have hnat : (12501279406482894987 : ℕ)^1024*10000000000000000^4581 ≤ 10000228781520553^4581*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501279406482894987 12500000000000000000 10000228781520553 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000228781520553/10000000000000000 : ℝ)) (X := (12501279406482894987/12500000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014607601062789189/50000000000000000000 : ℝ) ≤ (10000652979138811/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50014607601062789189/50000000000000000000 : ℝ)^1024 ≤ (10000652979138811/10000000000000000 : ℝ)^4581 := by
      have hnat : (50014607601062789189 : ℕ)^1024*10000000000000000^4581 ≤ 10000652979138811^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014607601062789189 50000000000000000000 10000652979138811 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652979138811/10000000000000000 : ℝ)) (X := (50014607601062789189/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002409757619399843/5000000000000000000 : ℝ) ≤ (10001077176757069/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (5002409757619399843/5000000000000000000 : ℝ)^1024 ≤ (10001077176757069/10000000000000000 : ℝ)^4581 := by
      have hnat : (5002409757619399843 : ℕ)^1024*10000000000000000^4581 ≤ 10001077176757069^4581*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002409757619399843 5000000000000000000 10001077176757069 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001077176757069/10000000000000000 : ℝ)) (X := (5002409757619399843/5000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1279406482894987/25000000000000000000 : ℝ) ≤ ((9092343959901117943/9094000000000000000 : ℝ)+2*(212098809129/227350000000000 : ℝ)*(5493/50000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (9092343959901117943/9094000000000000000 : ℝ)+2*(212098809129/227350000000000 : ℝ)*(5493/50000 : ℝ)=(10000228781520553/10000000000000000 : ℝ) by norm_num, show 1+2*(1279406482894987/25000000000000000000 : ℝ)=(12501279406482894987/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2409757619399843/10000000000000000000 : ℝ)+(1279406482894987/25000000000000000000 : ℝ) ≤ ((9092343959901117943/9094000000000000000 : ℝ)+(212098809129/227350000000000 : ℝ)*((15533/100000 : ℝ)+(5493/50000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (9092343959901117943/9094000000000000000 : ℝ)+(212098809129/227350000000000 : ℝ)*((15533/100000 : ℝ)+(5493/50000 : ℝ))=(10000652979138811/10000000000000000 : ℝ) by norm_num, show 1+(2409757619399843/10000000000000000000 : ℝ)+(1279406482894987/25000000000000000000 : ℝ)=(50014607601062789189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2409757619399843/10000000000000000000 : ℝ) ≤ ((9092343959901117943/9094000000000000000 : ℝ)+2*(212098809129/227350000000000 : ℝ)*(15533/100000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (9092343959901117943/9094000000000000000 : ℝ)+2*(212098809129/227350000000000 : ℝ)*(15533/100000 : ℝ)=(10001077176757069/10000000000000000 : ℝ) by norm_num, show 1+2*(2409757619399843/10000000000000000000 : ℝ)=(5002409757619399843/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9092343959901117943/9094000000000000000 : ℝ)*(X 1 0+X 2 0)+(212098809129/227350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (9092343959901117943/9094000000000000000 : ℝ)) (alpha := (212098809129/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9092343959901117943/9094000000000000000 : ℝ)*(X 0 1+X 2 1)+(212098809129/227350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (9092343959901117943/9094000000000000000 : ℝ)) (alpha := (212098809129/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9092343959901117943/9094000000000000000 : ℝ)*(X 0 2+X 1 2)+(212098809129/227350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (15533/100000 : ℝ)) (c := (9092343959901117943/9094000000000000000 : ℝ)) (alpha := (212098809129/227350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1823135513/10000000000 : ℝ)*X 0 0+(2714740651/5000000000 : ℝ)*X 0 1+(5218828001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349881413/10000000000 : ℝ)*X 1 0+(-482740501/2500000000 : ℝ)*X 1 1+(5218827991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349881417/10000000000 : ℝ)*X 2 0+(104376559/200000000 : ℝ)*X 2 1+(-1930962053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255527191/10000000000 : ℝ)*X 0 0+(2008628157/5000000000 : ℝ)*X 0 1+(4505383529/10000000000 : ℝ)*X 0 2+(4255527191/10000000000 : ℝ)*X 1 0+(2008628157/5000000000 : ℝ)*X 1 1+(4505383529/10000000000 : ℝ)*X 1 2+(4255527191/10000000000 : ℝ)*X 2 0+(2008628157/5000000000 : ℝ)*X 2 1+(4505383529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-455790817/2500000000 : ℝ)*X 0 0+(163122549/312500000 : ℝ)*X 0 1+(2714189887/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647169047/5000000000 : ℝ)*X 1 0+(-1721410331/10000000000 : ℝ)*X 1 1+(5428379751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294337993/10000000000 : ℝ)*X 2 0+(542837973/1000000000 : ℝ)*X 2 1+(-1721410499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((531948999/1250000000 : ℝ)*X 0 0+(2251424719/5000000000 : ℝ)*X 0 1+(100495227/250000000 : ℝ)*X 0 2+(531948999/1250000000 : ℝ)*X 1 0+(2251424719/5000000000 : ℝ)*X 1 1+(100495227/250000000 : ℝ)*X 1 2+(531948999/1250000000 : ℝ)*X 2 0+(2251424719/5000000000 : ℝ)*X 2 1+(100495227/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2512763222244569573726763003/227350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (497519011/25000000000000 : ℝ)*(base19) + (1885721581/100000000000000 : ℝ)*(base23) + (57727279/100000000000000 : ℝ)*(lower2) + (300109567/100000000000000 : ℝ)*(upper3) + (174111267/100000000000000 : ℝ)*(upper5) + (1698968931927807/50000000000000 : ℝ)*(major0) + (1698968931927807/50000000000000 : ℝ)*(major1) + (679587572771123/20000000000000 : ℝ)*(major2) + (1186792462125037/25000000000000 : ℝ)*(sp0) + (4747198716326683/100000000000000 : ℝ)*(sp1) + (2373599410340573/50000000000000 : ℝ)*(sp2) + (1024329769242743/50000000000000 : ℝ)*(sp3) + (15428951289/50000000000000 : ℝ)*(sp4) + (15114409663/100000000000000 : ℝ)*(sp7) + (40973493057903/2000000000000 : ℝ)*(f.failure) + (4747200706402727/100000000000000 : ℝ)*(f.sum) + (69597157086451/22735000000000000000000000000 : ℝ)*base65 + (669609096535558999/454700000000000000000000000000000 : ℝ)*base68 + (100619986139687989/181880000000000000000000000000000 : ℝ)*base69 + (601732738680341001/454700000000000000000000000000000 : ℝ)*base71 + (135928393587031/22735000000000000000000000000 : ℝ)*base73 + (1577747252586352011/181880000000000000000000000000000 : ℝ)*base76 + (2699093696626338999/454700000000000000000000000000000 : ℝ)*base78 + (3551008837508138999/454700000000000000000000000000000 : ℝ)*base80 + (112797723511/710468750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1777191/200000000000000000000 : ℝ)*base89 + (1777191/200000000000000000000 : ℝ)*base91 + (222809/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52865470942257970232877/5683750000000000000000000000 : ℝ) := by norm_num
    linear_combination (142078779/12500000000000 : ℝ)*(base19) + (657434571/50000000000000 : ℝ)*(base23) + (141344883/100000000000000 : ℝ)*(upper3) + (36945769/25000000000000 : ℝ)*(lower4) + (47986473/25000000000000 : ℝ)*(upper5) + (1716835442682931/50000000000000 : ℝ)*(major0) + (1716835442682931/50000000000000 : ℝ)*(major1) + (1716835442682931/50000000000000 : ℝ)*(major2) + (8762653987/50000000000000 : ℝ)*(sp1) + (16631119597/100000000000000 : ℝ)*(sp2) + (4797122760092333/100000000000000 : ℝ)*(sp4) + (2398552049077063/50000000000000 : ℝ)*(sp5) + (4797104814103593/100000000000000 : ℝ)*(sp6) + (20702187006007/1000000000000 : ℝ)*(sp7) + (20702187006007/1000000000000 : ℝ)*(f.failure) + (4797122760092333/100000000000000 : ℝ)*(f.sum) + (8260444201467/2841875000000000000000000000 : ℝ)*base65 + (129023687828909067/454700000000000000000000000000000 : ℝ)*base68 + (4313347691719509067/454700000000000000000000000000000 : ℝ)*base70 + (3560269899289690933/454700000000000000000000000000000 : ℝ)*base71 + (67480353215567/11367500000000000000000000000 : ℝ)*base74 + (1963699136374109067/454700000000000000000000000000000 : ℝ)*base76 + (4022165666837290933/454700000000000000000000000000000 : ℝ)*base77 + (1562656789859890933/454700000000000000000000000000000 : ℝ)*base79 + (9572319122989/1420937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (195921/100000000000000000000 : ℝ)*base90 + (195921/100000000000000000000 : ℝ)*base92 + (195921/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1543_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15533/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1543_s5_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823170803/10000000000 : ℝ)*x 0 + (5429254169/10000000000 : ℝ)*x 1 + (652378957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823170803/10000000000 : ℝ)^4583 ≤ (11172533504951/100000000000000 : ℝ)^3559 := by
    have hnat : (1823170803 : ℕ)^4583*100000000000000^3559 ≤ 11172533504951^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823170803 10000000000 11172533504951 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429254169/10000000000 : ℝ)^4583 ≤ (22771376486017/50000000000000 : ℝ)^3559 := by
    have hnat : (5429254169 : ℕ)^4583*50000000000000^3559 ≤ 22771376486017^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429254169 10000000000 22771376486017 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652378957/1250000000 : ℝ)^4583 ≤ (8656942701851/20000000000000 : ℝ)^3559 := by
    have hnat : (652378957 : ℕ)^4583*20000000000000^3559 ≤ 8656942701851^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652378957 1250000000 8656942701851 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823170803/10000000000 : ℝ), (5429254169/10000000000 : ℝ), (652378957/1250000000 : ℝ)] ![(11172533504951/100000000000000 : ℝ), (22771376486017/50000000000000 : ℝ), (8656942701851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823170803/10000000000 : ℝ)|^4583 ≤ (11172533504951/100000000000000 : ℝ)^3559
        have hw : |(-1823170803/10000000000 : ℝ)|=(1823170803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429254169/10000000000 : ℝ)|^4583 ≤ (22771376486017/50000000000000 : ℝ)^3559
        have hw : |(5429254169/10000000000 : ℝ)|=(5429254169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652378957/1250000000 : ℝ)|^4583 ≤ (8656942701851/20000000000000 : ℝ)^3559
        have hw : |(652378957/1250000000 : ℝ)|=(652378957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069964221/2000000000 : ℝ)*x 0 + (-96538589/500000000 : ℝ)*x 1 + (2609515813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069964221/2000000000 : ℝ)^4583 ≤ (22343267797143/50000000000000 : ℝ)^3559 := by
    have hnat : (1069964221 : ℕ)^4583*50000000000000^3559 ≤ 22343267797143^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069964221 2000000000 22343267797143 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96538589/500000000 : ℝ)^4583 ≤ (2405750240647/20000000000000 : ℝ)^3559 := by
    have hnat : (96538589 : ℕ)^4583*20000000000000^3559 ≤ 2405750240647^3559*500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96538589 500000000 2405750240647 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609515813/5000000000 : ℝ)^4583 ≤ (43284713188859/100000000000000 : ℝ)^3559 := by
    have hnat : (2609515813 : ℕ)^4583*100000000000000^3559 ≤ 43284713188859^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609515813 5000000000 43284713188859 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069964221/2000000000 : ℝ), (-96538589/500000000 : ℝ), (2609515813/5000000000 : ℝ)] ![(22343267797143/50000000000000 : ℝ), (2405750240647/20000000000000 : ℝ), (43284713188859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069964221/2000000000 : ℝ)|^4583 ≤ (22343267797143/50000000000000 : ℝ)^3559
        have hw : |(1069964221/2000000000 : ℝ)|=(1069964221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96538589/500000000 : ℝ)|^4583 ≤ (2405750240647/20000000000000 : ℝ)^3559
        have hw : |(-96538589/500000000 : ℝ)|=(96538589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609515813/5000000000 : ℝ)|^4583 ≤ (43284713188859/100000000000000 : ℝ)^3559
        have hw : |(2609515813/5000000000 : ℝ)|=(2609515813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674910551/5000000000 : ℝ)*x 0 + (5219031633/10000000000 : ℝ)*x 1 + (-77230871/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674910551/5000000000 : ℝ)^4583 ≤ (22343267781009/50000000000000 : ℝ)^3559 := by
    have hnat : (2674910551 : ℕ)^4583*50000000000000^3559 ≤ 22343267781009^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674910551 5000000000 22343267781009 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219031633/10000000000 : ℝ)^4583 ≤ (21642356631809/50000000000000 : ℝ)^3559 := by
    have hnat : (5219031633 : ℕ)^4583*50000000000000^3559 ≤ 21642356631809^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219031633 10000000000 21642356631809 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77230871/400000000 : ℝ)^4583 ≤ (6014375581561/50000000000000 : ℝ)^3559 := by
    have hnat : (77230871 : ℕ)^4583*50000000000000^3559 ≤ 6014375581561^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77230871 400000000 6014375581561 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674910551/5000000000 : ℝ), (5219031633/10000000000 : ℝ), (-77230871/400000000 : ℝ)] ![(22343267781009/50000000000000 : ℝ), (21642356631809/50000000000000 : ℝ), (6014375581561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674910551/5000000000 : ℝ)|^4583 ≤ (22343267781009/50000000000000 : ℝ)^3559
        have hw : |(2674910551/5000000000 : ℝ)|=(2674910551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219031633/10000000000 : ℝ)|^4583 ≤ (21642356631809/50000000000000 : ℝ)^3559
        have hw : |(5219031633/10000000000 : ℝ)|=(5219031633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77230871/400000000 : ℝ)|^4583 ≤ (6014375581561/50000000000000 : ℝ)^3559
        have hw : |(-77230871/400000000 : ℝ)|=(77230871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155809/9765625 : ℝ)*x 0 + (803550609/2000000000 : ℝ)*x 1 + (4504882023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155809/9765625 : ℝ)^4583 ≤ (16640568368979/50000000000000 : ℝ)^3559 := by
    have hnat : (4155809 : ℕ)^4583*50000000000000^3559 ≤ 16640568368979^3559*9765625^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155809 9765625 16640568368979 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803550609/2000000000 : ℝ)^4583 ≤ (30905857188783/100000000000000 : ℝ)^3559 := by
    have hnat : (803550609 : ℕ)^4583*100000000000000^3559 ≤ 30905857188783^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803550609 2000000000 30905857188783 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504882023/10000000000 : ℝ)^4583 ≤ (35813006056603/100000000000000 : ℝ)^3559 := by
    have hnat : (4504882023 : ℕ)^4583*100000000000000^3559 ≤ 35813006056603^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504882023 10000000000 35813006056603 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155809/9765625 : ℝ), (803550609/2000000000 : ℝ), (4504882023/10000000000 : ℝ)] ![(16640568368979/50000000000000 : ℝ), (30905857188783/100000000000000 : ℝ), (35813006056603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155809/9765625 : ℝ)|^4583 ≤ (16640568368979/50000000000000 : ℝ)^3559
        have hw : |(4155809/9765625 : ℝ)|=(4155809/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803550609/2000000000 : ℝ)|^4583 ≤ (30905857188783/100000000000000 : ℝ)^3559
        have hw : |(803550609/2000000000 : ℝ)|=(803550609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504882023/10000000000 : ℝ)|^4583 ≤ (35813006056603/100000000000000 : ℝ)^3559
        have hw : |(4504882023/10000000000 : ℝ)|=(4504882023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823198569/10000000000 : ℝ)*x 0 + (5220120741/10000000000 : ℝ)*x 1 + (5428157039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823198569/10000000000 : ℝ)^4583 ≤ (2793188153517/25000000000000 : ℝ)^3559 := by
    have hnat : (1823198569 : ℕ)^4583*25000000000000^3559 ≤ 2793188153517^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823198569 10000000000 2793188153517 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220120741/10000000000 : ℝ)^4583 ≤ (21648172579269/50000000000000 : ℝ)^3559 := by
    have hnat : (5220120741 : ℕ)^4583*50000000000000^3559 ≤ 21648172579269^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220120741 10000000000 21648172579269 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428157039/10000000000 : ℝ)^4583 ≤ (45530902205579/100000000000000 : ℝ)^3559 := by
    have hnat : (5428157039 : ℕ)^4583*100000000000000^3559 ≤ 45530902205579^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428157039 10000000000 45530902205579 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823198569/10000000000 : ℝ), (5220120741/10000000000 : ℝ), (5428157039/10000000000 : ℝ)] ![(2793188153517/25000000000000 : ℝ), (21648172579269/50000000000000 : ℝ), (45530902205579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823198569/10000000000 : ℝ)|^4583 ≤ (2793188153517/25000000000000 : ℝ)^3559
        have hw : |(-1823198569/10000000000 : ℝ)|=(1823198569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220120741/10000000000 : ℝ)|^4583 ≤ (21648172579269/50000000000000 : ℝ)^3559
        have hw : |(5220120741/10000000000 : ℝ)|=(5220120741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428157039/10000000000 : ℝ)|^4583 ≤ (45530902205579/100000000000000 : ℝ)^3559
        have hw : |(5428157039/10000000000 : ℝ)|=(5428157039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058878317/2000000000 : ℝ)*x 0 + (-1721646369/10000000000 : ℝ)*x 1 + (5428157021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058878317/2000000000 : ℝ)^4583 ≤ (22045607439171/50000000000000 : ℝ)^3559 := by
    have hnat : (1058878317 : ℕ)^4583*50000000000000^3559 ≤ 22045607439171^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058878317 2000000000 22045607439171 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721646369/10000000000 : ℝ)^4583 ≤ (5188941548003/50000000000000 : ℝ)^3559 := by
    have hnat : (1721646369 : ℕ)^4583*50000000000000^3559 ≤ 5188941548003^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721646369 10000000000 5188941548003 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428157021/10000000000 : ℝ)^4583 ≤ (9106180402231/20000000000000 : ℝ)^3559 := by
    have hnat : (5428157021 : ℕ)^4583*20000000000000^3559 ≤ 9106180402231^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428157021 10000000000 9106180402231 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058878317/2000000000 : ℝ), (-1721646369/10000000000 : ℝ), (5428157021/10000000000 : ℝ)] ![(22045607439171/50000000000000 : ℝ), (5188941548003/50000000000000 : ℝ), (9106180402231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058878317/2000000000 : ℝ)|^4583 ≤ (22045607439171/50000000000000 : ℝ)^3559
        have hw : |(1058878317/2000000000 : ℝ)|=(1058878317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1721646369/10000000000 : ℝ)|^4583 ≤ (5188941548003/50000000000000 : ℝ)^3559
        have hw : |(-1721646369/10000000000 : ℝ)|=(1721646369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428157021/10000000000 : ℝ)|^4583 ≤ (9106180402231/20000000000000 : ℝ)^3559
        have hw : |(5428157021/10000000000 : ℝ)|=(5428157021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294391539/10000000000 : ℝ)*x 0 + (108563141/200000000 : ℝ)*x 1 + (-215205799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294391539/10000000000 : ℝ)^4583 ≤ (44091214385037/100000000000000 : ℝ)^3559 := by
    have hnat : (5294391539 : ℕ)^4583*100000000000000^3559 ≤ 44091214385037^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294391539 10000000000 44091214385037 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108563141/200000000 : ℝ)^4583 ≤ (45530902324393/100000000000000 : ℝ)^3559 := by
    have hnat : (108563141 : ℕ)^4583*100000000000000^3559 ≤ 45530902324393^3559*200000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108563141 200000000 45530902324393 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215205799/1250000000 : ℝ)^4583 ≤ (10377883274537/100000000000000 : ℝ)^3559 := by
    have hnat : (215205799 : ℕ)^4583*100000000000000^3559 ≤ 10377883274537^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215205799 1250000000 10377883274537 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294391539/10000000000 : ℝ), (108563141/200000000 : ℝ), (-215205799/1250000000 : ℝ)] ![(44091214385037/100000000000000 : ℝ), (45530902324393/100000000000000 : ℝ), (10377883274537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294391539/10000000000 : ℝ)|^4583 ≤ (44091214385037/100000000000000 : ℝ)^3559
        have hw : |(5294391539/10000000000 : ℝ)|=(5294391539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108563141/200000000 : ℝ)|^4583 ≤ (45530902324393/100000000000000 : ℝ)^3559
        have hw : |(108563141/200000000 : ℝ)|=(108563141/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215205799/1250000000 : ℝ)|^4583 ≤ (10377883274537/100000000000000 : ℝ)^3559
        have hw : |(-215205799/1250000000 : ℝ)|=(215205799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s5_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255612783/10000000000 : ℝ)*x 0 + (180094333/400000000 : ℝ)*x 1 + (4020295341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255612783/10000000000 : ℝ)^4583 ≤ (33281784967319/100000000000000 : ℝ)^3559 := by
    have hnat : (4255612783 : ℕ)^4583*100000000000000^3559 ≤ 33281784967319^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255612783 10000000000 33281784967319 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180094333/400000000 : ℝ)^4583 ≤ (35787172654729/100000000000000 : ℝ)^3559 := by
    have hnat : (180094333 : ℕ)^4583*100000000000000^3559 ≤ 35787172654729^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180094333 400000000 35787172654729 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020295341/10000000000 : ℝ)^4583 ≤ (7732760592267/25000000000000 : ℝ)^3559 := by
    have hnat : (4020295341 : ℕ)^4583*25000000000000^3559 ≤ 7732760592267^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020295341 10000000000 7732760592267 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255612783/10000000000 : ℝ), (180094333/400000000 : ℝ), (4020295341/10000000000 : ℝ)] ![(33281784967319/100000000000000 : ℝ), (35787172654729/100000000000000 : ℝ), (7732760592267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255612783/10000000000 : ℝ)|^4583 ≤ (33281784967319/100000000000000 : ℝ)^3559
        have hw : |(4255612783/10000000000 : ℝ)|=(4255612783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180094333/400000000 : ℝ)|^4583 ≤ (35787172654729/100000000000000 : ℝ)^3559
        have hw : |(180094333/400000000 : ℝ)|=(180094333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020295341/10000000000 : ℝ)|^4583 ≤ (7732760592267/25000000000000 : ℝ)^3559
        have hw : |(4020295341/10000000000 : ℝ)|=(4020295341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (1103/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (441/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (441/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (441/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (441/4000 : ℝ) ^ (4581/1024 : ℝ) ≤ (1039880586258811/20000000000000000000 : ℝ) := by
    have hpowers : (441/4000 : ℝ)^4581 ≤ (1039880586258811/20000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4581*20000000000000000000^1024 ≤ 1039880586258811^1024*4000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 4000 1039880586258811 20000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/4000 : ℝ)) (X := (1039880586258811/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4581/1024 : ℝ) ≤ (4760114963953539/20000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4581 ≤ (4760114963953539/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4581*20000000000000000000^1024 ≤ 4760114963953539^1024*10000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 4760114963953539 20000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (4760114963953539/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001039880586258811/10000000000000000000 : ℝ) ≤ (10000232437182639/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (10001039880586258811/10000000000000000000 : ℝ)^1024 ≤ (10000232437182639/10000000000000000 : ℝ)^4581 := by
      have hnat : (10001039880586258811 : ℕ)^1024*10000000000000000^4581 ≤ 10000232437182639^4581*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001039880586258811 10000000000000000000 10000232437182639 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000232437182639/10000000000000000 : ℝ)) (X := (10001039880586258811/10000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (400115999911004247/400000000000000000 : ℝ) ≤ (10000648169272803/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (400115999911004247/400000000000000000 : ℝ)^1024 ≤ (10000648169272803/10000000000000000 : ℝ)^4581 := by
      have hnat : (400115999911004247 : ℕ)^1024*10000000000000000^4581 ≤ 10000648169272803^4581*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400115999911004247 400000000000000000 10000648169272803 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000648169272803/10000000000000000 : ℝ)) (X := (400115999911004247/400000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004760114963953539/10000000000000000000 : ℝ) ≤ (10001063901362967/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (10004760114963953539/10000000000000000000 : ℝ)^1024 ≤ (10001063901362967/10000000000000000 : ℝ)^4581 := by
      have hnat : (10004760114963953539 : ℕ)^1024*10000000000000000^4581 ≤ 10001063901362967^4581*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004760114963953539 10000000000000000000 10001063901362967 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001063901362967/10000000000000000 : ℝ)) (X := (10004760114963953539/10000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1039880586258811/20000000000000000000 : ℝ) ≤ ((8928374187886473387/8930000000000000000 : ℝ)+2*(103933022541/111625000000000 : ℝ)*(441/4000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (8928374187886473387/8930000000000000000 : ℝ)+2*(103933022541/111625000000000 : ℝ)*(441/4000 : ℝ)=(10000232437182639/10000000000000000 : ℝ) by norm_num, show 1+2*(1039880586258811/20000000000000000000 : ℝ)=(10001039880586258811/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4760114963953539/20000000000000000000 : ℝ)+(1039880586258811/20000000000000000000 : ℝ) ≤ ((8928374187886473387/8930000000000000000 : ℝ)+(103933022541/111625000000000 : ℝ)*((1549/10000 : ℝ)+(441/4000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (8928374187886473387/8930000000000000000 : ℝ)+(103933022541/111625000000000 : ℝ)*((1549/10000 : ℝ)+(441/4000 : ℝ))=(10000648169272803/10000000000000000 : ℝ) by norm_num, show 1+(4760114963953539/20000000000000000000 : ℝ)+(1039880586258811/20000000000000000000 : ℝ)=(400115999911004247/400000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4760114963953539/20000000000000000000 : ℝ) ≤ ((8928374187886473387/8930000000000000000 : ℝ)+2*(103933022541/111625000000000 : ℝ)*(1549/10000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (8928374187886473387/8930000000000000000 : ℝ)+2*(103933022541/111625000000000 : ℝ)*(1549/10000 : ℝ)=(10001063901362967/10000000000000000 : ℝ) by norm_num, show 1+2*(4760114963953539/20000000000000000000 : ℝ)=(10004760114963953539/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8928374187886473387/8930000000000000000 : ℝ)*(X 1 0+X 2 0)+(103933022541/111625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8928374187886473387/8930000000000000000 : ℝ)) (alpha := (103933022541/111625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8928374187886473387/8930000000000000000 : ℝ)*(X 0 1+X 2 1)+(103933022541/111625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8928374187886473387/8930000000000000000 : ℝ)) (alpha := (103933022541/111625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8928374187886473387/8930000000000000000 : ℝ)*(X 0 2+X 1 2)+(103933022541/111625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (441/4000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8928374187886473387/8930000000000000000 : ℝ)) (alpha := (103933022541/111625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1823170803/10000000000 : ℝ)*X 0 0+(5429254169/10000000000 : ℝ)*X 0 1+(652378957/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069964221/2000000000 : ℝ)*X 1 0+(-96538589/500000000 : ℝ)*X 1 1+(2609515813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674910551/5000000000 : ℝ)*X 2 0+(5219031633/10000000000 : ℝ)*X 2 1+(-77230871/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4155809/9765625 : ℝ)*X 0 0+(803550609/2000000000 : ℝ)*X 0 1+(4504882023/10000000000 : ℝ)*X 0 2+(4155809/9765625 : ℝ)*X 1 0+(803550609/2000000000 : ℝ)*X 1 1+(4504882023/10000000000 : ℝ)*X 1 2+(4155809/9765625 : ℝ)*X 2 0+(803550609/2000000000 : ℝ)*X 2 1+(4504882023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1823198569/10000000000 : ℝ)*X 0 0+(5220120741/10000000000 : ℝ)*X 0 1+(5428157039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058878317/2000000000 : ℝ)*X 1 0+(-1721646369/10000000000 : ℝ)*X 1 1+(5428157021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294391539/10000000000 : ℝ)*X 2 0+(108563141/200000000 : ℝ)*X 2 1+(-215205799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4255612783/10000000000 : ℝ)*X 0 0+(180094333/400000000 : ℝ)*X 0 1+(4020295341/10000000000 : ℝ)*X 0 2+(4255612783/10000000000 : ℝ)*X 1 0+(180094333/400000000 : ℝ)*X 1 1+(4020295341/10000000000 : ℝ)*X 1 2+(4255612783/10000000000 : ℝ)*X 2 0+(180094333/400000000 : ℝ)*X 2 1+(4020295341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27990816412284662387889/5937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (806131449/100000000000000 : ℝ)*(base19) + (750377057/100000000000000 : ℝ)*(base23) + (5680107/20000000000000 : ℝ)*(lower2) + (114620511/100000000000000 : ℝ)*(upper3) + (40400143/50000000000000 : ℝ)*(upper5) + (2128045393339/62500000000 : ℝ)*(major0) + (2128045393339/62500000000 : ℝ)*(major1) + (2128045393339/62500000000 : ℝ)*(major2) + (2378438547061597/50000000000000 : ℝ)*(sp0) + (237844427710399/5000000000000 : ℝ)*(sp1) + (1189222152490593/25000000000000 : ℝ)*(sp2) + (20528497841469/1000000000000 : ℝ)*(sp3) + (2453243247/20000000000000 : ℝ)*(sp4) + (5957057037/100000000000000 : ℝ)*(sp7) + (64151741912623/3125000000000 : ℝ)*(f.failure) + (4756889360339429/100000000000000 : ℝ)*(f.sum) + (1952093283669/446500000000000000000000000 : ℝ)*base66 + (7278082843309557/558125000000000000000000000000 : ℝ)*base68 + (6270433531372057/558125000000000000000000000000 : ℝ)*base70 + (264788218118659/279062500000000000000000000000 : ℝ)*base71 + (7621877062481/893000000000000000000000000 : ℝ)*base74 + (266421620502701/17441406250000000000000000000 : ℝ)*base76 + (1741156577910091/279062500000000000000000000000 : ℝ)*base78 + (433862036860983/139531250000000000000000000000 : ℝ)*base80 + (3379773338037/893000000000000000000000000 : ℝ)*base82 + (1170969/312500000000000000000 : ℝ)*base90 + (1170969/312500000000000000000 : ℝ)*base92 + (1170969/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262888066990029994826154099/44650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477498463/50000000000000 : ℝ)*(base19) + (998987139/100000000000000 : ℝ)*(base23) + (74445289/25000000000000 : ℝ)*(lower1) + (130176121/100000000000000 : ℝ)*(upper3) + (41222129/100000000000000 : ℝ)*(lower4) + (30913439/25000000000000 : ℝ)*(upper5) + (344062472111341/10000000000000 : ℝ)*(major0) + (344062472111341/10000000000000 : ℝ)*(major1) + (344062472111341/10000000000000 : ℝ)*(major2) + (754012233/100000000000000 : ℝ)*(sp2) + (4806837959273699/100000000000000 : ℝ)*(sp4) + (4806837004276773/100000000000000 : ℝ)*(sp5) + (4806836206274327/100000000000000 : ℝ)*(sp6) + (414882257338947/20000000000000 : ℝ)*(sp7) + (414882257338947/20000000000000 : ℝ)*(f.failure) + (4806837959273699/100000000000000 : ℝ)*(f.sum) + (2031126228031/2232500000000000000000000000 : ℝ)*base66 + (3075317521319661967/89300000000000000000000000000000 : ℝ)*base67 + (1087049711683061967/89300000000000000000000000000000 : ℝ)*base69 + (4307947797507138033/89300000000000000000000000000000 : ℝ)*base72 + (11777709681911/2232500000000000000000000000 : ℝ)*base74 + (11221415396616538033/89300000000000000000000000000000 : ℝ)*base76 + (615241142602661967/89300000000000000000000000000000 : ℝ)*base77 + (1415290273735661967/89300000000000000000000000000000 : ℝ)*base79 + (5349107858377/1116250000000000000000000000 : ℝ)*base81 + (20912741/2000000000000000000000 : ℝ)*base90 + (20912741/2000000000000000000000 : ℝ)*base92 + (20912741/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1543_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1543_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1543_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1543_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1543_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:49.470138+00:00
-- url     : https://prove2.me/submissions/964208ec-c30a-4760-b0c7-139d955ee0c5

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
theorem support_rectangle_w1529_s0_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416987909/2500000000 : ℝ)*x 0 + (1179971777/2000000000 : ℝ)*x 1 + (2431260887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416987909/2500000000 : ℝ)^4555 ≤ (9922347947663/100000000000000 : ℝ)^3531 := by
    have hnat : (416987909 : ℕ)^4555*100000000000000^3531 ≤ 9922347947663^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416987909 2500000000 9922347947663 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1179971777/2000000000 : ℝ)^4555 ≤ (25313666290023/50000000000000 : ℝ)^3531 := by
    have hnat : (1179971777 : ℕ)^4555*50000000000000^3531 ≤ 25313666290023^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179971777 2000000000 25313666290023 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431260887/5000000000 : ℝ)^4555 ≤ (2465644966251/6250000000000 : ℝ)^3531 := by
    have hnat : (2431260887 : ℕ)^4555*6250000000000^3531 ≤ 2465644966251^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431260887 5000000000 2465644966251 6250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416987909/2500000000 : ℝ), (1179971777/2000000000 : ℝ), (2431260887/5000000000 : ℝ)] ![(9922347947663/100000000000000 : ℝ), (25313666290023/50000000000000 : ℝ), (2465644966251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416987909/2500000000 : ℝ)|^4555 ≤ (9922347947663/100000000000000 : ℝ)^3531
        have hw : |(-416987909/2500000000 : ℝ)|=(416987909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1179971777/2000000000 : ℝ)|^4555 ≤ (25313666290023/50000000000000 : ℝ)^3531
        have hw : |(1179971777/2000000000 : ℝ)|=(1179971777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2431260887/5000000000 : ℝ)|^4555 ≤ (2465644966251/6250000000000 : ℝ)^3531
        have hw : |(2431260887/5000000000 : ℝ)|=(2431260887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6842863/12500000 : ℝ)*x 0 + (-35127169/156250000 : ℝ)*x 1 + (4862521679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6842863/12500000 : ℝ)^4555 ≤ (45966576797857/100000000000000 : ℝ)^3531 := by
    have hnat : (6842863 : ℕ)^4555*100000000000000^3531 ≤ 45966576797857^3531*12500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6842863 12500000 45966576797857 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35127169/156250000 : ℝ)^4555 ≤ (7291552360487/50000000000000 : ℝ)^3531 := by
    have hnat : (35127169 : ℕ)^4555*50000000000000^3531 ≤ 7291552360487^3531*156250000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35127169 156250000 7291552360487 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862521679/10000000000 : ℝ)^4555 ≤ (39450318465749/100000000000000 : ℝ)^3531 := by
    have hnat : (4862521679 : ℕ)^4555*100000000000000^3531 ≤ 39450318465749^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862521679 10000000000 39450318465749 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6842863/12500000 : ℝ), (-35127169/156250000 : ℝ), (4862521679/10000000000 : ℝ)] ![(45966576797857/100000000000000 : ℝ), (7291552360487/50000000000000 : ℝ), (39450318465749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6842863/12500000 : ℝ)|^4555 ≤ (45966576797857/100000000000000 : ℝ)^3531
        have hw : |(6842863/12500000 : ℝ)|=(6842863/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35127169/156250000 : ℝ)|^4555 ≤ (7291552360487/50000000000000 : ℝ)^3531
        have hw : |(-35127169/156250000 : ℝ)|=(35127169/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862521679/10000000000 : ℝ)|^4555 ≤ (39450318465749/100000000000000 : ℝ)^3531
        have hw : |(4862521679/10000000000 : ℝ)|=(4862521679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5474290559/10000000000 : ℝ)*x 0 + (486252177/1000000000 : ℝ)*x 1 + (-8781791/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5474290559/10000000000 : ℝ)^4555 ≤ (4596657852013/10000000000000 : ℝ)^3531 := by
    have hnat : (5474290559 : ℕ)^4555*10000000000000^3531 ≤ 4596657852013^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474290559 10000000000 4596657852013 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486252177/1000000000 : ℝ)^4555 ≤ (4931289927269/12500000000000 : ℝ)^3531 := by
    have hnat : (486252177 : ℕ)^4555*12500000000000^3531 ≤ 4931289927269^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486252177 1000000000 4931289927269 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8781791/39062500 : ℝ)^4555 ≤ (14583102043239/100000000000000 : ℝ)^3531 := by
    have hnat : (8781791 : ℕ)^4555*100000000000000^3531 ≤ 14583102043239^3531*39062500^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8781791 39062500 14583102043239 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5474290559/10000000000 : ℝ), (486252177/1000000000 : ℝ), (-8781791/39062500 : ℝ)] ![(4596657852013/10000000000000 : ℝ), (4931289927269/12500000000000 : ℝ), (14583102043239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5474290559/10000000000 : ℝ)|^4555 ≤ (4596657852013/10000000000000 : ℝ)^3531
        have hw : |(5474290559/10000000000 : ℝ)|=(5474290559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486252177/1000000000 : ℝ)|^4555 ≤ (4931289927269/12500000000000 : ℝ)^3531
        have hw : |(486252177/1000000000 : ℝ)|=(486252177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8781791/39062500 : ℝ)|^4555 ≤ (14583102043239/100000000000000 : ℝ)^3531
        have hw : |(-8781791/39062500 : ℝ)|=(8781791/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070295401/5000000000 : ℝ)*x 0 + (3091534431/10000000000 : ℝ)*x 1 + (683998773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070295401/5000000000 : ℝ)^4555 ≤ (4007922474243/12500000000000 : ℝ)^3531 := by
    have hnat : (2070295401 : ℕ)^4555*12500000000000^3531 ≤ 4007922474243^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070295401 5000000000 4007922474243 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091534431/10000000000 : ℝ)^4555 ≤ (5498739401693/25000000000000 : ℝ)^3531 := by
    have hnat : (3091534431 : ℕ)^4555*25000000000000^3531 ≤ 5498739401693^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091534431 10000000000 5498739401693 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683998773/1250000000 : ℝ)^4555 ≤ (45941662586173/100000000000000 : ℝ)^3531 := by
    have hnat : (683998773 : ℕ)^4555*100000000000000^3531 ≤ 45941662586173^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683998773 1250000000 45941662586173 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070295401/5000000000 : ℝ), (3091534431/10000000000 : ℝ), (683998773/1250000000 : ℝ)] ![(4007922474243/12500000000000 : ℝ), (5498739401693/25000000000000 : ℝ), (45941662586173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070295401/5000000000 : ℝ)|^4555 ≤ (4007922474243/12500000000000 : ℝ)^3531
        have hw : |(2070295401/5000000000 : ℝ)|=(2070295401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091534431/10000000000 : ℝ)|^4555 ≤ (5498739401693/25000000000000 : ℝ)^3531
        have hw : |(3091534431/10000000000 : ℝ)|=(3091534431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683998773/1250000000 : ℝ)|^4555 ≤ (45941662586173/100000000000000 : ℝ)^3531
        have hw : |(683998773/1250000000 : ℝ)|=(683998773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1671329223/10000000000 : ℝ)*x 0 + (4888893717/10000000000 : ℝ)*x 1 + (1174509001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1671329223/10000000000 : ℝ)^4555 ≤ (4974137574719/50000000000000 : ℝ)^3531 := by
    have hnat : (1671329223 : ℕ)^4555*50000000000000^3531 ≤ 4974137574719^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671329223 10000000000 4974137574719 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4888893717/10000000000 : ℝ)^4555 ≤ (39726544294933/100000000000000 : ℝ)^3531 := by
    have hnat : (4888893717 : ℕ)^4555*100000000000000^3531 ≤ 39726544294933^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888893717 10000000000 39726544294933 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174509001/2000000000 : ℝ)^4555 ≤ (12581295136097/25000000000000 : ℝ)^3531 := by
    have hnat : (1174509001 : ℕ)^4555*25000000000000^3531 ≤ 12581295136097^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174509001 2000000000 12581295136097 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1671329223/10000000000 : ℝ), (4888893717/10000000000 : ℝ), (1174509001/2000000000 : ℝ)] ![(4974137574719/50000000000000 : ℝ), (39726544294933/100000000000000 : ℝ), (12581295136097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1671329223/10000000000 : ℝ)|^4555 ≤ (4974137574719/50000000000000 : ℝ)^3531
        have hw : |(-1671329223/10000000000 : ℝ)|=(1671329223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4888893717/10000000000 : ℝ)|^4555 ≤ (39726544294933/100000000000000 : ℝ)^3531
        have hw : |(4888893717/10000000000 : ℝ)|=(4888893717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174509001/2000000000 : ℝ)|^4555 ≤ (12581295136097/25000000000000 : ℝ)^3531
        have hw : |(1174509001/2000000000 : ℝ)|=(1174509001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81106407/156250000 : ℝ)*x 0 + (-619057837/5000000000 : ℝ)*x 1 + (1174509013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81106407/156250000 : ℝ)^4555 ≤ (5364911136777/12500000000000 : ℝ)^3531 := by
    have hnat : (81106407 : ℕ)^4555*12500000000000^3531 ≤ 5364911136777^3531*156250000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81106407 156250000 5364911136777 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619057837/5000000000 : ℝ)^4555 ≤ (1351105936479/20000000000000 : ℝ)^3531 := by
    have hnat : (619057837 : ℕ)^4555*20000000000000^3531 ≤ 1351105936479^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619057837 5000000000 1351105936479 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174509013/2000000000 : ℝ)^4555 ≤ (25162590603837/50000000000000 : ℝ)^3531 := by
    have hnat : (1174509013 : ℕ)^4555*50000000000000^3531 ≤ 25162590603837^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174509013 2000000000 25162590603837 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81106407/156250000 : ℝ), (-619057837/5000000000 : ℝ), (1174509013/2000000000 : ℝ)] ![(5364911136777/12500000000000 : ℝ), (1351105936479/20000000000000 : ℝ), (25162590603837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81106407/156250000 : ℝ)|^4555 ≤ (5364911136777/12500000000000 : ℝ)^3531
        have hw : |(81106407/156250000 : ℝ)|=(81106407/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-619057837/5000000000 : ℝ)|^4555 ≤ (1351105936479/20000000000000 : ℝ)^3531
        have hw : |(-619057837/5000000000 : ℝ)|=(619057837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174509013/2000000000 : ℝ)|^4555 ≤ (25162590603837/50000000000000 : ℝ)^3531
        have hw : |(1174509013/2000000000 : ℝ)|=(1174509013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038162001/2000000000 : ℝ)*x 0 + (5872545307/10000000000 : ℝ)*x 1 + (-1238115359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038162001/2000000000 : ℝ)^4555 ≤ (42919288635571/100000000000000 : ℝ)^3531 := by
    have hnat : (1038162001 : ℕ)^4555*100000000000000^3531 ≤ 42919288635571^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038162001 2000000000 42919288635571 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5872545307/10000000000 : ℝ)^4555 ≤ (3145323992683/6250000000000 : ℝ)^3531 := by
    have hnat : (5872545307 : ℕ)^4555*6250000000000^3531 ≤ 3145323992683^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872545307 10000000000 3145323992683 6250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1238115359/10000000000 : ℝ)^4555 ≤ (6755527465223/100000000000000 : ℝ)^3531 := by
    have hnat : (1238115359 : ℕ)^4555*100000000000000^3531 ≤ 6755527465223^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238115359 10000000000 6755527465223 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038162001/2000000000 : ℝ), (5872545307/10000000000 : ℝ), (-1238115359/10000000000 : ℝ)] ![(42919288635571/100000000000000 : ℝ), (3145323992683/6250000000000 : ℝ), (6755527465223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038162001/2000000000 : ℝ)|^4555 ≤ (42919288635571/100000000000000 : ℝ)^3531
        have hw : |(1038162001/2000000000 : ℝ)|=(1038162001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5872545307/10000000000 : ℝ)|^4555 ≤ (3145323992683/6250000000000 : ℝ)^3531
        have hw : |(5872545307/10000000000 : ℝ)|=(5872545307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1238115359/10000000000 : ℝ)|^4555 ≤ (6755527465223/100000000000000 : ℝ)^3531
        have hw : |(-1238115359/10000000000 : ℝ)|=(1238115359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s0_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074170687/5000000000 : ℝ)*x 0 + (5411472553/10000000000 : ℝ)*x 1 + (630842763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074170687/5000000000 : ℝ)^4555 ≤ (16070412025127/50000000000000 : ℝ)^3531 := by
    have hnat : (2074170687 : ℕ)^4555*50000000000000^3531 ≤ 16070412025127^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074170687 5000000000 16070412025127 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411472553/10000000000 : ℝ)^4555 ≤ (2264363743967/5000000000000 : ℝ)^3531 := by
    have hnat : (5411472553 : ℕ)^4555*5000000000000^3531 ≤ 2264363743967^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411472553 10000000000 2264363743967 5000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630842763/2000000000 : ℝ)^4555 ≤ (22571901060307/100000000000000 : ℝ)^3531 := by
    have hnat : (630842763 : ℕ)^4555*100000000000000^3531 ≤ 22571901060307^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630842763 2000000000 22571901060307 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074170687/5000000000 : ℝ), (5411472553/10000000000 : ℝ), (630842763/2000000000 : ℝ)] ![(16070412025127/50000000000000 : ℝ), (2264363743967/5000000000000 : ℝ), (22571901060307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074170687/5000000000 : ℝ)|^4555 ≤ (16070412025127/50000000000000 : ℝ)^3531
        have hw : |(2074170687/5000000000 : ℝ)|=(2074170687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411472553/10000000000 : ℝ)|^4555 ≤ (2264363743967/5000000000000 : ℝ)^3531
        have hw : |(5411472553/10000000000 : ℝ)|=(5411472553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630842763/2000000000 : ℝ)|^4555 ≤ (22571901060307/100000000000000 : ℝ)^3531
        have hw : |(630842763/2000000000 : ℝ)|=(630842763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (761/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12633/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4553/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4553 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4553*1^1024 ≤ 0^1024*1^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4553/1024 : ℝ) ≤ (1700762579716830513/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4553 ≤ (1700762579716830513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4553*100000000000000000000^1024 ≤ 1700762579716830513^1024*5^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1700762579716830513 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1700762579716830513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4553 := by
      have hnat : (1 : ℕ)^1024*1^4553 ≤ 1^4553*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101700762579716830513/100000000000000000000 : ℝ) ≤ (1254750208275811/1250000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (101700762579716830513/100000000000000000000 : ℝ)^1024 ≤ (1254750208275811/1250000000000000 : ℝ)^4553 := by
      have hnat : (101700762579716830513 : ℕ)^1024*1250000000000000^4553 ≤ 1254750208275811^4553*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101700762579716830513 100000000000000000000 1254750208275811 1250000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254750208275811/1250000000000000 : ℝ)) (X := (101700762579716830513/100000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51700762579716830513/50000000000000000000 : ℝ) ≤ (629750208275811/625000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (51700762579716830513/50000000000000000000 : ℝ)^1024 ≤ (629750208275811/625000000000000 : ℝ)^4553 := by
      have hnat : (51700762579716830513 : ℕ)^1024*625000000000000^4553 ≤ 629750208275811^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51700762579716830513 50000000000000000000 629750208275811 625000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629750208275811/625000000000000 : ℝ)) (X := (51700762579716830513/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4750208275811/500000000000000 : ℝ)*(0 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4750208275811/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1700762579716830513/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4750208275811/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4750208275811/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254750208275811/1250000000000000 : ℝ) by norm_num, show 1+(1700762579716830513/100000000000000000000 : ℝ)+(0 : ℝ)=(101700762579716830513/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1700762579716830513/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4750208275811/500000000000000 : ℝ)*(2/5 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4750208275811/500000000000000 : ℝ)*(2/5 : ℝ)=(629750208275811/625000000000000 : ℝ) by norm_num, show 1+2*(1700762579716830513/100000000000000000000 : ℝ)=(51700762579716830513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4750208275811/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4750208275811/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4750208275811/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4750208275811/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4750208275811/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4750208275811/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416987909/2500000000 : ℝ)*X 0 0+(1179971777/2000000000 : ℝ)*X 0 1+(2431260887/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6842863/12500000 : ℝ)*X 1 0+(-35127169/156250000 : ℝ)*X 1 1+(4862521679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5474290559/10000000000 : ℝ)*X 2 0+(486252177/1000000000 : ℝ)*X 2 1+(-8781791/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2070295401/5000000000 : ℝ)*X 0 0+(3091534431/10000000000 : ℝ)*X 0 1+(683998773/1250000000 : ℝ)*X 0 2+(2070295401/5000000000 : ℝ)*X 1 0+(3091534431/10000000000 : ℝ)*X 1 1+(683998773/1250000000 : ℝ)*X 1 2+(2070295401/5000000000 : ℝ)*X 2 0+(3091534431/10000000000 : ℝ)*X 2 1+(683998773/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1671329223/10000000000 : ℝ)*X 0 0+(4888893717/10000000000 : ℝ)*X 0 1+(1174509001/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((81106407/156250000 : ℝ)*X 1 0+(-619057837/5000000000 : ℝ)*X 1 1+(1174509013/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038162001/2000000000 : ℝ)*X 2 0+(5872545307/10000000000 : ℝ)*X 2 1+(-1238115359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2074170687/5000000000 : ℝ)*X 0 0+(5411472553/10000000000 : ℝ)*X 0 1+(630842763/2000000000 : ℝ)*X 0 2+(2074170687/5000000000 : ℝ)*X 1 0+(5411472553/10000000000 : ℝ)*X 1 1+(630842763/2000000000 : ℝ)*X 1 2+(2074170687/5000000000 : ℝ)*X 2 0+(5411472553/10000000000 : ℝ)*X 2 1+(630842763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17863709658597090163239/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (791865059/100000000000000 : ℝ)*(base19) + (804050513/100000000000000 : ℝ)*(base23) + (63788247/100000000000000 : ℝ)*(upper3) + (1731423/20000000000000 : ℝ)*(upper4) + (6023759/4000000000000 : ℝ)*(upper5) + (346025709497567/50000000000000 : ℝ)*(major0) + (346025709497567/50000000000000 : ℝ)*(major1) + (346025709497567/50000000000000 : ℝ)*(major2) + (4820046073823/500000000000 : ℝ)*(sp0) + (15062683257699/1562500000000 : ℝ)*(sp1) + (482005858153641/50000000000000 : ℝ)*(sp2) + (105022250783697/25000000000000 : ℝ)*(sp3) + (661118639/20000000000000 : ℝ)*(sp4) + (609612281/50000000000000 : ℝ)*(sp7) + (8401804447187/2000000000000 : ℝ)*(f.failure) + (192802504071559/20000000000000 : ℝ)*(f.sum) + (47072894035663/12500000000000000000000000000 : ℝ)*base66 + (222474688726837/25000000000000000000000000000 : ℝ)*base67 + (19299009526837/25000000000000000000000000000 : ℝ)*base69 + (9326605351837/25000000000000000000000000000 : ℝ)*base71 + (37372521476837/12500000000000000000000000000 : ℝ)*base73 + (140539450301837/25000000000000000000000000000 : ℝ)*base75 + (33301199401837/25000000000000000000000000000 : ℝ)*base77 + (166284630601837/25000000000000000000000000000 : ℝ)*base79 + (41585294923163/12500000000000000000000000000 : ℝ)*base82 + (579067/200000000000000000000 : ℝ)*base90 + (579067/200000000000000000000 : ℝ)*base92 + (579067/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337219487343307512933/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (752703103/50000000000000 : ℝ)*(base19) + (758967017/50000000000000 : ℝ)*(base23) + (123633/3125000000000 : ℝ)*(base32) + (7020891/3125000000000 : ℝ)*(upper3) + (201099079/100000000000000 : ℝ)*(upper5) + (1459635809501/200000000000 : ℝ)*(major0) + (1459635809501/200000000000 : ℝ)*(major1) + (1459635809501/200000000000 : ℝ)*(major2) + (498479593/12500000000000 : ℝ)*(sp1) + (4371437593/100000000000000 : ℝ)*(sp2) + (15884691973381/1562500000000 : ℝ)*(sp4) + (203322958610687/20000000000000 : ℝ)*(sp5) + (508307198462379/50000000000000 : ℝ)*(sp6) + (443015294435363/100000000000000 : ℝ)*(sp7) + (443015298391619/100000000000000 : ℝ)*(f.failure) + (15884691973381/1562500000000 : ℝ)*(f.sum) + (25696676189/50000000000000000000000000 : ℝ)*base66 + (194011173611/100000000000000000000000000 : ℝ)*base67 + (102327896189/100000000000000000000000000 : ℝ)*base70 + (636235843889/100000000000000000000000000 : ℝ)*base72 + (225632458061/50000000000000000000000000 : ℝ)*base73 + (721783849289/100000000000000000000000000 : ℝ)*base76 + (1059317423589/100000000000000000000000000 : ℝ)*base78 + (10637925189/100000000000000000000000000 : ℝ)*base80 + (55107200561/50000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10060821/10000000000000000000000 : ℝ)*base89 + (10060821/10000000000000000000000 : ℝ)*base91 + (10060821/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1529_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (761/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12633/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1529_s1_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817142339/10000000000 : ℝ)*x 0 + (5559464297/10000000000 : ℝ)*x 1 + (5106954003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817142339/10000000000 : ℝ)^4555 ≤ (2216356615739/20000000000000 : ℝ)^3531 := by
    have hnat : (1817142339 : ℕ)^4555*20000000000000^3531 ≤ 2216356615739^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817142339 10000000000 2216356615739 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5559464297/10000000000 : ℝ)^4555 ≤ (11722811624957/25000000000000 : ℝ)^3531 := by
    have hnat : (5559464297 : ℕ)^4555*25000000000000^3531 ≤ 11722811624957^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559464297 10000000000 11722811624957 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5106954003/10000000000 : ℝ)^4555 ≤ (21013485204383/50000000000000 : ℝ)^3531 := by
    have hnat : (5106954003 : ℕ)^4555*50000000000000^3531 ≤ 21013485204383^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106954003 10000000000 21013485204383 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817142339/10000000000 : ℝ), (5559464297/10000000000 : ℝ), (5106954003/10000000000 : ℝ)] ![(2216356615739/20000000000000 : ℝ), (11722811624957/25000000000000 : ℝ), (21013485204383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817142339/10000000000 : ℝ)|^4555 ≤ (2216356615739/20000000000000 : ℝ)^3531
        have hw : |(-1817142339/10000000000 : ℝ)|=(1817142339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5559464297/10000000000 : ℝ)|^4555 ≤ (11722811624957/25000000000000 : ℝ)^3531
        have hw : |(5559464297/10000000000 : ℝ)|=(5559464297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5106954003/10000000000 : ℝ)|^4555 ≤ (21013485204383/50000000000000 : ℝ)^3531
        have hw : |(5106954003/10000000000 : ℝ)|=(5106954003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383559391/10000000000 : ℝ)*x 0 + (-1027462901/5000000000 : ℝ)*x 1 + (2553476247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383559391/10000000000 : ℝ)^4555 ≤ (22493079006123/50000000000000 : ℝ)^3531 := by
    have hnat : (5383559391 : ℕ)^4555*50000000000000^3531 ≤ 22493079006123^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383559391 10000000000 22493079006123 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027462901/5000000000 : ℝ)^4555 ≤ (3246721895501/25000000000000 : ℝ)^3531 := by
    have hnat : (1027462901 : ℕ)^4555*25000000000000^3531 ≤ 3246721895501^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027462901 5000000000 3246721895501 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2553476247/5000000000 : ℝ)^4555 ≤ (21013477194687/50000000000000 : ℝ)^3531 := by
    have hnat : (2553476247 : ℕ)^4555*50000000000000^3531 ≤ 21013477194687^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553476247 5000000000 21013477194687 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383559391/10000000000 : ℝ), (-1027462901/5000000000 : ℝ), (2553476247/5000000000 : ℝ)] ![(22493079006123/50000000000000 : ℝ), (3246721895501/25000000000000 : ℝ), (21013477194687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383559391/10000000000 : ℝ)|^4555 ≤ (22493079006123/50000000000000 : ℝ)^3531
        have hw : |(5383559391/10000000000 : ℝ)|=(5383559391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1027462901/5000000000 : ℝ)|^4555 ≤ (3246721895501/25000000000000 : ℝ)^3531
        have hw : |(-1027462901/5000000000 : ℝ)|=(1027462901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2553476247/5000000000 : ℝ)|^4555 ≤ (21013477194687/50000000000000 : ℝ)^3531
        have hw : |(2553476247/5000000000 : ℝ)|=(2553476247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076711663/2000000000 : ℝ)*x 0 + (2553476971/5000000000 : ℝ)*x 1 + (-2054925339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076711663/2000000000 : ℝ)^4555 ≤ (8997229282693/20000000000000 : ℝ)^3531 := by
    have hnat : (1076711663 : ℕ)^4555*20000000000000^3531 ≤ 8997229282693^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076711663 2000000000 8997229282693 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2553476971/5000000000 : ℝ)^4555 ≤ (10506742440299/25000000000000 : ℝ)^3531 := by
    have hnat : (2553476971 : ℕ)^4555*25000000000000^3531 ≤ 10506742440299^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553476971 5000000000 10506742440299 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054925339/10000000000 : ℝ)^4555 ≤ (324672095183/2500000000000 : ℝ)^3531 := by
    have hnat : (2054925339 : ℕ)^4555*2500000000000^3531 ≤ 324672095183^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054925339 10000000000 324672095183 2500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076711663/2000000000 : ℝ), (2553476971/5000000000 : ℝ), (-2054925339/10000000000 : ℝ)] ![(8997229282693/20000000000000 : ℝ), (10506742440299/25000000000000 : ℝ), (324672095183/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076711663/2000000000 : ℝ)|^4555 ≤ (8997229282693/20000000000000 : ℝ)^3531
        have hw : |(1076711663/2000000000 : ℝ)|=(1076711663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2553476971/5000000000 : ℝ)|^4555 ≤ (10506742440299/25000000000000 : ℝ)^3531
        have hw : |(2553476971/5000000000 : ℝ)|=(2553476971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054925339/10000000000 : ℝ)|^4555 ≤ (324672095183/2500000000000 : ℝ)^3531
        have hw : |(-2054925339/10000000000 : ℝ)|=(2054925339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121704737/5000000000 : ℝ)*x 0 + (750131191/2000000000 : ℝ)*x 1 + (4789068023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121704737/5000000000 : ℝ)^4555 ≤ (16547074596199/50000000000000 : ℝ)^3531 := by
    have hnat : (2121704737 : ℕ)^4555*50000000000000^3531 ≤ 16547074596199^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121704737 5000000000 16547074596199 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750131191/2000000000 : ℝ)^4555 ≤ (7055651592457/25000000000000 : ℝ)^3531 := by
    have hnat : (750131191 : ℕ)^4555*25000000000000^3531 ≤ 7055651592457^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750131191 2000000000 7055651592457 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789068023/10000000000 : ℝ)^4555 ≤ (3868324441859/10000000000000 : ℝ)^3531 := by
    have hnat : (4789068023 : ℕ)^4555*10000000000000^3531 ≤ 3868324441859^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789068023 10000000000 3868324441859 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121704737/5000000000 : ℝ), (750131191/2000000000 : ℝ), (4789068023/10000000000 : ℝ)] ![(16547074596199/50000000000000 : ℝ), (7055651592457/25000000000000 : ℝ), (3868324441859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121704737/5000000000 : ℝ)|^4555 ≤ (16547074596199/50000000000000 : ℝ)^3531
        have hw : |(2121704737/5000000000 : ℝ)|=(2121704737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750131191/2000000000 : ℝ)|^4555 ≤ (7055651592457/25000000000000 : ℝ)^3531
        have hw : |(750131191/2000000000 : ℝ)|=(750131191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789068023/10000000000 : ℝ)|^4555 ≤ (3868324441859/10000000000000 : ℝ)^3531
        have hw : |(4789068023/10000000000 : ℝ)|=(4789068023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-28397089/156250000 : ℝ)*x 0 + (5111894843/10000000000 : ℝ)*x 1 + (4339411/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28397089/156250000 : ℝ)^4555 ≤ (2216783580261/20000000000000 : ℝ)^3531 := by
    have hnat : (28397089 : ℕ)^4555*20000000000000^3531 ≤ 2216783580261^3531*156250000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28397089 156250000 2216783580261 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5111894843/10000000000 : ℝ)^4555 ≤ (10519857306627/25000000000000 : ℝ)^3531 := by
    have hnat : (5111894843 : ℕ)^4555*25000000000000^3531 ≤ 10519857306627^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111894843 10000000000 10519857306627 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4339411/7812500 : ℝ)^4555 ≤ (23418326428453/50000000000000 : ℝ)^3531 := by
    have hnat : (4339411 : ℕ)^4555*50000000000000^3531 ≤ 23418326428453^3531*7812500^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339411 7812500 23418326428453 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28397089/156250000 : ℝ), (5111894843/10000000000 : ℝ), (4339411/7812500 : ℝ)] ![(2216783580261/20000000000000 : ℝ), (10519857306627/25000000000000 : ℝ), (23418326428453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28397089/156250000 : ℝ)|^4555 ≤ (2216783580261/20000000000000 : ℝ)^3531
        have hw : |(-28397089/156250000 : ℝ)|=(28397089/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5111894843/10000000000 : ℝ)|^4555 ≤ (10519857306627/25000000000000 : ℝ)^3531
        have hw : |(5111894843/10000000000 : ℝ)|=(5111894843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4339411/7812500 : ℝ)|^4555 ≤ (23418326428453/50000000000000 : ℝ)^3531
        have hw : |(4339411/7812500 : ℝ)|=(4339411/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264132409/10000000000 : ℝ)*x 0 + (-1607432917/10000000000 : ℝ)*x 1 + (5554446213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264132409/10000000000 : ℝ)^4555 ≤ (1092573838907/2500000000000 : ℝ)^3531 := by
    have hnat : (5264132409 : ℕ)^4555*2500000000000^3531 ≤ 1092573838907^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264132409 10000000000 1092573838907 2500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1607432917/10000000000 : ℝ)^4555 ≤ (75683137013/800000000000 : ℝ)^3531 := by
    have hnat : (1607432917 : ℕ)^4555*800000000000^3531 ≤ 75683137013^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607432917 10000000000 75683137013 800000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5554446213/10000000000 : ℝ)^4555 ≤ (11709163575909/25000000000000 : ℝ)^3531 := by
    have hnat : (5554446213 : ℕ)^4555*25000000000000^3531 ≤ 11709163575909^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554446213 10000000000 11709163575909 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264132409/10000000000 : ℝ), (-1607432917/10000000000 : ℝ), (5554446213/10000000000 : ℝ)] ![(1092573838907/2500000000000 : ℝ), (75683137013/800000000000 : ℝ), (11709163575909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264132409/10000000000 : ℝ)|^4555 ≤ (1092573838907/2500000000000 : ℝ)^3531
        have hw : |(5264132409/10000000000 : ℝ)|=(5264132409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1607432917/10000000000 : ℝ)|^4555 ≤ (75683137013/800000000000 : ℝ)^3531
        have hw : |(-1607432917/10000000000 : ℝ)|=(1607432917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5554446213/10000000000 : ℝ)|^4555 ≤ (11709163575909/25000000000000 : ℝ)^3531
        have hw : |(5554446213/10000000000 : ℝ)|=(5554446213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632066113/5000000000 : ℝ)*x 0 + (5554446337/10000000000 : ℝ)*x 1 + (-803716499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632066113/5000000000 : ℝ)^4555 ≤ (43702951596417/100000000000000 : ℝ)^3531 := by
    have hnat : (2632066113 : ℕ)^4555*100000000000000^3531 ≤ 43702951596417^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632066113 5000000000 43702951596417 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5554446337/10000000000 : ℝ)^4555 ≤ (46836655652467/100000000000000 : ℝ)^3531 := by
    have hnat : (5554446337 : ℕ)^4555*100000000000000^3531 ≤ 46836655652467^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554446337 10000000000 46836655652467 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803716499/5000000000 : ℝ)^4555 ≤ (1182549092699/12500000000000 : ℝ)^3531 := by
    have hnat : (803716499 : ℕ)^4555*12500000000000^3531 ≤ 1182549092699^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803716499 5000000000 1182549092699 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632066113/5000000000 : ℝ), (5554446337/10000000000 : ℝ), (-803716499/5000000000 : ℝ)] ![(43702951596417/100000000000000 : ℝ), (46836655652467/100000000000000 : ℝ), (1182549092699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632066113/5000000000 : ℝ)|^4555 ≤ (43702951596417/100000000000000 : ℝ)^3531
        have hw : |(2632066113/5000000000 : ℝ)|=(2632066113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5554446337/10000000000 : ℝ)|^4555 ≤ (46836655652467/100000000000000 : ℝ)^3531
        have hw : |(5554446337/10000000000 : ℝ)|=(5554446337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-803716499/5000000000 : ℝ)|^4555 ≤ (1182549092699/12500000000000 : ℝ)^3531
        have hw : |(-803716499/5000000000 : ℝ)|=(803716499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s1_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244031593/10000000000 : ℝ)*x 0 + (95554591/200000000 : ℝ)*x 1 + (940543283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244031593/10000000000 : ℝ)^4555 ≤ (8275102064991/25000000000000 : ℝ)^3531 := by
    have hnat : (4244031593 : ℕ)^4555*25000000000000^3531 ≤ 8275102064991^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244031593 10000000000 8275102064991 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95554591/200000000 : ℝ)^4555 ≤ (38565139518423/100000000000000 : ℝ)^3531 := by
    have hnat : (95554591 : ℕ)^4555*100000000000000^3531 ≤ 38565139518423^3531*200000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95554591 200000000 38565139518423 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940543283/2500000000 : ℝ)^4555 ≤ (14167226098351/50000000000000 : ℝ)^3531 := by
    have hnat : (940543283 : ℕ)^4555*50000000000000^3531 ≤ 14167226098351^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940543283 2500000000 14167226098351 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244031593/10000000000 : ℝ), (95554591/200000000 : ℝ), (940543283/2500000000 : ℝ)] ![(8275102064991/25000000000000 : ℝ), (38565139518423/100000000000000 : ℝ), (14167226098351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244031593/10000000000 : ℝ)|^4555 ≤ (8275102064991/25000000000000 : ℝ)^3531
        have hw : |(4244031593/10000000000 : ℝ)|=(4244031593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95554591/200000000 : ℝ)|^4555 ≤ (38565139518423/100000000000000 : ℝ)^3531
        have hw : |(95554591/200000000 : ℝ)|=(95554591/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940543283/2500000000 : ℝ)|^4555 ≤ (14167226098351/50000000000000 : ℝ)^3531
        have hw : |(940543283/2500000000 : ℝ)|=(940543283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (761/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4289/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18153/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12633/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (761/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12633/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (761/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12633/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (761/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12633/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (761/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12633/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (761/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12633/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (761/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (761/25000 : ℝ) ^ (4553/1024 : ℝ) ≤ (18069932329499/100000000000000000000 : ℝ) := by
    have hpowers : (761/25000 : ℝ)^4553 ≤ (18069932329499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (761 : ℕ)^4553*100000000000000000000^1024 ≤ 18069932329499^1024*25000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        761 25000 18069932329499 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (761/25000 : ℝ)) (X := (18069932329499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12633/50000 : ℝ) ^ (4553/1024 : ℝ) ≤ (110274359152105339/50000000000000000000 : ℝ) := by
    have hpowers : (12633/50000 : ℝ)^4553 ≤ (110274359152105339/50000000000000000000 : ℝ)^1024 := by
      have hnat : (12633 : ℕ)^4553*50000000000000000000^1024 ≤ 110274359152105339^1024*50000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12633 50000 110274359152105339 50000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12633/50000 : ℝ)) (X := (110274359152105339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000018069932329499/50000000000000000000 : ℝ) ≤ (5000000406404747/5000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50000018069932329499/50000000000000000000 : ℝ)^1024 ≤ (5000000406404747/5000000000000000 : ℝ)^4553 := by
      have hnat : (50000018069932329499 : ℕ)^1024*5000000000000000^4553 ≤ 5000000406404747^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000018069932329499 50000000000000000000 5000000406404747 5000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000406404747/5000000000000000 : ℝ)) (X := (50000018069932329499/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100220566788236540177/100000000000000000000 : ℝ) ≤ (10004956458981859/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (100220566788236540177/100000000000000000000 : ℝ)^1024 ≤ (10004956458981859/10000000000000000 : ℝ)^4553 := by
      have hnat : (100220566788236540177 : ℕ)^1024*10000000000000000^4553 ≤ 10004956458981859^4553*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100220566788236540177 100000000000000000000 10004956458981859 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004956458981859/10000000000000000 : ℝ)) (X := (100220566788236540177/100000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25110274359152105339/25000000000000000000 : ℝ) ≤ (625619506572139/625000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (25110274359152105339/25000000000000000000 : ℝ)^1024 ≤ (625619506572139/625000000000000 : ℝ)^4553 := by
      have hnat : (25110274359152105339 : ℕ)^1024*625000000000000^4553 ≤ 625619506572139^4553*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25110274359152105339 25000000000000000000 625619506572139 625000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625619506572139/625000000000000 : ℝ)) (X := (25110274359152105339/25000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18069932329499/100000000000000000000 : ℝ) ≤ ((55547462022088804387/55555000000000000000 : ℝ)+2*(991129234473/444440000000000 : ℝ)*(761/25000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (55547462022088804387/55555000000000000000 : ℝ)+2*(991129234473/444440000000000 : ℝ)*(761/25000 : ℝ)=(5000000406404747/5000000000000000 : ℝ) by norm_num, show 1+2*(18069932329499/100000000000000000000 : ℝ)=(50000018069932329499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(110274359152105339/50000000000000000000 : ℝ)+(18069932329499/100000000000000000000 : ℝ) ≤ ((55547462022088804387/55555000000000000000 : ℝ)+(991129234473/444440000000000 : ℝ)*((12633/50000 : ℝ)+(761/25000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (55547462022088804387/55555000000000000000 : ℝ)+(991129234473/444440000000000 : ℝ)*((12633/50000 : ℝ)+(761/25000 : ℝ))=(10004956458981859/10000000000000000 : ℝ) by norm_num, show 1+(110274359152105339/50000000000000000000 : ℝ)+(18069932329499/100000000000000000000 : ℝ)=(100220566788236540177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(110274359152105339/50000000000000000000 : ℝ) ≤ ((55547462022088804387/55555000000000000000 : ℝ)+2*(991129234473/444440000000000 : ℝ)*(12633/50000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (55547462022088804387/55555000000000000000 : ℝ)+2*(991129234473/444440000000000 : ℝ)*(12633/50000 : ℝ)=(625619506572139/625000000000000 : ℝ) by norm_num, show 1+2*(110274359152105339/50000000000000000000 : ℝ)=(25110274359152105339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55547462022088804387/55555000000000000000 : ℝ)*(X 1 0+X 2 0)+(991129234473/444440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (761/25000 : ℝ)) (hi := (12633/50000 : ℝ)) (c := (55547462022088804387/55555000000000000000 : ℝ)) (alpha := (991129234473/444440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55547462022088804387/55555000000000000000 : ℝ)*(X 0 1+X 2 1)+(991129234473/444440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (761/25000 : ℝ)) (hi := (12633/50000 : ℝ)) (c := (55547462022088804387/55555000000000000000 : ℝ)) (alpha := (991129234473/444440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55547462022088804387/55555000000000000000 : ℝ)*(X 0 2+X 1 2)+(991129234473/444440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (761/25000 : ℝ)) (hi := (12633/50000 : ℝ)) (c := (55547462022088804387/55555000000000000000 : ℝ)) (alpha := (991129234473/444440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1817142339/10000000000 : ℝ)*X 0 0+(5559464297/10000000000 : ℝ)*X 0 1+(5106954003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5383559391/10000000000 : ℝ)*X 1 0+(-1027462901/5000000000 : ℝ)*X 1 1+(2553476247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1076711663/2000000000 : ℝ)*X 2 0+(2553476971/5000000000 : ℝ)*X 2 1+(-2054925339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121704737/5000000000 : ℝ)*X 0 0+(750131191/2000000000 : ℝ)*X 0 1+(4789068023/10000000000 : ℝ)*X 0 2+(2121704737/5000000000 : ℝ)*X 1 0+(750131191/2000000000 : ℝ)*X 1 1+(4789068023/10000000000 : ℝ)*X 1 2+(2121704737/5000000000 : ℝ)*X 2 0+(750131191/2000000000 : ℝ)*X 2 1+(4789068023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-28397089/156250000 : ℝ)*X 0 0+(5111894843/10000000000 : ℝ)*X 0 1+(4339411/7812500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264132409/10000000000 : ℝ)*X 1 0+(-1607432917/10000000000 : ℝ)*X 1 1+(5554446213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632066113/5000000000 : ℝ)*X 2 0+(5554446337/10000000000 : ℝ)*X 2 1+(-803716499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244031593/10000000000 : ℝ)*X 0 0+(95554591/200000000 : ℝ)*X 0 1+(940543283/2500000000 : ℝ)*X 0 2+(4244031593/10000000000 : ℝ)*X 1 0+(95554591/200000000 : ℝ)*X 1 1+(940543283/2500000000 : ℝ)*X 1 2+(4244031593/10000000000 : ℝ)*X 2 0+(95554591/200000000 : ℝ)*X 2 1+(940543283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23786163667676378283244377327/2777750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26017383/12500000000000 : ℝ)*(base1) + (2363346609/100000000000000 : ℝ)*(base19) + (30025869/1562500000000 : ℝ)*(base23) + (154714847/100000000000000 : ℝ)*(upper3) + (77292073/25000000000000 : ℝ)*(upper5) + (1586469983173207/100000000000000 : ℝ)*(major0) + (1586469983173207/100000000000000 : ℝ)*(major1) + (1586469983173207/100000000000000 : ℝ)*(major2) + (4316221954829/195312500000 : ℝ)*(sp0) + (2209915626247943/100000000000000 : ℝ)*(sp1) + (276239508492367/12500000000000 : ℝ)*(sp2) + (963015786453877/100000000000000 : ℝ)*(sp3) + (784803823/6250000000000 : ℝ)*(sp4) + (2848361049/50000000000000 : ℝ)*(sp7) + (6018885570719/625000000000 : ℝ)*(f.failure) + (276239748699319/12500000000000 : ℝ)*(f.sum) + (42776235418247/22222000000000000000000000000 : ℝ)*base65 + (371209501806165891/5555500000000000000000000000000000 : ℝ)*base68 + (14331155828625834109/5555500000000000000000000000000000 : ℝ)*base69 + (1669178927438834109/5555500000000000000000000000000000 : ℝ)*base71 + (87010945577833/22222000000000000000000000000 : ℝ)*base73 + (7548564583093165891/5555500000000000000000000000000000 : ℝ)*base76 + (21569311613109665891/5555500000000000000000000000000000 : ℝ)*base78 + (8523017049582165891/5555500000000000000000000000000000 : ℝ)*base80 + (17202685981729/4444400000000000000000000000 : ℝ)*base81 + (422721/62500000000000000000 : ℝ)*base89 + (422721/62500000000000000000 : ℝ)*base91 + (422721/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4836367988400537249650486877/694437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (630420293/50000000000000 : ℝ)*(base19) + (1322352903/100000000000000 : ℝ)*(base23) + (4603677/2500000000000 : ℝ)*(upper3) + (1893361/3125000000000 : ℝ)*(lower4) + (112688347/100000000000000 : ℝ)*(upper5) + (405538232034757/25000000000000 : ℝ)*(major0) + (405538232034757/25000000000000 : ℝ)*(major1) + (405538232034757/25000000000000 : ℝ)*(major2) + (1816424951/20000000000000 : ℝ)*(sp1) + (5091412997/50000000000000 : ℝ)*(sp2) + (1129811805617659/50000000000000 : ℝ)*(sp4) + (2259613268269977/100000000000000 : ℝ)*(sp5) + (1129806053028211/50000000000000 : ℝ)*(sp6) + (246170503223687/25000000000000 : ℝ)*(sp7) + (246170503223687/25000000000000 : ℝ)*(f.failure) + (1129811805617659/50000000000000 : ℝ)*(f.sum) + (7659924752037/5555500000000000000000000000 : ℝ)*base66 + (4594356340211046041/1388875000000000000000000000000000 : ℝ)*base68 + (5661519291673703959/1388875000000000000000000000000000 : ℝ)*base69 + (6013666991407046041/1388875000000000000000000000000000 : ℝ)*base72 + (41660516594769/11111000000000000000000000000 : ℝ)*base74 + (6837920540043578959/1388875000000000000000000000000000 : ℝ)*base75 + (4236027384647546041/1388875000000000000000000000000000 : ℝ)*base78 + (5299806907857046041/1388875000000000000000000000000000 : ℝ)*base80 + (5147757381121/1388875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4215567/2500000000000000000000 : ℝ)*base90 + (4215567/2500000000000000000000 : ℝ)*base92 + (4215567/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1529_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (761/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4289/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18153/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1529_s2_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839774449/10000000000 : ℝ)*x 0 + (2726337641/5000000000 : ℝ)*x 1 + (649882101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839774449/10000000000 : ℝ)^4555 ≤ (2252030279777/20000000000000 : ℝ)^3531 := by
    have hnat : (1839774449 : ℕ)^4555*20000000000000^3531 ≤ 2252030279777^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839774449 10000000000 2252030279777 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726337641/5000000000 : ℝ)^4555 ≤ (1429143062069/3125000000000 : ℝ)^3531 := by
    have hnat : (2726337641 : ℕ)^4555*3125000000000^3531 ≤ 1429143062069^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726337641 5000000000 1429143062069 3125000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649882101/1250000000 : ℝ)^4555 ≤ (21503635301029/50000000000000 : ℝ)^3531 := by
    have hnat : (649882101 : ℕ)^4555*50000000000000^3531 ≤ 21503635301029^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649882101 1250000000 21503635301029 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839774449/10000000000 : ℝ), (2726337641/5000000000 : ℝ), (649882101/1250000000 : ℝ)] ![(2252030279777/20000000000000 : ℝ), (1429143062069/3125000000000 : ℝ), (21503635301029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839774449/10000000000 : ℝ)|^4555 ≤ (2252030279777/20000000000000 : ℝ)^3531
        have hw : |(-1839774449/10000000000 : ℝ)|=(1839774449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726337641/5000000000 : ℝ)|^4555 ≤ (1429143062069/3125000000000 : ℝ)^3531
        have hw : |(2726337641/5000000000 : ℝ)|=(2726337641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649882101/1250000000 : ℝ)|^4555 ≤ (21503635301029/50000000000000 : ℝ)^3531
        have hw : |(649882101/1250000000 : ℝ)|=(649882101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356283823/10000000000 : ℝ)*x 0 + (-1970206403/10000000000 : ℝ)*x 1 + (259952861/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356283823/10000000000 : ℝ)^4555 ≤ (44692356308149/100000000000000 : ℝ)^3531 := by
    have hnat : (5356283823 : ℕ)^4555*100000000000000^3531 ≤ 44692356308149^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356283823 10000000000 44692356308149 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1970206403/10000000000 : ℝ)^4555 ≤ (12300368679333/100000000000000 : ℝ)^3531 := by
    have hnat : (1970206403 : ℕ)^4555*100000000000000^3531 ≤ 12300368679333^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970206403 10000000000 12300368679333 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259952861/500000000 : ℝ)^4555 ≤ (43007274998539/100000000000000 : ℝ)^3531 := by
    have hnat : (259952861 : ℕ)^4555*100000000000000^3531 ≤ 43007274998539^3531*500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259952861 500000000 43007274998539 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356283823/10000000000 : ℝ), (-1970206403/10000000000 : ℝ), (259952861/500000000 : ℝ)] ![(44692356308149/100000000000000 : ℝ), (12300368679333/100000000000000 : ℝ), (43007274998539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356283823/10000000000 : ℝ)|^4555 ≤ (44692356308149/100000000000000 : ℝ)^3531
        have hw : |(5356283823/10000000000 : ℝ)|=(5356283823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1970206403/10000000000 : ℝ)|^4555 ≤ (12300368679333/100000000000000 : ℝ)^3531
        have hw : |(-1970206403/10000000000 : ℝ)|=(1970206403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259952861/500000000 : ℝ)|^4555 ≤ (43007274998539/100000000000000 : ℝ)^3531
        have hw : |(259952861/500000000 : ℝ)|=(259952861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356284543/10000000000 : ℝ)*x 0 + (1039811359/2000000000 : ℝ)*x 1 + (-492551501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356284543/10000000000 : ℝ)^4555 ≤ (4469236405799/10000000000000 : ℝ)^3531 := by
    have hnat : (5356284543 : ℕ)^4555*10000000000000^3531 ≤ 4469236405799^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356284543 10000000000 4469236405799 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039811359/2000000000 : ℝ)^4555 ≤ (8601454092667/20000000000000 : ℝ)^3531 := by
    have hnat : (1039811359 : ℕ)^4555*20000000000000^3531 ≤ 8601454092667^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039811359 2000000000 8601454092667 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492551501/2500000000 : ℝ)^4555 ≤ (2460073093179/20000000000000 : ℝ)^3531 := by
    have hnat : (492551501 : ℕ)^4555*20000000000000^3531 ≤ 2460073093179^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492551501 2500000000 2460073093179 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356284543/10000000000 : ℝ), (1039811359/2000000000 : ℝ), (-492551501/2500000000 : ℝ)] ![(4469236405799/10000000000000 : ℝ), (8601454092667/20000000000000 : ℝ), (2460073093179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356284543/10000000000 : ℝ)|^4555 ≤ (4469236405799/10000000000000 : ℝ)^3531
        have hw : |(5356284543/10000000000 : ℝ)|=(5356284543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039811359/2000000000 : ℝ)|^4555 ≤ (8601454092667/20000000000000 : ℝ)^3531
        have hw : |(1039811359/2000000000 : ℝ)|=(1039811359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492551501/2500000000 : ℝ)|^4555 ≤ (2460073093179/20000000000000 : ℝ)^3531
        have hw : |(-492551501/2500000000 : ℝ)|=(492551501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851940359/2000000000 : ℝ)*x 0 + (1988508451/5000000000 : ℝ)*x 1 + (911803123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851940359/2000000000 : ℝ)^4555 ≤ (16629076021457/50000000000000 : ℝ)^3531 := by
    have hnat : (851940359 : ℕ)^4555*50000000000000^3531 ≤ 16629076021457^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851940359 2000000000 16629076021457 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988508451/5000000000 : ℝ)^4555 ≤ (30438830291259/100000000000000 : ℝ)^3531 := by
    have hnat : (1988508451 : ℕ)^4555*100000000000000^3531 ≤ 30438830291259^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988508451 5000000000 30438830291259 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911803123/2000000000 : ℝ)^4555 ≤ (28361732533/78125000000 : ℝ)^3531 := by
    have hnat : (911803123 : ℕ)^4555*78125000000^3531 ≤ 28361732533^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911803123 2000000000 28361732533 78125000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851940359/2000000000 : ℝ), (1988508451/5000000000 : ℝ), (911803123/2000000000 : ℝ)] ![(16629076021457/50000000000000 : ℝ), (30438830291259/100000000000000 : ℝ), (28361732533/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851940359/2000000000 : ℝ)|^4555 ≤ (16629076021457/50000000000000 : ℝ)^3531
        have hw : |(851940359/2000000000 : ℝ)|=(851940359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1988508451/5000000000 : ℝ)|^4555 ≤ (30438830291259/100000000000000 : ℝ)^3531
        have hw : |(1988508451/5000000000 : ℝ)|=(1988508451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911803123/2000000000 : ℝ)|^4555 ≤ (28361732533/78125000000 : ℝ)^3531
        have hw : |(911803123/2000000000 : ℝ)|=(911803123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839820933/10000000000 : ℝ)*x 0 + (1300154643/2500000000 : ℝ)*x 1 + (681387611/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839820933/10000000000 : ℝ)^4555 ≤ (11260518406769/100000000000000 : ℝ)^3531 := by
    have hnat : (1839820933 : ℕ)^4555*100000000000000^3531 ≤ 11260518406769^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839820933 10000000000 11260518406769 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300154643/2500000000 : ℝ)^4555 ≤ (21511968510707/50000000000000 : ℝ)^3531 := by
    have hnat : (1300154643 : ℕ)^4555*50000000000000^3531 ≤ 21511968510707^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300154643 2500000000 21511968510707 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681387611/1250000000 : ℝ)^4555 ≤ (45715544562343/100000000000000 : ℝ)^3531 := by
    have hnat : (681387611 : ℕ)^4555*100000000000000^3531 ≤ 45715544562343^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681387611 1250000000 45715544562343 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839820933/10000000000 : ℝ), (1300154643/2500000000 : ℝ), (681387611/1250000000 : ℝ)] ![(11260518406769/100000000000000 : ℝ), (21511968510707/50000000000000 : ℝ), (45715544562343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839820933/10000000000 : ℝ)|^4555 ≤ (11260518406769/100000000000000 : ℝ)^3531
        have hw : |(-1839820933/10000000000 : ℝ)|=(1839820933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300154643/2500000000 : ℝ)|^4555 ≤ (21511968510707/50000000000000 : ℝ)^3531
        have hw : |(1300154643/2500000000 : ℝ)|=(1300154643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681387611/1250000000 : ℝ)|^4555 ≤ (45715544562343/100000000000000 : ℝ)^3531
        have hw : |(681387611/1250000000 : ℝ)|=(681387611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289525951/10000000000 : ℝ)*x 0 + (-1718163149/10000000000 : ℝ)*x 1 + (1362775573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289525951/10000000000 : ℝ)^4555 ≤ (21987549558323/50000000000000 : ℝ)^3531 := by
    have hnat : (5289525951 : ℕ)^4555*50000000000000^3531 ≤ 21987549558323^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289525951 10000000000 21987549558323 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1718163149/10000000000 : ℝ)^4555 ≤ (322166909843/3125000000000 : ℝ)^3531 := by
    have hnat : (1718163149 : ℕ)^4555*3125000000000^3531 ≤ 322166909843^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718163149 10000000000 322166909843 3125000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362775573/2500000000 : ℝ)^4555 ≤ (45715559751633/100000000000000 : ℝ)^3531 := by
    have hnat : (1362775573 : ℕ)^4555*100000000000000^3531 ≤ 45715559751633^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362775573 2500000000 45715559751633 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289525951/10000000000 : ℝ), (-1718163149/10000000000 : ℝ), (1362775573/2500000000 : ℝ)] ![(21987549558323/50000000000000 : ℝ), (322166909843/3125000000000 : ℝ), (45715559751633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289525951/10000000000 : ℝ)|^4555 ≤ (21987549558323/50000000000000 : ℝ)^3531
        have hw : |(5289525951/10000000000 : ℝ)|=(5289525951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1718163149/10000000000 : ℝ)|^4555 ≤ (322166909843/3125000000000 : ℝ)^3531
        have hw : |(-1718163149/10000000000 : ℝ)|=(1718163149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362775573/2500000000 : ℝ)|^4555 ≤ (45715559751633/100000000000000 : ℝ)^3531
        have hw : |(1362775573/2500000000 : ℝ)|=(1362775573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057905361/2000000000 : ℝ)*x 0 + (170346949/312500000 : ℝ)*x 1 + (-1718161859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057905361/2000000000 : ℝ)^4555 ≤ (43975108275447/100000000000000 : ℝ)^3531 := by
    have hnat : (1057905361 : ℕ)^4555*100000000000000^3531 ≤ 43975108275447^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057905361 2000000000 43975108275447 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170346949/312500000 : ℝ)^4555 ≤ (9143112114769/20000000000000 : ℝ)^3531 := by
    have hnat : (170346949 : ℕ)^4555*20000000000000^3531 ≤ 9143112114769^3531*312500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170346949 312500000 9143112114769 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1718161859/10000000000 : ℝ)^4555 ≤ (2577332782501/25000000000000 : ℝ)^3531 := by
    have hnat : (1718161859 : ℕ)^4555*25000000000000^3531 ≤ 2577332782501^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718161859 10000000000 2577332782501 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057905361/2000000000 : ℝ), (170346949/312500000 : ℝ), (-1718161859/10000000000 : ℝ)] ![(43975108275447/100000000000000 : ℝ), (9143112114769/20000000000000 : ℝ), (2577332782501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057905361/2000000000 : ℝ)|^4555 ≤ (43975108275447/100000000000000 : ℝ)^3531
        have hw : |(1057905361/2000000000 : ℝ)|=(1057905361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170346949/312500000 : ℝ)|^4555 ≤ (9143112114769/20000000000000 : ℝ)^3531
        have hw : |(170346949/312500000 : ℝ)|=(170346949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1718161859/10000000000 : ℝ)|^4555 ≤ (2577332782501/25000000000000 : ℝ)^3531
        have hw : |(-1718161859/10000000000 : ℝ)|=(1718161859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s2_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129906277/5000000000 : ℝ)*x 0 + (2277717027/5000000000 : ℝ)*x 1 + (3980629279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129906277/5000000000 : ℝ)^4555 ≤ (33259267596007/100000000000000 : ℝ)^3531 := by
    have hnat : (2129906277 : ℕ)^4555*100000000000000^3531 ≤ 33259267596007^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129906277 5000000000 33259267596007 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277717027/5000000000 : ℝ)^4555 ≤ (9066557855233/25000000000000 : ℝ)^3531 := by
    have hnat : (2277717027 : ℕ)^4555*25000000000000^3531 ≤ 9066557855233^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277717027 5000000000 9066557855233 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3980629279/10000000000 : ℝ)^4555 ≤ (30474500975343/100000000000000 : ℝ)^3531 := by
    have hnat : (3980629279 : ℕ)^4555*100000000000000^3531 ≤ 30474500975343^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980629279 10000000000 30474500975343 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129906277/5000000000 : ℝ), (2277717027/5000000000 : ℝ), (3980629279/10000000000 : ℝ)] ![(33259267596007/100000000000000 : ℝ), (9066557855233/25000000000000 : ℝ), (30474500975343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129906277/5000000000 : ℝ)|^4555 ≤ (33259267596007/100000000000000 : ℝ)^3531
        have hw : |(2129906277/5000000000 : ℝ)|=(2129906277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2277717027/5000000000 : ℝ)|^4555 ≤ (9066557855233/25000000000000 : ℝ)^3531
        have hw : |(2277717027/5000000000 : ℝ)|=(2277717027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3980629279/10000000000 : ℝ)|^4555 ≤ (30474500975343/100000000000000 : ℝ)^3531
        have hw : |(3980629279/10000000000 : ℝ)|=(3980629279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18153/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2641/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3187/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18153/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18153/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4289/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18153/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18153/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4289/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18153/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18153/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4289/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (4289/50000 : ℝ) ^ (4553/1024 : ℝ) ≤ (1809364329441941/100000000000000000000 : ℝ) := by
    have hpowers : (4289/50000 : ℝ)^4553 ≤ (1809364329441941/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4289 : ℕ)^4553*100000000000000000000^1024 ≤ 1809364329441941^1024*50000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4289 50000 1809364329441941 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4289/50000 : ℝ)) (X := (1809364329441941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18153/100000 : ℝ) ^ (4553/1024 : ℝ) ≤ (50707291104296619/100000000000000000000 : ℝ) := by
    have hpowers : (18153/100000 : ℝ)^4553 ≤ (50707291104296619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18153 : ℕ)^4553*100000000000000000000^1024 ≤ 50707291104296619^1024*100000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18153 100000 50707291104296619 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18153/100000 : ℝ)) (X := (50707291104296619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001809364329441941/50000000000000000000 : ℝ) ≤ (10000081386474409/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50001809364329441941/50000000000000000000 : ℝ)^1024 ≤ (10000081386474409/10000000000000000 : ℝ)^4553 := by
      have hnat : (50001809364329441941 : ℕ)^1024*10000000000000000^4553 ≤ 10000081386474409^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001809364329441941 50000000000000000000 10000081386474409 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081386474409/10000000000000000 : ℝ)) (X := (50001809364329441941/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (312664114548230433/312500000000000000 : ℝ) ≤ (10001180894212727/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (312664114548230433/312500000000000000 : ℝ)^1024 ≤ (10001180894212727/10000000000000000 : ℝ)^4553 := by
      have hnat : (312664114548230433 : ℕ)^1024*10000000000000000^4553 ≤ 10001180894212727^4553*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312664114548230433 312500000000000000 10001180894212727 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001180894212727/10000000000000000 : ℝ)) (X := (312664114548230433/312500000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50050707291104296619/50000000000000000000 : ℝ) ≤ (2000456080390209/2000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50050707291104296619/50000000000000000000 : ℝ)^1024 ≤ (2000456080390209/2000000000000000 : ℝ)^4553 := by
      have hnat : (50050707291104296619 : ℕ)^1024*2000000000000000^4553 ≤ 2000456080390209^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050707291104296619 50000000000000000000 2000456080390209 2000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000456080390209/2000000000000000 : ℝ)) (X := (50050707291104296619/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1809364329441941/100000000000000000000 : ℝ) ≤ ((95731916120733882567/95750000000000000000 : ℝ)+2*(549753869159/478750000000000 : ℝ)*(4289/50000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (95731916120733882567/95750000000000000000 : ℝ)+2*(549753869159/478750000000000 : ℝ)*(4289/50000 : ℝ)=(10000081386474409/10000000000000000 : ℝ) by norm_num, show 1+2*(1809364329441941/100000000000000000000 : ℝ)=(50001809364329441941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50707291104296619/100000000000000000000 : ℝ)+(1809364329441941/100000000000000000000 : ℝ) ≤ ((95731916120733882567/95750000000000000000 : ℝ)+(549753869159/478750000000000 : ℝ)*((18153/100000 : ℝ)+(4289/50000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (95731916120733882567/95750000000000000000 : ℝ)+(549753869159/478750000000000 : ℝ)*((18153/100000 : ℝ)+(4289/50000 : ℝ))=(10001180894212727/10000000000000000 : ℝ) by norm_num, show 1+(50707291104296619/100000000000000000000 : ℝ)+(1809364329441941/100000000000000000000 : ℝ)=(312664114548230433/312500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50707291104296619/100000000000000000000 : ℝ) ≤ ((95731916120733882567/95750000000000000000 : ℝ)+2*(549753869159/478750000000000 : ℝ)*(18153/100000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (95731916120733882567/95750000000000000000 : ℝ)+2*(549753869159/478750000000000 : ℝ)*(18153/100000 : ℝ)=(2000456080390209/2000000000000000 : ℝ) by norm_num, show 1+2*(50707291104296619/100000000000000000000 : ℝ)=(50050707291104296619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95731916120733882567/95750000000000000000 : ℝ)*(X 1 0+X 2 0)+(549753869159/478750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (4289/50000 : ℝ)) (hi := (18153/100000 : ℝ)) (c := (95731916120733882567/95750000000000000000 : ℝ)) (alpha := (549753869159/478750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95731916120733882567/95750000000000000000 : ℝ)*(X 0 1+X 2 1)+(549753869159/478750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (4289/50000 : ℝ)) (hi := (18153/100000 : ℝ)) (c := (95731916120733882567/95750000000000000000 : ℝ)) (alpha := (549753869159/478750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95731916120733882567/95750000000000000000 : ℝ)*(X 0 2+X 1 2)+(549753869159/478750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (4289/50000 : ℝ)) (hi := (18153/100000 : ℝ)) (c := (95731916120733882567/95750000000000000000 : ℝ)) (alpha := (549753869159/478750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1839774449/10000000000 : ℝ)*X 0 0+(2726337641/5000000000 : ℝ)*X 0 1+(649882101/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356283823/10000000000 : ℝ)*X 1 0+(-1970206403/10000000000 : ℝ)*X 1 1+(259952861/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356284543/10000000000 : ℝ)*X 2 0+(1039811359/2000000000 : ℝ)*X 2 1+(-492551501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((851940359/2000000000 : ℝ)*X 0 0+(1988508451/5000000000 : ℝ)*X 0 1+(911803123/2000000000 : ℝ)*X 0 2+(851940359/2000000000 : ℝ)*X 1 0+(1988508451/5000000000 : ℝ)*X 1 1+(911803123/2000000000 : ℝ)*X 1 2+(851940359/2000000000 : ℝ)*X 2 0+(1988508451/5000000000 : ℝ)*X 2 1+(911803123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1839820933/10000000000 : ℝ)*X 0 0+(1300154643/2500000000 : ℝ)*X 0 1+(681387611/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289525951/10000000000 : ℝ)*X 1 0+(-1718163149/10000000000 : ℝ)*X 1 1+(1362775573/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057905361/2000000000 : ℝ)*X 2 0+(170346949/312500000 : ℝ)*X 2 1+(-1718161859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129906277/5000000000 : ℝ)*X 0 0+(2277717027/5000000000 : ℝ)*X 0 1+(3980629279/10000000000 : ℝ)*X 0 2+(2129906277/5000000000 : ℝ)*X 1 0+(2277717027/5000000000 : ℝ)*X 1 1+(3980629279/10000000000 : ℝ)*X 1 2+(2129906277/5000000000 : ℝ)*X 2 0+(2277717027/5000000000 : ℝ)*X 2 1+(3980629279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11246274042201483084773673267/1196875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1912048329/100000000000000 : ℝ)*(base19) + (1080482649/50000000000000 : ℝ)*(base23) + (151919843/100000000000000 : ℝ)*(upper3) + (75284167/50000000000000 : ℝ)*(upper4) + (378716533/100000000000000 : ℝ)*(upper5) + (1415310312207633/50000000000000 : ℝ)*(major0) + (1415310312207633/50000000000000 : ℝ)*(major1) + (1415310312207633/50000000000000 : ℝ)*(major2) + (394295598006887/10000000000000 : ℝ)*(sp0) + (30804616457917/781250000000 : ℝ)*(sp1) + (492873832212051/12500000000000 : ℝ)*(sp2) + (1718232566875931/100000000000000 : ℝ)*(sp3) + (36838592837/100000000000000 : ℝ)*(sp4) + (7775040363/50000000000000 : ℝ)*(sp7) + (1718248116956657/100000000000000 : ℝ)*(f.failure) + (1971496409330853/50000000000000 : ℝ)*(f.sum) + (44279823545831/23937500000000000000000000000 : ℝ)*base66 + (19801463664647433911/4787500000000000000000000000000000 : ℝ)*base67 + (18659761454040066089/4787500000000000000000000000000000 : ℝ)*base70 + (55301361546634933911/4787500000000000000000000000000000 : ℝ)*base71 + (25993216571669/23937500000000000000000000000 : ℝ)*base73 + (72695943083059933911/4787500000000000000000000000000000 : ℝ)*base75 + (33409057149534933911/4787500000000000000000000000000000 : ℝ)*base77 + (55686398489047433911/4787500000000000000000000000000000 : ℝ)*base79 + (40039995327537/47875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (69031337/10000000000000000000000 : ℝ)*base90 + (69031337/10000000000000000000000 : ℝ)*base92 + (69031337/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19066405752023314443371330499/4787500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130572327/100000000000000 : ℝ)*(base8) + (199271113/25000000000000 : ℝ)*(base15) + (14500707/4000000000000 : ℝ)*(base29) + (248158311/100000000000000 : ℝ)*(lower2) + (170168423/100000000000000 : ℝ)*(lower4) + (1433007224972063/50000000000000 : ℝ)*(major0) + (2866014812461801/100000000000000 : ℝ)*(major1) + (2866014812461801/100000000000000 : ℝ)*(major2) + (16853832719/100000000000000 : ℝ)*(sp2) + (6391005017/100000000000000 : ℝ)*(sp3) + (3992296204776927/100000000000000 : ℝ)*(sp4) + (1996147587873563/50000000000000 : ℝ)*(sp5) + (199613955949943/5000000000000 : ℝ)*(sp6) + (217465845727253/12500000000000 : ℝ)*(sp7) + (1739733156823041/100000000000000 : ℝ)*(f.failure) + (1996148167674627/50000000000000 : ℝ)*(f.sum) + (76588844714641/23937500000000000000000000000 : ℝ)*base66 + (30030432409370876833/9575000000000000000000000000000000 : ℝ)*base68 + (1507688678154123167/9575000000000000000000000000000000 : ℝ)*base69 + (17329160566496125721/4787500000000000000000000000000000 : ℝ)*base71 + (67704219125607/47875000000000000000000000000 : ℝ)*base74 + (50233963227889123167/9575000000000000000000000000000000 : ℝ)*base75 + (25907412086666374279/4787500000000000000000000000000000 : ℝ)*base78 + (89235956535989123167/9575000000000000000000000000000000 : ℝ)*base79 + (31626225283183/11968750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (56946119/10000000000000000000000 : ℝ)*base89 + (56946119/10000000000000000000000 : ℝ)*base91 + (56946119/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1529_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18153/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4289/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1529_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1529_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1529_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1529_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

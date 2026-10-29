-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:41.958677+00:00
-- url     : https://prove2.me/submissions/86646e5e-1c47-4e0a-8afa-8c414ca36259

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
theorem support_rectangle_w1594_s0_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399056747/2500000000 : ℝ)*x 0 + (585917353/1000000000 : ℝ)*x 1 + (4880799061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399056747/2500000000 : ℝ)^4695 ≤ (9567609171511/100000000000000 : ℝ)^3671 := by
    have hnat : (399056747 : ℕ)^4695*100000000000000^3671 ≤ 9567609171511^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399056747 2500000000 9567609171511 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585917353/1000000000 : ℝ)^4695 ≤ (50474952966307/100000000000000 : ℝ)^3671 := by
    have hnat : (585917353 : ℕ)^4695*100000000000000^3671 ≤ 50474952966307^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585917353 1000000000 50474952966307 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880799061/10000000000 : ℝ)^4695 ≤ (9989359460129/25000000000000 : ℝ)^3671 := by
    have hnat : (4880799061 : ℕ)^4695*25000000000000^3671 ≤ 9989359460129^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880799061 10000000000 9989359460129 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399056747/2500000000 : ℝ), (585917353/1000000000 : ℝ), (4880799061/10000000000 : ℝ)] ![(9567609171511/100000000000000 : ℝ), (50474952966307/100000000000000 : ℝ), (9989359460129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399056747/2500000000 : ℝ)|^4695 ≤ (9567609171511/100000000000000 : ℝ)^3671
        have hw : |(-399056747/2500000000 : ℝ)|=(399056747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585917353/1000000000 : ℝ)|^4695 ≤ (50474952966307/100000000000000 : ℝ)^3671
        have hw : |(585917353/1000000000 : ℝ)|=(585917353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880799061/10000000000 : ℝ)|^4695 ≤ (9989359460129/25000000000000 : ℝ)^3671
        have hw : |(4880799061/10000000000 : ℝ)|=(4880799061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1365089801/2500000000 : ℝ)*x 0 + (-2139912151/10000000000 : ℝ)*x 1 + (4880798923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1365089801/2500000000 : ℝ)^4695 ≤ (1441354851141/3125000000000 : ℝ)^3671 := by
    have hnat : (1365089801 : ℕ)^4695*3125000000000^3671 ≤ 1441354851141^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365089801 2500000000 1441354851141 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139912151/10000000000 : ℝ)^4695 ≤ (3479802088533/25000000000000 : ℝ)^3671 := by
    have hnat : (2139912151 : ℕ)^4695*25000000000000^3671 ≤ 3479802088533^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139912151 10000000000 3479802088533 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880798923/10000000000 : ℝ)^4695 ≤ (39957436395619/100000000000000 : ℝ)^3671 := by
    have hnat : (4880798923 : ℕ)^4695*100000000000000^3671 ≤ 39957436395619^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880798923 10000000000 39957436395619 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1365089801/2500000000 : ℝ), (-2139912151/10000000000 : ℝ), (4880798923/10000000000 : ℝ)] ![(1441354851141/3125000000000 : ℝ), (3479802088533/25000000000000 : ℝ), (39957436395619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1365089801/2500000000 : ℝ)|^4695 ≤ (1441354851141/3125000000000 : ℝ)^3671
        have hw : |(1365089801/2500000000 : ℝ)|=(1365089801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139912151/10000000000 : ℝ)|^4695 ≤ (3479802088533/25000000000000 : ℝ)^3671
        have hw : |(-2139912151/10000000000 : ℝ)|=(2139912151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880798923/10000000000 : ℝ)|^4695 ≤ (39957436395619/100000000000000 : ℝ)^3671
        have hw : |(4880798923/10000000000 : ℝ)|=(4880798923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5460359211/10000000000 : ℝ)*x 0 + (4880798877/10000000000 : ℝ)*x 1 + (-10699561/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5460359211/10000000000 : ℝ)^4695 ≤ (23061677656067/50000000000000 : ℝ)^3671 := by
    have hnat : (5460359211 : ℕ)^4695*50000000000000^3671 ≤ 23061677656067^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460359211 10000000000 23061677656067 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4880798877/10000000000 : ℝ)^4695 ≤ (39957435913987/100000000000000 : ℝ)^3671 := by
    have hnat : (4880798877 : ℕ)^4695*100000000000000^3671 ≤ 39957435913987^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880798877 10000000000 39957435913987 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10699561/50000000 : ℝ)^4695 ≤ (6959604380881/50000000000000 : ℝ)^3671 := by
    have hnat : (10699561 : ℕ)^4695*50000000000000^3671 ≤ 6959604380881^3671*50000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10699561 50000000 6959604380881 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5460359211/10000000000 : ℝ), (4880798877/10000000000 : ℝ), (-10699561/50000000 : ℝ)] ![(23061677656067/50000000000000 : ℝ), (39957435913987/100000000000000 : ℝ), (6959604380881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5460359211/10000000000 : ℝ)|^4695 ≤ (23061677656067/50000000000000 : ℝ)^3671
        have hw : |(5460359211/10000000000 : ℝ)|=(5460359211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4880798877/10000000000 : ℝ)|^4695 ≤ (39957435913987/100000000000000 : ℝ)^3671
        have hw : |(4880798877/10000000000 : ℝ)|=(4880798877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10699561/50000000 : ℝ)|^4695 ≤ (6959604380881/50000000000000 : ℝ)^3671
        have hw : |(-10699561/50000000 : ℝ)|=(10699561/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1029428533/2500000000 : ℝ)*x 0 + (614400631/2000000000 : ℝ)*x 1 + (1356407769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029428533/2500000000 : ℝ)^4695 ≤ (4018622600687/12500000000000 : ℝ)^3671 := by
    have hnat : (1029428533 : ℕ)^4695*12500000000000^3671 ≤ 4018622600687^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029428533 2500000000 4018622600687 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614400631/2000000000 : ℝ)^4695 ≤ (11051252112927/50000000000000 : ℝ)^3671 := by
    have hnat : (614400631 : ℕ)^4695*50000000000000^3671 ≤ 11051252112927^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614400631 2000000000 11051252112927 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356407769/2500000000 : ℝ)^4695 ≤ (4574851494753/10000000000000 : ℝ)^3671 := by
    have hnat : (1356407769 : ℕ)^4695*10000000000000^3671 ≤ 4574851494753^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356407769 2500000000 4574851494753 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1029428533/2500000000 : ℝ), (614400631/2000000000 : ℝ), (1356407769/2500000000 : ℝ)] ![(4018622600687/12500000000000 : ℝ), (11051252112927/50000000000000 : ℝ), (4574851494753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1029428533/2500000000 : ℝ)|^4695 ≤ (4018622600687/12500000000000 : ℝ)^3671
        have hw : |(1029428533/2500000000 : ℝ)|=(1029428533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614400631/2000000000 : ℝ)|^4695 ≤ (11051252112927/50000000000000 : ℝ)^3671
        have hw : |(614400631/2000000000 : ℝ)|=(614400631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356407769/2500000000 : ℝ)|^4695 ≤ (4574851494753/10000000000000 : ℝ)^3671
        have hw : |(1356407769/2500000000 : ℝ)|=(1356407769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-799624269/5000000000 : ℝ)*x 0 + (1226435809/2500000000 : ℝ)*x 1 + (1458333267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (799624269/5000000000 : ℝ)^4695 ≤ (4795389007757/50000000000000 : ℝ)^3671 := by
    have hnat : (799624269 : ℕ)^4695*50000000000000^3671 ≤ 4795389007757^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799624269 5000000000 4795389007757 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226435809/2500000000 : ℝ)^4695 ≤ (2010939802127/5000000000000 : ℝ)^3671 := by
    have hnat : (1226435809 : ℕ)^4695*5000000000000^3671 ≤ 2010939802127^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226435809 2500000000 2010939802127 5000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458333267/2500000000 : ℝ)^4695 ≤ (50190425926451/100000000000000 : ℝ)^3671 := by
    have hnat : (1458333267 : ℕ)^4695*100000000000000^3671 ≤ 50190425926451^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458333267 2500000000 50190425926451 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-799624269/5000000000 : ℝ), (1226435809/2500000000 : ℝ), (1458333267/2500000000 : ℝ)] ![(4795389007757/50000000000000 : ℝ), (2010939802127/5000000000000 : ℝ), (50190425926451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-799624269/5000000000 : ℝ)|^4695 ≤ (4795389007757/50000000000000 : ℝ)^3671
        have hw : |(-799624269/5000000000 : ℝ)|=(799624269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1226435809/2500000000 : ℝ)|^4695 ≤ (2010939802127/5000000000000 : ℝ)^3671
        have hw : |(1226435809/2500000000 : ℝ)|=(1226435809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458333267/2500000000 : ℝ)|^4695 ≤ (50190425926451/100000000000000 : ℝ)^3671
        have hw : |(1458333267/2500000000 : ℝ)|=(1458333267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596565563/5000000000 : ℝ)*x 0 + (-593689059/5000000000 : ℝ)*x 1 + (5833333571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596565563/5000000000 : ℝ)^4695 ≤ (10814097234641/25000000000000 : ℝ)^3671 := by
    have hnat : (2596565563 : ℕ)^4695*25000000000000^3671 ≤ 10814097234641^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596565563 5000000000 10814097234641 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593689059/5000000000 : ℝ)^4695 ≤ (3276589793383/50000000000000 : ℝ)^3671 := by
    have hnat : (593689059 : ℕ)^4695*50000000000000^3671 ≤ 3276589793383^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593689059 5000000000 3276589793383 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5833333571/10000000000 : ℝ)^4695 ≤ (12547607865381/25000000000000 : ℝ)^3671 := by
    have hnat : (5833333571 : ℕ)^4695*25000000000000^3671 ≤ 12547607865381^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5833333571 10000000000 12547607865381 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596565563/5000000000 : ℝ), (-593689059/5000000000 : ℝ), (5833333571/10000000000 : ℝ)] ![(10814097234641/25000000000000 : ℝ), (3276589793383/50000000000000 : ℝ), (12547607865381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596565563/5000000000 : ℝ)|^4695 ≤ (10814097234641/25000000000000 : ℝ)^3671
        have hw : |(2596565563/5000000000 : ℝ)|=(2596565563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-593689059/5000000000 : ℝ)|^4695 ≤ (3276589793383/50000000000000 : ℝ)^3671
        have hw : |(-593689059/5000000000 : ℝ)|=(593689059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5833333571/10000000000 : ℝ)|^4695 ≤ (12547607865381/25000000000000 : ℝ)^3671
        have hw : |(5833333571/10000000000 : ℝ)|=(5833333571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519312971/1000000000 : ℝ)*x 0 + (2916667571/5000000000 : ℝ)*x 1 + (-237475561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519312971/1000000000 : ℝ)^4695 ≤ (10814093463477/25000000000000 : ℝ)^3671 := by
    have hnat : (519312971 : ℕ)^4695*25000000000000^3671 ≤ 10814093463477^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519312971 1000000000 10814093463477 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2916667571/5000000000 : ℝ)^4695 ≤ (50190448748997/100000000000000 : ℝ)^3671 := by
    have hnat : (2916667571 : ℕ)^4695*100000000000000^3671 ≤ 50190448748997^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916667571 5000000000 50190448748997 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237475561/2000000000 : ℝ)^4695 ≤ (3276588688723/50000000000000 : ℝ)^3671 := by
    have hnat : (237475561 : ℕ)^4695*50000000000000^3671 ≤ 3276588688723^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237475561 2000000000 3276588688723 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519312971/1000000000 : ℝ), (2916667571/5000000000 : ℝ), (-237475561/2000000000 : ℝ)] ![(10814093463477/25000000000000 : ℝ), (50190448748997/100000000000000 : ℝ), (3276588688723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519312971/1000000000 : ℝ)|^4695 ≤ (10814093463477/25000000000000 : ℝ)^3671
        have hw : |(519312971/1000000000 : ℝ)|=(519312971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2916667571/5000000000 : ℝ)|^4695 ≤ (50190448748997/100000000000000 : ℝ)^3671
        have hw : |(2916667571/5000000000 : ℝ)|=(2916667571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237475561/2000000000 : ℝ)|^4695 ≤ (3276588688723/50000000000000 : ℝ)^3671
        have hw : |(-237475561/2000000000 : ℝ)|=(237475561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4124979523/10000000000 : ℝ)*x 0 + (5365619637/10000000000 : ℝ)*x 1 + (3134163841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124979523/10000000000 : ℝ)^4695 ≤ (32221545945233/100000000000000 : ℝ)^3671 := by
    have hnat : (4124979523 : ℕ)^4695*100000000000000^3671 ≤ 32221545945233^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124979523 10000000000 32221545945233 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5365619637/10000000000 : ℝ)^4695 ≤ (5637794434117/12500000000000 : ℝ)^3671 := by
    have hnat : (5365619637 : ℕ)^4695*12500000000000^3671 ≤ 5637794434117^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365619637 10000000000 5637794434117 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134163841/10000000000 : ℝ)^4695 ≤ (22676098569009/100000000000000 : ℝ)^3671 := by
    have hnat : (3134163841 : ℕ)^4695*100000000000000^3671 ≤ 22676098569009^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134163841 10000000000 22676098569009 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124979523/10000000000 : ℝ), (5365619637/10000000000 : ℝ), (3134163841/10000000000 : ℝ)] ![(32221545945233/100000000000000 : ℝ), (5637794434117/12500000000000 : ℝ), (22676098569009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124979523/10000000000 : ℝ)|^4695 ≤ (32221545945233/100000000000000 : ℝ)^3671
        have hw : |(4124979523/10000000000 : ℝ)|=(4124979523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5365619637/10000000000 : ℝ)|^4695 ≤ (5637794434117/12500000000000 : ℝ)^3671
        have hw : |(5365619637/10000000000 : ℝ)|=(5365619637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134163841/10000000000 : ℝ)|^4695 ≤ (22676098569009/100000000000000 : ℝ)^3671
        have hw : |(3134163841/10000000000 : ℝ)|=(3134163841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_8 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (844597/156250000 : ℝ)*x 0 + (33258441/62500000 : ℝ)*x 1 + (6287996487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844597/156250000 : ℝ)^4695 ≤ (126013773713/100000000000000 : ℝ)^3671 := by
    have hnat : (844597 : ℕ)^4695*100000000000000^3671 ≤ 126013773713^3671*156250000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844597 156250000 126013773713 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33258441/62500000 : ℝ)^4695 ≤ (44626987422653/100000000000000 : ℝ)^3671 := by
    have hnat : (33258441 : ℕ)^4695*100000000000000^3671 ≤ 44626987422653^3671*62500000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33258441 62500000 44626987422653 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6287996487/10000000000 : ℝ)^4695 ≤ (2209879951893/4000000000000 : ℝ)^3671 := by
    have hnat : (6287996487 : ℕ)^4695*4000000000000^3671 ≤ 2209879951893^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6287996487 10000000000 2209879951893 4000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844597/156250000 : ℝ), (33258441/62500000 : ℝ), (6287996487/10000000000 : ℝ)] ![(126013773713/100000000000000 : ℝ), (44626987422653/100000000000000 : ℝ), (2209879951893/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844597/156250000 : ℝ)|^4695 ≤ (126013773713/100000000000000 : ℝ)^3671
        have hw : |(844597/156250000 : ℝ)|=(844597/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33258441/62500000 : ℝ)|^4695 ≤ (44626987422653/100000000000000 : ℝ)^3671
        have hw : |(33258441/62500000 : ℝ)|=(33258441/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6287996487/10000000000 : ℝ)|^4695 ≤ (2209879951893/4000000000000 : ℝ)^3671
        have hw : |(6287996487/10000000000 : ℝ)|=(6287996487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_9 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (310669841/2500000000 : ℝ)*x 0 + (-3651211667/10000000000 : ℝ)*x 1 + (3591077903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (310669841/2500000000 : ℝ)^4695 ≤ (6946032838909/100000000000000 : ℝ)^3671 := by
    have hnat : (310669841 : ℕ)^4695*100000000000000^3671 ≤ 6946032838909^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310669841 2500000000 6946032838909 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3651211667/10000000000 : ℝ)^4695 ≤ (27566513897339/100000000000000 : ℝ)^3671 := by
    have hnat : (3651211667 : ℕ)^4695*100000000000000^3671 ≤ 27566513897339^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3651211667 10000000000 27566513897339 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3591077903/5000000000 : ℝ)^4695 ≤ (65487453256439/100000000000000 : ℝ)^3671 := by
    have hnat : (3591077903 : ℕ)^4695*100000000000000^3671 ≤ 65487453256439^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3591077903 5000000000 65487453256439 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(310669841/2500000000 : ℝ), (-3651211667/10000000000 : ℝ), (3591077903/5000000000 : ℝ)] ![(6946032838909/100000000000000 : ℝ), (27566513897339/100000000000000 : ℝ), (65487453256439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(310669841/2500000000 : ℝ)|^4695 ≤ (6946032838909/100000000000000 : ℝ)^3671
        have hw : |(310669841/2500000000 : ℝ)|=(310669841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3651211667/10000000000 : ℝ)|^4695 ≤ (27566513897339/100000000000000 : ℝ)^3671
        have hw : |(-3651211667/10000000000 : ℝ)|=(3651211667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3591077903/5000000000 : ℝ)|^4695 ≤ (65487453256439/100000000000000 : ℝ)^3671
        have hw : |(3591077903/5000000000 : ℝ)|=(3591077903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_10 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1377633591/10000000000 : ℝ)*x 0 + (3755496811/5000000000 : ℝ)*x 1 + (-49059853/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377633591/10000000000 : ℝ)^4695 ≤ (7925032356791/100000000000000 : ℝ)^3671 := by
    have hnat : (1377633591 : ℕ)^4695*100000000000000^3671 ≤ 7925032356791^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377633591 10000000000 7925032356791 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3755496811/5000000000 : ℝ)^4695 ≤ (69346419551713/100000000000000 : ℝ)^3671 := by
    have hnat : (3755496811 : ℕ)^4695*100000000000000^3671 ≤ 69346419551713^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755496811 5000000000 69346419551713 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49059853/156250000 : ℝ)^4695 ≤ (5682137019841/25000000000000 : ℝ)^3671 := by
    have hnat : (49059853 : ℕ)^4695*25000000000000^3671 ≤ 5682137019841^3671*156250000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49059853 156250000 5682137019841 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377633591/10000000000 : ℝ), (3755496811/5000000000 : ℝ), (-49059853/156250000 : ℝ)] ![(7925032356791/100000000000000 : ℝ), (69346419551713/100000000000000 : ℝ), (5682137019841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377633591/10000000000 : ℝ)|^4695 ≤ (7925032356791/100000000000000 : ℝ)^3671
        have hw : |(1377633591/10000000000 : ℝ)|=(1377633591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3755496811/5000000000 : ℝ)|^4695 ≤ (69346419551713/100000000000000 : ℝ)^3671
        have hw : |(3755496811/5000000000 : ℝ)|=(3755496811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49059853/156250000 : ℝ)|^4695 ≤ (5682137019841/25000000000000 : ℝ)^3671
        have hw : |(-49059853/156250000 : ℝ)|=(49059853/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s0_11 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2364108737/10000000000 : ℝ)*x 0 + (5588550189/10000000000 : ℝ)*x 1 + (4564525663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2364108737/10000000000 : ℝ)^4695 ≤ (15810890277557/100000000000000 : ℝ)^3671 := by
    have hnat : (2364108737 : ℕ)^4695*100000000000000^3671 ≤ 15810890277557^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364108737 10000000000 15810890277557 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5588550189/10000000000 : ℝ)^4695 ≤ (23756366199939/50000000000000 : ℝ)^3671 := by
    have hnat : (5588550189 : ℕ)^4695*50000000000000^3671 ≤ 23756366199939^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5588550189 10000000000 23756366199939 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564525663/10000000000 : ℝ)^4695 ≤ (1833818865471/5000000000000 : ℝ)^3671 := by
    have hnat : (4564525663 : ℕ)^4695*5000000000000^3671 ≤ 1833818865471^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564525663 10000000000 1833818865471 5000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2364108737/10000000000 : ℝ), (5588550189/10000000000 : ℝ), (4564525663/10000000000 : ℝ)] ![(15810890277557/100000000000000 : ℝ), (23756366199939/50000000000000 : ℝ), (1833818865471/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2364108737/10000000000 : ℝ)|^4695 ≤ (15810890277557/100000000000000 : ℝ)^3671
        have hw : |(2364108737/10000000000 : ℝ)|=(2364108737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5588550189/10000000000 : ℝ)|^4695 ≤ (23756366199939/50000000000000 : ℝ)^3671
        have hw : |(5588550189/10000000000 : ℝ)|=(5588550189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564525663/10000000000 : ℝ)|^4695 ≤ (1833818865471/5000000000000 : ℝ)^3671
        have hw : |(4564525663/10000000000 : ℝ)|=(4564525663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1833/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3077/12500 : ℝ)*pair X 0 0 := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4691/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4691 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4691*1^1024 ≤ 0^1024*1^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4691/1024 : ℝ) ≤ (1503194084177163981/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4691 ≤ (1503194084177163981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4691*100000000000000000000^1024 ≤ 1503194084177163981^1024*5^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1503194084177163981 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1503194084177163981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4691 := by
      have hnat : (1 : ℕ)^1024*1^4691 ≤ 1^4691*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101503194084177163981/100000000000000000000 : ℝ) ≤ (10032622190529153/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (101503194084177163981/100000000000000000000 : ℝ)^1024 ≤ (10032622190529153/10000000000000000 : ℝ)^4691 := by
      have hnat : (101503194084177163981 : ℕ)^1024*10000000000000000^4691 ≤ 10032622190529153^4691*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101503194084177163981 100000000000000000000 10032622190529153 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032622190529153/10000000000000000 : ℝ)) (X := (101503194084177163981/100000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51503194084177163981/50000000000000000000 : ℝ) ≤ (5032622190529153/5000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (51503194084177163981/50000000000000000000 : ℝ)^1024 ≤ (5032622190529153/5000000000000000 : ℝ)^4691 := by
      have hnat : (51503194084177163981 : ℕ)^1024*5000000000000000^4691 ≤ 5032622190529153^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51503194084177163981 50000000000000000000 5032622190529153 5000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032622190529153/5000000000000000 : ℝ)) (X := (51503194084177163981/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(32622190529153/4000000000000000 : ℝ)*(0 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32622190529153/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1503194084177163981/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(32622190529153/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (1 : ℝ)+(32622190529153/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10032622190529153/10000000000000000 : ℝ) by norm_num, show 1+(1503194084177163981/100000000000000000000 : ℝ)+(0 : ℝ)=(101503194084177163981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1503194084177163981/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(32622190529153/4000000000000000 : ℝ)*(2/5 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32622190529153/4000000000000000 : ℝ)*(2/5 : ℝ)=(5032622190529153/5000000000000000 : ℝ) by norm_num, show 1+2*(1503194084177163981/100000000000000000000 : ℝ)=(51503194084177163981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(32622190529153/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32622190529153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(32622190529153/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32622190529153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(32622190529153/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32622190529153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399056747/2500000000 : ℝ)*X 0 0+(585917353/1000000000 : ℝ)*X 0 1+(4880799061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1365089801/2500000000 : ℝ)*X 1 0+(-2139912151/10000000000 : ℝ)*X 1 1+(4880798923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5460359211/10000000000 : ℝ)*X 2 0+(4880798877/10000000000 : ℝ)*X 2 1+(-10699561/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1029428533/2500000000 : ℝ)*X 0 0+(614400631/2000000000 : ℝ)*X 0 1+(1356407769/2500000000 : ℝ)*X 0 2+(1029428533/2500000000 : ℝ)*X 1 0+(614400631/2000000000 : ℝ)*X 1 1+(1356407769/2500000000 : ℝ)*X 1 2+(1029428533/2500000000 : ℝ)*X 2 0+(614400631/2000000000 : ℝ)*X 2 1+(1356407769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-799624269/5000000000 : ℝ)*X 0 0+(1226435809/2500000000 : ℝ)*X 0 1+(1458333267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596565563/5000000000 : ℝ)*X 1 0+(-593689059/5000000000 : ℝ)*X 1 1+(5833333571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519312971/1000000000 : ℝ)*X 2 0+(2916667571/5000000000 : ℝ)*X 2 1+(-237475561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4124979523/10000000000 : ℝ)*X 0 0+(5365619637/10000000000 : ℝ)*X 0 1+(3134163841/10000000000 : ℝ)*X 0 2+(4124979523/10000000000 : ℝ)*X 1 0+(5365619637/10000000000 : ℝ)*X 1 1+(3134163841/10000000000 : ℝ)*X 1 2+(4124979523/10000000000 : ℝ)*X 2 0+(5365619637/10000000000 : ℝ)*X 2 1+(3134163841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((844597/156250000 : ℝ)*X 0 0+(33258441/62500000 : ℝ)*X 0 1+(6287996487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((310669841/2500000000 : ℝ)*X 1 0+(-3651211667/10000000000 : ℝ)*X 1 1+(3591077903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1377633591/10000000000 : ℝ)*X 2 0+(3755496811/5000000000 : ℝ)*X 2 1+(-49059853/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2364108737/10000000000 : ℝ)*X 0 0+(5588550189/10000000000 : ℝ)*X 0 1+(4564525663/10000000000 : ℝ)*X 0 2+(2364108737/10000000000 : ℝ)*X 1 0+(5588550189/10000000000 : ℝ)*X 1 1+(4564525663/10000000000 : ℝ)*X 1 2+(2364108737/10000000000 : ℝ)*X 2 0+(5588550189/10000000000 : ℝ)*X 2 1+(4564525663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s0_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113318248822982856714939/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180873397803721/25000000000000 : ℝ)*(major0) + (180873397803721/25000000000000 : ℝ)*(major1) + (180873397803721/25000000000000 : ℝ)*(major2) + (511052991669823/50000000000000 : ℝ)*(sp0) + (1022106147916229/100000000000000 : ℝ)*(sp1) + (511053196953583/50000000000000 : ℝ)*(sp2) + (13277396920353/3125000000000 : ℝ)*(sp3) + (44964963/4000000000000 : ℝ)*(sp4) + (331321971/20000000000000 : ℝ)*(sp5) + (683599203/50000000000000 : ℝ)*(sp6) + (692286121/50000000000000 : ℝ)*(sp8) + (687509879/100000000000000 : ℝ)*(sp9) + (730930391/100000000000000 : ℝ)*(sp10) + (322243001/20000000000000 : ℝ)*(sp11) + (4248783126663/1000000000000 : ℝ)*(f.failure) + (255527123008991/25000000000000 : ℝ)*(f.sum) + (136017452371687/50000000000000000000000000000 : ℝ)*base66 + (7321279878313/100000000000000000000000000000 : ℝ)*base67 + (87587594721687/100000000000000000000000000000 : ℝ)*base70 + (151194893521687/100000000000000000000000000000 : ℝ)*base72 + (232928730771687/50000000000000000000000000000 : ℝ)*base74 + (166944863321687/100000000000000000000000000000 : ℝ)*base76 + (338715590021687/100000000000000000000000000000 : ℝ)*base78 + (58905703721687/100000000000000000000000000000 : ℝ)*base80 + (230779093071687/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (191327/50000000000000000000 : ℝ)*base90 + (191327/50000000000000000000 : ℝ)*base92 + (191327/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106579757364307366046679/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17020557/12500000000000 : ℝ)*(base21) + (4508161/6250000000000 : ℝ)*(base59) + (1687851/3125000000000 : ℝ)*(upper5) + (763101011087581/100000000000000 : ℝ)*(major0) + (763101011087581/100000000000000 : ℝ)*(major1) + (763101011087581/100000000000000 : ℝ)*(major2) + (493926223/100000000000000 : ℝ)*(sp0) + (563963639/100000000000000 : ℝ)*(sp2) + (215612218577227/20000000000000 : ℝ)*(sp4) + (539031907139527/50000000000000 : ℝ)*(sp5) + (13475788926887/1250000000000 : ℝ)*(sp6) + (56017161399427/12500000000000 : ℝ)*(sp7) + (278433337/12500000000000 : ℝ)*(sp8) + (169129503/20000000000000 : ℝ)*(sp11) + (448138136842931/100000000000000 : ℝ)*(f.failure) + (539031907139527/50000000000000 : ℝ)*(f.sum) + (654904570651107/200000000000000000000000000000 : ℝ)*base66 + (2550447238051107/400000000000000000000000000000 : ℝ)*base68 + (514743997651107/400000000000000000000000000000 : ℝ)*base70 + (2197673554051107/400000000000000000000000000000 : ℝ)*base72 + (918512374251107/200000000000000000000000000000 : ℝ)*base74 + (205518437251107/400000000000000000000000000000 : ℝ)*base76 + (3840279804051107/400000000000000000000000000000 : ℝ)*base78 + (3410931203251107/400000000000000000000000000000 : ℝ)*base80 + (6164076548893/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22705301/5000000000000000000000 : ℝ)*base89 + (22705301/5000000000000000000000 : ℝ)*base91 + (22705301/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1594_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1833/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3077/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1594_s1_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431800981/2500000000 : ℝ)*x 0 + (5545599461/10000000000 : ℝ)*x 1 + (2554909289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431800981/2500000000 : ℝ)^4695 ≤ (10582929547379/100000000000000 : ℝ)^3671 := by
    have hnat : (431800981 : ℕ)^4695*100000000000000^3671 ≤ 10582929547379^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431800981 2500000000 10582929547379 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5545599461/10000000000 : ℝ)^4695 ≤ (1470194282199/3125000000000 : ℝ)^3671 := by
    have hnat : (5545599461 : ℕ)^4695*3125000000000^3671 ≤ 1470194282199^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5545599461 10000000000 1470194282199 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2554909289/5000000000 : ℝ)^4695 ≤ (42370853411277/100000000000000 : ℝ)^3671 := by
    have hnat : (2554909289 : ℕ)^4695*100000000000000^3671 ≤ 42370853411277^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554909289 5000000000 42370853411277 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431800981/2500000000 : ℝ), (5545599461/10000000000 : ℝ), (2554909289/5000000000 : ℝ)] ![(10582929547379/100000000000000 : ℝ), (1470194282199/3125000000000 : ℝ), (42370853411277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431800981/2500000000 : ℝ)|^4695 ≤ (10582929547379/100000000000000 : ℝ)^3671
        have hw : |(-431800981/2500000000 : ℝ)|=(431800981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5545599461/10000000000 : ℝ)|^4695 ≤ (1470194282199/3125000000000 : ℝ)^3671
        have hw : |(5545599461/10000000000 : ℝ)|=(5545599461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2554909289/5000000000 : ℝ)|^4695 ≤ (42370853411277/100000000000000 : ℝ)^3671
        have hw : |(2554909289/5000000000 : ℝ)|=(2554909289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688424743/5000000000 : ℝ)*x 0 + (-1955759623/10000000000 : ℝ)*x 1 + (5109818433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688424743/5000000000 : ℝ)^4695 ≤ (353305607131/781250000000 : ℝ)^3671 := by
    have hnat : (2688424743 : ℕ)^4695*781250000000^3671 ≤ 353305607131^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688424743 5000000000 353305607131 781250000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955759623/10000000000 : ℝ)^4695 ≤ (12406030395639/100000000000000 : ℝ)^3671 := by
    have hnat : (1955759623 : ℕ)^4695*100000000000000^3671 ≤ 12406030395639^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955759623 10000000000 12406030395639 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5109818433/10000000000 : ℝ)^4695 ≤ (5296356484193/12500000000000 : ℝ)^3671 := by
    have hnat : (5109818433 : ℕ)^4695*12500000000000^3671 ≤ 5296356484193^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109818433 10000000000 5296356484193 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688424743/5000000000 : ℝ), (-1955759623/10000000000 : ℝ), (5109818433/10000000000 : ℝ)] ![(353305607131/781250000000 : ℝ), (12406030395639/100000000000000 : ℝ), (5296356484193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688424743/5000000000 : ℝ)|^4695 ≤ (353305607131/781250000000 : ℝ)^3671
        have hw : |(2688424743/5000000000 : ℝ)|=(2688424743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955759623/10000000000 : ℝ)|^4695 ≤ (12406030395639/100000000000000 : ℝ)^3671
        have hw : |(-1955759623/10000000000 : ℝ)|=(1955759623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5109818433/10000000000 : ℝ)|^4695 ≤ (5296356484193/12500000000000 : ℝ)^3671
        have hw : |(5109818433/10000000000 : ℝ)|=(5109818433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13442123/25000000 : ℝ)*x 0 + (5109818671/10000000000 : ℝ)*x 1 + (-1955759691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13442123/25000000 : ℝ)^4695 ≤ (22611557318159/50000000000000 : ℝ)^3671 := by
    have hnat : (13442123 : ℕ)^4695*50000000000000^3671 ≤ 22611557318159^3671*25000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13442123 25000000 22611557318159 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5109818671/10000000000 : ℝ)^4695 ≤ (42370854397547/100000000000000 : ℝ)^3671 := by
    have hnat : (5109818671 : ℕ)^4695*100000000000000^3671 ≤ 42370854397547^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109818671 10000000000 42370854397547 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955759691/10000000000 : ℝ)^4695 ≤ (12406030947307/100000000000000 : ℝ)^3671 := by
    have hnat : (1955759691 : ℕ)^4695*100000000000000^3671 ≤ 12406030947307^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955759691 10000000000 12406030947307 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13442123/25000000 : ℝ), (5109818671/10000000000 : ℝ), (-1955759691/10000000000 : ℝ)] ![(22611557318159/50000000000000 : ℝ), (42370854397547/100000000000000 : ℝ), (12406030947307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13442123/25000000 : ℝ)|^4695 ≤ (22611557318159/50000000000000 : ℝ)^3671
        have hw : |(13442123/25000000 : ℝ)|=(13442123/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5109818671/10000000000 : ℝ)|^4695 ≤ (42370854397547/100000000000000 : ℝ)^3671
        have hw : |(5109818671/10000000000 : ℝ)|=(5109818671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955759691/10000000000 : ℝ)|^4695 ≤ (12406030947307/100000000000000 : ℝ)^3671
        have hw : |(-1955759691/10000000000 : ℝ)|=(1955759691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2106352331/5000000000 : ℝ)*x 0 + (3714193951/10000000000 : ℝ)*x 1 + (4762530787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106352331/5000000000 : ℝ)^4695 ≤ (33100527189497/100000000000000 : ℝ)^3671 := by
    have hnat : (2106352331 : ℕ)^4695*100000000000000^3671 ≤ 33100527189497^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106352331 5000000000 33100527189497 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3714193951/10000000000 : ℝ)^4695 ≤ (14088063122163/50000000000000 : ℝ)^3671 := by
    have hnat : (3714193951 : ℕ)^4695*50000000000000^3671 ≤ 14088063122163^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714193951 10000000000 14088063122163 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4762530787/10000000000 : ℝ)^4695 ≤ (2420209159289/6250000000000 : ℝ)^3671 := by
    have hnat : (4762530787 : ℕ)^4695*6250000000000^3671 ≤ 2420209159289^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762530787 10000000000 2420209159289 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106352331/5000000000 : ℝ), (3714193951/10000000000 : ℝ), (4762530787/10000000000 : ℝ)] ![(33100527189497/100000000000000 : ℝ), (14088063122163/50000000000000 : ℝ), (2420209159289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106352331/5000000000 : ℝ)|^4695 ≤ (33100527189497/100000000000000 : ℝ)^3671
        have hw : |(2106352331/5000000000 : ℝ)|=(2106352331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3714193951/10000000000 : ℝ)|^4695 ≤ (14088063122163/50000000000000 : ℝ)^3671
        have hw : |(3714193951/10000000000 : ℝ)|=(3714193951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4762530787/10000000000 : ℝ)|^4695 ≤ (2420209159289/6250000000000 : ℝ)^3671
        have hw : |(4762530787/10000000000 : ℝ)|=(4762530787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1727463753/10000000000 : ℝ)*x 0 + (1022942371/2000000000 : ℝ)*x 1 + (5540627701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1727463753/10000000000 : ℝ)^4695 ≤ (10584965699563/100000000000000 : ℝ)^3671 := by
    have hnat : (1727463753 : ℕ)^4695*100000000000000^3671 ≤ 10584965699563^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727463753 10000000000 10584965699563 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022942371/2000000000 : ℝ)^4695 ≤ (42422753814419/100000000000000 : ℝ)^3671 := by
    have hnat : (1022942371 : ℕ)^4695*100000000000000^3671 ≤ 42422753814419^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022942371 2000000000 42422753814419 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540627701/10000000000 : ℝ)^4695 ≤ (23496140234343/50000000000000 : ℝ)^3671 := by
    have hnat : (5540627701 : ℕ)^4695*50000000000000^3671 ≤ 23496140234343^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540627701 10000000000 23496140234343 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1727463753/10000000000 : ℝ), (1022942371/2000000000 : ℝ), (5540627701/10000000000 : ℝ)] ![(10584965699563/100000000000000 : ℝ), (42422753814419/100000000000000 : ℝ), (23496140234343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1727463753/10000000000 : ℝ)|^4695 ≤ (10584965699563/100000000000000 : ℝ)^3671
        have hw : |(-1727463753/10000000000 : ℝ)|=(1727463753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1022942371/2000000000 : ℝ)|^4695 ≤ (42422753814419/100000000000000 : ℝ)^3671
        have hw : |(1022942371/2000000000 : ℝ)|=(1022942371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540627701/10000000000 : ℝ)|^4695 ≤ (23496140234343/50000000000000 : ℝ)^3671
        have hw : |(5540627701/10000000000 : ℝ)|=(5540627701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261220061/10000000000 : ℝ)*x 0 + (-1524950379/10000000000 : ℝ)*x 1 + (5540627937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261220061/10000000000 : ℝ)^4695 ≤ (43983063058917/100000000000000 : ℝ)^3671 := by
    have hnat : (5261220061 : ℕ)^4695*100000000000000^3671 ≤ 43983063058917^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261220061 10000000000 43983063058917 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1524950379/10000000000 : ℝ)^4695 ≤ (4512326949137/50000000000000 : ℝ)^3671 := by
    have hnat : (1524950379 : ℕ)^4695*50000000000000^3671 ≤ 4512326949137^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524950379 10000000000 4512326949137 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540627937/10000000000 : ℝ)^4695 ≤ (5874035378579/12500000000000 : ℝ)^3671 := by
    have hnat : (5540627937 : ℕ)^4695*12500000000000^3671 ≤ 5874035378579^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540627937 10000000000 5874035378579 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261220061/10000000000 : ℝ), (-1524950379/10000000000 : ℝ), (5540627937/10000000000 : ℝ)] ![(43983063058917/100000000000000 : ℝ), (4512326949137/50000000000000 : ℝ), (5874035378579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261220061/10000000000 : ℝ)|^4695 ≤ (43983063058917/100000000000000 : ℝ)^3671
        have hw : |(5261220061/10000000000 : ℝ)|=(5261220061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1524950379/10000000000 : ℝ)|^4695 ≤ (4512326949137/50000000000000 : ℝ)^3671
        have hw : |(-1524950379/10000000000 : ℝ)|=(1524950379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540627937/10000000000 : ℝ)|^4695 ≤ (5874035378579/12500000000000 : ℝ)^3671
        have hw : |(5540627937/10000000000 : ℝ)|=(5540627937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261219607/10000000000 : ℝ)*x 0 + (5540628099/10000000000 : ℝ)*x 1 + (-381237697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261219607/10000000000 : ℝ)^4695 ≤ (43983058204847/100000000000000 : ℝ)^3671 := by
    have hnat : (5261219607 : ℕ)^4695*100000000000000^3671 ≤ 43983058204847^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261219607 10000000000 43983058204847 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5540628099/10000000000 : ℝ)^4695 ≤ (23496142392941/50000000000000 : ℝ)^3671 := by
    have hnat : (5540628099 : ℕ)^4695*50000000000000^3671 ≤ 23496142392941^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540628099 10000000000 23496142392941 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381237697/2500000000 : ℝ)^4695 ≤ (9024656993907/100000000000000 : ℝ)^3671 := by
    have hnat : (381237697 : ℕ)^4695*100000000000000^3671 ≤ 9024656993907^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381237697 2500000000 9024656993907 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261219607/10000000000 : ℝ), (5540628099/10000000000 : ℝ), (-381237697/2500000000 : ℝ)] ![(43983058204847/100000000000000 : ℝ), (23496142392941/50000000000000 : ℝ), (9024656993907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261219607/10000000000 : ℝ)|^4695 ≤ (43983058204847/100000000000000 : ℝ)^3671
        have hw : |(5261219607/10000000000 : ℝ)|=(5261219607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5540628099/10000000000 : ℝ)|^4695 ≤ (23496142392941/50000000000000 : ℝ)^3671
        have hw : |(5540628099/10000000000 : ℝ)|=(5540628099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381237697/2500000000 : ℝ)|^4695 ≤ (9024656993907/100000000000000 : ℝ)^3671
        have hw : |(-381237697/2500000000 : ℝ)|=(381237697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s1_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213329103/10000000000 : ℝ)*x 0 + (950151963/2000000000 : ℝ)*x 1 + (3726153713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213329103/10000000000 : ℝ)^4695 ≤ (8276700589883/25000000000000 : ℝ)^3671 := by
    have hnat : (4213329103 : ℕ)^4695*25000000000000^3671 ≤ 8276700589883^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213329103 10000000000 8276700589883 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950151963/2000000000 : ℝ)^4695 ≤ (9650245979667/25000000000000 : ℝ)^3671 := by
    have hnat : (950151963 : ℕ)^4695*25000000000000^3671 ≤ 9650245979667^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950151963 2000000000 9650245979667 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3726153713/10000000000 : ℝ)^4695 ≤ (28292213702719/100000000000000 : ℝ)^3671 := by
    have hnat : (3726153713 : ℕ)^4695*100000000000000^3671 ≤ 28292213702719^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726153713 10000000000 28292213702719 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213329103/10000000000 : ℝ), (950151963/2000000000 : ℝ), (3726153713/10000000000 : ℝ)] ![(8276700589883/25000000000000 : ℝ), (9650245979667/25000000000000 : ℝ), (28292213702719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213329103/10000000000 : ℝ)|^4695 ≤ (8276700589883/25000000000000 : ℝ)^3671
        have hw : |(4213329103/10000000000 : ℝ)|=(4213329103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(950151963/2000000000 : ℝ)|^4695 ≤ (9650245979667/25000000000000 : ℝ)^3671
        have hw : |(950151963/2000000000 : ℝ)|=(950151963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3726153713/10000000000 : ℝ)|^4695 ≤ (28292213702719/100000000000000 : ℝ)^3671
        have hw : |(3726153713/10000000000 : ℝ)|=(3726153713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3077/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2207/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3611/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3077/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3077/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3077/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3077/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3077/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3077/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1833/50000 : ℝ) ^ (4691/1024 : ℝ) ≤ (26453743692887/100000000000000000000 : ℝ) := by
    have hpowers : (1833/50000 : ℝ)^4691 ≤ (26453743692887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1833 : ℕ)^4691*100000000000000000000^1024 ≤ 26453743692887^1024*50000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1833 50000 26453743692887 100000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1833/50000 : ℝ)) (X := (26453743692887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3077/12500 : ℝ) ^ (4691/1024 : ℝ) ≤ (81302519129494889/50000000000000000000 : ℝ) := by
    have hpowers : (3077/12500 : ℝ)^4691 ≤ (81302519129494889/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3077 : ℕ)^4691*50000000000000000000^1024 ≤ 81302519129494889^1024*12500^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3077 12500 81302519129494889 50000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3077/12500 : ℝ)) (X := (81302519129494889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000026453743692887/50000000000000000000 : ℝ) ≤ (125000014436489/125000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (50000026453743692887/50000000000000000000 : ℝ)^1024 ≤ (125000014436489/125000000000000 : ℝ)^4691 := by
      have hnat : (50000026453743692887 : ℕ)^1024*125000000000000^4691 ≤ 125000014436489^4691*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000026453743692887 50000000000000000000 125000014436489 125000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125000014436489/125000000000000 : ℝ)) (X := (50000026453743692887/50000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20032526298400536533/20000000000000000000 : ℝ) ≤ (2500886958493317/2500000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (20032526298400536533/20000000000000000000 : ℝ)^1024 ≤ (2500886958493317/2500000000000000 : ℝ)^4691 := by
      have hnat : (20032526298400536533 : ℕ)^1024*2500000000000000^4691 ≤ 2500886958493317^4691*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20032526298400536533 20000000000000000000 2500886958493317 2500000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500886958493317/2500000000000000 : ℝ)) (X := (20032526298400536533/20000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25081302519129494889/25000000000000000000 : ℝ) ≤ (1250886814128427/1250000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25081302519129494889/25000000000000000000 : ℝ)^1024 ≤ (1250886814128427/1250000000000000 : ℝ)^4691 := by
      have hnat : (25081302519129494889 : ℕ)^1024*1250000000000000^4691 ≤ 1250886814128427^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25081302519129494889 25000000000000000000 1250886814128427 1250000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250886814128427/1250000000000000 : ℝ)) (X := (25081302519129494889/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26453743692887/100000000000000000000 : ℝ) ≤ ((13092126246545659429/13093750000000000000 : ℝ)+2*(886669763537/523750000000000 : ℝ)*(1833/50000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (13092126246545659429/13093750000000000000 : ℝ)+2*(886669763537/523750000000000 : ℝ)*(1833/50000 : ℝ)=(125000014436489/125000000000000 : ℝ) by norm_num, show 1+2*(26453743692887/100000000000000000000 : ℝ)=(50000026453743692887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81302519129494889/50000000000000000000 : ℝ)+(26453743692887/100000000000000000000 : ℝ) ≤ ((13092126246545659429/13093750000000000000 : ℝ)+(886669763537/523750000000000 : ℝ)*((3077/12500 : ℝ)+(1833/50000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (13092126246545659429/13093750000000000000 : ℝ)+(886669763537/523750000000000 : ℝ)*((3077/12500 : ℝ)+(1833/50000 : ℝ))=(2500886958493317/2500000000000000 : ℝ) by norm_num, show 1+(81302519129494889/50000000000000000000 : ℝ)+(26453743692887/100000000000000000000 : ℝ)=(20032526298400536533/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81302519129494889/50000000000000000000 : ℝ) ≤ ((13092126246545659429/13093750000000000000 : ℝ)+2*(886669763537/523750000000000 : ℝ)*(3077/12500 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (13092126246545659429/13093750000000000000 : ℝ)+2*(886669763537/523750000000000 : ℝ)*(3077/12500 : ℝ)=(1250886814128427/1250000000000000 : ℝ) by norm_num, show 1+2*(81302519129494889/50000000000000000000 : ℝ)=(25081302519129494889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13092126246545659429/13093750000000000000 : ℝ)*(X 1 0+X 2 0)+(886669763537/523750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (1833/50000 : ℝ)) (hi := (3077/12500 : ℝ)) (c := (13092126246545659429/13093750000000000000 : ℝ)) (alpha := (886669763537/523750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13092126246545659429/13093750000000000000 : ℝ)*(X 0 1+X 2 1)+(886669763537/523750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (1833/50000 : ℝ)) (hi := (3077/12500 : ℝ)) (c := (13092126246545659429/13093750000000000000 : ℝ)) (alpha := (886669763537/523750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13092126246545659429/13093750000000000000 : ℝ)*(X 0 2+X 1 2)+(886669763537/523750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (1833/50000 : ℝ)) (hi := (3077/12500 : ℝ)) (c := (13092126246545659429/13093750000000000000 : ℝ)) (alpha := (886669763537/523750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431800981/2500000000 : ℝ)*X 0 0+(5545599461/10000000000 : ℝ)*X 0 1+(2554909289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688424743/5000000000 : ℝ)*X 1 0+(-1955759623/10000000000 : ℝ)*X 1 1+(5109818433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((13442123/25000000 : ℝ)*X 2 0+(5109818671/10000000000 : ℝ)*X 2 1+(-1955759691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2106352331/5000000000 : ℝ)*X 0 0+(3714193951/10000000000 : ℝ)*X 0 1+(4762530787/10000000000 : ℝ)*X 0 2+(2106352331/5000000000 : ℝ)*X 1 0+(3714193951/10000000000 : ℝ)*X 1 1+(4762530787/10000000000 : ℝ)*X 1 2+(2106352331/5000000000 : ℝ)*X 2 0+(3714193951/10000000000 : ℝ)*X 2 1+(4762530787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1727463753/10000000000 : ℝ)*X 0 0+(1022942371/2000000000 : ℝ)*X 0 1+(5540627701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261220061/10000000000 : ℝ)*X 1 0+(-1524950379/10000000000 : ℝ)*X 1 1+(5540627937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261219607/10000000000 : ℝ)*X 2 0+(5540628099/10000000000 : ℝ)*X 2 1+(-381237697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213329103/10000000000 : ℝ)*X 0 0+(950151963/2000000000 : ℝ)*X 0 1+(3726153713/10000000000 : ℝ)*X 0 2+(4213329103/10000000000 : ℝ)*X 1 0+(950151963/2000000000 : ℝ)*X 1 1+(3726153713/10000000000 : ℝ)*X 1 2+(4213329103/10000000000 : ℝ)*X 2 0+(950151963/2000000000 : ℝ)*X 2 1+(3726153713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1210532175712514817205324407/163671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64945479/100000000000000 : ℝ)*(base1) + (822072853/50000000000000 : ℝ)*(base19) + (761042683/50000000000000 : ℝ)*(base23) + (200624239/100000000000000 : ℝ)*(upper3) + (141525561/100000000000000 : ℝ)*(upper5) + (812165045879761/50000000000000 : ℝ)*(major0) + (812165045879761/50000000000000 : ℝ)*(major1) + (812165045879761/50000000000000 : ℝ)*(major2) + (1147372323562831/50000000000000 : ℝ)*(sp0) + (573688850348651/25000000000000 : ℝ)*(sp1) + (458951104690989/20000000000000 : ℝ)*(sp2) + (38155887926733/4000000000000 : ℝ)*(sp3) + (97370001/781250000000 : ℝ)*(sp4) + (2814164269/50000000000000 : ℝ)*(sp7) + (953902891442343/100000000000000 : ℝ)*(f.failure) + (2294757045540311/100000000000000 : ℝ)*(f.sum) + (232663629377/818359375000000000000000000 : ℝ)*base65 + (3355438779776471031/654687500000000000000000000000000 : ℝ)*base68 + (1402276542517096031/654687500000000000000000000000000 : ℝ)*base70 + (1238675619274908531/654687500000000000000000000000000 : ℝ)*base72 + (15231236547753/52375000000000000000000000000 : ℝ)*base73 + (756829692807903969/654687500000000000000000000000000 : ℝ)*base75 + (2586494167812408531/654687500000000000000000000000000 : ℝ)*base78 + (3477140258193658531/654687500000000000000000000000000 : ℝ)*base80 + (9092874082311/26187500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6237953/5000000000000000000000 : ℝ)*base89 + (6237953/5000000000000000000000 : ℝ)*base91 + (6237953/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (788405405547194620878810399/81835937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (459665121/25000000000000 : ℝ)*(base19) + (813159429/50000000000000 : ℝ)*(base23) + (8855183/100000000000000 : ℝ)*(upper2) + (290697789/100000000000000 : ℝ)*(upper3) + (11280873/6250000000000 : ℝ)*(upper5) + (25967692510919/1562500000000 : ℝ)*(major0) + (25967692510919/1562500000000 : ℝ)*(major1) + (25967692510919/1562500000000 : ℝ)*(major2) + (13570714513/100000000000000 : ℝ)*(sp1) + (494469429/4000000000000 : ℝ)*(sp2) + (1173939585797247/50000000000000 : ℝ)*(sp4) + (2347863762219497/100000000000000 : ℝ)*(sp5) + (293483147942489/12500000000000 : ℝ)*(sp6) + (975985148670623/100000000000000 : ℝ)*(sp7) + (975985148670623/100000000000000 : ℝ)*(f.failure) + (1173939585797247/50000000000000 : ℝ)*(f.sum) + (170167575259/52375000000000000000000000000 : ℝ)*base65 + (758645955771401383/163671875000000000000000000000000 : ℝ)*base67 + (29173945940317367/163671875000000000000000000000000 : ℝ)*base70 + (5387090128536373/40917968750000000000000000000000 : ℝ)*base72 + (170132196484759/52375000000000000000000000000 : ℝ)*base73 + (342904700845004867/163671875000000000000000000000000 : ℝ)*base76 + (1147709873651254867/163671875000000000000000000000000 : ℝ)*base78 + (2527971104276127/40917968750000000000000000000000 : ℝ)*base79 + (2735034543113/1636718750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2581833/5000000000000000000000 : ℝ)*base89 + (2581833/5000000000000000000000 : ℝ)*base91 + (2581833/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1594_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3077/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1594_s2_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-871736661/5000000000 : ℝ)*x 0 + (5473962699/10000000000 : ℝ)*x 1 + (1034167623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871736661/5000000000 : ℝ)^4695 ≤ (2677647316331/25000000000000 : ℝ)^3671 := by
    have hnat : (871736661 : ℕ)^4695*25000000000000^3671 ≤ 2677647316331^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871736661 5000000000 2677647316331 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473962699/10000000000 : ℝ)^4695 ≤ (9254073406257/20000000000000 : ℝ)^3671 := by
    have hnat : (5473962699 : ℕ)^4695*20000000000000^3671 ≤ 9254073406257^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473962699 10000000000 9254073406257 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034167623/2000000000 : ℝ)^4695 ≤ (43019043687263/100000000000000 : ℝ)^3671 := by
    have hnat : (1034167623 : ℕ)^4695*100000000000000^3671 ≤ 43019043687263^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034167623 2000000000 43019043687263 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-871736661/5000000000 : ℝ), (5473962699/10000000000 : ℝ), (1034167623/2000000000 : ℝ)] ![(2677647316331/25000000000000 : ℝ), (9254073406257/20000000000000 : ℝ), (43019043687263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-871736661/5000000000 : ℝ)|^4695 ≤ (2677647316331/25000000000000 : ℝ)^3671
        have hw : |(-871736661/5000000000 : ℝ)|=(871736661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473962699/10000000000 : ℝ)|^4695 ≤ (9254073406257/20000000000000 : ℝ)^3671
        have hw : |(5473962699/10000000000 : ℝ)|=(5473962699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034167623/2000000000 : ℝ)|^4695 ≤ (43019043687263/100000000000000 : ℝ)^3671
        have hw : |(1034167623/2000000000 : ℝ)|=(1034167623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339580003/2500000000 : ℝ)*x 0 + (-1900196967/10000000000 : ℝ)*x 1 + (5170837973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339580003/2500000000 : ℝ)^4695 ≤ (45023895407943/100000000000000 : ℝ)^3671 := by
    have hnat : (1339580003 : ℕ)^4695*100000000000000^3671 ≤ 45023895407943^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339580003 2500000000 45023895407943 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900196967/10000000000 : ℝ)^4695 ≤ (2391412479747/20000000000000 : ℝ)^3671 := by
    have hnat : (1900196967 : ℕ)^4695*20000000000000^3671 ≤ 2391412479747^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900196967 10000000000 2391412479747 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170837973/10000000000 : ℝ)^4695 ≤ (860380843527/2000000000000 : ℝ)^3671 := by
    have hnat : (5170837973 : ℕ)^4695*2000000000000^3671 ≤ 860380843527^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170837973 10000000000 860380843527 2000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339580003/2500000000 : ℝ), (-1900196967/10000000000 : ℝ), (5170837973/10000000000 : ℝ)] ![(45023895407943/100000000000000 : ℝ), (2391412479747/20000000000000 : ℝ), (860380843527/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339580003/2500000000 : ℝ)|^4695 ≤ (45023895407943/100000000000000 : ℝ)^3671
        have hw : |(1339580003/2500000000 : ℝ)|=(1339580003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900196967/10000000000 : ℝ)|^4695 ≤ (2391412479747/20000000000000 : ℝ)^3671
        have hw : |(-1900196967/10000000000 : ℝ)|=(1900196967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170837973/10000000000 : ℝ)|^4695 ≤ (860380843527/2000000000000 : ℝ)^3671
        have hw : |(5170837973/10000000000 : ℝ)|=(5170837973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358319743/10000000000 : ℝ)*x 0 + (1292709611/2500000000 : ℝ)*x 1 + (-59381147/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358319743/10000000000 : ℝ)^4695 ≤ (5627986564643/12500000000000 : ℝ)^3671 := by
    have hnat : (5358319743 : ℕ)^4695*12500000000000^3671 ≤ 5627986564643^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358319743 10000000000 5627986564643 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292709611/2500000000 : ℝ)^4695 ≤ (43019047187899/100000000000000 : ℝ)^3671 := by
    have hnat : (1292709611 : ℕ)^4695*100000000000000^3671 ≤ 43019047187899^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292709611 2500000000 43019047187899 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59381147/312500000 : ℝ)^4695 ≤ (2989265070541/25000000000000 : ℝ)^3671 := by
    have hnat : (59381147 : ℕ)^4695*25000000000000^3671 ≤ 2989265070541^3671*312500000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59381147 312500000 2989265070541 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358319743/10000000000 : ℝ), (1292709611/2500000000 : ℝ), (-59381147/312500000 : ℝ)] ![(5627986564643/12500000000000 : ℝ), (43019047187899/100000000000000 : ℝ), (2989265070541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358319743/10000000000 : ℝ)|^4695 ≤ (5627986564643/12500000000000 : ℝ)^3671
        have hw : |(5358319743/10000000000 : ℝ)|=(5358319743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292709611/2500000000 : ℝ)|^4695 ≤ (43019047187899/100000000000000 : ℝ)^3671
        have hw : |(1292709611/2500000000 : ℝ)|=(1292709611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59381147/312500000 : ℝ)|^4695 ≤ (2989265070541/25000000000000 : ℝ)^3671
        have hw : |(-59381147/312500000 : ℝ)|=(59381147/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112327763/5000000000 : ℝ)*x 0 + (1936232881/5000000000 : ℝ)*x 1 + (575209629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112327763/5000000000 : ℝ)^4695 ≤ (16610334766137/50000000000000 : ℝ)^3671 := by
    have hnat : (2112327763 : ℕ)^4695*50000000000000^3671 ≤ 16610334766137^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112327763 5000000000 16610334766137 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936232881/5000000000 : ℝ)^4695 ≤ (29720737390651/100000000000000 : ℝ)^3671 := by
    have hnat : (1936232881 : ℕ)^4695*100000000000000^3671 ≤ 29720737390651^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936232881 5000000000 29720737390651 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575209629/1250000000 : ℝ)^4695 ≤ (18529296528123/50000000000000 : ℝ)^3671 := by
    have hnat : (575209629 : ℕ)^4695*50000000000000^3671 ≤ 18529296528123^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575209629 1250000000 18529296528123 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112327763/5000000000 : ℝ), (1936232881/5000000000 : ℝ), (575209629/1250000000 : ℝ)] ![(16610334766137/50000000000000 : ℝ), (29720737390651/100000000000000 : ℝ), (18529296528123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112327763/5000000000 : ℝ)|^4695 ≤ (16610334766137/50000000000000 : ℝ)^3671
        have hw : |(2112327763/5000000000 : ℝ)|=(2112327763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936232881/5000000000 : ℝ)|^4695 ≤ (29720737390651/100000000000000 : ℝ)^3671
        have hw : |(1936232881/5000000000 : ℝ)|=(1936232881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(575209629/1250000000 : ℝ)|^4695 ≤ (18529296528123/50000000000000 : ℝ)^3671
        have hw : |(575209629/1250000000 : ℝ)|=(575209629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-174356057/1000000000 : ℝ)*x 0 + (129330347/250000000 : ℝ)*x 1 + (5471560681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174356057/1000000000 : ℝ)^4695 ≤ (5355637382917/50000000000000 : ℝ)^3671 := by
    have hnat : (174356057 : ℕ)^4695*50000000000000^3671 ≤ 5355637382917^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174356057 1000000000 5355637382917 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129330347/250000000 : ℝ)^4695 ≤ (43044323993379/100000000000000 : ℝ)^3671 := by
    have hnat : (129330347 : ℕ)^4695*100000000000000^3671 ≤ 43044323993379^3671*250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129330347 250000000 43044323993379 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471560681/10000000000 : ℝ)^4695 ≤ (11561100303489/25000000000000 : ℝ)^3671 := by
    have hnat : (5471560681 : ℕ)^4695*25000000000000^3671 ≤ 11561100303489^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471560681 10000000000 11561100303489 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174356057/1000000000 : ℝ), (129330347/250000000 : ℝ), (5471560681/10000000000 : ℝ)] ![(5355637382917/50000000000000 : ℝ), (43044323993379/100000000000000 : ℝ), (11561100303489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174356057/1000000000 : ℝ)|^4695 ≤ (5355637382917/50000000000000 : ℝ)^3671
        have hw : |(-174356057/1000000000 : ℝ)|=(174356057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129330347/250000000 : ℝ)|^4695 ≤ (43044323993379/100000000000000 : ℝ)^3671
        have hw : |(129330347/250000000 : ℝ)|=(129330347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471560681/10000000000 : ℝ)|^4695 ≤ (11561100303489/25000000000000 : ℝ)^3671
        have hw : |(5471560681/10000000000 : ℝ)|=(5471560681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639025127/5000000000 : ℝ)*x 0 + (-1599474273/10000000000 : ℝ)*x 1 + (5471560799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639025127/5000000000 : ℝ)^4695 ≤ (5520386010697/12500000000000 : ℝ)^3671 := by
    have hnat : (2639025127 : ℕ)^4695*12500000000000^3671 ≤ 5520386010697^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639025127 5000000000 5520386010697 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1599474273/10000000000 : ℝ)^4695 ≤ (959250941203/10000000000000 : ℝ)^3671 := by
    have hnat : (1599474273 : ℕ)^4695*10000000000000^3671 ≤ 959250941203^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599474273 10000000000 959250941203 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471560799/10000000000 : ℝ)^4695 ≤ (23122201244729/50000000000000 : ℝ)^3671 := by
    have hnat : (5471560799 : ℕ)^4695*50000000000000^3671 ≤ 23122201244729^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471560799 10000000000 23122201244729 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639025127/5000000000 : ℝ), (-1599474273/10000000000 : ℝ), (5471560799/10000000000 : ℝ)] ![(5520386010697/12500000000000 : ℝ), (959250941203/10000000000000 : ℝ), (23122201244729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639025127/5000000000 : ℝ)|^4695 ≤ (5520386010697/12500000000000 : ℝ)^3671
        have hw : |(2639025127/5000000000 : ℝ)|=(2639025127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1599474273/10000000000 : ℝ)|^4695 ≤ (959250941203/10000000000000 : ℝ)^3671
        have hw : |(-1599474273/10000000000 : ℝ)|=(1599474273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471560799/10000000000 : ℝ)|^4695 ≤ (23122201244729/50000000000000 : ℝ)^3671
        have hw : |(5471560799/10000000000 : ℝ)|=(5471560799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055610083/2000000000 : ℝ)*x 0 + (5471560501/10000000000 : ℝ)*x 1 + (-1599474467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055610083/2000000000 : ℝ)^4695 ≤ (44163089808487/100000000000000 : ℝ)^3671 := by
    have hnat : (1055610083 : ℕ)^4695*100000000000000^3671 ≤ 44163089808487^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055610083 2000000000 44163089808487 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471560501/10000000000 : ℝ)^4695 ≤ (1849775970731/4000000000000 : ℝ)^3671 := by
    have hnat : (5471560501 : ℕ)^4695*4000000000000^3671 ≤ 1849775970731^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471560501 10000000000 1849775970731 4000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1599474467/10000000000 : ℝ)^4695 ≤ (9592510900047/100000000000000 : ℝ)^3671 := by
    have hnat : (1599474467 : ℕ)^4695*100000000000000^3671 ≤ 9592510900047^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599474467 10000000000 9592510900047 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055610083/2000000000 : ℝ), (5471560501/10000000000 : ℝ), (-1599474467/10000000000 : ℝ)] ![(44163089808487/100000000000000 : ℝ), (1849775970731/4000000000000 : ℝ), (9592510900047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055610083/2000000000 : ℝ)|^4695 ≤ (44163089808487/100000000000000 : ℝ)^3671
        have hw : |(1055610083/2000000000 : ℝ)|=(1055610083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471560501/10000000000 : ℝ)|^4695 ≤ (1849775970731/4000000000000 : ℝ)^3671
        have hw : |(5471560501/10000000000 : ℝ)|=(5471560501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1599474467/10000000000 : ℝ)|^4695 ≤ (9592510900047/100000000000000 : ℝ)^3671
        have hw : |(-1599474467/10000000000 : ℝ)|=(1599474467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_s2_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528108249/1250000000 : ℝ)*x 0 + (2297981359/5000000000 : ℝ)*x 1 + (1939121963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528108249/1250000000 : ℝ)^4695 ≤ (33222786202763/100000000000000 : ℝ)^3671 := by
    have hnat : (528108249 : ℕ)^4695*100000000000000^3671 ≤ 33222786202763^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528108249 1250000000 33222786202763 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297981359/5000000000 : ℝ)^4695 ≤ (36999747610151/100000000000000 : ℝ)^3671 := by
    have hnat : (2297981359 : ℕ)^4695*100000000000000^3671 ≤ 36999747610151^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297981359 5000000000 36999747610151 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939121963/5000000000 : ℝ)^4695 ≤ (14888733082993/50000000000000 : ℝ)^3671 := by
    have hnat : (1939121963 : ℕ)^4695*50000000000000^3671 ≤ 14888733082993^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939121963 5000000000 14888733082993 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528108249/1250000000 : ℝ), (2297981359/5000000000 : ℝ), (1939121963/5000000000 : ℝ)] ![(33222786202763/100000000000000 : ℝ), (36999747610151/100000000000000 : ℝ), (14888733082993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528108249/1250000000 : ℝ)|^4695 ≤ (33222786202763/100000000000000 : ℝ)^3671
        have hw : |(528108249/1250000000 : ℝ)|=(528108249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297981359/5000000000 : ℝ)|^4695 ≤ (36999747610151/100000000000000 : ℝ)^3671
        have hw : |(2297981359/5000000000 : ℝ)|=(2297981359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1939121963/5000000000 : ℝ)|^4695 ≤ (14888733082993/50000000000000 : ℝ)^3671
        have hw : |(1939121963/5000000000 : ℝ)|=(1939121963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5073/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16567/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2207/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2207/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2207/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2207/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2207/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2207/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2207/25000 : ℝ) ^ (4691/1024 : ℝ) ≤ (741152648115839/50000000000000000000 : ℝ) := by
    have hpowers : (2207/25000 : ℝ)^4691 ≤ (741152648115839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2207 : ℕ)^4691*50000000000000000000^1024 ≤ 741152648115839^1024*25000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 25000 741152648115839 50000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/25000 : ℝ)) (X := (741152648115839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3611/20000 : ℝ) ^ (4691/1024 : ℝ) ≤ (7860722321646677/20000000000000000000 : ℝ) := by
    have hpowers : (3611/20000 : ℝ)^4691 ≤ (7860722321646677/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3611 : ℕ)^4691*20000000000000000000^1024 ≤ 7860722321646677^1024*20000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3611 20000 7860722321646677 20000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3611/20000 : ℝ)) (X := (7860722321646677/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000741152648115839/25000000000000000000 : ℝ) ≤ (2500016178459129/2500000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25000741152648115839/25000000000000000000 : ℝ)^1024 ≤ (2500016178459129/2500000000000000 : ℝ)^4691 := by
      have hnat : (25000741152648115839 : ℕ)^1024*2500000000000000^4691 ≤ 2500016178459129^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000741152648115839 25000000000000000000 2500016178459129 2500000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016178459129/2500000000000000 : ℝ)) (X := (25000741152648115839/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040785916904465063/100000000000000000000 : ℝ) ≤ (5000445087642757/5000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (100040785916904465063/100000000000000000000 : ℝ)^1024 ≤ (5000445087642757/5000000000000000 : ℝ)^4691 := by
      have hnat : (100040785916904465063 : ℕ)^1024*5000000000000000^4691 ≤ 5000445087642757^4691*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040785916904465063 100000000000000000000 5000445087642757 5000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000445087642757/5000000000000000 : ℝ)) (X := (100040785916904465063/100000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007860722321646677/10000000000000000000 : ℝ) ≤ (625107227295907/625000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (10007860722321646677/10000000000000000000 : ℝ)^1024 ≤ (625107227295907/625000000000000 : ℝ)^4691 := by
      have hnat : (10007860722321646677 : ℕ)^1024*625000000000000^4691 ≤ 625107227295907^4691*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007860722321646677 10000000000000000000 625107227295907 625000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625107227295907/625000000000000 : ℝ)) (X := (10007860722321646677/10000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(741152648115839/50000000000000000000 : ℝ) ≤ ((23064005691806506111/23067500000000000000 : ℝ)+2*(412730724499/461350000000000 : ℝ)*(2207/25000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (23064005691806506111/23067500000000000000 : ℝ)+2*(412730724499/461350000000000 : ℝ)*(2207/25000 : ℝ)=(2500016178459129/2500000000000000 : ℝ) by norm_num, show 1+2*(741152648115839/50000000000000000000 : ℝ)=(25000741152648115839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7860722321646677/20000000000000000000 : ℝ)+(741152648115839/50000000000000000000 : ℝ) ≤ ((23064005691806506111/23067500000000000000 : ℝ)+(412730724499/461350000000000 : ℝ)*((3611/20000 : ℝ)+(2207/25000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (23064005691806506111/23067500000000000000 : ℝ)+(412730724499/461350000000000 : ℝ)*((3611/20000 : ℝ)+(2207/25000 : ℝ))=(5000445087642757/5000000000000000 : ℝ) by norm_num, show 1+(7860722321646677/20000000000000000000 : ℝ)+(741152648115839/50000000000000000000 : ℝ)=(100040785916904465063/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7860722321646677/20000000000000000000 : ℝ) ≤ ((23064005691806506111/23067500000000000000 : ℝ)+2*(412730724499/461350000000000 : ℝ)*(3611/20000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (23064005691806506111/23067500000000000000 : ℝ)+2*(412730724499/461350000000000 : ℝ)*(3611/20000 : ℝ)=(625107227295907/625000000000000 : ℝ) by norm_num, show 1+2*(7860722321646677/20000000000000000000 : ℝ)=(10007860722321646677/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23064005691806506111/23067500000000000000 : ℝ)*(X 1 0+X 2 0)+(412730724499/461350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (23064005691806506111/23067500000000000000 : ℝ)) (alpha := (412730724499/461350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23064005691806506111/23067500000000000000 : ℝ)*(X 0 1+X 2 1)+(412730724499/461350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (23064005691806506111/23067500000000000000 : ℝ)) (alpha := (412730724499/461350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23064005691806506111/23067500000000000000 : ℝ)*(X 0 2+X 1 2)+(412730724499/461350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (23064005691806506111/23067500000000000000 : ℝ)) (alpha := (412730724499/461350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-871736661/5000000000 : ℝ)*X 0 0+(5473962699/10000000000 : ℝ)*X 0 1+(1034167623/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339580003/2500000000 : ℝ)*X 1 0+(-1900196967/10000000000 : ℝ)*X 1 1+(5170837973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358319743/10000000000 : ℝ)*X 2 0+(1292709611/2500000000 : ℝ)*X 2 1+(-59381147/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2112327763/5000000000 : ℝ)*X 0 0+(1936232881/5000000000 : ℝ)*X 0 1+(575209629/1250000000 : ℝ)*X 0 2+(2112327763/5000000000 : ℝ)*X 1 0+(1936232881/5000000000 : ℝ)*X 1 1+(575209629/1250000000 : ℝ)*X 1 2+(2112327763/5000000000 : ℝ)*X 2 0+(1936232881/5000000000 : ℝ)*X 2 1+(575209629/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-174356057/1000000000 : ℝ)*X 0 0+(129330347/250000000 : ℝ)*X 0 1+(5471560681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639025127/5000000000 : ℝ)*X 1 0+(-1599474273/10000000000 : ℝ)*X 1 1+(5471560799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055610083/2000000000 : ℝ)*X 2 0+(5471560501/10000000000 : ℝ)*X 2 1+(-1599474467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((528108249/1250000000 : ℝ)*X 0 0+(2297981359/5000000000 : ℝ)*X 0 1+(1939121963/5000000000 : ℝ)*X 0 2+(528108249/1250000000 : ℝ)*X 1 0+(2297981359/5000000000 : ℝ)*X 1 1+(1939121963/5000000000 : ℝ)*X 1 2+(528108249/1250000000 : ℝ)*X 2 0+(2297981359/5000000000 : ℝ)*X 2 1+(1939121963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214156661687460627154785849/18021484375000000000000000000000 : ℝ) := by norm_num
    linear_combination (245654413/12500000000000 : ℝ)*(base19) + (1672258207/100000000000000 : ℝ)*(base23) + (68243013/100000000000000 : ℝ)*(lower2) + (28987269/12500000000000 : ℝ)*(upper3) + (294156197/100000000000000 : ℝ)*(upper5) + (583797249618501/25000000000000 : ℝ)*(major0) + (583797249618501/25000000000000 : ℝ)*(major1) + (583797249618501/25000000000000 : ℝ)*(major2) + (1649496971292281/50000000000000 : ℝ)*(sp0) + (3299014266989719/100000000000000 : ℝ)*(sp1) + (103094204998963/3125000000000 : ℝ)*(sp2) + (342838294095721/25000000000000 : ℝ)*(sp3) + (22289640461/100000000000000 : ℝ)*(sp4) + (8192226473/100000000000000 : ℝ)*(sp7) + (1371361368609357/100000000000000 : ℝ)*(f.failure) + (3299016232225023/100000000000000 : ℝ)*(f.sum) + (114776870387041/23067500000000000000000000000 : ℝ)*base65 + (856923685901359611/576687500000000000000000000000000 : ℝ)*base67 + (7505862333741422111/576687500000000000000000000000000 : ℝ)*base69 + (2997427892715359611/576687500000000000000000000000000 : ℝ)*base71 + (87479924885877/46135000000000000000000000000 : ℝ)*base73 + (4869647872326922111/576687500000000000000000000000000 : ℝ)*base75 + (5718417333539109611/576687500000000000000000000000000 : ℝ)*base77 + (550783642000015389/576687500000000000000000000000000 : ℝ)*base80 + (112773380597511/23067500000000000000000000000 : ℝ)*base81 + (42527253/5000000000000000000000 : ℝ)*base90 + (42527253/5000000000000000000000 : ℝ)*base92 + (42527253/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121753904569931585038945611/9010742187500000000000000000000 : ℝ) := by norm_num
    linear_combination (813394559/50000000000000 : ℝ)*(base19) + (1032539849/50000000000000 : ℝ)*(base23) + (267345299/100000000000000 : ℝ)*(upper3) + (39555771/25000000000000 : ℝ)*(lower4) + (201754011/100000000000000 : ℝ)*(upper5) + (593138085898797/25000000000000 : ℝ)*(major0) + (593138085898797/25000000000000 : ℝ)*(major1) + (593138085898797/25000000000000 : ℝ)*(major2) + (16922144539/100000000000000 : ℝ)*(sp1) + (19307321301/100000000000000 : ℝ)*(sp2) + (13092972256581/390625000000 : ℝ)*(sp4) + (3351782348751079/100000000000000 : ℝ)*(sp5) + (418972440660467/12500000000000 : ℝ)*(sp6) + (348325834775709/25000000000000 : ℝ)*(sp7) + (348325834775709/25000000000000 : ℝ)*(f.failure) + (13092972256581/390625000000 : ℝ)*(f.sum) + (16004537234037/5766875000000000000000000000 : ℝ)*base66 + (2969971082885301533/576687500000000000000000000000000 : ℝ)*base68 + (5572928211463301533/576687500000000000000000000000000 : ℝ)*base70 + (2605036265346926533/576687500000000000000000000000000 : ℝ)*base72 + (3318533127389/11533750000000000000000000000 : ℝ)*base74 + (6662675175832301533/576687500000000000000000000000000 : ℝ)*base76 + (2029131646885864033/576687500000000000000000000000000 : ℝ)*base78 + (3692573593620948467/576687500000000000000000000000000 : ℝ)*base79 + (18819462690447/5766875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14186139/1250000000000000000000 : ℝ)*base89 + (14186139/1250000000000000000000 : ℝ)*base91 + (14186139/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1594_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1594_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1594_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1594_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1594_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1594_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5073/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16567/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

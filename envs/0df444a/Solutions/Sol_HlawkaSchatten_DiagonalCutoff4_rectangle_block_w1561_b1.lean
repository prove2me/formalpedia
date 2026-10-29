-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1561_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:38.488287+00:00
-- url     : https://prove2.me/submissions/1e878c50-09b8-4a51-a338-dd6be42ade69

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
theorem support_rectangle_w1561_s3_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797706131/10000000000 : ℝ)*x 0 + (5428789763/10000000000 : ℝ)*x 1 + (2609037327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797706131/10000000000 : ℝ)^4619 ≤ (551318717017/5000000000000 : ℝ)^3595 := by
    have hnat : (1797706131 : ℕ)^4619*5000000000000^3595 ≤ 551318717017^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797706131 10000000000 551318717017 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428789763/10000000000 : ℝ)^4619 ≤ (45617955558089/100000000000000 : ℝ)^3595 := by
    have hnat : (5428789763 : ℕ)^4619*100000000000000^3595 ≤ 45617955558089^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428789763 10000000000 45617955558089 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609037327/5000000000 : ℝ)^4619 ≤ (43355670093151/100000000000000 : ℝ)^3595 := by
    have hnat : (2609037327 : ℕ)^4619*100000000000000^3595 ≤ 43355670093151^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609037327 5000000000 43355670093151 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797706131/10000000000 : ℝ), (5428789763/10000000000 : ℝ), (2609037327/5000000000 : ℝ)] ![(551318717017/5000000000000 : ℝ), (45617955558089/100000000000000 : ℝ), (43355670093151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797706131/10000000000 : ℝ)|^4619 ≤ (551318717017/5000000000000 : ℝ)^3595
        have hw : |(-1797706131/10000000000 : ℝ)|=(1797706131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428789763/10000000000 : ℝ)|^4619 ≤ (45617955558089/100000000000000 : ℝ)^3595
        have hw : |(5428789763/10000000000 : ℝ)|=(5428789763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609037327/5000000000 : ℝ)|^4619 ≤ (43355670093151/100000000000000 : ℝ)^3595
        have hw : |(2609037327/5000000000 : ℝ)|=(2609037327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069846179/2000000000 : ℝ)*x 0 + (-952782079/5000000000 : ℝ)*x 1 + (2609037363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069846179/2000000000 : ℝ)^4619 ≤ (22380399776139/50000000000000 : ℝ)^3595 := by
    have hnat : (1069846179 : ℕ)^4619*50000000000000^3595 ≤ 22380399776139^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069846179 2000000000 22380399776139 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952782079/5000000000 : ℝ)^4619 ≤ (11883529557253/100000000000000 : ℝ)^3595 := by
    have hnat : (952782079 : ℕ)^4619*100000000000000^3595 ≤ 11883529557253^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952782079 5000000000 11883529557253 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609037363/5000000000 : ℝ)^4619 ≤ (43355670861781/100000000000000 : ℝ)^3595 := by
    have hnat : (2609037363 : ℕ)^4619*100000000000000^3595 ≤ 43355670861781^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609037363 5000000000 43355670861781 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069846179/2000000000 : ℝ), (-952782079/5000000000 : ℝ), (2609037363/5000000000 : ℝ)] ![(22380399776139/50000000000000 : ℝ), (11883529557253/100000000000000 : ℝ), (43355670861781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069846179/2000000000 : ℝ)|^4619 ≤ (22380399776139/50000000000000 : ℝ)^3595
        have hw : |(1069846179/2000000000 : ℝ)|=(1069846179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952782079/5000000000 : ℝ)|^4619 ≤ (11883529557253/100000000000000 : ℝ)^3595
        have hw : |(-952782079/5000000000 : ℝ)|=(952782079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609037363/5000000000 : ℝ)|^4619 ≤ (43355670861781/100000000000000 : ℝ)^3595
        have hw : |(2609037363/5000000000 : ℝ)|=(2609037363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674615349/5000000000 : ℝ)*x 0 + (1304518707/2500000000 : ℝ)*x 1 + (-14887221/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674615349/5000000000 : ℝ)^4619 ≤ (44760797434299/100000000000000 : ℝ)^3595 := by
    have hnat : (2674615349 : ℕ)^4619*100000000000000^3595 ≤ 44760797434299^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674615349 5000000000 44760797434299 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304518707/2500000000 : ℝ)^4619 ≤ (43355671950673/100000000000000 : ℝ)^3595 := by
    have hnat : (1304518707 : ℕ)^4619*100000000000000^3595 ≤ 43355671950673^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304518707 2500000000 43355671950673 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14887221/78125000 : ℝ)^4619 ≤ (2376706119777/20000000000000 : ℝ)^3595 := by
    have hnat : (14887221 : ℕ)^4619*20000000000000^3595 ≤ 2376706119777^3595*78125000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14887221 78125000 2376706119777 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674615349/5000000000 : ℝ), (1304518707/2500000000 : ℝ), (-14887221/78125000 : ℝ)] ![(44760797434299/100000000000000 : ℝ), (43355671950673/100000000000000 : ℝ), (2376706119777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674615349/5000000000 : ℝ)|^4619 ≤ (44760797434299/100000000000000 : ℝ)^3595
        have hw : |(2674615349/5000000000 : ℝ)|=(2674615349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304518707/2500000000 : ℝ)|^4619 ≤ (43355671950673/100000000000000 : ℝ)^3595
        have hw : |(1304518707/2500000000 : ℝ)|=(1304518707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14887221/78125000 : ℝ)|^4619 ≤ (2376706119777/20000000000000 : ℝ)^3595
        have hw : |(-14887221/78125000 : ℝ)|=(14887221/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84946221/200000000 : ℝ)*x 0 + (2002999349/5000000000 : ℝ)*x 1 + (4500356481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84946221/200000000 : ℝ)^4619 ≤ (33280209983141/100000000000000 : ℝ)^3595 := by
    have hnat : (84946221 : ℕ)^4619*100000000000000^3595 ≤ 33280209983141^3595*200000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84946221 200000000 33280209983141 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002999349/5000000000 : ℝ)^4619 ≤ (15435365984397/50000000000000 : ℝ)^3595 := by
    have hnat : (2002999349 : ℕ)^4619*50000000000000^3595 ≤ 15435365984397^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002999349 5000000000 15435365984397 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500356481/10000000000 : ℝ)^4619 ≤ (358490580371/1000000000000 : ℝ)^3595 := by
    have hnat : (4500356481 : ℕ)^4619*1000000000000^3595 ≤ 358490580371^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500356481 10000000000 358490580371 1000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84946221/200000000 : ℝ), (2002999349/5000000000 : ℝ), (4500356481/10000000000 : ℝ)] ![(33280209983141/100000000000000 : ℝ), (15435365984397/50000000000000 : ℝ), (358490580371/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84946221/200000000 : ℝ)|^4619 ≤ (33280209983141/100000000000000 : ℝ)^3595
        have hw : |(84946221/200000000 : ℝ)|=(84946221/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002999349/5000000000 : ℝ)|^4619 ≤ (15435365984397/50000000000000 : ℝ)^3595
        have hw : |(2002999349/5000000000 : ℝ)|=(2002999349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500356481/10000000000 : ℝ)|^4619 ≤ (358490580371/1000000000000 : ℝ)^3595
        have hw : |(4500356481/10000000000 : ℝ)|=(4500356481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-449433673/2500000000 : ℝ)*x 0 + (5219188693/10000000000 : ℝ)*x 1 + (5427667301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449433673/2500000000 : ℝ)^4619 ≤ (2756649855161/25000000000000 : ℝ)^3595 := by
    have hnat : (449433673 : ℕ)^4619*25000000000000^3595 ≤ 2756649855161^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449433673 2500000000 2756649855161 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219188693/10000000000 : ℝ)^4619 ≤ (43367563281081/100000000000000 : ℝ)^3595 := by
    have hnat : (5219188693 : ℕ)^4619*100000000000000^3595 ≤ 43367563281081^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219188693 10000000000 43367563281081 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427667301/10000000000 : ℝ)^4619 ≤ (5700729660679/12500000000000 : ℝ)^3595 := by
    have hnat : (5427667301 : ℕ)^4619*12500000000000^3595 ≤ 5700729660679^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427667301 10000000000 5700729660679 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449433673/2500000000 : ℝ), (5219188693/10000000000 : ℝ), (5427667301/10000000000 : ℝ)] ![(2756649855161/25000000000000 : ℝ), (43367563281081/100000000000000 : ℝ), (5700729660679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449433673/2500000000 : ℝ)|^4619 ≤ (2756649855161/25000000000000 : ℝ)^3595
        have hw : |(-449433673/2500000000 : ℝ)|=(449433673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219188693/10000000000 : ℝ)|^4619 ≤ (43367563281081/100000000000000 : ℝ)^3595
        have hw : |(5219188693/10000000000 : ℝ)|=(5219188693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427667301/10000000000 : ℝ)|^4619 ≤ (5700729660679/12500000000000 : ℝ)^3595
        have hw : |(5427667301/10000000000 : ℝ)|=(5427667301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529354247/1000000000 : ℝ)*x 0 + (-847985847/5000000000 : ℝ)*x 1 + (5427667181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529354247/1000000000 : ℝ)^4619 ≤ (8832594794681/20000000000000 : ℝ)^3595 := by
    have hnat : (529354247 : ℕ)^4619*20000000000000^3595 ≤ 8832594794681^3595*1000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529354247 1000000000 8832594794681 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847985847/5000000000 : ℝ)^4619 ≤ (204623800327/2000000000000 : ℝ)^3595 := by
    have hnat : (847985847 : ℕ)^4619*2000000000000^3595 ≤ 204623800327^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847985847 5000000000 204623800327 2000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427667181/10000000000 : ℝ)^4619 ≤ (45605835989931/100000000000000 : ℝ)^3595 := by
    have hnat : (5427667181 : ℕ)^4619*100000000000000^3595 ≤ 45605835989931^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427667181 10000000000 45605835989931 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529354247/1000000000 : ℝ), (-847985847/5000000000 : ℝ), (5427667181/10000000000 : ℝ)] ![(8832594794681/20000000000000 : ℝ), (204623800327/2000000000000 : ℝ), (45605835989931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529354247/1000000000 : ℝ)|^4619 ≤ (8832594794681/20000000000000 : ℝ)^3595
        have hw : |(529354247/1000000000 : ℝ)|=(529354247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-847985847/5000000000 : ℝ)|^4619 ≤ (204623800327/2000000000000 : ℝ)^3595
        have hw : |(-847985847/5000000000 : ℝ)|=(847985847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427667181/10000000000 : ℝ)|^4619 ≤ (45605835989931/100000000000000 : ℝ)^3595
        have hw : |(5427667181/10000000000 : ℝ)|=(5427667181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058708499/2000000000 : ℝ)*x 0 + (217106687/400000000 : ℝ)*x 1 + (-423992917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058708499/2000000000 : ℝ)^4619 ≤ (5520371780173/12500000000000 : ℝ)^3595 := by
    have hnat : (1058708499 : ℕ)^4619*12500000000000^3595 ≤ 5520371780173^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058708499 2000000000 5520371780173 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217106687/400000000 : ℝ)^4619 ≤ (11401458981289/25000000000000 : ℝ)^3595 := by
    have hnat : (217106687 : ℕ)^4619*25000000000000^3595 ≤ 11401458981289^3595*400000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217106687 400000000 11401458981289 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423992917/2500000000 : ℝ)^4619 ≤ (1278898726853/12500000000000 : ℝ)^3595 := by
    have hnat : (423992917 : ℕ)^4619*12500000000000^3595 ≤ 1278898726853^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423992917 2500000000 1278898726853 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058708499/2000000000 : ℝ), (217106687/400000000 : ℝ), (-423992917/2500000000 : ℝ)] ![(5520371780173/12500000000000 : ℝ), (11401458981289/25000000000000 : ℝ), (1278898726853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058708499/2000000000 : ℝ)|^4619 ≤ (5520371780173/12500000000000 : ℝ)^3595
        have hw : |(1058708499/2000000000 : ℝ)|=(1058708499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217106687/400000000 : ℝ)|^4619 ≤ (11401458981289/25000000000000 : ℝ)^3595
        have hw : |(217106687/400000000 : ℝ)|=(217106687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423992917/2500000000 : ℝ)|^4619 ≤ (1278898726853/12500000000000 : ℝ)^3595
        have hw : |(-423992917/2500000000 : ℝ)|=(423992917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s3_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247377887/10000000000 : ℝ)*x 0 + (1124435703/2500000000 : ℝ)*x 1 + (4008632019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247377887/10000000000 : ℝ)^4619 ≤ (33280882865247/100000000000000 : ℝ)^3595 := by
    have hnat : (4247377887 : ℕ)^4619*100000000000000^3595 ≤ 33280882865247^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247377887 10000000000 33280882865247 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124435703/2500000000 : ℝ)^4619 ≤ (3582230983731/10000000000000 : ℝ)^3595 := by
    have hnat : (1124435703 : ℕ)^4619*10000000000000^3595 ≤ 3582230983731^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124435703 2500000000 3582230983731 10000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008632019/10000000000 : ℝ)^4619 ≤ (15448403644289/50000000000000 : ℝ)^3595 := by
    have hnat : (4008632019 : ℕ)^4619*50000000000000^3595 ≤ 15448403644289^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008632019 10000000000 15448403644289 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247377887/10000000000 : ℝ), (1124435703/2500000000 : ℝ), (4008632019/10000000000 : ℝ)] ![(33280882865247/100000000000000 : ℝ), (3582230983731/10000000000000 : ℝ), (15448403644289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247377887/10000000000 : ℝ)|^4619 ≤ (33280882865247/100000000000000 : ℝ)^3595
        have hw : |(4247377887/10000000000 : ℝ)|=(4247377887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124435703/2500000000 : ℝ)|^4619 ≤ (3582230983731/10000000000000 : ℝ)^3595
        have hw : |(1124435703/2500000000 : ℝ)|=(1124435703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008632019/10000000000 : ℝ)|^4619 ≤ (15448403644289/50000000000000 : ℝ)^3595
        have hw : |(4008632019/10000000000 : ℝ)|=(4008632019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (691/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3881/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3959/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (673/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3959/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (673/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3959/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (673/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3959/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (673/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3959/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (673/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3959/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (673/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (673/6250 : ℝ) ^ (4617/1024 : ℝ) ≤ (432614513686669/10000000000000000000 : ℝ) := by
    have hpowers : (673/6250 : ℝ)^4617 ≤ (432614513686669/10000000000000000000 : ℝ)^1024 := by
      have hnat : (673 : ℕ)^4617*10000000000000000000^1024 ≤ 432614513686669^1024*6250^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        673 6250 432614513686669 10000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (673/6250 : ℝ)) (X := (432614513686669/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3959/25000 : ℝ) ^ (4617/1024 : ℝ) ≤ (24624666254008541/100000000000000000000 : ℝ) := by
    have hpowers : (3959/25000 : ℝ)^4617 ≤ (24624666254008541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3959 : ℕ)^4617*100000000000000000000^1024 ≤ 24624666254008541^1024*25000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3959 25000 24624666254008541 100000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3959/25000 : ℝ)) (X := (24624666254008541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000432614513686669/5000000000000000000 : ℝ) ≤ (1250023986481947/1250000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (5000432614513686669/5000000000000000000 : ℝ)^1024 ≤ (1250023986481947/1250000000000000 : ℝ)^4617 := by
      have hnat : (5000432614513686669 : ℕ)^1024*1250000000000000^4617 ≤ 1250023986481947^4617*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000432614513686669 5000000000000000000 1250023986481947 1250000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250023986481947/1250000000000000 : ℝ)) (X := (5000432614513686669/5000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028950811390875231/100000000000000000000 : ℝ) ≤ (5000321012474343/5000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (100028950811390875231/100000000000000000000 : ℝ)^1024 ≤ (5000321012474343/5000000000000000 : ℝ)^4617 := by
      have hnat : (100028950811390875231 : ℕ)^1024*5000000000000000^4617 ≤ 5000321012474343^4617*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028950811390875231 100000000000000000000 5000321012474343 5000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000321012474343/5000000000000000 : ℝ)) (X := (100028950811390875231/100000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024624666254008541/50000000000000000000 : ℝ) ≤ (2500273039510449/2500000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (50024624666254008541/50000000000000000000 : ℝ)^1024 ≤ (2500273039510449/2500000000000000 : ℝ)^4617 := by
      have hnat : (50024624666254008541 : ℕ)^1024*2500000000000000^4617 ≤ 2500273039510449^4617*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024624666254008541 50000000000000000000 2500273039510449 2500000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500273039510449/2500000000000000 : ℝ)) (X := (50024624666254008541/50000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(432614513686669/10000000000000000000 : ℝ) ≤ ((1583477451300963819/1583750000000000000 : ℝ)+2*(45013309311/50680000000000 : ℝ)*(673/6250 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1583477451300963819/1583750000000000000 : ℝ)+2*(45013309311/50680000000000 : ℝ)*(673/6250 : ℝ)=(1250023986481947/1250000000000000 : ℝ) by norm_num, show 1+2*(432614513686669/10000000000000000000 : ℝ)=(5000432614513686669/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24624666254008541/100000000000000000000 : ℝ)+(432614513686669/10000000000000000000 : ℝ) ≤ ((1583477451300963819/1583750000000000000 : ℝ)+(45013309311/50680000000000 : ℝ)*((3959/25000 : ℝ)+(673/6250 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (1583477451300963819/1583750000000000000 : ℝ)+(45013309311/50680000000000 : ℝ)*((3959/25000 : ℝ)+(673/6250 : ℝ))=(5000321012474343/5000000000000000 : ℝ) by norm_num, show 1+(24624666254008541/100000000000000000000 : ℝ)+(432614513686669/10000000000000000000 : ℝ)=(100028950811390875231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24624666254008541/100000000000000000000 : ℝ) ≤ ((1583477451300963819/1583750000000000000 : ℝ)+2*(45013309311/50680000000000 : ℝ)*(3959/25000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1583477451300963819/1583750000000000000 : ℝ)+2*(45013309311/50680000000000 : ℝ)*(3959/25000 : ℝ)=(2500273039510449/2500000000000000 : ℝ) by norm_num, show 1+2*(24624666254008541/100000000000000000000 : ℝ)=(50024624666254008541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1583477451300963819/1583750000000000000 : ℝ)*(X 1 0+X 2 0)+(45013309311/50680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (673/6250 : ℝ)) (hi := (3959/25000 : ℝ)) (c := (1583477451300963819/1583750000000000000 : ℝ)) (alpha := (45013309311/50680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1583477451300963819/1583750000000000000 : ℝ)*(X 0 1+X 2 1)+(45013309311/50680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (673/6250 : ℝ)) (hi := (3959/25000 : ℝ)) (c := (1583477451300963819/1583750000000000000 : ℝ)) (alpha := (45013309311/50680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1583477451300963819/1583750000000000000 : ℝ)*(X 0 2+X 1 2)+(45013309311/50680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (673/6250 : ℝ)) (hi := (3959/25000 : ℝ)) (c := (1583477451300963819/1583750000000000000 : ℝ)) (alpha := (45013309311/50680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1797706131/10000000000 : ℝ)*X 0 0+(5428789763/10000000000 : ℝ)*X 0 1+(2609037327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069846179/2000000000 : ℝ)*X 1 0+(-952782079/5000000000 : ℝ)*X 1 1+(2609037363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674615349/5000000000 : ℝ)*X 2 0+(1304518707/2500000000 : ℝ)*X 2 1+(-14887221/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((84946221/200000000 : ℝ)*X 0 0+(2002999349/5000000000 : ℝ)*X 0 1+(4500356481/10000000000 : ℝ)*X 0 2+(84946221/200000000 : ℝ)*X 1 0+(2002999349/5000000000 : ℝ)*X 1 1+(4500356481/10000000000 : ℝ)*X 1 2+(84946221/200000000 : ℝ)*X 2 0+(2002999349/5000000000 : ℝ)*X 2 1+(4500356481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-449433673/2500000000 : ℝ)*X 0 0+(5219188693/10000000000 : ℝ)*X 0 1+(5427667301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529354247/1000000000 : ℝ)*X 1 0+(-847985847/5000000000 : ℝ)*X 1 1+(5427667181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058708499/2000000000 : ℝ)*X 2 0+(217106687/400000000 : ℝ)*X 2 1+(-423992917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247377887/10000000000 : ℝ)*X 0 0+(1124435703/2500000000 : ℝ)*X 0 1+(4008632019/10000000000 : ℝ)*X 0 2+(4247377887/10000000000 : ℝ)*X 1 0+(1124435703/2500000000 : ℝ)*X 1 1+(4008632019/10000000000 : ℝ)*X 1 2+(4247377887/10000000000 : ℝ)*X 2 0+(1124435703/2500000000 : ℝ)*X 2 1+(4008632019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7514399688063512039250537/1131250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314819121/25000000000000 : ℝ)*(base19) + (46151429/5000000000000 : ℝ)*(base23) + (86374801/100000000000000 : ℝ)*(lower2) + (274982591/100000000000000 : ℝ)*(upper3) + (306967/10000000000000 : ℝ)*(upper5) + (338431512291413/10000000000000 : ℝ)*(major0) + (338431512291413/10000000000000 : ℝ)*(major1) + (338431512291413/10000000000000 : ℝ)*(major2) + (4745768798744567/100000000000000 : ℝ)*(sp0) + (4745784780706219/100000000000000 : ℝ)*(sp1) + (1186446279238531/25000000000000 : ℝ)*(sp2) + (80913347409407/4000000000000 : ℝ)*(sp3) + (2155154767/12500000000000 : ℝ)*(sp4) + (5149595801/50000000000000 : ℝ)*(sp7) + (2022843984426777/100000000000000 : ℝ)*(f.failure) + (4745786039982703/100000000000000 : ℝ)*(f.sum) + (792085147023/126700000000000000000000000 : ℝ)*base66 + (76833587572717497/15837500000000000000000000000000 : ℝ)*base67 + (53022088073867497/15837500000000000000000000000000 : ℝ)*base69 + (54214566903192497/15837500000000000000000000000000 : ℝ)*base71 + (5017310695109/1267000000000000000000000000 : ℝ)*base74 + (176703060835367497/15837500000000000000000000000000 : ℝ)*base75 + (5414611184920003/15837500000000000000000000000000 : ℝ)*base78 + (4921595669795003/15837500000000000000000000000000 : ℝ)*base80 + (159865640147/79187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4741577/5000000000000000000000 : ℝ)*base89 + (4741577/5000000000000000000000 : ℝ)*base91 + (4741577/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171529346528770962022343571/15837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124133763/6250000000000 : ℝ)*(base19) + (546104713/25000000000000 : ℝ)*(base23) + (118513879/50000000000000 : ℝ)*(upper3) + (77225219/100000000000000 : ℝ)*(lower4) + (30676741/12500000000000 : ℝ)*(upper5) + (684118070404799/20000000000000 : ℝ)*(major0) + (684118070404799/20000000000000 : ℝ)*(major1) + (684118070404799/20000000000000 : ℝ)*(major2) + (29273086077/100000000000000 : ℝ)*(sp1) + (6420031131/20000000000000 : ℝ)*(sp2) + (4796654237899803/100000000000000 : ℝ)*(sp4) + (2398311489336759/50000000000000 : ℝ)*(sp5) + (299788747082831/6250000000000 : ℝ)*(sp6) + (1022263052564383/50000000000000 : ℝ)*(sp7) + (1022263052564383/50000000000000 : ℝ)*(f.failure) + (4796654237899803/100000000000000 : ℝ)*(f.sum) + (2343119822401/2534000000000000000000000000 : ℝ)*base65 + (233762843523073631/31675000000000000000000000000000 : ℝ)*base67 + (339090365776523631/31675000000000000000000000000000 : ℝ)*base69 + (76990650913523631/31675000000000000000000000000000 : ℝ)*base71 + (7125866003089/2534000000000000000000000000 : ℝ)*base73 + (613992592463548631/31675000000000000000000000000000 : ℝ)*base75 + (255679071202398631/31675000000000000000000000000000 : ℝ)*base77 + (374742451060898631/31675000000000000000000000000000 : ℝ)*base79 + (392790182121/2534000000000000000000000000 : ℝ)*base81 + (29966417/2500000000000000000000 : ℝ)*base90 + (29966417/2500000000000000000000 : ℝ)*base92 + (29966417/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1561_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1561_s4_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797954967/10000000000 : ℝ)*x 0 + (2713560713/5000000000 : ℝ)*x 1 + (2609789039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797954967/10000000000 : ℝ)^4619 ≤ (1102833537321/10000000000000 : ℝ)^3595 := by
    have hnat : (1797954967 : ℕ)^4619*10000000000000^3595 ≤ 1102833537321^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797954967 10000000000 1102833537321 10000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713560713/5000000000 : ℝ)^4619 ≤ (45599944192821/100000000000000 : ℝ)^3595 := by
    have hnat : (2713560713 : ℕ)^4619*100000000000000^3595 ≤ 45599944192821^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713560713 5000000000 45599944192821 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609789039/5000000000 : ℝ)^4619 ≤ (21685860211839/50000000000000 : ℝ)^3595 := by
    have hnat : (2609789039 : ℕ)^4619*50000000000000^3595 ≤ 21685860211839^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609789039 5000000000 21685860211839 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797954967/10000000000 : ℝ), (2713560713/5000000000 : ℝ), (2609789039/5000000000 : ℝ)] ![(1102833537321/10000000000000 : ℝ), (45599944192821/100000000000000 : ℝ), (21685860211839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797954967/10000000000 : ℝ)|^4619 ≤ (1102833537321/10000000000000 : ℝ)^3595
        have hw : |(-1797954967/10000000000 : ℝ)|=(1797954967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713560713/5000000000 : ℝ)|^4619 ≤ (45599944192821/100000000000000 : ℝ)^3595
        have hw : |(2713560713/5000000000 : ℝ)|=(2713560713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609789039/5000000000 : ℝ)|^4619 ≤ (21685860211839/50000000000000 : ℝ)^3595
        have hw : |(2609789039/5000000000 : ℝ)|=(2609789039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337197539/2500000000 : ℝ)*x 0 + (-952076189/5000000000 : ℝ)*x 1 + (5219578043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337197539/2500000000 : ℝ)^4619 ≤ (1790242445993/4000000000000 : ℝ)^3595 := by
    have hnat : (1337197539 : ℕ)^4619*4000000000000^3595 ≤ 1790242445993^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337197539 2500000000 1790242445993 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952076189/5000000000 : ℝ)^4619 ≤ (371006837133/3125000000000 : ℝ)^3595 := by
    have hnat : (952076189 : ℕ)^4619*3125000000000^3595 ≤ 371006837133^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952076189 5000000000 371006837133 3125000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219578043/10000000000 : ℝ)^4619 ≤ (5421465006251/12500000000000 : ℝ)^3595 := by
    have hnat : (5219578043 : ℕ)^4619*12500000000000^3595 ≤ 5421465006251^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219578043 10000000000 5421465006251 12500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337197539/2500000000 : ℝ), (-952076189/5000000000 : ℝ), (5219578043/10000000000 : ℝ)] ![(1790242445993/4000000000000 : ℝ), (371006837133/3125000000000 : ℝ), (5421465006251/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337197539/2500000000 : ℝ)|^4619 ≤ (1790242445993/4000000000000 : ℝ)^3595
        have hw : |(1337197539/2500000000 : ℝ)|=(1337197539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952076189/5000000000 : ℝ)|^4619 ≤ (371006837133/3125000000000 : ℝ)^3595
        have hw : |(-952076189/5000000000 : ℝ)|=(952076189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219578043/10000000000 : ℝ)|^4619 ≤ (5421465006251/12500000000000 : ℝ)^3595
        have hw : |(5219578043/10000000000 : ℝ)|=(5219578043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348790091/10000000000 : ℝ)*x 0 + (5219578453/10000000000 : ℝ)*x 1 + (-1904151919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348790091/10000000000 : ℝ)^4619 ≤ (8951212090203/20000000000000 : ℝ)^3595 := by
    have hnat : (5348790091 : ℕ)^4619*20000000000000^3595 ≤ 8951212090203^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348790091 10000000000 8951212090203 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219578453/10000000000 : ℝ)^4619 ≤ (43371724427287/100000000000000 : ℝ)^3595 := by
    have hnat : (5219578453 : ℕ)^4619*100000000000000^3595 ≤ 43371724427287^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219578453 10000000000 43371724427287 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904151919/10000000000 : ℝ)^4619 ≤ (11872215111271/100000000000000 : ℝ)^3595 := by
    have hnat : (1904151919 : ℕ)^4619*100000000000000^3595 ≤ 11872215111271^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904151919 10000000000 11872215111271 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348790091/10000000000 : ℝ), (5219578453/10000000000 : ℝ), (-1904151919/10000000000 : ℝ)] ![(8951212090203/20000000000000 : ℝ), (43371724427287/100000000000000 : ℝ), (11872215111271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348790091/10000000000 : ℝ)|^4619 ≤ (8951212090203/20000000000000 : ℝ)^3595
        have hw : |(5348790091/10000000000 : ℝ)|=(5348790091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219578453/10000000000 : ℝ)|^4619 ≤ (43371724427287/100000000000000 : ℝ)^3595
        have hw : |(5219578453/10000000000 : ℝ)|=(5219578453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904151919/10000000000 : ℝ)|^4619 ≤ (11872215111271/100000000000000 : ℝ)^3595
        have hw : |(-1904151919/10000000000 : ℝ)|=(1904151919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247468501/10000000000 : ℝ)*x 0 + (80194051/200000000 : ℝ)*x 1 + (1124154397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247468501/10000000000 : ℝ)^4619 ≤ (33281795127333/100000000000000 : ℝ)^3595 := by
    have hnat : (4247468501 : ℕ)^4619*100000000000000^3595 ≤ 33281795127333^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247468501 10000000000 33281795127333 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80194051/200000000 : ℝ)^4619 ≤ (1931713072061/6250000000000 : ℝ)^3595 := by
    have hnat : (80194051 : ℕ)^4619*6250000000000^3595 ≤ 1931713072061^3595*200000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80194051 200000000 1931713072061 6250000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124154397/2500000000 : ℝ)^4619 ≤ (1790539784811/5000000000000 : ℝ)^3595 := by
    have hnat : (1124154397 : ℕ)^4619*5000000000000^3595 ≤ 1790539784811^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124154397 2500000000 1790539784811 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247468501/10000000000 : ℝ), (80194051/200000000 : ℝ), (1124154397/2500000000 : ℝ)] ![(33281795127333/100000000000000 : ℝ), (1931713072061/6250000000000 : ℝ), (1790539784811/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247468501/10000000000 : ℝ)|^4619 ≤ (33281795127333/100000000000000 : ℝ)^3595
        have hw : |(4247468501/10000000000 : ℝ)|=(4247468501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80194051/200000000 : ℝ)|^4619 ≤ (1931713072061/6250000000000 : ℝ)^3595
        have hw : |(80194051/200000000 : ℝ)|=(80194051/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124154397/2500000000 : ℝ)|^4619 ≤ (1790539784811/5000000000000 : ℝ)^3595
        have hw : |(1124154397/2500000000 : ℝ)|=(1124154397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898991103/5000000000 : ℝ)*x 0 + (2610329627/5000000000 : ℝ)*x 1 + (5426032243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898991103/5000000000 : ℝ)^4619 ≤ (5514275021843/50000000000000 : ℝ)^3595 := by
    have hnat : (898991103 : ℕ)^4619*50000000000000^3595 ≤ 5514275021843^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898991103 5000000000 5514275021843 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610329627/5000000000 : ℝ)^4619 ≤ (43383263711553/100000000000000 : ℝ)^3595 := by
    have hnat : (2610329627 : ℕ)^4619*100000000000000^3595 ≤ 43383263711553^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610329627 5000000000 43383263711553 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426032243/10000000000 : ℝ)^4619 ≤ (45588186224647/100000000000000 : ℝ)^3595 := by
    have hnat : (5426032243 : ℕ)^4619*100000000000000^3595 ≤ 45588186224647^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426032243 10000000000 45588186224647 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898991103/5000000000 : ℝ), (2610329627/5000000000 : ℝ), (5426032243/10000000000 : ℝ)] ![(5514275021843/50000000000000 : ℝ), (43383263711553/100000000000000 : ℝ), (45588186224647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898991103/5000000000 : ℝ)|^4619 ≤ (5514275021843/50000000000000 : ℝ)^3595
        have hw : |(-898991103/5000000000 : ℝ)|=(898991103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610329627/5000000000 : ℝ)|^4619 ≤ (43383263711553/100000000000000 : ℝ)^3595
        have hw : |(2610329627/5000000000 : ℝ)|=(2610329627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426032243/10000000000 : ℝ)|^4619 ≤ (45588186224647/100000000000000 : ℝ)^3595
        have hw : |(5426032243/10000000000 : ℝ)|=(5426032243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82717813/156250000 : ℝ)*x 0 + (-424424657/2500000000 : ℝ)*x 1 + (5426032319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82717813/156250000 : ℝ)^4619 ≤ (4416723555187/10000000000000 : ℝ)^3595 := by
    have hnat : (82717813 : ℕ)^4619*10000000000000^3595 ≤ 4416723555187^3595*156250000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82717813 156250000 4416723555187 10000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424424657/2500000000 : ℝ)^4619 ≤ (10244577388001/100000000000000 : ℝ)^3595 := by
    have hnat : (424424657 : ℕ)^4619*100000000000000^3595 ≤ 10244577388001^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424424657 2500000000 10244577388001 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426032319/10000000000 : ℝ)^4619 ≤ (45588187045061/100000000000000 : ℝ)^3595 := by
    have hnat : (5426032319 : ℕ)^4619*100000000000000^3595 ≤ 45588187045061^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426032319 10000000000 45588187045061 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82717813/156250000 : ℝ), (-424424657/2500000000 : ℝ), (5426032319/10000000000 : ℝ)] ![(4416723555187/10000000000000 : ℝ), (10244577388001/100000000000000 : ℝ), (45588187045061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82717813/156250000 : ℝ)|^4619 ≤ (4416723555187/10000000000000 : ℝ)^3595
        have hw : |(82717813/156250000 : ℝ)|=(82717813/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424424657/2500000000 : ℝ)|^4619 ≤ (10244577388001/100000000000000 : ℝ)^3595
        have hw : |(-424424657/2500000000 : ℝ)|=(424424657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426032319/10000000000 : ℝ)|^4619 ≤ (45588187045061/100000000000000 : ℝ)^3595
        have hw : |(5426032319/10000000000 : ℝ)|=(5426032319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646970037/5000000000 : ℝ)*x 0 + (5426032329/10000000000 : ℝ)*x 1 + (-1697698557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646970037/5000000000 : ℝ)^4619 ≤ (11041809000521/25000000000000 : ℝ)^3595 := by
    have hnat : (2646970037 : ℕ)^4619*25000000000000^3595 ≤ 11041809000521^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646970037 5000000000 11041809000521 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426032329/10000000000 : ℝ)^4619 ≤ (4558818715301/10000000000000 : ℝ)^3595 := by
    have hnat : (5426032329 : ℕ)^4619*10000000000000^3595 ≤ 4558818715301^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426032329 10000000000 4558818715301 10000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1697698557/10000000000 : ℝ)^4619 ≤ (5122288418761/50000000000000 : ℝ)^3595 := by
    have hnat : (1697698557 : ℕ)^4619*50000000000000^3595 ≤ 5122288418761^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697698557 10000000000 5122288418761 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646970037/5000000000 : ℝ), (5426032329/10000000000 : ℝ), (-1697698557/10000000000 : ℝ)] ![(11041809000521/25000000000000 : ℝ), (4558818715301/10000000000000 : ℝ), (5122288418761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646970037/5000000000 : ℝ)|^4619 ≤ (11041809000521/25000000000000 : ℝ)^3595
        have hw : |(2646970037/5000000000 : ℝ)|=(2646970037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426032329/10000000000 : ℝ)|^4619 ≤ (4558818715301/10000000000000 : ℝ)^3595
        have hw : |(5426032329/10000000000 : ℝ)|=(5426032329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1697698557/10000000000 : ℝ)|^4619 ≤ (5122288418761/50000000000000 : ℝ)^3595
        have hw : |(-1697698557/10000000000 : ℝ)|=(1697698557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s4_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123766183/5000000000 : ℝ)*x 0 + (898816387/2000000000 : ℝ)*x 1 + (4012256983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123766183/5000000000 : ℝ)^4619 ≤ (33282438095527/100000000000000 : ℝ)^3595 := by
    have hnat : (2123766183 : ℕ)^4619*100000000000000^3595 ≤ 33282438095527^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123766183 5000000000 33282438095527 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898816387/2000000000 : ℝ)^4619 ≤ (35784851989891/100000000000000 : ℝ)^3595 := by
    have hnat : (898816387 : ℕ)^4619*100000000000000^3595 ≤ 35784851989891^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898816387 2000000000 35784851989891 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4012256983/10000000000 : ℝ)^4619 ≤ (15466354952331/50000000000000 : ℝ)^3595 := by
    have hnat : (4012256983 : ℕ)^4619*50000000000000^3595 ≤ 15466354952331^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012256983 10000000000 15466354952331 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123766183/5000000000 : ℝ), (898816387/2000000000 : ℝ), (4012256983/10000000000 : ℝ)] ![(33282438095527/100000000000000 : ℝ), (35784851989891/100000000000000 : ℝ), (15466354952331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123766183/5000000000 : ℝ)|^4619 ≤ (33282438095527/100000000000000 : ℝ)^3595
        have hw : |(2123766183/5000000000 : ℝ)|=(2123766183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898816387/2000000000 : ℝ)|^4619 ≤ (35784851989891/100000000000000 : ℝ)^3595
        have hw : |(898816387/2000000000 : ℝ)|=(898816387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4012256983/10000000000 : ℝ)|^4619 ≤ (15466354952331/50000000000000 : ℝ)^3595
        have hw : |(4012256983/10000000000 : ℝ)|=(4012256983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (693/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3881/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3881/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (691/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3881/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3881/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (691/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3881/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3881/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (691/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (691/6250 : ℝ) ^ (4617/1024 : ℝ) ≤ (609109357516521/12500000000000000000 : ℝ) := by
    have hpowers : (691/6250 : ℝ)^4617 ≤ (609109357516521/12500000000000000000 : ℝ)^1024 := by
      have hnat : (691 : ℕ)^4617*12500000000000000000^1024 ≤ 609109357516521^1024*6250^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        691 6250 609109357516521 12500000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (691/6250 : ℝ)) (X := (609109357516521/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3881/25000 : ℝ) ^ (4617/1024 : ℝ) ≤ (4502316582388727/20000000000000000000 : ℝ) := by
    have hpowers : (3881/25000 : ℝ)^4617 ≤ (4502316582388727/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3881 : ℕ)^4617*20000000000000000000^1024 ≤ 4502316582388727^1024*25000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3881 25000 4502316582388727 20000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3881/25000 : ℝ)) (X := (4502316582388727/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250609109357516521/6250000000000000000 : ℝ) ≤ (5000108070925869/5000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (6250609109357516521/6250000000000000000 : ℝ)^1024 ≤ (5000108070925869/5000000000000000 : ℝ)^4617 := by
      have hnat : (6250609109357516521 : ℕ)^1024*5000000000000000^4617 ≤ 5000108070925869^4617*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250609109357516521 6250000000000000000 5000108070925869 5000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000108070925869/5000000000000000 : ℝ)) (X := (6250609109357516521/6250000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027384457772075803/100000000000000000000 : ℝ) ≤ (5000303646277647/5000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (100027384457772075803/100000000000000000000 : ℝ)^1024 ≤ (5000303646277647/5000000000000000 : ℝ)^4617 := by
      have hnat : (100027384457772075803 : ℕ)^1024*5000000000000000^4617 ≤ 5000303646277647^4617*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027384457772075803 100000000000000000000 5000303646277647 5000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000303646277647/5000000000000000 : ℝ)) (X := (100027384457772075803/100000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004502316582388727/10000000000000000000 : ℝ) ≤ (200019968865177/200000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (10004502316582388727/10000000000000000000 : ℝ)^1024 ≤ (200019968865177/200000000000000 : ℝ)^4617 := by
      have hnat : (10004502316582388727 : ℕ)^1024*200000000000000^4617 ≤ 200019968865177^4617*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004502316582388727 10000000000000000000 200019968865177 200000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200019968865177/200000000000000 : ℝ)) (X := (10004502316582388727/10000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(609109357516521/12500000000000000000 : ℝ) ≤ ((5584039574679566889/5585000000000000000 : ℝ)+2*(97787675889/111700000000000 : ℝ)*(691/6250 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (5584039574679566889/5585000000000000000 : ℝ)+2*(97787675889/111700000000000 : ℝ)*(691/6250 : ℝ)=(5000108070925869/5000000000000000 : ℝ) by norm_num, show 1+2*(609109357516521/12500000000000000000 : ℝ)=(6250609109357516521/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4502316582388727/20000000000000000000 : ℝ)+(609109357516521/12500000000000000000 : ℝ) ≤ ((5584039574679566889/5585000000000000000 : ℝ)+(97787675889/111700000000000 : ℝ)*((3881/25000 : ℝ)+(691/6250 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (5584039574679566889/5585000000000000000 : ℝ)+(97787675889/111700000000000 : ℝ)*((3881/25000 : ℝ)+(691/6250 : ℝ))=(5000303646277647/5000000000000000 : ℝ) by norm_num, show 1+(4502316582388727/20000000000000000000 : ℝ)+(609109357516521/12500000000000000000 : ℝ)=(100027384457772075803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4502316582388727/20000000000000000000 : ℝ) ≤ ((5584039574679566889/5585000000000000000 : ℝ)+2*(97787675889/111700000000000 : ℝ)*(3881/25000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (5584039574679566889/5585000000000000000 : ℝ)+2*(97787675889/111700000000000 : ℝ)*(3881/25000 : ℝ)=(200019968865177/200000000000000 : ℝ) by norm_num, show 1+2*(4502316582388727/20000000000000000000 : ℝ)=(10004502316582388727/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5584039574679566889/5585000000000000000 : ℝ)*(X 1 0+X 2 0)+(97787675889/111700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5584039574679566889/5585000000000000000 : ℝ)) (alpha := (97787675889/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5584039574679566889/5585000000000000000 : ℝ)*(X 0 1+X 2 1)+(97787675889/111700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5584039574679566889/5585000000000000000 : ℝ)) (alpha := (97787675889/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5584039574679566889/5585000000000000000 : ℝ)*(X 0 2+X 1 2)+(97787675889/111700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (691/6250 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5584039574679566889/5585000000000000000 : ℝ)) (alpha := (97787675889/111700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1797954967/10000000000 : ℝ)*X 0 0+(2713560713/5000000000 : ℝ)*X 0 1+(2609789039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337197539/2500000000 : ℝ)*X 1 0+(-952076189/5000000000 : ℝ)*X 1 1+(5219578043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348790091/10000000000 : ℝ)*X 2 0+(5219578453/10000000000 : ℝ)*X 2 1+(-1904151919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4247468501/10000000000 : ℝ)*X 0 0+(80194051/200000000 : ℝ)*X 0 1+(1124154397/2500000000 : ℝ)*X 0 2+(4247468501/10000000000 : ℝ)*X 1 0+(80194051/200000000 : ℝ)*X 1 1+(1124154397/2500000000 : ℝ)*X 1 2+(4247468501/10000000000 : ℝ)*X 2 0+(80194051/200000000 : ℝ)*X 2 1+(1124154397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-898991103/5000000000 : ℝ)*X 0 0+(2610329627/5000000000 : ℝ)*X 0 1+(5426032243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82717813/156250000 : ℝ)*X 1 0+(-424424657/2500000000 : ℝ)*X 1 1+(5426032319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646970037/5000000000 : ℝ)*X 2 0+(5426032329/10000000000 : ℝ)*X 2 1+(-1697698557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123766183/5000000000 : ℝ)*X 0 0+(898816387/2000000000 : ℝ)*X 0 1+(4012256983/10000000000 : ℝ)*X 0 2+(2123766183/5000000000 : ℝ)*X 1 0+(898816387/2000000000 : ℝ)*X 1 1+(4012256983/10000000000 : ℝ)*X 1 2+(2123766183/5000000000 : ℝ)*X 2 0+(898816387/2000000000 : ℝ)*X 2 1+(4012256983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135291521429329880292706461/17453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1892379883/100000000000000 : ℝ)*(base19) + (1720386349/100000000000000 : ℝ)*(base23) + (2692247/4000000000000 : ℝ)*(lower2) + (19330743/6250000000000 : ℝ)*(upper5) + (107376890632877/3125000000000 : ℝ)*(major0) + (107376890632877/3125000000000 : ℝ)*(major1) + (107376890632877/3125000000000 : ℝ)*(major2) + (2409151871095193/50000000000000 : ℝ)*(sp0) + (963668970158949/20000000000000 : ℝ)*(sp1) + (4818346231480847/100000000000000 : ℝ)*(sp2) + (1026880512292303/50000000000000 : ℝ)*(sp3) + (4420967681/10000000000000 : ℝ)*(sp4) + (1208692569/100000000000000 : ℝ)*(sp5) + (11765662063/100000000000000 : ℝ)*(sp7) + (2053772790246669/100000000000000 : ℝ)*(f.failure) + (4818347951867197/100000000000000 : ℝ)*(f.sum) + (9911218651087/2792500000000000000000000000 : ℝ)*base66 + (10056601771911007/4363281250000000000000000000000 : ℝ)*base67 + (42981080879912361/8726562500000000000000000000000 : ℝ)*base70 + (225903934180902847/17453125000000000000000000000000 : ℝ)*base72 + (25867376936041/5585000000000000000000000000 : ℝ)*base73 + (122336762951287361/8726562500000000000000000000000 : ℝ)*base76 + (49701267931682743/4363281250000000000000000000000 : ℝ)*base78 + (147846365072590347/17453125000000000000000000000000 : ℝ)*base80 + (314115105659/349062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (44102269/5000000000000000000000 : ℝ)*base89 + (44102269/5000000000000000000000 : ℝ)*base91 + (44102269/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1510567166230332054167327661/139625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (330712957/25000000000000 : ℝ)*(base19) + (195051573/12500000000000 : ℝ)*(base23) + (59016653/25000000000000 : ℝ)*(upper3) + (19397023/25000000000000 : ℝ)*(lower4) + (5047687/2500000000000 : ℝ)*(upper5) + (1736157593958017/50000000000000 : ℝ)*(major0) + (1736157593958017/50000000000000 : ℝ)*(major1) + (1736157593958017/50000000000000 : ℝ)*(major2) + (19665728029/100000000000000 : ℝ)*(sp1) + (4944076113/20000000000000 : ℝ)*(sp2) + (2434593691058263/50000000000000 : ℝ)*(sp4) + (4869166393536669/100000000000000 : ℝ)*(sp5) + (4869161101323377/100000000000000 : ℝ)*(sp6) + (2075442633090731/100000000000000 : ℝ)*(sp7) + (2075442633090731/100000000000000 : ℝ)*(f.failure) + (2434593691058263/50000000000000 : ℝ)*(f.sum) + (1874885722019/1396250000000000000000000000 : ℝ)*base65 + (25758457438300887/279250000000000000000000000000000 : ℝ)*base68 + (3389938024771800887/279250000000000000000000000000000 : ℝ)*base70 + (476294118183449113/279250000000000000000000000000000 : ℝ)*base71 + (14861197285491/5585000000000000000000000000 : ℝ)*base73 + (289313413658199113/279250000000000000000000000000000 : ℝ)*base75 + (33187093039199113/279250000000000000000000000000000 : ℝ)*base77 + (43721909872199113/279250000000000000000000000000000 : ℝ)*base79 + (31475045399939/5585000000000000000000000000 : ℝ)*base82 + (1004869/5000000000000000000000 : ℝ)*base90 + (1004869/5000000000000000000000 : ℝ)*base92 + (1004869/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1561_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1561_s5_0 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359596323/2000000000 : ℝ)*x 0 + (135673667/250000000 : ℝ)*x 1 + (5219735103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359596323/2000000000 : ℝ)^4619 ≤ (11028545386007/100000000000000 : ℝ)^3595 := by
    have hnat : (359596323 : ℕ)^4619*100000000000000^3595 ≤ 11028545386007^3595*2000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359596323 2000000000 11028545386007 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135673667/250000000 : ℝ)^4619 ≤ (9119611545269/20000000000000 : ℝ)^3595 := by
    have hnat : (135673667 : ℕ)^4619*20000000000000^3595 ≤ 9119611545269^3595*250000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135673667 250000000 9119611545269 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219735103/10000000000 : ℝ)^4619 ≤ (43373396875131/100000000000000 : ℝ)^3595 := by
    have hnat : (5219735103 : ℕ)^4619*100000000000000^3595 ≤ 43373396875131^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219735103 10000000000 43373396875131 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359596323/2000000000 : ℝ), (135673667/250000000 : ℝ), (5219735103/10000000000 : ℝ)] ![(11028545386007/100000000000000 : ℝ), (9119611545269/20000000000000 : ℝ), (43373396875131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359596323/2000000000 : ℝ)|^4619 ≤ (11028545386007/100000000000000 : ℝ)^3595
        have hw : |(-359596323/2000000000 : ℝ)|=(359596323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135673667/250000000 : ℝ)|^4619 ≤ (9119611545269/20000000000000 : ℝ)^3595
        have hw : |(135673667/250000000 : ℝ)|=(135673667/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219735103/10000000000 : ℝ)|^4619 ≤ (43373396875131/100000000000000 : ℝ)^3595
        have hw : |(5219735103/10000000000 : ℝ)|=(5219735103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_1 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33429647/62500000 : ℝ)*x 0 + (-1904005669/10000000000 : ℝ)*x 1 + (1304933771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33429647/62500000 : ℝ)^4619 ≤ (44755559770847/100000000000000 : ℝ)^3595 := by
    have hnat : (33429647 : ℕ)^4619*100000000000000^3595 ≤ 44755559770847^3595*62500000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33429647 62500000 44755559770847 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904005669/10000000000 : ℝ)^4619 ≤ (474841741423/4000000000000 : ℝ)^3595 := by
    have hnat : (1904005669 : ℕ)^4619*4000000000000^3595 ≤ 474841741423^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904005669 10000000000 474841741423 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304933771/2500000000 : ℝ)^4619 ≤ (1084334916807/2500000000000 : ℝ)^3595 := by
    have hnat : (1304933771 : ℕ)^4619*2500000000000^3595 ≤ 1084334916807^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304933771 2500000000 1084334916807 2500000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33429647/62500000 : ℝ), (-1904005669/10000000000 : ℝ), (1304933771/2500000000 : ℝ)] ![(44755559770847/100000000000000 : ℝ), (474841741423/4000000000000 : ℝ), (1084334916807/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33429647/62500000 : ℝ)|^4619 ≤ (44755559770847/100000000000000 : ℝ)^3595
        have hw : |(33429647/62500000 : ℝ)|=(33429647/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904005669/10000000000 : ℝ)|^4619 ≤ (474841741423/4000000000000 : ℝ)^3595
        have hw : |(-1904005669/10000000000 : ℝ)|=(1904005669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304933771/2500000000 : ℝ)|^4619 ≤ (1084334916807/2500000000000 : ℝ)^3595
        have hw : |(1304933771/2500000000 : ℝ)|=(1304933771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_2 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348743503/10000000000 : ℝ)*x 0 + (5219735093/10000000000 : ℝ)*x 1 + (-1904005681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348743503/10000000000 : ℝ)^4619 ≤ (22377779794041/50000000000000 : ℝ)^3595 := by
    have hnat : (5348743503 : ℕ)^4619*50000000000000^3595 ≤ 22377779794041^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348743503 10000000000 22377779794041 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219735093/10000000000 : ℝ)^4619 ≤ (43373396768367/100000000000000 : ℝ)^3595 := by
    have hnat : (5219735093 : ℕ)^4619*100000000000000^3595 ≤ 43373396768367^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219735093 10000000000 43373396768367 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904005681/10000000000 : ℝ)^4619 ≤ (11871043631703/100000000000000 : ℝ)^3595 := by
    have hnat : (1904005681 : ℕ)^4619*100000000000000^3595 ≤ 11871043631703^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904005681 10000000000 11871043631703 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348743503/10000000000 : ℝ), (5219735093/10000000000 : ℝ), (-1904005681/10000000000 : ℝ)] ![(22377779794041/50000000000000 : ℝ), (43373396768367/100000000000000 : ℝ), (11871043631703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348743503/10000000000 : ℝ)|^4619 ≤ (22377779794041/50000000000000 : ℝ)^3595
        have hw : |(5348743503/10000000000 : ℝ)|=(5348743503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219735093/10000000000 : ℝ)|^4619 ≤ (43373396768367/100000000000000 : ℝ)^3595
        have hw : |(5219735093/10000000000 : ℝ)|=(5219735093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904005681/10000000000 : ℝ)|^4619 ≤ (11871043631703/100000000000000 : ℝ)^3595
        have hw : |(-1904005681/10000000000 : ℝ)|=(1904005681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_3 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123742407/5000000000 : ℝ)*x 0 + (4010089053/10000000000 : ℝ)*x 1 + (4496227439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123742407/5000000000 : ℝ)^4619 ≤ (6656391872013/20000000000000 : ℝ)^3595 := by
    have hnat : (2123742407 : ℕ)^4619*20000000000000^3595 ≤ 6656391872013^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123742407 5000000000 6656391872013 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010089053/10000000000 : ℝ)^4619 ≤ (7727809258307/25000000000000 : ℝ)^3595 := by
    have hnat : (4010089053 : ℕ)^4619*25000000000000^3595 ≤ 7727809258307^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010089053 10000000000 7727809258307 25000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496227439/10000000000 : ℝ)^4619 ≤ (7161360717767/20000000000000 : ℝ)^3595 := by
    have hnat : (4496227439 : ℕ)^4619*20000000000000^3595 ≤ 7161360717767^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496227439 10000000000 7161360717767 20000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123742407/5000000000 : ℝ), (4010089053/10000000000 : ℝ), (4496227439/10000000000 : ℝ)] ![(6656391872013/20000000000000 : ℝ), (7727809258307/25000000000000 : ℝ), (7161360717767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123742407/5000000000 : ℝ)|^4619 ≤ (6656391872013/20000000000000 : ℝ)^3595
        have hw : |(2123742407/5000000000 : ℝ)|=(2123742407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010089053/10000000000 : ℝ)|^4619 ≤ (7727809258307/25000000000000 : ℝ)^3595
        have hw : |(4010089053/10000000000 : ℝ)|=(4010089053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496227439/10000000000 : ℝ)|^4619 ≤ (7161360717767/20000000000000 : ℝ)^3595
        have hw : |(4496227439/10000000000 : ℝ)|=(4496227439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_4 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-899004361/5000000000 : ℝ)*x 0 + (2610406251/5000000000 : ℝ)*x 1 + (5425861311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899004361/5000000000 : ℝ)^4619 ≤ (11028759017091/100000000000000 : ℝ)^3595 := by
    have hnat : (899004361 : ℕ)^4619*100000000000000^3595 ≤ 11028759017091^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899004361 5000000000 11028759017091 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610406251/5000000000 : ℝ)^4619 ≤ (21692449967423/50000000000000 : ℝ)^3595 := by
    have hnat : (2610406251 : ℕ)^4619*50000000000000^3595 ≤ 21692449967423^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610406251 5000000000 21692449967423 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425861311/10000000000 : ℝ)^4619 ≤ (45586341037433/100000000000000 : ℝ)^3595 := by
    have hnat : (5425861311 : ℕ)^4619*100000000000000^3595 ≤ 45586341037433^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425861311 10000000000 45586341037433 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899004361/5000000000 : ℝ), (2610406251/5000000000 : ℝ), (5425861311/10000000000 : ℝ)] ![(11028759017091/100000000000000 : ℝ), (21692449967423/50000000000000 : ℝ), (45586341037433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899004361/5000000000 : ℝ)|^4619 ≤ (11028759017091/100000000000000 : ℝ)^3595
        have hw : |(-899004361/5000000000 : ℝ)|=(899004361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610406251/5000000000 : ℝ)|^4619 ≤ (21692449967423/50000000000000 : ℝ)^3595
        have hw : |(2610406251/5000000000 : ℝ)|=(2610406251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425861311/10000000000 : ℝ)|^4619 ≤ (45586341037433/100000000000000 : ℝ)^3595
        have hw : |(5425861311/10000000000 : ℝ)|=(5425861311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_5 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646990713/5000000000 : ℝ)*x 0 + (-848939737/5000000000 : ℝ)*x 1 + (5425861323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646990713/5000000000 : ℝ)^4619 ≤ (44167679270993/100000000000000 : ℝ)^3595 := by
    have hnat : (2646990713 : ℕ)^4619*100000000000000^3595 ≤ 44167679270993^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646990713 5000000000 44167679270993 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848939737/5000000000 : ℝ)^4619 ≤ (512298977471/5000000000000 : ℝ)^3595 := by
    have hnat : (848939737 : ℕ)^4619*5000000000000^3595 ≤ 512298977471^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848939737 5000000000 512298977471 5000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425861323/10000000000 : ℝ)^4619 ≤ (45586341166971/100000000000000 : ℝ)^3595 := by
    have hnat : (5425861323 : ℕ)^4619*100000000000000^3595 ≤ 45586341166971^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425861323 10000000000 45586341166971 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646990713/5000000000 : ℝ), (-848939737/5000000000 : ℝ), (5425861323/10000000000 : ℝ)] ![(44167679270993/100000000000000 : ℝ), (512298977471/5000000000000 : ℝ), (45586341166971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646990713/5000000000 : ℝ)|^4619 ≤ (44167679270993/100000000000000 : ℝ)^3595
        have hw : |(2646990713/5000000000 : ℝ)|=(2646990713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-848939737/5000000000 : ℝ)|^4619 ≤ (512298977471/5000000000000 : ℝ)^3595
        have hw : |(-848939737/5000000000 : ℝ)|=(848939737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425861323/10000000000 : ℝ)|^4619 ≤ (45586341166971/100000000000000 : ℝ)^3595
        have hw : |(5425861323/10000000000 : ℝ)|=(5425861323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_6 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293981431/10000000000 : ℝ)*x 0 + (5425861329/10000000000 : ℝ)*x 1 + (-1697879459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293981431/10000000000 : ℝ)^4619 ≤ (4416767932459/10000000000000 : ℝ)^3595 := by
    have hnat : (5293981431 : ℕ)^4619*10000000000000^3595 ≤ 4416767932459^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293981431 10000000000 4416767932459 10000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425861329/10000000000 : ℝ)^4619 ≤ (45586341231739/100000000000000 : ℝ)^3595 := by
    have hnat : (5425861329 : ℕ)^4619*100000000000000^3595 ≤ 45586341231739^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425861329 10000000000 45586341231739 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1697879459/10000000000 : ℝ)^4619 ≤ (5122989716559/50000000000000 : ℝ)^3595 := by
    have hnat : (1697879459 : ℕ)^4619*50000000000000^3595 ≤ 5122989716559^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697879459 10000000000 5122989716559 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293981431/10000000000 : ℝ), (5425861329/10000000000 : ℝ), (-1697879459/10000000000 : ℝ)] ![(4416767932459/10000000000000 : ℝ), (45586341231739/100000000000000 : ℝ), (5122989716559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293981431/10000000000 : ℝ)|^4619 ≤ (4416767932459/10000000000000 : ℝ)^3595
        have hw : |(5293981431/10000000000 : ℝ)|=(5293981431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425861329/10000000000 : ℝ)|^4619 ≤ (45586341231739/100000000000000 : ℝ)^3595
        have hw : |(5425861329/10000000000 : ℝ)|=(5425861329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1697879459/10000000000 : ℝ)|^4619 ≤ (5122989716559/50000000000000 : ℝ)^3595
        have hw : |(-1697879459/10000000000 : ℝ)|=(1697879459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1561_s5_7 (p : ℝ) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247548379/10000000000 : ℝ)*x 0 + (2246849849/5000000000 : ℝ)*x 1 + (1003158871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247548379/10000000000 : ℝ)^4619 ≤ (33282599308669/100000000000000 : ℝ)^3595 := by
    have hnat : (4247548379 : ℕ)^4619*100000000000000^3595 ≤ 33282599308669^3595*10000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247548379 10000000000 33282599308669 100000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246849849/5000000000 : ℝ)^4619 ≤ (17890470733783/50000000000000 : ℝ)^3595 := by
    have hnat : (2246849849 : ℕ)^4619*50000000000000^3595 ≤ 17890470733783^3595*5000000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246849849 5000000000 17890470733783 50000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003158871/2500000000 : ℝ)^4619 ≤ (1237458368521/4000000000000 : ℝ)^3595 := by
    have hnat : (1003158871 : ℕ)^4619*4000000000000^3595 ≤ 1237458368521^3595*2500000000^4619 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003158871 2500000000 1237458368521 4000000000000 4619 3595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4619/1024 : ℝ)) 4619 3595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247548379/10000000000 : ℝ), (2246849849/5000000000 : ℝ), (1003158871/2500000000 : ℝ)] ![(33282599308669/100000000000000 : ℝ), (17890470733783/50000000000000 : ℝ), (1237458368521/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247548379/10000000000 : ℝ)|^4619 ≤ (33282599308669/100000000000000 : ℝ)^3595
        have hw : |(4247548379/10000000000 : ℝ)|=(4247548379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246849849/5000000000 : ℝ)|^4619 ≤ (17890470733783/50000000000000 : ℝ)^3595
        have hw : |(2246849849/5000000000 : ℝ)|=(2246849849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003158871/2500000000 : ℝ)|^4619 ≤ (1237458368521/4000000000000 : ℝ)^3595
        have hw : |(1003158871/2500000000 : ℝ)|=(1003158871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1561_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2773/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (693/6250 : ℝ) ^ (4617/1024 : ℝ) ≤ (308549360249209/6250000000000000000 : ℝ) := by
    have hpowers : (693/6250 : ℝ)^4617 ≤ (308549360249209/6250000000000000000 : ℝ)^1024 := by
      have hnat : (693 : ℕ)^4617*6250000000000000000^1024 ≤ 308549360249209^1024*6250^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 6250 308549360249209 6250000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/6250 : ℝ)) (X := (308549360249209/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4617/1024 : ℝ) ≤ (11141823595481227/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4617 ≤ (11141823595481227/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4617*50000000000000000000^1024 ≤ 11141823595481227^1024*100000^4617 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 11141823595481227 50000000000000000000 4617 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (11141823595481227/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125308549360249209/3125000000000000000 : ℝ) ≤ (2500054744190091/2500000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (3125308549360249209/3125000000000000000 : ℝ)^1024 ≤ (2500054744190091/2500000000000000 : ℝ)^4617 := by
      have hnat : (3125308549360249209 : ℕ)^1024*2500000000000000^4617 ≤ 2500054744190091^4617*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125308549360249209 3125000000000000000 2500054744190091 2500000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500054744190091/2500000000000000 : ℝ)) (X := (3125308549360249209/3125000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013610218477474899/50000000000000000000 : ℝ) ≤ (10000603655526067/10000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (50013610218477474899/50000000000000000000 : ℝ)^1024 ≤ (10000603655526067/10000000000000000 : ℝ)^4617 := by
      have hnat : (50013610218477474899 : ℕ)^1024*10000000000000000^4617 ≤ 10000603655526067^4617*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013610218477474899 50000000000000000000 10000603655526067 10000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000603655526067/10000000000000000 : ℝ)) (X := (50013610218477474899/50000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011141823595481227/25000000000000000000 : ℝ) ≤ (1000098833429177/1000000000000000 : ℝ) ^ (4617/1024 : ℝ) := by
    have hpowers : (25011141823595481227/25000000000000000000 : ℝ)^1024 ≤ (1000098833429177/1000000000000000 : ℝ)^4617 := by
      have hnat : (25011141823595481227 : ℕ)^1024*1000000000000000^4617 ≤ 1000098833429177^4617*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011141823595481227 25000000000000000000 1000098833429177 1000000000000000 1024 4617 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000098833429177/1000000000000000 : ℝ)) (X := (25011141823595481227/25000000000000000000 : ℝ)) (by norm_num) 4617 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(308549360249209/6250000000000000000 : ℝ) ≤ ((1222289807789281451/1222500000000000000 : ℝ)+2*(384678765703/440100000000000 : ℝ)*(693/6250 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1222289807789281451/1222500000000000000 : ℝ)+2*(384678765703/440100000000000 : ℝ)*(693/6250 : ℝ)=(2500054744190091/2500000000000000 : ℝ) by norm_num, show 1+2*(308549360249209/6250000000000000000 : ℝ)=(3125308549360249209/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11141823595481227/50000000000000000000 : ℝ)+(308549360249209/6250000000000000000 : ℝ) ≤ ((1222289807789281451/1222500000000000000 : ℝ)+(384678765703/440100000000000 : ℝ)*((15489/100000 : ℝ)+(693/6250 : ℝ)))^(4617/1024 : ℝ) := by
    rw [show (1222289807789281451/1222500000000000000 : ℝ)+(384678765703/440100000000000 : ℝ)*((15489/100000 : ℝ)+(693/6250 : ℝ))=(10000603655526067/10000000000000000 : ℝ) by norm_num, show 1+(11141823595481227/50000000000000000000 : ℝ)+(308549360249209/6250000000000000000 : ℝ)=(50013610218477474899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11141823595481227/50000000000000000000 : ℝ) ≤ ((1222289807789281451/1222500000000000000 : ℝ)+2*(384678765703/440100000000000 : ℝ)*(15489/100000 : ℝ))^(4617/1024 : ℝ) := by
    rw [show (1222289807789281451/1222500000000000000 : ℝ)+2*(384678765703/440100000000000 : ℝ)*(15489/100000 : ℝ)=(1000098833429177/1000000000000000 : ℝ) by norm_num, show 1+2*(11141823595481227/50000000000000000000 : ℝ)=(25011141823595481227/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1222289807789281451/1222500000000000000 : ℝ)*(X 1 0+X 2 0)+(384678765703/440100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1222289807789281451/1222500000000000000 : ℝ)) (alpha := (384678765703/440100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1222289807789281451/1222500000000000000 : ℝ)*(X 0 1+X 2 1)+(384678765703/440100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1222289807789281451/1222500000000000000 : ℝ)) (alpha := (384678765703/440100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1222289807789281451/1222500000000000000 : ℝ)*(X 0 2+X 1 2)+(384678765703/440100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4617/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1222289807789281451/1222500000000000000 : ℝ)) (alpha := (384678765703/440100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-359596323/2000000000 : ℝ)*X 0 0+(135673667/250000000 : ℝ)*X 0 1+(5219735103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33429647/62500000 : ℝ)*X 1 0+(-1904005669/10000000000 : ℝ)*X 1 1+(1304933771/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348743503/10000000000 : ℝ)*X 2 0+(5219735093/10000000000 : ℝ)*X 2 1+(-1904005681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2123742407/5000000000 : ℝ)*X 0 0+(4010089053/10000000000 : ℝ)*X 0 1+(4496227439/10000000000 : ℝ)*X 0 2+(2123742407/5000000000 : ℝ)*X 1 0+(4010089053/10000000000 : ℝ)*X 1 1+(4496227439/10000000000 : ℝ)*X 1 2+(2123742407/5000000000 : ℝ)*X 2 0+(4010089053/10000000000 : ℝ)*X 2 1+(4496227439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-899004361/5000000000 : ℝ)*X 0 0+(2610406251/5000000000 : ℝ)*X 0 1+(5425861311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646990713/5000000000 : ℝ)*X 1 0+(-848939737/5000000000 : ℝ)*X 1 1+(5425861323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293981431/10000000000 : ℝ)*X 2 0+(5425861329/10000000000 : ℝ)*X 2 1+(-1697879459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247548379/10000000000 : ℝ)*X 0 0+(2246849849/5000000000 : ℝ)*X 0 1+(1003158871/2500000000 : ℝ)*X 0 2+(4247548379/10000000000 : ℝ)*X 1 0+(2246849849/5000000000 : ℝ)*X 1 1+(1003158871/2500000000 : ℝ)*X 1 2+(4247548379/10000000000 : ℝ)*X 2 0+(2246849849/5000000000 : ℝ)*X 2 1+(1003158871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1561_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6715477817012083061572993/3056250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19976361/5000000000000 : ℝ)*(base19) + (358437053/100000000000000 : ℝ)*(base23) + (13773883/100000000000000 : ℝ)*(lower2) + (67017367/100000000000000 : ℝ)*(upper3) + (17305863/50000000000000 : ℝ)*(upper5) + (172075755988123/5000000000000 : ℝ)*(major0) + (172075755988123/5000000000000 : ℝ)*(major1) + (172075755988123/5000000000000 : ℝ)*(major2) + (4825991518063027/100000000000000 : ℝ)*(sp0) + (1206499171958517/25000000000000 : ℝ)*(sp1) + (965199345784847/20000000000000 : ℝ)*(sp2) + (1028515025380599/50000000000000 : ℝ)*(sp3) + (5569298261/100000000000000 : ℝ)*(sp4) + (3028159309/100000000000000 : ℝ)*(sp7) + (514258269730127/25000000000000 : ℝ)*(f.failure) + (4825997087361289/100000000000000 : ℝ)*(f.sum) + (693547201681/110025000000000000000000000 : ℝ)*base65 + (836440166969108257/55012500000000000000000000000000 : ℝ)*base67 + (480809887310708257/55012500000000000000000000000000 : ℝ)*base69 + (27861871255545757/55012500000000000000000000000000 : ℝ)*base71 + (4746586043699/550125000000000000000000000 : ℝ)*base73 + (132458372701208257/55012500000000000000000000000000 : ℝ)*base75 + (573296734082483257/55012500000000000000000000000000 : ℝ)*base77 + (24256550710695757/55012500000000000000000000000000 : ℝ)*base79 + (5576791979233/4401000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4415073/1250000000000000000000 : ℝ)*base90 + (4415073/1250000000000000000000 : ℝ)*base92 + (4415073/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64628360354549489745008393/10187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (488661669/50000000000000 : ℝ)*(base19) + (26448779/2500000000000 : ℝ)*(base23) + (313440171/100000000000000 : ℝ)*(lower1) + (69726663/50000000000000 : ℝ)*(upper3) + (403277/1250000000000 : ℝ)*(lower4) + (1360607/1000000000000 : ℝ)*(upper5) + (1738897461843819/50000000000000 : ℝ)*(major0) + (1738897461843819/50000000000000 : ℝ)*(major1) + (1738897461843819/50000000000000 : ℝ)*(major2) + (291574999/20000000000000 : ℝ)*(sp2) + (243843585093511/5000000000000 : ℝ)*(sp4) + (2438435362273441/50000000000000 : ℝ)*(sp5) + (975373837208813/20000000000000 : ℝ)*(sp6) + (2078717934042107/100000000000000 : ℝ)*(sp7) + (2078717934042107/100000000000000 : ℝ)*(f.failure) + (243843585093511/5000000000000 : ℝ)*(f.sum) + (4939668704983/7335000000000000000000000000 : ℝ)*base65 + (2561591240429829107/183375000000000000000000000000000 : ℝ)*base67 + (2001177237518079107/183375000000000000000000000000000 : ℝ)*base69 + (3877612339023204107/183375000000000000000000000000000 : ℝ)*base71 + (302701801363/458437500000000000000000000 : ℝ)*base73 + (7373517094315329107/183375000000000000000000000000000 : ℝ)*base75 + (837997366941204107/183375000000000000000000000000000 : ℝ)*base77 + (723317107784829107/183375000000000000000000000000000 : ℝ)*base79 + (3500365584727/1833750000000000000000000000 : ℝ)*base81 + (14351093/5000000000000000000000 : ℝ)*base90 + (14351093/5000000000000000000000 : ℝ)*base92 + (14351093/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1561_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1561_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1561_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1561_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1561_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1561_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4617/1024 : ℝ) ≤ p) (hpb : p ≤ (4619/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83652401/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3959/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1561_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

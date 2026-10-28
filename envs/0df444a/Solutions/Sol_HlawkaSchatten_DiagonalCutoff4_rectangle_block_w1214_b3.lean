-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:15.149882+00:00
-- url     : https://prove2.me/submissions/2d23602f-ba6e-413e-970e-11bdce2c77cd

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
theorem support_rectangle_w1214_box_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-502088241/2500000000 : ℝ)*x 0 + (1075052383/2000000000 : ℝ)*x 1 + (2687631111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502088241/2500000000 : ℝ)^8407 ≤ (11975963459743/100000000000000 : ℝ)^6359 := by
    have hnat : (502088241 : ℕ)^8407*100000000000000^6359 ≤ 11975963459743^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502088241 2500000000 11975963459743 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075052383/2000000000 : ℝ)^8407 ≤ (8802403320397/20000000000000 : ℝ)^6359 := by
    have hnat : (1075052383 : ℕ)^8407*20000000000000^6359 ≤ 8802403320397^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075052383 2000000000 8802403320397 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687631111/5000000000 : ℝ)^8407 ≤ (44012019925229/100000000000000 : ℝ)^6359 := by
    have hnat : (2687631111 : ℕ)^8407*100000000000000^6359 ≤ 44012019925229^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687631111 5000000000 44012019925229 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502088241/2500000000 : ℝ), (1075052383/2000000000 : ℝ), (2687631111/5000000000 : ℝ)] ![(11975963459743/100000000000000 : ℝ), (8802403320397/20000000000000 : ℝ), (44012019925229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502088241/2500000000 : ℝ)|^8407 ≤ (11975963459743/100000000000000 : ℝ)^6359
        have hw : |(-502088241/2500000000 : ℝ)|=(502088241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075052383/2000000000 : ℝ)|^8407 ≤ (8802403320397/20000000000000 : ℝ)^6359
        have hw : |(1075052383/2000000000 : ℝ)|=(1075052383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687631111/5000000000 : ℝ)|^8407 ≤ (44012019925229/100000000000000 : ℝ)^6359
        have hw : |(2687631111/5000000000 : ℝ)|=(2687631111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648295639/5000000000 : ℝ)*x 0 + (-2115215407/10000000000 : ℝ)*x 1 + (1075052397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648295639/5000000000 : ℝ)^8407 ≤ (43162428629023/100000000000000 : ℝ)^6359 := by
    have hnat : (2648295639 : ℕ)^8407*100000000000000^6359 ≤ 43162428629023^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648295639 5000000000 43162428629023 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115215407/10000000000 : ℝ)^8407 ≤ (2565110798911/20000000000000 : ℝ)^6359 := by
    have hnat : (2115215407 : ℕ)^8407*20000000000000^6359 ≤ 2565110798911^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115215407 10000000000 2565110798911 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075052397/2000000000 : ℝ)^8407 ≤ (2750751084983/6250000000000 : ℝ)^6359 := by
    have hnat : (1075052397 : ℕ)^8407*6250000000000^6359 ≤ 2750751084983^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075052397 2000000000 2750751084983 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648295639/5000000000 : ℝ), (-2115215407/10000000000 : ℝ), (1075052397/2000000000 : ℝ)] ![(43162428629023/100000000000000 : ℝ), (2565110798911/20000000000000 : ℝ), (2750751084983/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648295639/5000000000 : ℝ)|^8407 ≤ (43162428629023/100000000000000 : ℝ)^6359
        have hw : |(2648295639/5000000000 : ℝ)|=(2648295639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115215407/10000000000 : ℝ)|^8407 ≤ (2565110798911/20000000000000 : ℝ)^6359
        have hw : |(-2115215407/10000000000 : ℝ)|=(2115215407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075052397/2000000000 : ℝ)|^8407 ≤ (2750751084983/6250000000000 : ℝ)^6359
        have hw : |(1075052397/2000000000 : ℝ)|=(1075052397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296592497/10000000000 : ℝ)*x 0 + (2687630799/5000000000 : ℝ)*x 1 + (-211521429/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296592497/10000000000 : ℝ)^8407 ≤ (8632488352413/20000000000000 : ℝ)^6359 := by
    have hnat : (5296592497 : ℕ)^8407*20000000000000^6359 ≤ 8632488352413^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296592497 10000000000 8632488352413 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687630799/5000000000 : ℝ)^8407 ≤ (11003003292623/25000000000000 : ℝ)^6359 := by
    have hnat : (2687630799 : ℕ)^8407*25000000000000^6359 ≤ 11003003292623^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687630799 5000000000 11003003292623 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211521429/1000000000 : ℝ)^8407 ≤ (12825545040353/100000000000000 : ℝ)^6359 := by
    have hnat : (211521429 : ℕ)^8407*100000000000000^6359 ≤ 12825545040353^6359*1000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211521429 1000000000 12825545040353 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296592497/10000000000 : ℝ), (2687630799/5000000000 : ℝ), (-211521429/1000000000 : ℝ)] ![(8632488352413/20000000000000 : ℝ), (11003003292623/25000000000000 : ℝ), (12825545040353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296592497/10000000000 : ℝ)|^8407 ≤ (8632488352413/20000000000000 : ℝ)^6359
        have hw : |(5296592497/10000000000 : ℝ)|=(5296592497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687630799/5000000000 : ℝ)|^8407 ≤ (11003003292623/25000000000000 : ℝ)^6359
        have hw : |(2687630799/5000000000 : ℝ)|=(2687630799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211521429/1000000000 : ℝ)|^8407 ≤ (12825545040353/100000000000000 : ℝ)^6359
        have hw : |(-211521429/1000000000 : ℝ)|=(211521429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2230716383/5000000000 : ℝ)*x 0 + (1075821977/2500000000 : ℝ)*x 1 + (26895551/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230716383/5000000000 : ℝ)^8407 ≤ (6880388009959/20000000000000 : ℝ)^6359 := by
    have hnat : (2230716383 : ℕ)^8407*20000000000000^6359 ≤ 6880388009959^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230716383 5000000000 6880388009959 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075821977/2500000000 : ℝ)^8407 ≤ (3279902869523/10000000000000 : ℝ)^6359 := by
    have hnat : (1075821977 : ℕ)^8407*10000000000000^6359 ≤ 3279902869523^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075821977 2500000000 3279902869523 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26895551/62500000 : ℝ)^8407 ≤ (16399515617263/50000000000000 : ℝ)^6359 := by
    have hnat : (26895551 : ℕ)^8407*50000000000000^6359 ≤ 16399515617263^6359*62500000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26895551 62500000 16399515617263 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2230716383/5000000000 : ℝ), (1075821977/2500000000 : ℝ), (26895551/62500000 : ℝ)] ![(6880388009959/20000000000000 : ℝ), (3279902869523/10000000000000 : ℝ), (16399515617263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2230716383/5000000000 : ℝ)|^8407 ≤ (6880388009959/20000000000000 : ℝ)^6359
        have hw : |(2230716383/5000000000 : ℝ)|=(2230716383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075821977/2500000000 : ℝ)|^8407 ≤ (3279902869523/10000000000000 : ℝ)^6359
        have hw : |(1075821977/2500000000 : ℝ)|=(1075821977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26895551/62500000 : ℝ)|^8407 ≤ (16399515617263/50000000000000 : ℝ)^6359
        have hw : |(26895551/62500000 : ℝ)|=(26895551/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-564719707/2500000000 : ℝ)*x 0 + (1056398087/2000000000 : ℝ)*x 1 + (5281990491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564719707/2500000000 : ℝ)^8407 ≤ (13989610231347/100000000000000 : ℝ)^6359 := by
    have hnat : (564719707 : ℕ)^8407*100000000000000^6359 ≤ 13989610231347^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564719707 2500000000 13989610231347 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056398087/2000000000 : ℝ)^8407 ≤ (8601038914719/20000000000000 : ℝ)^6359 := by
    have hnat : (1056398087 : ℕ)^8407*20000000000000^6359 ≤ 8601038914719^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056398087 2000000000 8601038914719 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281990491/10000000000 : ℝ)^8407 ≤ (21502597588191/50000000000000 : ℝ)^6359 := by
    have hnat : (5281990491 : ℕ)^8407*50000000000000^6359 ≤ 21502597588191^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281990491 10000000000 21502597588191 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-564719707/2500000000 : ℝ), (1056398087/2000000000 : ℝ), (5281990491/10000000000 : ℝ)] ![(13989610231347/100000000000000 : ℝ), (8601038914719/20000000000000 : ℝ), (21502597588191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-564719707/2500000000 : ℝ)|^8407 ≤ (13989610231347/100000000000000 : ℝ)^6359
        have hw : |(-564719707/2500000000 : ℝ)|=(564719707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056398087/2000000000 : ℝ)|^8407 ≤ (8601038914719/20000000000000 : ℝ)^6359
        have hw : |(1056398087/2000000000 : ℝ)|=(1056398087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281990491/10000000000 : ℝ)|^8407 ≤ (21502597588191/50000000000000 : ℝ)^6359
        have hw : |(5281990491/10000000000 : ℝ)|=(5281990491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362382329/10000000000 : ℝ)*x 0 + (-134507007/625000000 : ℝ)*x 1 + (5281990317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362382329/10000000000 : ℝ)^8407 ≤ (21936325102959/50000000000000 : ℝ)^6359 := by
    have hnat : (5362382329 : ℕ)^8407*50000000000000^6359 ≤ 21936325102959^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362382329 10000000000 21936325102959 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134507007/625000000 : ℝ)^8407 ≤ (1312215647571/10000000000000 : ℝ)^6359 := by
    have hnat : (134507007 : ℕ)^8407*10000000000000^6359 ≤ 1312215647571^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134507007 625000000 1312215647571 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281990317/10000000000 : ℝ)^8407 ≤ (21502596651719/50000000000000 : ℝ)^6359 := by
    have hnat : (5281990317 : ℕ)^8407*50000000000000^6359 ≤ 21502596651719^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281990317 10000000000 21502596651719 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362382329/10000000000 : ℝ), (-134507007/625000000 : ℝ), (5281990317/10000000000 : ℝ)] ![(21936325102959/50000000000000 : ℝ), (1312215647571/10000000000000 : ℝ), (21502596651719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362382329/10000000000 : ℝ)|^8407 ≤ (21936325102959/50000000000000 : ℝ)^6359
        have hw : |(5362382329/10000000000 : ℝ)|=(5362382329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134507007/625000000 : ℝ)|^8407 ≤ (1312215647571/10000000000000 : ℝ)^6359
        have hw : |(-134507007/625000000 : ℝ)|=(134507007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281990317/10000000000 : ℝ)|^8407 ≤ (21502596651719/50000000000000 : ℝ)^6359
        have hw : |(5281990317/10000000000 : ℝ)|=(5281990317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134059549/250000000 : ℝ)*x 0 + (1320497647/2500000000 : ℝ)*x 1 + (-1076056123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134059549/250000000 : ℝ)^8407 ≤ (8774529242923/20000000000000 : ℝ)^6359 := by
    have hnat : (134059549 : ℕ)^8407*20000000000000^6359 ≤ 8774529242923^6359*250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134059549 250000000 8774529242923 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320497647/2500000000 : ℝ)^8407 ≤ (21502598110247/50000000000000 : ℝ)^6359 := by
    have hnat : (1320497647 : ℕ)^8407*50000000000000^6359 ≤ 21502598110247^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320497647 2500000000 21502598110247 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076056123/5000000000 : ℝ)^8407 ≤ (13122157555893/100000000000000 : ℝ)^6359 := by
    have hnat : (1076056123 : ℕ)^8407*100000000000000^6359 ≤ 13122157555893^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076056123 5000000000 13122157555893 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134059549/250000000 : ℝ), (1320497647/2500000000 : ℝ), (-1076056123/5000000000 : ℝ)] ![(8774529242923/20000000000000 : ℝ), (21502598110247/50000000000000 : ℝ), (13122157555893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134059549/250000000 : ℝ)|^8407 ≤ (8774529242923/20000000000000 : ℝ)^6359
        have hw : |(134059549/250000000 : ℝ)|=(134059549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320497647/2500000000 : ℝ)|^8407 ≤ (21502598110247/50000000000000 : ℝ)^6359
        have hw : |(1320497647/2500000000 : ℝ)|=(1320497647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076056123/5000000000 : ℝ)|^8407 ≤ (13122157555893/100000000000000 : ℝ)^6359
        have hw : |(-1076056123/5000000000 : ℝ)|=(1076056123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2123717523/5000000000 : ℝ)*x 0 + (2205133307/5000000000 : ℝ)*x 1 + (551283321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123717523/5000000000 : ℝ)^8407 ≤ (1611870154113/5000000000000 : ℝ)^6359 := by
    have hnat : (2123717523 : ℕ)^8407*5000000000000^6359 ≤ 1611870154113^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123717523 5000000000 1611870154113 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205133307/5000000000 : ℝ)^8407 ≤ (3388129868139/10000000000000 : ℝ)^6359 := by
    have hnat : (2205133307 : ℕ)^8407*10000000000000^6359 ≤ 3388129868139^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205133307 5000000000 3388129868139 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551283321/1250000000 : ℝ)^8407 ≤ (33881298214187/100000000000000 : ℝ)^6359 := by
    have hnat : (551283321 : ℕ)^8407*100000000000000^6359 ≤ 33881298214187^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551283321 1250000000 33881298214187 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123717523/5000000000 : ℝ), (2205133307/5000000000 : ℝ), (551283321/1250000000 : ℝ)] ![(1611870154113/5000000000000 : ℝ), (3388129868139/10000000000000 : ℝ), (33881298214187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123717523/5000000000 : ℝ)|^8407 ≤ (1611870154113/5000000000000 : ℝ)^6359
        have hw : |(2123717523/5000000000 : ℝ)|=(2123717523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205133307/5000000000 : ℝ)|^8407 ≤ (3388129868139/10000000000000 : ℝ)^6359
        have hw : |(2205133307/5000000000 : ℝ)|=(2205133307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551283321/1250000000 : ℝ)|^8407 ≤ (33881298214187/100000000000000 : ℝ)^6359
        have hw : |(551283321/1250000000 : ℝ)|=(551283321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_8 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-551602737/2500000000 : ℝ)*x 0 + (2609210739/5000000000 : ℝ)*x 1 + (5384874651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551602737/2500000000 : ℝ)^8407 ≤ (52975122539/390625000000 : ℝ)^6359 := by
    have hnat : (551602737 : ℕ)^8407*390625000000^6359 ≤ 52975122539^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551602737 2500000000 52975122539 390625000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609210739/5000000000 : ℝ)^8407 ≤ (42322265155533/100000000000000 : ℝ)^6359 := by
    have hnat : (2609210739 : ℕ)^8407*100000000000000^6359 ≤ 42322265155533^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609210739 5000000000 42322265155533 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384874651/10000000000 : ℝ)^8407 ≤ (44116103453937/100000000000000 : ℝ)^6359 := by
    have hnat : (5384874651 : ℕ)^8407*100000000000000^6359 ≤ 44116103453937^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384874651 10000000000 44116103453937 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551602737/2500000000 : ℝ), (2609210739/5000000000 : ℝ), (5384874651/10000000000 : ℝ)] ![(52975122539/390625000000 : ℝ), (42322265155533/100000000000000 : ℝ), (44116103453937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551602737/2500000000 : ℝ)|^8407 ≤ (52975122539/390625000000 : ℝ)^6359
        have hw : |(-551602737/2500000000 : ℝ)|=(551602737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609210739/5000000000 : ℝ)|^8407 ≤ (42322265155533/100000000000000 : ℝ)^6359
        have hw : |(2609210739/5000000000 : ℝ)|=(2609210739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384874651/10000000000 : ℝ)|^8407 ≤ (44116103453937/100000000000000 : ℝ)^6359
        have hw : |(5384874651/10000000000 : ℝ)|=(5384874651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_9 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289808081/10000000000 : ℝ)*x 0 + (-1055672249/5000000000 : ℝ)*x 1 + (673109327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289808081/10000000000 : ℝ)^8407 ≤ (43089364120777/100000000000000 : ℝ)^6359 := by
    have hnat : (5289808081 : ℕ)^8407*100000000000000^6359 ≤ 43089364120777^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289808081 10000000000 43089364120777 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055672249/5000000000 : ℝ)^8407 ≤ (12794532789743/100000000000000 : ℝ)^6359 := by
    have hnat : (1055672249 : ℕ)^8407*100000000000000^6359 ≤ 12794532789743^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055672249 5000000000 12794532789743 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673109327/1250000000 : ℝ)^8407 ≤ (44116103074847/100000000000000 : ℝ)^6359 := by
    have hnat : (673109327 : ℕ)^8407*100000000000000^6359 ≤ 44116103074847^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673109327 1250000000 44116103074847 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289808081/10000000000 : ℝ), (-1055672249/5000000000 : ℝ), (673109327/1250000000 : ℝ)] ![(43089364120777/100000000000000 : ℝ), (12794532789743/100000000000000 : ℝ), (44116103074847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289808081/10000000000 : ℝ)|^8407 ≤ (43089364120777/100000000000000 : ℝ)^6359
        have hw : |(5289808081/10000000000 : ℝ)|=(5289808081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055672249/5000000000 : ℝ)|^8407 ≤ (12794532789743/100000000000000 : ℝ)^6359
        have hw : |(-1055672249/5000000000 : ℝ)|=(1055672249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673109327/1250000000 : ℝ)|^8407 ≤ (44116103074847/100000000000000 : ℝ)^6359
        have hw : |(673109327/1250000000 : ℝ)|=(673109327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_10 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8463693/16000000 : ℝ)*x 0 + (1076974931/2000000000 : ℝ)*x 1 + (-2111344387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8463693/16000000 : ℝ)^8407 ≤ (43089364594621/100000000000000 : ℝ)^6359 := by
    have hnat : (8463693 : ℕ)^8407*100000000000000^6359 ≤ 43089364594621^6359*16000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8463693 16000000 43089364594621 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076974931/2000000000 : ℝ)^8407 ≤ (44116103497261/100000000000000 : ℝ)^6359 := by
    have hnat : (1076974931 : ℕ)^8407*100000000000000^6359 ≤ 44116103497261^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076974931 2000000000 44116103497261 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111344387/10000000000 : ℝ)^8407 ≤ (12794531900459/100000000000000 : ℝ)^6359 := by
    have hnat : (2111344387 : ℕ)^8407*100000000000000^6359 ≤ 12794531900459^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111344387 10000000000 12794531900459 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8463693/16000000 : ℝ), (1076974931/2000000000 : ℝ), (-2111344387/10000000000 : ℝ)] ![(43089364594621/100000000000000 : ℝ), (44116103497261/100000000000000 : ℝ), (12794531900459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8463693/16000000 : ℝ)|^8407 ≤ (43089364594621/100000000000000 : ℝ)^6359
        have hw : |(8463693/16000000 : ℝ)|=(8463693/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076974931/2000000000 : ℝ)|^8407 ≤ (44116103497261/100000000000000 : ℝ)^6359
        have hw : |(1076974931/2000000000 : ℝ)|=(1076974931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111344387/10000000000 : ℝ)|^8407 ≤ (12794531900459/100000000000000 : ℝ)^6359
        have hw : |(-2111344387/10000000000 : ℝ)|=(2111344387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_11 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1120803833/2500000000 : ℝ)*x 0 + (858451229/2000000000 : ℝ)*x 1 + (268266017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120803833/2500000000 : ℝ)^8407 ≤ (34624174194361/100000000000000 : ℝ)^6359 := by
    have hnat : (1120803833 : ℕ)^8407*100000000000000^6359 ≤ 34624174194361^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120803833 2500000000 34624174194361 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858451229/2000000000 : ℝ)^8407 ≤ (8171978064961/25000000000000 : ℝ)^6359 := by
    have hnat : (858451229 : ℕ)^8407*25000000000000^6359 ≤ 8171978064961^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858451229 2000000000 8171978064961 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268266017/625000000 : ℝ)^8407 ≤ (32687913538511/100000000000000 : ℝ)^6359 := by
    have hnat : (268266017 : ℕ)^8407*100000000000000^6359 ≤ 32687913538511^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268266017 625000000 32687913538511 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120803833/2500000000 : ℝ), (858451229/2000000000 : ℝ), (268266017/625000000 : ℝ)] ![(34624174194361/100000000000000 : ℝ), (8171978064961/25000000000000 : ℝ), (32687913538511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120803833/2500000000 : ℝ)|^8407 ≤ (34624174194361/100000000000000 : ℝ)^6359
        have hw : |(1120803833/2500000000 : ℝ)|=(1120803833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(858451229/2000000000 : ℝ)|^8407 ≤ (8171978064961/25000000000000 : ℝ)^6359
        have hw : |(858451229/2000000000 : ℝ)|=(858451229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268266017/625000000 : ℝ)|^8407 ≤ (32687913538511/100000000000000 : ℝ)^6359
        have hw : |(268266017/625000000 : ℝ)|=(268266017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_12 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061096933/10000000000 : ℝ)*x 0 + (5437603533/10000000000 : ℝ)*x 1 + (329620099/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061096933/10000000000 : ℝ)^8407 ≤ (1549190265437/12500000000000 : ℝ)^6359 := by
    have hnat : (2061096933 : ℕ)^8407*12500000000000^6359 ≤ 1549190265437^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061096933 10000000000 1549190265437 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437603533/10000000000 : ℝ)^8407 ≤ (11172028848763/25000000000000 : ℝ)^6359 := by
    have hnat : (5437603533 : ℕ)^8407*25000000000000^6359 ≤ 11172028848763^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437603533 10000000000 11172028848763 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329620099/625000000 : ℝ)^8407 ≤ (42918362466333/100000000000000 : ℝ)^6359 := by
    have hnat : (329620099 : ℕ)^8407*100000000000000^6359 ≤ 42918362466333^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329620099 625000000 42918362466333 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061096933/10000000000 : ℝ), (5437603533/10000000000 : ℝ), (329620099/625000000 : ℝ)] ![(1549190265437/12500000000000 : ℝ), (11172028848763/25000000000000 : ℝ), (42918362466333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061096933/10000000000 : ℝ)|^8407 ≤ (1549190265437/12500000000000 : ℝ)^6359
        have hw : |(-2061096933/10000000000 : ℝ)|=(2061096933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437603533/10000000000 : ℝ)|^8407 ≤ (11172028848763/25000000000000 : ℝ)^6359
        have hw : |(5437603533/10000000000 : ℝ)|=(5437603533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329620099/625000000 : ℝ)|^8407 ≤ (42918362466333/100000000000000 : ℝ)^6359
        have hw : |(329620099/625000000 : ℝ)|=(329620099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_13 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684035621/5000000000 : ℝ)*x 0 + (-1077623991/5000000000 : ℝ)*x 1 + (1318480433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684035621/5000000000 : ℝ)^8407 ≤ (21967097532279/50000000000000 : ℝ)^6359 := by
    have hnat : (2684035621 : ℕ)^8407*50000000000000^6359 ≤ 21967097532279^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684035621 5000000000 21967097532279 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077623991/5000000000 : ℝ)^8407 ≤ (6573720432003/50000000000000 : ℝ)^6359 := by
    have hnat : (1077623991 : ℕ)^8407*50000000000000^6359 ≤ 6573720432003^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077623991 5000000000 6573720432003 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318480433/2500000000 : ℝ)^8407 ≤ (42918364058627/100000000000000 : ℝ)^6359 := by
    have hnat : (1318480433 : ℕ)^8407*100000000000000^6359 ≤ 42918364058627^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318480433 2500000000 42918364058627 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684035621/5000000000 : ℝ), (-1077623991/5000000000 : ℝ), (1318480433/2500000000 : ℝ)] ![(21967097532279/50000000000000 : ℝ), (6573720432003/50000000000000 : ℝ), (42918364058627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684035621/5000000000 : ℝ)|^8407 ≤ (21967097532279/50000000000000 : ℝ)^6359
        have hw : |(2684035621/5000000000 : ℝ)|=(2684035621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077623991/5000000000 : ℝ)|^8407 ≤ (6573720432003/50000000000000 : ℝ)^6359
        have hw : |(-1077623991/5000000000 : ℝ)|=(1077623991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318480433/2500000000 : ℝ)|^8407 ≤ (42918364058627/100000000000000 : ℝ)^6359
        have hw : |(1318480433/2500000000 : ℝ)|=(1318480433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_14 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684035873/5000000000 : ℝ)*x 0 + (659240193/1250000000 : ℝ)*x 1 + (-538811889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684035873/5000000000 : ℝ)^8407 ≤ (8786840103591/20000000000000 : ℝ)^6359 := by
    have hnat : (2684035873 : ℕ)^8407*20000000000000^6359 ≤ 8786840103591^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684035873 5000000000 8786840103591 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659240193/1250000000 : ℝ)^8407 ≤ (42918362035983/100000000000000 : ℝ)^6359 := by
    have hnat : (659240193 : ℕ)^8407*100000000000000^6359 ≤ 42918362035983^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659240193 1250000000 42918362035983 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538811889/2500000000 : ℝ)^8407 ≤ (657371871419/5000000000000 : ℝ)^6359 := by
    have hnat : (538811889 : ℕ)^8407*5000000000000^6359 ≤ 657371871419^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538811889 2500000000 657371871419 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684035873/5000000000 : ℝ), (659240193/1250000000 : ℝ), (-538811889/2500000000 : ℝ)] ![(8786840103591/20000000000000 : ℝ), (42918362035983/100000000000000 : ℝ), (657371871419/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684035873/5000000000 : ℝ)|^8407 ≤ (8786840103591/20000000000000 : ℝ)^6359
        have hw : |(2684035873/5000000000 : ℝ)|=(2684035873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659240193/1250000000 : ℝ)|^8407 ≤ (42918362035983/100000000000000 : ℝ)^6359
        have hw : |(659240193/1250000000 : ℝ)|=(659240193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538811889/2500000000 : ℝ)|^8407 ≤ (657371871419/5000000000000 : ℝ)^6359
        have hw : |(-538811889/2500000000 : ℝ)|=(538811889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_box_15 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2114344957/5000000000 : ℝ)*x 0 + (4419517147/10000000000 : ℝ)*x 1 + (4419516003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114344957/5000000000 : ℝ)^8407 ≤ (8012360821357/25000000000000 : ℝ)^6359 := by
    have hnat : (2114344957 : ℕ)^8407*25000000000000^6359 ≤ 8012360821357^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114344957 5000000000 8012360821357 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419517147/10000000000 : ℝ)^8407 ≤ (849382104111/2500000000000 : ℝ)^6359 := by
    have hnat : (4419517147 : ℕ)^8407*2500000000000^6359 ≤ 849382104111^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419517147 10000000000 849382104111 2500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419516003/10000000000 : ℝ)^8407 ≤ (33975272537471/100000000000000 : ℝ)^6359 := by
    have hnat : (4419516003 : ℕ)^8407*100000000000000^6359 ≤ 33975272537471^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419516003 10000000000 33975272537471 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114344957/5000000000 : ℝ), (4419517147/10000000000 : ℝ), (4419516003/10000000000 : ℝ)] ![(8012360821357/25000000000000 : ℝ), (849382104111/2500000000000 : ℝ), (33975272537471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114344957/5000000000 : ℝ)|^8407 ≤ (8012360821357/25000000000000 : ℝ)^6359
        have hw : |(2114344957/5000000000 : ℝ)|=(2114344957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419517147/10000000000 : ℝ)|^8407 ≤ (849382104111/2500000000000 : ℝ)^6359
        have hw : |(4419517147/10000000000 : ℝ)|=(4419517147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419516003/10000000000 : ℝ)|^8407 ≤ (33975272537471/100000000000000 : ℝ)^6359
        have hw : |(4419516003/10000000000 : ℝ)|=(4419516003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31121/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11871/20000 : ℝ) ∧ (40013/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20821/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2289/20000 : ℝ) ^ (4203/1024 : ℝ) ≤ (3420077142890113/25000000000000000000 : ℝ) := by
    have hpowers : (2289/20000 : ℝ)^4203 ≤ (3420077142890113/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2289 : ℕ)^4203*25000000000000000000^1024 ≤ 3420077142890113^1024*20000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 20000 3420077142890113 25000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/20000 : ℝ)) (X := (3420077142890113/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (3210593362878239/10000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^4203 ≤ (3210593362878239/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14089 : ℕ)^4203*10000000000000000000^1024 ≤ 3210593362878239^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 3210593362878239 10000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (3210593362878239/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503420077142890113/12500000000000000000 : ℝ) ≤ (10000666532795331/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (12503420077142890113/12500000000000000000 : ℝ)^1024 ≤ (10000666532795331/10000000000000000 : ℝ)^4203 := by
      have hnat : (12503420077142890113 : ℕ)^1024*10000000000000000^4203 ≤ 10000666532795331^4203*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503420077142890113 12500000000000000000 10000666532795331 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666532795331/10000000000000000 : ℝ)) (X := (12503420077142890113/12500000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022893121100171421/50000000000000000000 : ℝ) ≤ (250027883057207/250000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50022893121100171421/50000000000000000000 : ℝ)^1024 ≤ (250027883057207/250000000000000 : ℝ)^4203 := by
      have hnat : (50022893121100171421 : ℕ)^1024*250000000000000^4203 ≤ 250027883057207^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022893121100171421 50000000000000000000 250027883057207 250000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250027883057207/250000000000000 : ℝ)) (X := (50022893121100171421/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003210593362878239/5000000000000000000 : ℝ) ≤ (10001564111781229/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (5003210593362878239/5000000000000000000 : ℝ)^1024 ≤ (10001564111781229/10000000000000000 : ℝ)^4203 := by
      have hnat : (5003210593362878239 : ℕ)^1024*10000000000000000^4203 ≤ 10001564111781229^4203*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003210593362878239 5000000000000000000 10001564111781229 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001564111781229/10000000000000000 : ℝ)) (X := (5003210593362878239/5000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3420077142890113/25000000000000000000 : ℝ) ≤ ((13215744760608626277/13220000000000000000 : ℝ)+2*(448789492949/264400000000000 : ℝ)*(2289/20000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (13215744760608626277/13220000000000000000 : ℝ)+2*(448789492949/264400000000000 : ℝ)*(2289/20000 : ℝ)=(10000666532795331/10000000000000000 : ℝ) by norm_num, show 1+2*(3420077142890113/25000000000000000000 : ℝ)=(12503420077142890113/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3210593362878239/10000000000000000000 : ℝ)+(3420077142890113/25000000000000000000 : ℝ) ≤ ((13215744760608626277/13220000000000000000 : ℝ)+(448789492949/264400000000000 : ℝ)*((14089/100000 : ℝ)+(2289/20000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (13215744760608626277/13220000000000000000 : ℝ)+(448789492949/264400000000000 : ℝ)*((14089/100000 : ℝ)+(2289/20000 : ℝ))=(250027883057207/250000000000000 : ℝ) by norm_num, show 1+(3210593362878239/10000000000000000000 : ℝ)+(3420077142890113/25000000000000000000 : ℝ)=(50022893121100171421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3210593362878239/10000000000000000000 : ℝ) ≤ ((13215744760608626277/13220000000000000000 : ℝ)+2*(448789492949/264400000000000 : ℝ)*(14089/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (13215744760608626277/13220000000000000000 : ℝ)+2*(448789492949/264400000000000 : ℝ)*(14089/100000 : ℝ)=(10001564111781229/10000000000000000 : ℝ) by norm_num, show 1+2*(3210593362878239/10000000000000000000 : ℝ)=(5003210593362878239/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13215744760608626277/13220000000000000000 : ℝ)*(X 1 0+X 2 0)+(448789492949/264400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13215744760608626277/13220000000000000000 : ℝ)) (alpha := (448789492949/264400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13215744760608626277/13220000000000000000 : ℝ)*(X 0 1+X 2 1)+(448789492949/264400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13215744760608626277/13220000000000000000 : ℝ)) (alpha := (448789492949/264400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13215744760608626277/13220000000000000000 : ℝ)*(X 0 2+X 1 2)+(448789492949/264400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13215744760608626277/13220000000000000000 : ℝ)) (alpha := (448789492949/264400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-502088241/2500000000 : ℝ)*X 0 0+(1075052383/2000000000 : ℝ)*X 0 1+(2687631111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648295639/5000000000 : ℝ)*X 1 0+(-2115215407/10000000000 : ℝ)*X 1 1+(1075052397/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296592497/10000000000 : ℝ)*X 2 0+(2687630799/5000000000 : ℝ)*X 2 1+(-211521429/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2230716383/5000000000 : ℝ)*X 0 0+(1075821977/2500000000 : ℝ)*X 0 1+(26895551/62500000 : ℝ)*X 0 2+(2230716383/5000000000 : ℝ)*X 1 0+(1075821977/2500000000 : ℝ)*X 1 1+(26895551/62500000 : ℝ)*X 1 2+(2230716383/5000000000 : ℝ)*X 2 0+(1075821977/2500000000 : ℝ)*X 2 1+(26895551/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-564719707/2500000000 : ℝ)*X 0 0+(1056398087/2000000000 : ℝ)*X 0 1+(5281990491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362382329/10000000000 : ℝ)*X 1 0+(-134507007/625000000 : ℝ)*X 1 1+(5281990317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134059549/250000000 : ℝ)*X 2 0+(1320497647/2500000000 : ℝ)*X 2 1+(-1076056123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123717523/5000000000 : ℝ)*X 0 0+(2205133307/5000000000 : ℝ)*X 0 1+(551283321/1250000000 : ℝ)*X 0 2+(2123717523/5000000000 : ℝ)*X 1 0+(2205133307/5000000000 : ℝ)*X 1 1+(551283321/1250000000 : ℝ)*X 1 2+(2123717523/5000000000 : ℝ)*X 2 0+(2205133307/5000000000 : ℝ)*X 2 1+(551283321/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-551602737/2500000000 : ℝ)*X 0 0+(2609210739/5000000000 : ℝ)*X 0 1+(5384874651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289808081/10000000000 : ℝ)*X 1 0+(-1055672249/5000000000 : ℝ)*X 1 1+(673109327/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((8463693/16000000 : ℝ)*X 2 0+(1076974931/2000000000 : ℝ)*X 2 1+(-2111344387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1120803833/2500000000 : ℝ)*X 0 0+(858451229/2000000000 : ℝ)*X 0 1+(268266017/625000000 : ℝ)*X 0 2+(1120803833/2500000000 : ℝ)*X 1 0+(858451229/2000000000 : ℝ)*X 1 1+(268266017/625000000 : ℝ)*X 1 2+(1120803833/2500000000 : ℝ)*X 2 0+(858451229/2000000000 : ℝ)*X 2 1+(268266017/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2061096933/10000000000 : ℝ)*X 0 0+(5437603533/10000000000 : ℝ)*X 0 1+(329620099/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684035621/5000000000 : ℝ)*X 1 0+(-1077623991/5000000000 : ℝ)*X 1 1+(1318480433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684035873/5000000000 : ℝ)*X 2 0+(659240193/1250000000 : ℝ)*X 2 1+(-538811889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2114344957/5000000000 : ℝ)*X 0 0+(4419517147/10000000000 : ℝ)*X 0 1+(4419516003/10000000000 : ℝ)*X 0 2+(2114344957/5000000000 : ℝ)*X 1 0+(4419517147/10000000000 : ℝ)*X 1 1+(4419516003/10000000000 : ℝ)*X 1 2+(2114344957/5000000000 : ℝ)*X 2 0+(4419517147/10000000000 : ℝ)*X 2 1+(4419516003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31121/50000 : ℝ) ≤ (-205700056229203256065173223762317/330500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2953227/2500000000000 : ℝ)*(upper1) + (36378759/20000000000000 : ℝ)*(lower4) + (12994621/50000000000000 : ℝ)*(upper5) + (3980124917470507/100000000000000 : ℝ)*(major0) + (3980124917470507/100000000000000 : ℝ)*(major1) + (3980124917470507/100000000000000 : ℝ)*(major2) + (3033569977/50000000000000 : ℝ)*(sp3) + (5343062637406609/100000000000000 : ℝ)*(sp4) + (5343031454989013/100000000000000 : ℝ)*(sp5) + (2671502315332169/50000000000000 : ℝ)*(sp6) + (2637926932969607/100000000000000 : ℝ)*(sp7) + (547019309/100000000000000 : ℝ)*(sp12) + (15864718453/50000000000000 : ℝ)*(sp13) + (58553761581/100000000000000 : ℝ)*(sp14) + (1318966500054781/50000000000000 : ℝ)*(f.failure) + (2671531592212959/50000000000000 : ℝ)*(f.sum) + (103467588424003/13220000000000000000000000000 : ℝ)*base65 + (2646967448165862439/1322000000000000000000000000000000 : ℝ)*base67 + (7428134660787862439/1322000000000000000000000000000000 : ℝ)*base69 + (7080548704459862439/1322000000000000000000000000000000 : ℝ)*base71 + (22499032677103/13220000000000000000000000000 : ℝ)*base73 + (6839569898951862439/1322000000000000000000000000000000 : ℝ)*base75 + (4779575478065862439/1322000000000000000000000000000000 : ℝ)*base77 + (3430594666946137561/1322000000000000000000000000000000 : ℝ)*base80 + (43948661808103/13220000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (784591/125000000000000000000 : ℝ)*base89 + (784591/125000000000000000000 : ℝ)*base91 + (784591/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11871/20000 : ℝ) ≤ (98088070923081082194605619/165250000000000000000000000 : ℝ) := by norm_num
    linear_combination (446195423/100000000000000 : ℝ)*(lower1) + (16108551/12500000000000 : ℝ)*(lower2) + (102266179/100000000000000 : ℝ)*(lower3) + (74040993/10000000000000 : ℝ)*(upper4) + (202272114823661/5000000000000 : ℝ)*(major0) + (202272114823661/5000000000000 : ℝ)*(major1) + (202272114823661/5000000000000 : ℝ)*(major2) + (1347468744966833/25000000000000 : ℝ)*(sp0) + (2694692151651749/50000000000000 : ℝ)*(sp1) + (1347424310860899/25000000000000 : ℝ)*(sp2) + (1340610065314449/50000000000000 : ℝ)*(sp3) + (3689021429/100000000000000 : ℝ)*(sp7) + (245338281917/50000000000000 : ℝ)*(sp9) + (177736423737/100000000000000 : ℝ)*(sp10) + (1340611909825163/50000000000000 : ℝ)*(f.failure) + (1347468744966833/25000000000000 : ℝ)*(f.sum) + (242549040019/132200000000000000000000000 : ℝ)*base65 + (641238475243390097/66100000000000000000000000000000 : ℝ)*base67 + (2455167605581209903/66100000000000000000000000000000 : ℝ)*base70 + (66309675539609903/66100000000000000000000000000000 : ℝ)*base72 + (945722021003/661000000000000000000000000 : ℝ)*base74 + (1626135279841790097/66100000000000000000000000000000 : ℝ)*base75 + (393010864847509903/66100000000000000000000000000000 : ℝ)*base78 + (38588160149090097/66100000000000000000000000000000 : ℝ)*base79 + (2267710784923/82625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2087207/125000000000000000000 : ℝ)*base90 + (2087207/125000000000000000000 : ℝ)*base92 + (2087207/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40013/50000 : ℝ) ≤ (264493284751439564605280638322127/330500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1469969/10000000000000 : ℝ)*(upper0) + (285309/5000000000000 : ℝ)*(lower1) + (38047949/50000000000000 : ℝ)*(lower3) + (40768287/100000000000000 : ℝ)*(upper4) + (2256307403177983/50000000000000 : ℝ)*(major0) + (2256307403177983/50000000000000 : ℝ)*(major1) + (2256307403177983/50000000000000 : ℝ)*(major2) + (6418998759/12500000000000 : ℝ)*(sp1) + (72471671717/100000000000000 : ℝ)*(sp2) + (32135803089/100000000000000 : ℝ)*(sp3) + (6007698787734139/100000000000000 : ℝ)*(sp8) + (6007647435744067/100000000000000 : ℝ)*(sp9) + (3003813158031211/50000000000000 : ℝ)*(sp10) + (1495411307030543/50000000000000 : ℝ)*(sp11) + (1495427374932087/50000000000000 : ℝ)*(f.failure) + (6007698787734139/100000000000000 : ℝ)*(f.sum) + (15272671935927/6610000000000000000000000000 : ℝ)*base65 + (2184331455708990709/661000000000000000000000000000000 : ℝ)*base68 + (254884532874009291/661000000000000000000000000000000 : ℝ)*base69 + (4653512452853990709/661000000000000000000000000000000 : ℝ)*base72 + (4536989816547/6610000000000000000000000000 : ℝ)*base73 + (6368139263191009291/661000000000000000000000000000000 : ℝ)*base75 + (601511145530009291/661000000000000000000000000000000 : ℝ)*base77 + (7752414959117009291/661000000000000000000000000000000 : ℝ)*base79 + (28388462417187/6610000000000000000000000000 : ℝ)*base81 + (1083043/125000000000000000000 : ℝ)*base90 + (1083043/125000000000000000000 : ℝ)*base92 + (1083043/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-20821/25000 : ℝ) ≤ (-55049326591255090386584116890057/66100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189629731/100000000000000 : ℝ)*(lower0) + (4207403/4000000000000 : ℝ)*(upper1) + (153956307/50000000000000 : ℝ)*(lower2) + (38158967/20000000000000 : ℝ)*(upper3) + (401063349/100000000000000 : ℝ)*(upper5) + (909588610410047/20000000000000 : ℝ)*(major0) + (909588610410047/20000000000000 : ℝ)*(major1) + (909588610410047/20000000000000 : ℝ)*(major2) + (5959940183/100000000000000 : ℝ)*(sp4) + (242863504097/100000000000000 : ℝ)*(sp7) + (6109371294230579/100000000000000 : ℝ)*(sp12) + (3054688627085381/50000000000000 : ℝ)*(sp13) + (3054688627085381/50000000000000 : ℝ)*(sp14) + (753506653766163/25000000000000 : ℝ)*(sp15) + (3014269478568749/100000000000000 : ℝ)*(f.failure) + (3054688627085381/50000000000000 : ℝ)*(f.sum) + (3298134624207/2644000000000000000000000000 : ℝ)*base65 + (412405705062444981/264400000000000000000000000000000 : ℝ)*base68 + (8926788885638755019/264400000000000000000000000000000 : ℝ)*base69 + (2520176535745555019/264400000000000000000000000000000 : ℝ)*base71 + (23500517014611/2644000000000000000000000000 : ℝ)*base73 + (848024994640755019/264400000000000000000000000000000 : ℝ)*base75 + (3550790801454355019/264400000000000000000000000000000 : ℝ)*base77 + (18914834702987155019/264400000000000000000000000000000 : ℝ)*base79 + (5376178214117/2644000000000000000000000000 : ℝ)*base82 + (2015761/250000000000000000000 : ℝ)*base90 + (2015761/250000000000000000000 : ℝ)*base92 + (2015761/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11871/20000 : ℝ) else (40013/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20821/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1214_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1214_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11871/20000 : ℝ) else (40013/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20821/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1214_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11871/20000 : ℝ) else (40013/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20821/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

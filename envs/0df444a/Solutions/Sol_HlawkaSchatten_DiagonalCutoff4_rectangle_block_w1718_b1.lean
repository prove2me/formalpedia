-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1718_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:25.221151+00:00
-- url     : https://prove2.me/submissions/28a396e4-2802-49e6-a817-945297a40671

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
theorem support_rectangle_w1718_s3_0 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86480593/625000000 : ℝ)*x 0 + (5464961621/10000000000 : ℝ)*x 1 + (1284805827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86480593/625000000 : ℝ)^5367 ≤ (8679830753961/100000000000000 : ℝ)^4343 := by
    have hnat : (86480593 : ℕ)^5367*100000000000000^4343 ≤ 8679830753961^4343*625000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86480593 625000000 8679830753961 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464961621/10000000000 : ℝ)^5367 ≤ (47393082421567/100000000000000 : ℝ)^4343 := by
    have hnat : (5464961621 : ℕ)^5367*100000000000000^4343 ≤ 47393082421567^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464961621 10000000000 47393082421567 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284805827/2500000000 : ℝ)^5367 ≤ (274544292517/625000000000 : ℝ)^4343 := by
    have hnat : (1284805827 : ℕ)^5367*625000000000^4343 ≤ 274544292517^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284805827 2500000000 274544292517 625000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86480593/625000000 : ℝ), (5464961621/10000000000 : ℝ), (1284805827/2500000000 : ℝ)] ![(8679830753961/100000000000000 : ℝ), (47393082421567/100000000000000 : ℝ), (274544292517/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86480593/625000000 : ℝ)|^5367 ≤ (8679830753961/100000000000000 : ℝ)^4343
        have hw : |(-86480593/625000000 : ℝ)|=(86480593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464961621/10000000000 : ℝ)|^5367 ≤ (47393082421567/100000000000000 : ℝ)^4343
        have hw : |(5464961621/10000000000 : ℝ)|=(5464961621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284805827/2500000000 : ℝ)|^5367 ≤ (274544292517/625000000000 : ℝ)^4343
        have hw : |(1284805827/2500000000 : ℝ)|=(1284805827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_1 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267041363/500000000 : ℝ)*x 0 + (-776241623/5000000000 : ℝ)*x 1 + (5139223309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267041363/500000000 : ℝ)^5367 ≤ (11516582208659/25000000000000 : ℝ)^4343 := by
    have hnat : (267041363 : ℕ)^5367*25000000000000^4343 ≤ 11516582208659^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267041363 500000000 11516582208659 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776241623/5000000000 : ℝ)^5367 ≤ (400263373633/4000000000000 : ℝ)^4343 := by
    have hnat : (776241623 : ℕ)^5367*4000000000000^4343 ≤ 400263373633^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776241623 5000000000 400263373633 4000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139223309/10000000000 : ℝ)^5367 ≤ (43927086813283/100000000000000 : ℝ)^4343 := by
    have hnat : (5139223309 : ℕ)^5367*100000000000000^4343 ≤ 43927086813283^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139223309 10000000000 43927086813283 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267041363/500000000 : ℝ), (-776241623/5000000000 : ℝ), (5139223309/10000000000 : ℝ)] ![(11516582208659/25000000000000 : ℝ), (400263373633/4000000000000 : ℝ), (43927086813283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267041363/500000000 : ℝ)|^5367 ≤ (11516582208659/25000000000000 : ℝ)^4343
        have hw : |(267041363/500000000 : ℝ)|=(267041363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776241623/5000000000 : ℝ)|^5367 ≤ (400263373633/4000000000000 : ℝ)^4343
        have hw : |(-776241623/5000000000 : ℝ)|=(776241623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139223309/10000000000 : ℝ)|^5367 ≤ (43927086813283/100000000000000 : ℝ)^4343
        have hw : |(5139223309/10000000000 : ℝ)|=(5139223309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_2 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267041363/500000000 : ℝ)*x 0 + (5139223309/10000000000 : ℝ)*x 1 + (-776241623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267041363/500000000 : ℝ)^5367 ≤ (11516582208659/25000000000000 : ℝ)^4343 := by
    have hnat : (267041363 : ℕ)^5367*25000000000000^4343 ≤ 11516582208659^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267041363 500000000 11516582208659 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139223309/10000000000 : ℝ)^5367 ≤ (43927086813283/100000000000000 : ℝ)^4343 := by
    have hnat : (5139223309 : ℕ)^5367*100000000000000^4343 ≤ 43927086813283^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139223309 10000000000 43927086813283 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (776241623/5000000000 : ℝ)^5367 ≤ (400263373633/4000000000000 : ℝ)^4343 := by
    have hnat : (776241623 : ℕ)^5367*4000000000000^4343 ≤ 400263373633^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776241623 5000000000 400263373633 4000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267041363/500000000 : ℝ), (5139223309/10000000000 : ℝ), (-776241623/5000000000 : ℝ)] ![(11516582208659/25000000000000 : ℝ), (43927086813283/100000000000000 : ℝ), (400263373633/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267041363/500000000 : ℝ)|^5367 ≤ (11516582208659/25000000000000 : ℝ)^4343
        have hw : |(267041363/500000000 : ℝ)|=(267041363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139223309/10000000000 : ℝ)|^5367 ≤ (43927086813283/100000000000000 : ℝ)^4343
        have hw : |(5139223309/10000000000 : ℝ)|=(5139223309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-776241623/5000000000 : ℝ)|^5367 ≤ (400263373633/4000000000000 : ℝ)^4343
        have hw : |(-776241623/5000000000 : ℝ)|=(776241623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_3 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2047284761/5000000000 : ℝ)*x 0 + (3631238097/10000000000 : ℝ)*x 1 + (4592882147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047284761/5000000000 : ℝ)^5367 ≤ (829304559327/2500000000000 : ℝ)^4343 := by
    have hnat : (2047284761 : ℕ)^5367*2500000000000^4343 ≤ 829304559327^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047284761 5000000000 829304559327 2500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3631238097/10000000000 : ℝ)^5367 ≤ (28597210606029/100000000000000 : ℝ)^4343 := by
    have hnat : (3631238097 : ℕ)^5367*100000000000000^4343 ≤ 28597210606029^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3631238097 10000000000 28597210606029 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4592882147/10000000000 : ℝ)^5367 ≤ (152922428021/400000000000 : ℝ)^4343 := by
    have hnat : (4592882147 : ℕ)^5367*400000000000^4343 ≤ 152922428021^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592882147 10000000000 152922428021 400000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2047284761/5000000000 : ℝ), (3631238097/10000000000 : ℝ), (4592882147/10000000000 : ℝ)] ![(829304559327/2500000000000 : ℝ), (28597210606029/100000000000000 : ℝ), (152922428021/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2047284761/5000000000 : ℝ)|^5367 ≤ (829304559327/2500000000000 : ℝ)^4343
        have hw : |(2047284761/5000000000 : ℝ)|=(2047284761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3631238097/10000000000 : ℝ)|^5367 ≤ (28597210606029/100000000000000 : ℝ)^4343
        have hw : |(3631238097/10000000000 : ℝ)|=(3631238097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4592882147/10000000000 : ℝ)|^5367 ≤ (152922428021/400000000000 : ℝ)^4343
        have hw : |(4592882147/10000000000 : ℝ)|=(4592882147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_4 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-276767819/2000000000 : ℝ)*x 0 + (321428349/625000000 : ℝ)*x 1 + (136531869/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276767819/2000000000 : ℝ)^5367 ≤ (542561907741/6250000000000 : ℝ)^4343 := by
    have hnat : (276767819 : ℕ)^5367*6250000000000^4343 ≤ 542561907741^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276767819 2000000000 542561907741 6250000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321428349/625000000 : ℝ)^5367 ≤ (879308713297/2000000000000 : ℝ)^4343 := by
    have hnat : (321428349 : ℕ)^5367*2000000000000^4343 ≤ 879308713297^4343*625000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321428349 625000000 879308713297 2000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136531869/250000000 : ℝ)^5367 ≤ (47353573805099/100000000000000 : ℝ)^4343 := by
    have hnat : (136531869 : ℕ)^5367*100000000000000^4343 ≤ 47353573805099^4343*250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136531869 250000000 47353573805099 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276767819/2000000000 : ℝ), (321428349/625000000 : ℝ), (136531869/250000000 : ℝ)] ![(542561907741/6250000000000 : ℝ), (879308713297/2000000000000 : ℝ), (47353573805099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276767819/2000000000 : ℝ)|^5367 ≤ (542561907741/6250000000000 : ℝ)^4343
        have hw : |(-276767819/2000000000 : ℝ)|=(276767819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321428349/625000000 : ℝ)|^5367 ≤ (879308713297/2000000000000 : ℝ)^4343
        have hw : |(321428349/625000000 : ℝ)|=(321428349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136531869/250000000 : ℝ)|^5367 ≤ (47353573805099/100000000000000 : ℝ)^4343
        have hw : |(136531869/250000000 : ℝ)|=(136531869/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_5 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050725967/2000000000 : ℝ)*x 0 + (-615216497/5000000000 : ℝ)*x 1 + (5461272981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050725967/2000000000 : ℝ)^5367 ≤ (9027737422469/20000000000000 : ℝ)^4343 := by
    have hnat : (1050725967 : ℕ)^5367*20000000000000^4343 ≤ 9027737422469^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050725967 2000000000 9027737422469 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615216497/5000000000 : ℝ)^5367 ≤ (469234883111/6250000000000 : ℝ)^4343 := by
    have hnat : (615216497 : ℕ)^5367*6250000000000^4343 ≤ 469234883111^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615216497 5000000000 469234883111 6250000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461272981/10000000000 : ℝ)^5367 ≤ (189414218971/400000000000 : ℝ)^4343 := by
    have hnat : (5461272981 : ℕ)^5367*400000000000^4343 ≤ 189414218971^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461272981 10000000000 189414218971 400000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050725967/2000000000 : ℝ), (-615216497/5000000000 : ℝ), (5461272981/10000000000 : ℝ)] ![(9027737422469/20000000000000 : ℝ), (469234883111/6250000000000 : ℝ), (189414218971/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050725967/2000000000 : ℝ)|^5367 ≤ (9027737422469/20000000000000 : ℝ)^4343
        have hw : |(1050725967/2000000000 : ℝ)|=(1050725967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-615216497/5000000000 : ℝ)|^5367 ≤ (469234883111/6250000000000 : ℝ)^4343
        have hw : |(-615216497/5000000000 : ℝ)|=(615216497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461272981/10000000000 : ℝ)|^5367 ≤ (189414218971/400000000000 : ℝ)^4343
        have hw : |(5461272981/10000000000 : ℝ)|=(5461272981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_6 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253631823/10000000000 : ℝ)*x 0 + (5461269849/10000000000 : ℝ)*x 1 + (-615217323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253631823/10000000000 : ℝ)^5367 ≤ (45138708220371/100000000000000 : ℝ)^4343 := by
    have hnat : (5253631823 : ℕ)^5367*100000000000000^4343 ≤ 45138708220371^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253631823 10000000000 45138708220371 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461269849/10000000000 : ℝ)^5367 ≤ (47353521182731/100000000000000 : ℝ)^4343 := by
    have hnat : (5461269849 : ℕ)^5367*100000000000000^4343 ≤ 47353521182731^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461269849 10000000000 47353521182731 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615217323/5000000000 : ℝ)^5367 ≤ (750777058651/10000000000000 : ℝ)^4343 := by
    have hnat : (615217323 : ℕ)^5367*10000000000000^4343 ≤ 750777058651^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615217323 5000000000 750777058651 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253631823/10000000000 : ℝ), (5461269849/10000000000 : ℝ), (-615217323/5000000000 : ℝ)] ![(45138708220371/100000000000000 : ℝ), (47353521182731/100000000000000 : ℝ), (750777058651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253631823/10000000000 : ℝ)|^5367 ≤ (45138708220371/100000000000000 : ℝ)^4343
        have hw : |(5253631823/10000000000 : ℝ)|=(5253631823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461269849/10000000000 : ℝ)|^5367 ≤ (47353521182731/100000000000000 : ℝ)^4343
        have hw : |(5461269849/10000000000 : ℝ)|=(5461269849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-615217323/5000000000 : ℝ)|^5367 ≤ (750777058651/10000000000000 : ℝ)^4343
        have hw : |(-615217323/5000000000 : ℝ)|=(615217323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_7 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4094998943/10000000000 : ℝ)*x 0 + (4582165213/10000000000 : ℝ)*x 1 + (3642116709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4094998943/10000000000 : ℝ)^5367 ≤ (1658824082891/5000000000000 : ℝ)^4343 := by
    have hnat : (4094998943 : ℕ)^5367*5000000000000^4343 ≤ 1658824082891^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4094998943 10000000000 1658824082891 5000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582165213/10000000000 : ℝ)^5367 ≤ (9530099399981/25000000000000 : ℝ)^4343 := by
    have hnat : (4582165213 : ℕ)^5367*25000000000000^4343 ≤ 9530099399981^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582165213 10000000000 9530099399981 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3642116709/10000000000 : ℝ)^5367 ≤ (28703120721631/100000000000000 : ℝ)^4343 := by
    have hnat : (3642116709 : ℕ)^5367*100000000000000^4343 ≤ 28703120721631^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642116709 10000000000 28703120721631 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4094998943/10000000000 : ℝ), (4582165213/10000000000 : ℝ), (3642116709/10000000000 : ℝ)] ![(1658824082891/5000000000000 : ℝ), (9530099399981/25000000000000 : ℝ), (28703120721631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4094998943/10000000000 : ℝ)|^5367 ≤ (1658824082891/5000000000000 : ℝ)^4343
        have hw : |(4094998943/10000000000 : ℝ)|=(4094998943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582165213/10000000000 : ℝ)|^5367 ≤ (9530099399981/25000000000000 : ℝ)^4343
        have hw : |(4582165213/10000000000 : ℝ)|=(4582165213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3642116709/10000000000 : ℝ)|^5367 ≤ (28703120721631/100000000000000 : ℝ)^4343
        have hw : |(3642116709/10000000000 : ℝ)|=(3642116709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_8 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-603522401/10000000000 : ℝ)*x 0 + (5555653637/10000000000 : ℝ)*x 1 + (2784935237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603522401/10000000000 : ℝ)^5367 ≤ (778293130629/25000000000000 : ℝ)^4343 := by
    have hnat : (603522401 : ℕ)^5367*25000000000000^4343 ≤ 778293130629^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603522401 10000000000 778293130629 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5555653637/10000000000 : ℝ)^5367 ≤ (48366914182833/100000000000000 : ℝ)^4343 := by
    have hnat : (5555653637 : ℕ)^5367*100000000000000^4343 ≤ 48366914182833^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5555653637 10000000000 48366914182833 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2784935237/5000000000 : ℝ)^5367 ≤ (24259956642357/50000000000000 : ℝ)^4343 := by
    have hnat : (2784935237 : ℕ)^5367*50000000000000^4343 ≤ 24259956642357^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784935237 5000000000 24259956642357 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-603522401/10000000000 : ℝ), (5555653637/10000000000 : ℝ), (2784935237/5000000000 : ℝ)] ![(778293130629/25000000000000 : ℝ), (48366914182833/100000000000000 : ℝ), (24259956642357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-603522401/10000000000 : ℝ)|^5367 ≤ (778293130629/25000000000000 : ℝ)^4343
        have hw : |(-603522401/10000000000 : ℝ)|=(603522401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5555653637/10000000000 : ℝ)|^5367 ≤ (48366914182833/100000000000000 : ℝ)^4343
        have hw : |(5555653637/10000000000 : ℝ)|=(5555653637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2784935237/5000000000 : ℝ)|^5367 ≤ (24259956642357/50000000000000 : ℝ)^4343
        have hw : |(2784935237/5000000000 : ℝ)|=(2784935237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_9 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3394991243/10000000000 : ℝ)*x 0 + (-212592569/1000000000 : ℝ)*x 1 + (1303671109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3394991243/10000000000 : ℝ)^5367 ≤ (26315946293387/100000000000000 : ℝ)^4343 := by
    have hnat : (3394991243 : ℕ)^5367*100000000000000^4343 ≤ 26315946293387^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394991243 10000000000 26315946293387 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212592569/1000000000 : ℝ)^5367 ≤ (14756936594903/100000000000000 : ℝ)^4343 := by
    have hnat : (212592569 : ℕ)^5367*100000000000000^4343 ≤ 14756936594903^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212592569 1000000000 14756936594903 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303671109/2000000000 : ℝ)^5367 ≤ (58927117099023/100000000000000 : ℝ)^4343 := by
    have hnat : (1303671109 : ℕ)^5367*100000000000000^4343 ≤ 58927117099023^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303671109 2000000000 58927117099023 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3394991243/10000000000 : ℝ), (-212592569/1000000000 : ℝ), (1303671109/2000000000 : ℝ)] ![(26315946293387/100000000000000 : ℝ), (14756936594903/100000000000000 : ℝ), (58927117099023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3394991243/10000000000 : ℝ)|^5367 ≤ (26315946293387/100000000000000 : ℝ)^4343
        have hw : |(3394991243/10000000000 : ℝ)|=(3394991243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212592569/1000000000 : ℝ)|^5367 ≤ (14756936594903/100000000000000 : ℝ)^4343
        have hw : |(-212592569/1000000000 : ℝ)|=(212592569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303671109/2000000000 : ℝ)|^5367 ≤ (58927117099023/100000000000000 : ℝ)^4343
        have hw : |(1303671109/2000000000 : ℝ)|=(1303671109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_10 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1590597179/5000000000 : ℝ)*x 0 + (7304036693/10000000000 : ℝ)*x 1 + (-64050629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590597179/5000000000 : ℝ)^5367 ≤ (12141716037527/50000000000000 : ℝ)^4343 := by
    have hnat : (1590597179 : ℕ)^5367*50000000000000^4343 ≤ 12141716037527^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590597179 5000000000 12141716037527 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7304036693/10000000000 : ℝ)^5367 ≤ (33912795242989/50000000000000 : ℝ)^4343 := by
    have hnat : (7304036693 : ℕ)^5367*50000000000000^4343 ≤ 33912795242989^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7304036693 10000000000 33912795242989 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64050629/500000000 : ℝ)^5367 ≤ (7890977428709/100000000000000 : ℝ)^4343 := by
    have hnat : (64050629 : ℕ)^5367*100000000000000^4343 ≤ 7890977428709^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64050629 500000000 7890977428709 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1590597179/5000000000 : ℝ), (7304036693/10000000000 : ℝ), (-64050629/500000000 : ℝ)] ![(12141716037527/50000000000000 : ℝ), (33912795242989/50000000000000 : ℝ), (7890977428709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1590597179/5000000000 : ℝ)|^5367 ≤ (12141716037527/50000000000000 : ℝ)^4343
        have hw : |(1590597179/5000000000 : ℝ)|=(1590597179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7304036693/10000000000 : ℝ)|^5367 ≤ (33912795242989/50000000000000 : ℝ)^4343
        have hw : |(7304036693/10000000000 : ℝ)|=(7304036693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64050629/500000000 : ℝ)|^5367 ≤ (7890977428709/100000000000000 : ℝ)^4343
        have hw : |(-64050629/500000000 : ℝ)|=(64050629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_s3_11 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (198960361/625000000 : ℝ)*x 0 + (4550002551/10000000000 : ℝ)*x 1 + (4561306721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198960361/625000000 : ℝ)^5367 ≤ (24303917265387/100000000000000 : ℝ)^4343 := by
    have hnat : (198960361 : ℕ)^5367*100000000000000^4343 ≤ 24303917265387^4343*625000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198960361 625000000 24303917265387 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4550002551/10000000000 : ℝ)^5367 ≤ (4723751580511/12500000000000 : ℝ)^4343 := by
    have hnat : (4550002551 : ℕ)^5367*12500000000000^4343 ≤ 4723751580511^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550002551 10000000000 4723751580511 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4561306721/10000000000 : ℝ)^5367 ≤ (1895303503653/5000000000000 : ℝ)^4343 := by
    have hnat : (4561306721 : ℕ)^5367*5000000000000^4343 ≤ 1895303503653^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561306721 10000000000 1895303503653 5000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(198960361/625000000 : ℝ), (4550002551/10000000000 : ℝ), (4561306721/10000000000 : ℝ)] ![(24303917265387/100000000000000 : ℝ), (4723751580511/12500000000000 : ℝ), (1895303503653/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(198960361/625000000 : ℝ)|^5367 ≤ (24303917265387/100000000000000 : ℝ)^4343
        have hw : |(198960361/625000000 : ℝ)|=(198960361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4550002551/10000000000 : ℝ)|^5367 ≤ (4723751580511/12500000000000 : ℝ)^4343
        have hw : |(4550002551/10000000000 : ℝ)|=(4550002551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4561306721/10000000000 : ℝ)|^5367 ≤ (1895303503653/5000000000000 : ℝ)^4343
        have hw : |(4561306721/10000000000 : ℝ)|=(4561306721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1718_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1259/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3407/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4261/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2013/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4261/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2013/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4261/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2013/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4261/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2013/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4261/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2013/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4261/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2013/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2013/20000 : ℝ) ^ (5359/1024 : ℝ) ≤ (302201902874871/50000000000000000000 : ℝ) := by
    have hpowers : (2013/20000 : ℝ)^5359 ≤ (302201902874871/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2013 : ℕ)^5359*50000000000000000000^1024 ≤ 302201902874871^1024*20000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2013 20000 302201902874871 50000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2013/20000 : ℝ)) (X := (302201902874871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4261/25000 : ℝ) ^ (5359/1024 : ℝ) ≤ (4758582758456843/50000000000000000000 : ℝ) := by
    have hpowers : (4261/25000 : ℝ)^5359 ≤ (4758582758456843/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4261 : ℕ)^5359*50000000000000000000^1024 ≤ 4758582758456843^1024*25000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4261 25000 4758582758456843 50000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4261/25000 : ℝ)) (X := (4758582758456843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000302201902874871/25000000000000000000 : ℝ) ≤ (5000011548917171/5000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (25000302201902874871/25000000000000000000 : ℝ)^1024 ≤ (5000011548917171/5000000000000000 : ℝ)^5359 := by
      have hnat : (25000302201902874871 : ℕ)^1024*5000000000000000^5359 ≤ 5000011548917171^5359*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000302201902874871 25000000000000000000 5000011548917171 5000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000011548917171/5000000000000000 : ℝ)) (X := (25000302201902874871/25000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002530392330665857/25000000000000000000 : ℝ) ≤ (10000193395460241/10000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (25002530392330665857/25000000000000000000 : ℝ)^1024 ≤ (10000193395460241/10000000000000000 : ℝ)^5359 := by
      have hnat : (25002530392330665857 : ℕ)^1024*10000000000000000^5359 ≤ 10000193395460241^5359*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002530392330665857 25000000000000000000 10000193395460241 10000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000193395460241/10000000000000000 : ℝ)) (X := (25002530392330665857/25000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004758582758456843/25000000000000000000 : ℝ) ≤ (500018184654307/500000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (25004758582758456843/25000000000000000000 : ℝ)^1024 ≤ (500018184654307/500000000000000 : ℝ)^5359 := by
      have hnat : (25004758582758456843 : ℕ)^1024*500000000000000^5359 ≤ 500018184654307^5359*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004758582758456843 25000000000000000000 500018184654307 500000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500018184654307/500000000000000 : ℝ)) (X := (25004758582758456843/25000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(302201902874871/50000000000000000000 : ℝ) ≤ ((17446683277144131487/17447500000000000000 : ℝ)+2*(170297625899/697900000000000 : ℝ)*(2013/20000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (17446683277144131487/17447500000000000000 : ℝ)+2*(170297625899/697900000000000 : ℝ)*(2013/20000 : ℝ)=(5000011548917171/5000000000000000 : ℝ) by norm_num, show 1+2*(302201902874871/50000000000000000000 : ℝ)=(25000302201902874871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4758582758456843/50000000000000000000 : ℝ)+(302201902874871/50000000000000000000 : ℝ) ≤ ((17446683277144131487/17447500000000000000 : ℝ)+(170297625899/697900000000000 : ℝ)*((4261/25000 : ℝ)+(2013/20000 : ℝ)))^(5359/1024 : ℝ) := by
    rw [show (17446683277144131487/17447500000000000000 : ℝ)+(170297625899/697900000000000 : ℝ)*((4261/25000 : ℝ)+(2013/20000 : ℝ))=(10000193395460241/10000000000000000 : ℝ) by norm_num, show 1+(4758582758456843/50000000000000000000 : ℝ)+(302201902874871/50000000000000000000 : ℝ)=(25002530392330665857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4758582758456843/50000000000000000000 : ℝ) ≤ ((17446683277144131487/17447500000000000000 : ℝ)+2*(170297625899/697900000000000 : ℝ)*(4261/25000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (17446683277144131487/17447500000000000000 : ℝ)+2*(170297625899/697900000000000 : ℝ)*(4261/25000 : ℝ)=(500018184654307/500000000000000 : ℝ) by norm_num, show 1+2*(4758582758456843/50000000000000000000 : ℝ)=(25004758582758456843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17446683277144131487/17447500000000000000 : ℝ)*(X 1 0+X 2 0)+(170297625899/697900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (4261/25000 : ℝ)) (c := (17446683277144131487/17447500000000000000 : ℝ)) (alpha := (170297625899/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17446683277144131487/17447500000000000000 : ℝ)*(X 0 1+X 2 1)+(170297625899/697900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (4261/25000 : ℝ)) (c := (17446683277144131487/17447500000000000000 : ℝ)) (alpha := (170297625899/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17446683277144131487/17447500000000000000 : ℝ)*(X 0 2+X 1 2)+(170297625899/697900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (4261/25000 : ℝ)) (c := (17446683277144131487/17447500000000000000 : ℝ)) (alpha := (170297625899/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86480593/625000000 : ℝ)*X 0 0+(5464961621/10000000000 : ℝ)*X 0 1+(1284805827/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267041363/500000000 : ℝ)*X 1 0+(-776241623/5000000000 : ℝ)*X 1 1+(5139223309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267041363/500000000 : ℝ)*X 2 0+(5139223309/10000000000 : ℝ)*X 2 1+(-776241623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2047284761/5000000000 : ℝ)*X 0 0+(3631238097/10000000000 : ℝ)*X 0 1+(4592882147/10000000000 : ℝ)*X 0 2+(2047284761/5000000000 : ℝ)*X 1 0+(3631238097/10000000000 : ℝ)*X 1 1+(4592882147/10000000000 : ℝ)*X 1 2+(2047284761/5000000000 : ℝ)*X 2 0+(3631238097/10000000000 : ℝ)*X 2 1+(4592882147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-276767819/2000000000 : ℝ)*X 0 0+(321428349/625000000 : ℝ)*X 0 1+(136531869/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050725967/2000000000 : ℝ)*X 1 0+(-615216497/5000000000 : ℝ)*X 1 1+(5461272981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253631823/10000000000 : ℝ)*X 2 0+(5461269849/10000000000 : ℝ)*X 2 1+(-615217323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4094998943/10000000000 : ℝ)*X 0 0+(4582165213/10000000000 : ℝ)*X 0 1+(3642116709/10000000000 : ℝ)*X 0 2+(4094998943/10000000000 : ℝ)*X 1 0+(4582165213/10000000000 : ℝ)*X 1 1+(3642116709/10000000000 : ℝ)*X 1 2+(4094998943/10000000000 : ℝ)*X 2 0+(4582165213/10000000000 : ℝ)*X 2 1+(3642116709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-603522401/10000000000 : ℝ)*X 0 0+(5555653637/10000000000 : ℝ)*X 0 1+(2784935237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((3394991243/10000000000 : ℝ)*X 1 0+(-212592569/1000000000 : ℝ)*X 1 1+(1303671109/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1590597179/5000000000 : ℝ)*X 2 0+(7304036693/10000000000 : ℝ)*X 2 1+(-64050629/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((198960361/625000000 : ℝ)*X 0 0+(4550002551/10000000000 : ℝ)*X 0 1+(4561306721/10000000000 : ℝ)*X 0 2+(198960361/625000000 : ℝ)*X 1 0+(4550002551/10000000000 : ℝ)*X 1 1+(4561306721/10000000000 : ℝ)*X 1 2+(198960361/625000000 : ℝ)*X 2 0+(4550002551/10000000000 : ℝ)*X 2 1+(4561306721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (492527059754569660436426817/54523437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (110005079/100000000000000 : ℝ)*(lower2) + (55200419/100000000000000 : ℝ)*(lower3) + (513730232860769/25000000000000 : ℝ)*(major0) + (513730232860769/25000000000000 : ℝ)*(major1) + (513730232860769/25000000000000 : ℝ)*(major2) + (3069948346531057/100000000000000 : ℝ)*(sp0) + (3069952795357529/100000000000000 : ℝ)*(sp1) + (1534976710315207/50000000000000 : ℝ)*(sp2) + (259971376340127/25000000000000 : ℝ)*(sp3) + (46103657/2000000000000 : ℝ)*(sp4) + (1657211833/50000000000000 : ℝ)*(sp8) + (292695011/25000000000000 : ℝ)*(sp9) + (545507159/100000000000000 : ℝ)*(sp10) + (2090277763/100000000000000 : ℝ)*(sp11) + (1039887595638271/100000000000000 : ℝ)*(f.failure) + (3069953966137573/100000000000000 : ℝ)*(f.sum) + (28338296772921/8723750000000000000000000000 : ℝ)*base65 + (285255593489113071/62312500000000000000000000000000 : ℝ)*base68 + (45823445743300571/62312500000000000000000000000000 : ℝ)*base70 + (1059317281407613071/62312500000000000000000000000000 : ℝ)*base72 + (79704896005799/34895000000000000000000000000 : ℝ)*base73 + (124200556955613071/62312500000000000000000000000000 : ℝ)*base76 + (265004091591761929/62312500000000000000000000000000 : ℝ)*base77 + (240025072975238071/62312500000000000000000000000000 : ℝ)*base80 + (3437136267501/34895000000000000000000000000 : ℝ)*base82 + (70772661/10000000000000000000000 : ℝ)*base90 + (70772661/10000000000000000000000 : ℝ)*base92 + (70772661/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262483811609218248077805639/218093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1090898701/100000000000000 : ℝ)*(upper1) + (280668627/100000000000000 : ℝ)*(lower5) + (1051084256442151/50000000000000 : ℝ)*(major0) + (1051084256442151/50000000000000 : ℝ)*(major1) + (1051084256442151/50000000000000 : ℝ)*(major2) + (11802355481/100000000000000 : ℝ)*(sp1) + (1111832759/25000000000000 : ℝ)*(sp3) + (314052324351221/10000000000000 : ℝ)*(sp4) + (78513194953689/2500000000000 : ℝ)*(sp5) + (49070892379153/1562500000000 : ℝ)*(sp6) + (265948167168769/25000000000000 : ℝ)*(sp7) + (16626132391/100000000000000 : ℝ)*(sp8) + (6728539/2500000000000 : ℝ)*(sp9) + (275737881/10000000000000 : ℝ)*(sp10) + (33243659875191/3125000000000 : ℝ)*(f.failure) + (3140539869644601/100000000000000 : ℝ)*(f.sum) + (70787307112007/34895000000000000000000000000 : ℝ)*base66 + (1303847630487529791/124625000000000000000000000000000 : ℝ)*base67 + (582122356008654791/124625000000000000000000000000000 : ℝ)*base69 + (67888313917404791/124625000000000000000000000000000 : ℝ)*base71 + (40017072828867/8723750000000000000000000000 : ℝ)*base73 + (247704845479279791/124625000000000000000000000000000 : ℝ)*base75 + (277852892813404791/124625000000000000000000000000000 : ℝ)*base77 + (118804574375845209/124625000000000000000000000000000 : ℝ)*base80 + (6593257664691/17447500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1117619/312500000000000000000 : ℝ)*base89 + (1117619/312500000000000000000 : ℝ)*base91 + (1117619/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1718_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1718_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1718_box_0 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071141861/10000000000 : ℝ)*x 0 + (1082606613/2000000000 : ℝ)*x 1 + (5413032991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071141861/10000000000 : ℝ)^5367 ≤ (6325613455013/100000000000000 : ℝ)^4343 := by
    have hnat : (1071141861 : ℕ)^5367*100000000000000^4343 ≤ 6325613455013^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071141861 10000000000 6325613455013 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082606613/2000000000 : ℝ)^5367 ≤ (5854649207461/12500000000000 : ℝ)^4343 := by
    have hnat : (1082606613 : ℕ)^5367*12500000000000^4343 ≤ 5854649207461^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082606613 2000000000 5854649207461 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413032991/10000000000 : ℝ)^5367 ≤ (2341859643421/5000000000000 : ℝ)^4343 := by
    have hnat : (5413032991 : ℕ)^5367*5000000000000^4343 ≤ 2341859643421^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413032991 10000000000 2341859643421 5000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071141861/10000000000 : ℝ), (1082606613/2000000000 : ℝ), (5413032991/10000000000 : ℝ)] ![(6325613455013/100000000000000 : ℝ), (5854649207461/12500000000000 : ℝ), (2341859643421/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071141861/10000000000 : ℝ)|^5367 ≤ (6325613455013/100000000000000 : ℝ)^4343
        have hw : |(-1071141861/10000000000 : ℝ)|=(1071141861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082606613/2000000000 : ℝ)|^5367 ≤ (5854649207461/12500000000000 : ℝ)^4343
        have hw : |(1082606613/2000000000 : ℝ)|=(1082606613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413032991/10000000000 : ℝ)|^5367 ≤ (2341859643421/5000000000000 : ℝ)^4343
        have hw : |(5413032991/10000000000 : ℝ)|=(5413032991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_1 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130624349/250000000 : ℝ)*x 0 + (-1338149409/10000000000 : ℝ)*x 1 + (541303291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130624349/250000000 : ℝ)^5367 ≤ (44834623011703/100000000000000 : ℝ)^4343 := by
    have hnat : (130624349 : ℕ)^5367*100000000000000^4343 ≤ 44834623011703^4343*250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130624349 250000000 44834623011703 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338149409/10000000000 : ℝ)^5367 ≤ (8328184970257/100000000000000 : ℝ)^4343 := by
    have hnat : (1338149409 : ℕ)^5367*100000000000000^4343 ≤ 8328184970257^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338149409 10000000000 8328184970257 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541303291/1000000000 : ℝ)^5367 ≤ (46837192002303/100000000000000 : ℝ)^4343 := by
    have hnat : (541303291 : ℕ)^5367*100000000000000^4343 ≤ 46837192002303^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541303291 1000000000 46837192002303 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130624349/250000000 : ℝ), (-1338149409/10000000000 : ℝ), (541303291/1000000000 : ℝ)] ![(44834623011703/100000000000000 : ℝ), (8328184970257/100000000000000 : ℝ), (46837192002303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130624349/250000000 : ℝ)|^5367 ≤ (44834623011703/100000000000000 : ℝ)^4343
        have hw : |(130624349/250000000 : ℝ)|=(130624349/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338149409/10000000000 : ℝ)|^5367 ≤ (8328184970257/100000000000000 : ℝ)^4343
        have hw : |(-1338149409/10000000000 : ℝ)|=(1338149409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541303291/1000000000 : ℝ)|^5367 ≤ (46837192002303/100000000000000 : ℝ)^4343
        have hw : |(541303291/1000000000 : ℝ)|=(541303291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_2 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224973671/10000000000 : ℝ)*x 0 + (541303317/1000000000 : ℝ)*x 1 + (-669074723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224973671/10000000000 : ℝ)^5367 ≤ (44834619947137/100000000000000 : ℝ)^4343 := by
    have hnat : (5224973671 : ℕ)^5367*100000000000000^4343 ≤ 44834619947137^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224973671 10000000000 44834619947137 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541303317/1000000000 : ℝ)^5367 ≤ (23418597391217/50000000000000 : ℝ)^4343 := by
    have hnat : (541303317 : ℕ)^5367*50000000000000^4343 ≤ 23418597391217^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541303317 1000000000 23418597391217 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (669074723/5000000000 : ℝ)^5367 ≤ (8328185254827/100000000000000 : ℝ)^4343 := by
    have hnat : (669074723 : ℕ)^5367*100000000000000^4343 ≤ 8328185254827^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669074723 5000000000 8328185254827 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224973671/10000000000 : ℝ), (541303317/1000000000 : ℝ), (-669074723/5000000000 : ℝ)] ![(44834619947137/100000000000000 : ℝ), (23418597391217/50000000000000 : ℝ), (8328185254827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224973671/10000000000 : ℝ)|^5367 ≤ (44834619947137/100000000000000 : ℝ)^4343
        have hw : |(5224973671/10000000000 : ℝ)|=(5224973671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541303317/1000000000 : ℝ)|^5367 ≤ (23418597391217/50000000000000 : ℝ)^4343
        have hw : |(541303317/1000000000 : ℝ)|=(541303317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-669074723/5000000000 : ℝ)|^5367 ≤ (8328185254827/100000000000000 : ℝ)^4343
        have hw : |(-669074723/5000000000 : ℝ)|=(669074723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_3 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34965727/78125000 : ℝ)*x 0 + (196265801/500000000 : ℝ)*x 1 + (3925315819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34965727/78125000 : ℝ)^5367 ≤ (18513986669583/50000000000000 : ℝ)^4343 := by
    have hnat : (34965727 : ℕ)^5367*50000000000000^4343 ≤ 18513986669583^4343*78125000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34965727 78125000 18513986669583 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196265801/500000000 : ℝ)^5367 ≤ (31486014319811/100000000000000 : ℝ)^4343 := by
    have hnat : (196265801 : ℕ)^5367*100000000000000^4343 ≤ 31486014319811^4343*500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196265801 500000000 31486014319811 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3925315819/10000000000 : ℝ)^5367 ≤ (31486012327391/100000000000000 : ℝ)^4343 := by
    have hnat : (3925315819 : ℕ)^5367*100000000000000^4343 ≤ 31486012327391^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3925315819 10000000000 31486012327391 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34965727/78125000 : ℝ), (196265801/500000000 : ℝ), (3925315819/10000000000 : ℝ)] ![(18513986669583/50000000000000 : ℝ), (31486014319811/100000000000000 : ℝ), (31486012327391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34965727/78125000 : ℝ)|^5367 ≤ (18513986669583/50000000000000 : ℝ)^4343
        have hw : |(34965727/78125000 : ℝ)|=(34965727/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196265801/500000000 : ℝ)|^5367 ≤ (31486014319811/100000000000000 : ℝ)^4343
        have hw : |(196265801/500000000 : ℝ)|=(196265801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3925315819/10000000000 : ℝ)|^5367 ≤ (31486012327391/100000000000000 : ℝ)^4343
        have hw : |(3925315819/10000000000 : ℝ)|=(3925315819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_4 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214593319/1250000000 : ℝ)*x 0 + (5177765439/10000000000 : ℝ)*x 1 + (5177765447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214593319/1250000000 : ℝ)^5367 ≤ (11330886603789/100000000000000 : ℝ)^4343 := by
    have hnat : (214593319 : ℕ)^5367*100000000000000^4343 ≤ 11330886603789^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214593319 1250000000 11330886603789 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177765439/10000000000 : ℝ)^5367 ≤ (11083639162629/25000000000000 : ℝ)^4343 := by
    have hnat : (5177765439 : ℕ)^5367*25000000000000^4343 ≤ 11083639162629^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177765439 10000000000 11083639162629 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177765447/10000000000 : ℝ)^5367 ≤ (44334556735167/100000000000000 : ℝ)^4343 := by
    have hnat : (5177765447 : ℕ)^5367*100000000000000^4343 ≤ 44334556735167^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177765447 10000000000 44334556735167 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214593319/1250000000 : ℝ), (5177765439/10000000000 : ℝ), (5177765447/10000000000 : ℝ)] ![(11330886603789/100000000000000 : ℝ), (11083639162629/25000000000000 : ℝ), (44334556735167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214593319/1250000000 : ℝ)|^5367 ≤ (11330886603789/100000000000000 : ℝ)^4343
        have hw : |(-214593319/1250000000 : ℝ)|=(214593319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177765439/10000000000 : ℝ)|^5367 ≤ (11083639162629/25000000000000 : ℝ)^4343
        have hw : |(5177765439/10000000000 : ℝ)|=(5177765439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177765447/10000000000 : ℝ)|^5367 ≤ (44334556735167/100000000000000 : ℝ)^4343
        have hw : |(5177765447/10000000000 : ℝ)|=(5177765447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_5 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538422439/1000000000 : ℝ)*x 0 + (-721129457/5000000000 : ℝ)*x 1 + (1294441327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538422439/1000000000 : ℝ)^5367 ≤ (2326467071907/5000000000000 : ℝ)^4343 := by
    have hnat : (538422439 : ℕ)^5367*5000000000000^4343 ≤ 2326467071907^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538422439 1000000000 2326467071907 5000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721129457/5000000000 : ℝ)^5367 ≤ (9136103281267/100000000000000 : ℝ)^4343 := by
    have hnat : (721129457 : ℕ)^5367*100000000000000^4343 ≤ 9136103281267^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721129457 5000000000 9136103281267 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294441327/2500000000 : ℝ)^5367 ≤ (44334555264357/100000000000000 : ℝ)^4343 := by
    have hnat : (1294441327 : ℕ)^5367*100000000000000^4343 ≤ 44334555264357^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294441327 2500000000 44334555264357 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538422439/1000000000 : ℝ), (-721129457/5000000000 : ℝ), (1294441327/2500000000 : ℝ)] ![(2326467071907/5000000000000 : ℝ), (9136103281267/100000000000000 : ℝ), (44334555264357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538422439/1000000000 : ℝ)|^5367 ≤ (2326467071907/5000000000000 : ℝ)^4343
        have hw : |(538422439/1000000000 : ℝ)|=(538422439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-721129457/5000000000 : ℝ)|^5367 ≤ (9136103281267/100000000000000 : ℝ)^4343
        have hw : |(-721129457/5000000000 : ℝ)|=(721129457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294441327/2500000000 : ℝ)|^5367 ≤ (44334555264357/100000000000000 : ℝ)^4343
        have hw : |(1294441327/2500000000 : ℝ)|=(1294441327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_6 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692112149/5000000000 : ℝ)*x 0 + (207110619/400000000 : ℝ)*x 1 + (-1442258813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692112149/5000000000 : ℝ)^5367 ≤ (23264670227819/50000000000000 : ℝ)^4343 := by
    have hnat : (2692112149 : ℕ)^5367*50000000000000^4343 ≤ 23264670227819^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692112149 5000000000 23264670227819 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207110619/400000000 : ℝ)^5367 ≤ (8866911406289/20000000000000 : ℝ)^4343 := by
    have hnat : (207110619 : ℕ)^5367*20000000000000^4343 ≤ 8866911406289^4343*400000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207110619 400000000 8866911406289 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1442258813/10000000000 : ℝ)^5367 ≤ (9136102490623/100000000000000 : ℝ)^4343 := by
    have hnat : (1442258813 : ℕ)^5367*100000000000000^4343 ≤ 9136102490623^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442258813 10000000000 9136102490623 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692112149/5000000000 : ℝ), (207110619/400000000 : ℝ), (-1442258813/10000000000 : ℝ)] ![(23264670227819/50000000000000 : ℝ), (8866911406289/20000000000000 : ℝ), (9136102490623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692112149/5000000000 : ℝ)|^5367 ≤ (23264670227819/50000000000000 : ℝ)^4343
        have hw : |(2692112149/5000000000 : ℝ)|=(2692112149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207110619/400000000 : ℝ)|^5367 ≤ (8866911406289/20000000000000 : ℝ)^4343
        have hw : |(207110619/400000000 : ℝ)|=(207110619/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1442258813/10000000000 : ℝ)|^5367 ≤ (9136102490623/100000000000000 : ℝ)^4343
        have hw : |(-1442258813/10000000000 : ℝ)|=(1442258813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_7 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (369746657/1000000000 : ℝ)*x 0 + (862714827/2000000000 : ℝ)*x 1 + (2156787037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (369746657/1000000000 : ℝ)^5367 ≤ (29243138380669/100000000000000 : ℝ)^4343 := by
    have hnat : (369746657 : ℕ)^5367*100000000000000^4343 ≤ 29243138380669^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369746657 1000000000 29243138380669 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862714827/2000000000 : ℝ)^5367 ≤ (35378431113897/100000000000000 : ℝ)^4343 := by
    have hnat : (862714827 : ℕ)^5367*100000000000000^4343 ≤ 35378431113897^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862714827 2000000000 35378431113897 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156787037/5000000000 : ℝ)^5367 ≤ (7075686099127/20000000000000 : ℝ)^4343 := by
    have hnat : (2156787037 : ℕ)^5367*20000000000000^4343 ≤ 7075686099127^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156787037 5000000000 7075686099127 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(369746657/1000000000 : ℝ), (862714827/2000000000 : ℝ), (2156787037/5000000000 : ℝ)] ![(29243138380669/100000000000000 : ℝ), (35378431113897/100000000000000 : ℝ), (7075686099127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(369746657/1000000000 : ℝ)|^5367 ≤ (29243138380669/100000000000000 : ℝ)^4343
        have hw : |(369746657/1000000000 : ℝ)|=(369746657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862714827/2000000000 : ℝ)|^5367 ≤ (35378431113897/100000000000000 : ℝ)^4343
        have hw : |(862714827/2000000000 : ℝ)|=(862714827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156787037/5000000000 : ℝ)|^5367 ≤ (7075686099127/20000000000000 : ℝ)^4343
        have hw : |(2156787037/5000000000 : ℝ)|=(2156787037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_8 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7888913/50000000 : ℝ)*x 0 + (625466099/1250000000 : ℝ)*x 1 + (2727723781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7888913/50000000 : ℝ)^5367 ≤ (1276060771083/12500000000000 : ℝ)^4343 := by
    have hnat : (7888913 : ℕ)^5367*12500000000000^4343 ≤ 1276060771083^4343*50000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7888913 50000000 1276060771083 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625466099/1250000000 : ℝ)^5367 ≤ (10625092945417/25000000000000 : ℝ)^4343 := by
    have hnat : (625466099 : ℕ)^5367*25000000000000^4343 ≤ 10625092945417^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625466099 1250000000 10625092945417 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727723781/5000000000 : ℝ)^5367 ≤ (47291142038059/100000000000000 : ℝ)^4343 := by
    have hnat : (2727723781 : ℕ)^5367*100000000000000^4343 ≤ 47291142038059^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727723781 5000000000 47291142038059 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7888913/50000000 : ℝ), (625466099/1250000000 : ℝ), (2727723781/5000000000 : ℝ)] ![(1276060771083/12500000000000 : ℝ), (10625092945417/25000000000000 : ℝ), (47291142038059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7888913/50000000 : ℝ)|^5367 ≤ (1276060771083/12500000000000 : ℝ)^4343
        have hw : |(-7888913/50000000 : ℝ)|=(7888913/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625466099/1250000000 : ℝ)|^5367 ≤ (10625092945417/25000000000000 : ℝ)^4343
        have hw : |(625466099/1250000000 : ℝ)|=(625466099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727723781/5000000000 : ℝ)|^5367 ≤ (47291142038059/100000000000000 : ℝ)^4343
        have hw : |(2727723781/5000000000 : ℝ)|=(2727723781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_9 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196286073/10000000000 : ℝ)*x 0 + (-329655147/2500000000 : ℝ)*x 1 + (5455447427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196286073/10000000000 : ℝ)^5367 ≤ (11132653208643/25000000000000 : ℝ)^4343 := by
    have hnat : (5196286073 : ℕ)^5367*25000000000000^4343 ≤ 11132653208643^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196286073 10000000000 11132653208643 25000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329655147/2500000000 : ℝ)^5367 ≤ (1022280819911/12500000000000 : ℝ)^4343 := by
    have hnat : (329655147 : ℕ)^5367*12500000000000^4343 ≤ 1022280819911^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329655147 2500000000 1022280819911 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455447427/10000000000 : ℝ)^5367 ≤ (4729114059187/10000000000000 : ℝ)^4343 := by
    have hnat : (5455447427 : ℕ)^5367*10000000000000^4343 ≤ 4729114059187^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455447427 10000000000 4729114059187 10000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196286073/10000000000 : ℝ), (-329655147/2500000000 : ℝ), (5455447427/10000000000 : ℝ)] ![(11132653208643/25000000000000 : ℝ), (1022280819911/12500000000000 : ℝ), (4729114059187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196286073/10000000000 : ℝ)|^5367 ≤ (11132653208643/25000000000000 : ℝ)^4343
        have hw : |(5196286073/10000000000 : ℝ)|=(5196286073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329655147/2500000000 : ℝ)|^5367 ≤ (1022280819911/12500000000000 : ℝ)^4343
        have hw : |(-329655147/2500000000 : ℝ)|=(329655147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455447427/10000000000 : ℝ)|^5367 ≤ (4729114059187/10000000000000 : ℝ)^4343
        have hw : |(5455447427/10000000000 : ℝ)|=(5455447427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_10 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8314057/16000000 : ℝ)*x 0 + (2727723791/5000000000 : ℝ)*x 1 + (-131862099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8314057/16000000 : ℝ)^5367 ≤ (44530608090127/100000000000000 : ℝ)^4343 := by
    have hnat : (8314057 : ℕ)^5367*100000000000000^4343 ≤ 44530608090127^4343*16000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8314057 16000000 44530608090127 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727723791/5000000000 : ℝ)^5367 ≤ (47291142252309/100000000000000 : ℝ)^4343 := by
    have hnat : (2727723791 : ℕ)^5367*100000000000000^4343 ≤ 47291142252309^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727723791 5000000000 47291142252309 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131862099/1000000000 : ℝ)^5367 ≤ (1635649928081/20000000000000 : ℝ)^4343 := by
    have hnat : (131862099 : ℕ)^5367*20000000000000^4343 ≤ 1635649928081^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131862099 1000000000 1635649928081 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8314057/16000000 : ℝ), (2727723791/5000000000 : ℝ), (-131862099/1000000000 : ℝ)] ![(44530608090127/100000000000000 : ℝ), (47291142252309/100000000000000 : ℝ), (1635649928081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8314057/16000000 : ℝ)|^5367 ≤ (44530608090127/100000000000000 : ℝ)^4343
        have hw : |(8314057/16000000 : ℝ)|=(8314057/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727723791/5000000000 : ℝ)|^5367 ≤ (47291142252309/100000000000000 : ℝ)^4343
        have hw : |(2727723791/5000000000 : ℝ)|=(2727723791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131862099/1000000000 : ℝ)|^5367 ≤ (1635649928081/20000000000000 : ℝ)^4343
        have hw : |(-131862099/1000000000 : ℝ)|=(131862099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_11 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2305465443/5000000000 : ℝ)*x 0 + (1927567919/5000000000 : ℝ)*x 1 + (3855135973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2305465443/5000000000 : ℝ)^5367 ≤ (19208175648103/50000000000000 : ℝ)^4343 := by
    have hnat : (2305465443 : ℕ)^5367*50000000000000^4343 ≤ 19208175648103^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305465443 5000000000 19208175648103 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927567919/5000000000 : ℝ)^5367 ≤ (1231672947129/4000000000000 : ℝ)^4343 := by
    have hnat : (1927567919 : ℕ)^5367*4000000000000^4343 ≤ 1231672947129^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927567919 5000000000 1231672947129 4000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3855135973/10000000000 : ℝ)^5367 ≤ (30791825010737/100000000000000 : ℝ)^4343 := by
    have hnat : (3855135973 : ℕ)^5367*100000000000000^4343 ≤ 30791825010737^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855135973 10000000000 30791825010737 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2305465443/5000000000 : ℝ), (1927567919/5000000000 : ℝ), (3855135973/10000000000 : ℝ)] ![(19208175648103/50000000000000 : ℝ), (1231672947129/4000000000000 : ℝ), (30791825010737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2305465443/5000000000 : ℝ)|^5367 ≤ (19208175648103/50000000000000 : ℝ)^4343
        have hw : |(2305465443/5000000000 : ℝ)|=(2305465443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1927567919/5000000000 : ℝ)|^5367 ≤ (1231672947129/4000000000000 : ℝ)^4343
        have hw : |(1927567919/5000000000 : ℝ)|=(1927567919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3855135973/10000000000 : ℝ)|^5367 ≤ (30791825010737/100000000000000 : ℝ)^4343
        have hw : |(3855135973/10000000000 : ℝ)|=(3855135973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_12 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-602214817/5000000000 : ℝ)*x 0 + (1115796227/2000000000 : ℝ)*x 1 + (1030546351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602214817/5000000000 : ℝ)^5367 ≤ (1462434740499/20000000000000 : ℝ)^4343 := by
    have hnat : (602214817 : ℕ)^5367*20000000000000^4343 ≤ 1462434740499^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602214817 5000000000 1462434740499 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115796227/2000000000 : ℝ)^5367 ≤ (9723601810799/20000000000000 : ℝ)^4343 := by
    have hnat : (1115796227 : ℕ)^5367*20000000000000^4343 ≤ 9723601810799^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115796227 2000000000 9723601810799 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030546351/2000000000 : ℝ)^5367 ≤ (44069817231051/100000000000000 : ℝ)^4343 := by
    have hnat : (1030546351 : ℕ)^5367*100000000000000^4343 ≤ 44069817231051^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030546351 2000000000 44069817231051 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-602214817/5000000000 : ℝ), (1115796227/2000000000 : ℝ), (1030546351/2000000000 : ℝ)] ![(1462434740499/20000000000000 : ℝ), (9723601810799/20000000000000 : ℝ), (44069817231051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-602214817/5000000000 : ℝ)|^5367 ≤ (1462434740499/20000000000000 : ℝ)^4343
        have hw : |(-602214817/5000000000 : ℝ)|=(602214817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115796227/2000000000 : ℝ)|^5367 ≤ (9723601810799/20000000000000 : ℝ)^4343
        have hw : |(1115796227/2000000000 : ℝ)|=(1115796227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030546351/2000000000 : ℝ)|^5367 ≤ (44069817231051/100000000000000 : ℝ)^4343
        have hw : |(1030546351/2000000000 : ℝ)|=(1030546351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_13 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700600709/5000000000 : ℝ)*x 0 + (-726449661/5000000000 : ℝ)*x 1 + (206109269/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700600709/5000000000 : ℝ)^5367 ≤ (5838839086901/12500000000000 : ℝ)^4343 := by
    have hnat : (2700600709 : ℕ)^5367*12500000000000^4343 ≤ 5838839086901^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700600709 5000000000 5838839086901 12500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (726449661/5000000000 : ℝ)^5367 ≤ (9219470377109/100000000000000 : ℝ)^4343 := by
    have hnat : (726449661 : ℕ)^5367*100000000000000^4343 ≤ 9219470377109^4343*5000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726449661 5000000000 9219470377109 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206109269/400000000 : ℝ)^5367 ≤ (44069816913973/100000000000000 : ℝ)^4343 := by
    have hnat : (206109269 : ℕ)^5367*100000000000000^4343 ≤ 44069816913973^4343*400000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206109269 400000000 44069816913973 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700600709/5000000000 : ℝ), (-726449661/5000000000 : ℝ), (206109269/400000000 : ℝ)] ![(5838839086901/12500000000000 : ℝ), (9219470377109/100000000000000 : ℝ), (44069816913973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700600709/5000000000 : ℝ)|^5367 ≤ (5838839086901/12500000000000 : ℝ)^4343
        have hw : |(2700600709/5000000000 : ℝ)|=(2700600709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-726449661/5000000000 : ℝ)|^5367 ≤ (9219470377109/100000000000000 : ℝ)^4343
        have hw : |(-726449661/5000000000 : ℝ)|=(726449661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206109269/400000000 : ℝ)|^5367 ≤ (44069816913973/100000000000000 : ℝ)^4343
        have hw : |(206109269/400000000 : ℝ)|=(206109269/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_14 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540120137/1000000000 : ℝ)*x 0 + (5152731777/10000000000 : ℝ)*x 1 + (-1452899317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540120137/1000000000 : ℝ)^5367 ≤ (23355356091109/50000000000000 : ℝ)^4343 := by
    have hnat : (540120137 : ℕ)^5367*50000000000000^4343 ≤ 23355356091109^4343*1000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540120137 1000000000 23355356091109 50000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152731777/10000000000 : ℝ)^5367 ≤ (1762792698543/4000000000000 : ℝ)^4343 := by
    have hnat : (5152731777 : ℕ)^5367*4000000000000^4343 ≤ 1762792698543^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152731777 10000000000 1762792698543 4000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452899317/10000000000 : ℝ)^5367 ≤ (92194703379/1000000000000 : ℝ)^4343 := by
    have hnat : (1452899317 : ℕ)^5367*1000000000000^4343 ≤ 92194703379^4343*10000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452899317 10000000000 92194703379 1000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540120137/1000000000 : ℝ), (5152731777/10000000000 : ℝ), (-1452899317/10000000000 : ℝ)] ![(23355356091109/50000000000000 : ℝ), (1762792698543/4000000000000 : ℝ), (92194703379/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540120137/1000000000 : ℝ)|^5367 ≤ (23355356091109/50000000000000 : ℝ)^4343
        have hw : |(540120137/1000000000 : ℝ)|=(540120137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152731777/10000000000 : ℝ)|^5367 ≤ (1762792698543/4000000000000 : ℝ)^4343
        have hw : |(5152731777/10000000000 : ℝ)|=(5152731777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1452899317/10000000000 : ℝ)|^5367 ≤ (92194703379/1000000000000 : ℝ)^4343
        have hw : |(-1452899317/10000000000 : ℝ)|=(1452899317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1718_box_15 (p : ℝ) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (451460543/1250000000 : ℝ)*x 0 + (1088693631/2500000000 : ℝ)*x 1 + (870954903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451460543/1250000000 : ℝ)^5367 ≤ (710175767049/2500000000000 : ℝ)^4343 := by
    have hnat : (451460543 : ℕ)^5367*2500000000000^4343 ≤ 710175767049^4343*1250000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451460543 1250000000 710175767049 2500000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088693631/2500000000 : ℝ)^5367 ≤ (35796484696279/100000000000000 : ℝ)^4343 := by
    have hnat : (1088693631 : ℕ)^5367*100000000000000^4343 ≤ 35796484696279^4343*2500000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088693631 2500000000 35796484696279 100000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870954903/2000000000 : ℝ)^5367 ≤ (7159296920971/20000000000000 : ℝ)^4343 := by
    have hnat : (870954903 : ℕ)^5367*20000000000000^4343 ≤ 7159296920971^4343*2000000000^5367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870954903 2000000000 7159296920971 20000000000000 5367 4343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5367/1024 : ℝ)) 5367 4343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(451460543/1250000000 : ℝ), (1088693631/2500000000 : ℝ), (870954903/2000000000 : ℝ)] ![(710175767049/2500000000000 : ℝ), (35796484696279/100000000000000 : ℝ), (7159296920971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(451460543/1250000000 : ℝ)|^5367 ≤ (710175767049/2500000000000 : ℝ)^4343
        have hw : |(451460543/1250000000 : ℝ)|=(451460543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088693631/2500000000 : ℝ)|^5367 ≤ (35796484696279/100000000000000 : ℝ)^4343
        have hw : |(1088693631/2500000000 : ℝ)|=(1088693631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(870954903/2000000000 : ℝ)|^5367 ≤ (7159296920971/20000000000000 : ℝ)^4343
        have hw : |(870954903/2000000000 : ℝ)|=(870954903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1718_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(66823/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5859/10000 : ℝ) ∧ (81737/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11317/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3407/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3407/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3407/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3407/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3407/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3407/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1259/12500 : ℝ) ^ (5359/1024 : ℝ) ≤ (6066069076951/1000000000000000000 : ℝ) := by
    have hpowers : (1259/12500 : ℝ)^5359 ≤ (6066069076951/1000000000000000000 : ℝ)^1024 := by
      have hnat : (1259 : ℕ)^5359*1000000000000000000^1024 ≤ 6066069076951^1024*12500^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 12500 6066069076951 1000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/12500 : ℝ)) (X := (6066069076951/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3407/20000 : ℝ) ^ (5359/1024 : ℝ) ≤ (9490894493269579/100000000000000000000 : ℝ) := by
    have hpowers : (3407/20000 : ℝ)^5359 ≤ (9490894493269579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3407 : ℕ)^5359*100000000000000000000^1024 ≤ 9490894493269579^1024*20000^5359 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3407 20000 9490894493269579 100000000000000000000 5359 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3407/20000 : ℝ)) (X := (9490894493269579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500006066069076951/500000000000000000 : ℝ) ≤ (1250002897753431/1250000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (500006066069076951/500000000000000000 : ℝ)^1024 ≤ (1250002897753431/1250000000000000 : ℝ)^5359 := by
      have hnat : (500006066069076951 : ℕ)^1024*1250000000000000^5359 ≤ 1250002897753431^5359*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500006066069076951 500000000000000000 1250002897753431 1250000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002897753431/1250000000000000 : ℝ)) (X := (500006066069076951/500000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010097501400964679/100000000000000000000 : ℝ) ≤ (5000096467803487/5000000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (100010097501400964679/100000000000000000000 : ℝ)^1024 ≤ (5000096467803487/5000000000000000 : ℝ)^5359 := by
      have hnat : (100010097501400964679 : ℕ)^1024*5000000000000000^5359 ≤ 5000096467803487^5359*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010097501400964679 100000000000000000000 5000096467803487 5000000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000096467803487/5000000000000000 : ℝ)) (X := (100010097501400964679/100000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009490894493269579/50000000000000000000 : ℝ) ≤ (20000725378373/20000000000000 : ℝ) ^ (5359/1024 : ℝ) := by
    have hpowers : (50009490894493269579/50000000000000000000 : ℝ)^1024 ≤ (20000725378373/20000000000000 : ℝ)^5359 := by
      have hnat : (50009490894493269579 : ℕ)^1024*20000000000000^5359 ≤ 20000725378373^5359*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009490894493269579 50000000000000000000 20000725378373 20000000000000 1024 5359 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20000725378373/20000000000000 : ℝ)) (X := (50009490894493269579/50000000000000000000 : ℝ)) (by norm_num) 5359 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6066069076951/1000000000000000000 : ℝ) ≤ ((1740668547508778717/1740750000000000000 : ℝ)+2*(84876789763/348150000000000 : ℝ)*(1259/12500 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (1740668547508778717/1740750000000000000 : ℝ)+2*(84876789763/348150000000000 : ℝ)*(1259/12500 : ℝ)=(1250002897753431/1250000000000000 : ℝ) by norm_num, show 1+2*(6066069076951/1000000000000000000 : ℝ)=(500006066069076951/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9490894493269579/100000000000000000000 : ℝ)+(6066069076951/1000000000000000000 : ℝ) ≤ ((1740668547508778717/1740750000000000000 : ℝ)+(84876789763/348150000000000 : ℝ)*((3407/20000 : ℝ)+(1259/12500 : ℝ)))^(5359/1024 : ℝ) := by
    rw [show (1740668547508778717/1740750000000000000 : ℝ)+(84876789763/348150000000000 : ℝ)*((3407/20000 : ℝ)+(1259/12500 : ℝ))=(5000096467803487/5000000000000000 : ℝ) by norm_num, show 1+(9490894493269579/100000000000000000000 : ℝ)+(6066069076951/1000000000000000000 : ℝ)=(100010097501400964679/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9490894493269579/100000000000000000000 : ℝ) ≤ ((1740668547508778717/1740750000000000000 : ℝ)+2*(84876789763/348150000000000 : ℝ)*(3407/20000 : ℝ))^(5359/1024 : ℝ) := by
    rw [show (1740668547508778717/1740750000000000000 : ℝ)+2*(84876789763/348150000000000 : ℝ)*(3407/20000 : ℝ)=(20000725378373/20000000000000 : ℝ) by norm_num, show 1+2*(9490894493269579/100000000000000000000 : ℝ)=(50009490894493269579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1740668547508778717/1740750000000000000 : ℝ)*(X 1 0+X 2 0)+(84876789763/348150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (1740668547508778717/1740750000000000000 : ℝ)) (alpha := (84876789763/348150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1740668547508778717/1740750000000000000 : ℝ)*(X 0 1+X 2 1)+(84876789763/348150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (1740668547508778717/1740750000000000000 : ℝ)) (alpha := (84876789763/348150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1740668547508778717/1740750000000000000 : ℝ)*(X 0 2+X 1 2)+(84876789763/348150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5359/1024 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3407/20000 : ℝ)) (c := (1740668547508778717/1740750000000000000 : ℝ)) (alpha := (84876789763/348150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071141861/10000000000 : ℝ)*X 0 0+(1082606613/2000000000 : ℝ)*X 0 1+(5413032991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((130624349/250000000 : ℝ)*X 1 0+(-1338149409/10000000000 : ℝ)*X 1 1+(541303291/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224973671/10000000000 : ℝ)*X 2 0+(541303317/1000000000 : ℝ)*X 2 1+(-669074723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34965727/78125000 : ℝ)*X 0 0+(196265801/500000000 : ℝ)*X 0 1+(3925315819/10000000000 : ℝ)*X 0 2+(34965727/78125000 : ℝ)*X 1 0+(196265801/500000000 : ℝ)*X 1 1+(3925315819/10000000000 : ℝ)*X 1 2+(34965727/78125000 : ℝ)*X 2 0+(196265801/500000000 : ℝ)*X 2 1+(3925315819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214593319/1250000000 : ℝ)*X 0 0+(5177765439/10000000000 : ℝ)*X 0 1+(5177765447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538422439/1000000000 : ℝ)*X 1 0+(-721129457/5000000000 : ℝ)*X 1 1+(1294441327/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2692112149/5000000000 : ℝ)*X 2 0+(207110619/400000000 : ℝ)*X 2 1+(-1442258813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((369746657/1000000000 : ℝ)*X 0 0+(862714827/2000000000 : ℝ)*X 0 1+(2156787037/5000000000 : ℝ)*X 0 2+(369746657/1000000000 : ℝ)*X 1 0+(862714827/2000000000 : ℝ)*X 1 1+(2156787037/5000000000 : ℝ)*X 1 2+(369746657/1000000000 : ℝ)*X 2 0+(862714827/2000000000 : ℝ)*X 2 1+(2156787037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-7888913/50000000 : ℝ)*X 0 0+(625466099/1250000000 : ℝ)*X 0 1+(2727723781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196286073/10000000000 : ℝ)*X 1 0+(-329655147/2500000000 : ℝ)*X 1 1+(5455447427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((8314057/16000000 : ℝ)*X 2 0+(2727723791/5000000000 : ℝ)*X 2 1+(-131862099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2305465443/5000000000 : ℝ)*X 0 0+(1927567919/5000000000 : ℝ)*X 0 1+(3855135973/10000000000 : ℝ)*X 0 2+(2305465443/5000000000 : ℝ)*X 1 0+(1927567919/5000000000 : ℝ)*X 1 1+(3855135973/10000000000 : ℝ)*X 1 2+(2305465443/5000000000 : ℝ)*X 2 0+(1927567919/5000000000 : ℝ)*X 2 1+(3855135973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-602214817/5000000000 : ℝ)*X 0 0+(1115796227/2000000000 : ℝ)*X 0 1+(1030546351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2700600709/5000000000 : ℝ)*X 1 0+(-726449661/5000000000 : ℝ)*X 1 1+(206109269/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540120137/1000000000 : ℝ)*X 2 0+(5152731777/10000000000 : ℝ)*X 2 1+(-1452899317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((451460543/1250000000 : ℝ)*X 0 0+(1088693631/2500000000 : ℝ)*X 0 1+(870954903/2000000000 : ℝ)*X 0 2+(451460543/1250000000 : ℝ)*X 1 0+(1088693631/2500000000 : ℝ)*X 1 1+(870954903/2000000000 : ℝ)*X 1 2+(451460543/1250000000 : ℝ)*X 2 0+(1088693631/2500000000 : ℝ)*X 2 1+(870954903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1718_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66823/100000 : ℝ) ≤ (-2423285508233775360247073030421/3626562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3446159/25000000000000 : ℝ)*(upper1) + (15062943/100000000000000 : ℝ)*(upper3) + (33092109/100000000000000 : ℝ)*(upper5) + (172107182802521/12500000000000 : ℝ)*(major0) + (172107182802521/12500000000000 : ℝ)*(major1) + (172107182802521/12500000000000 : ℝ)*(major2) + (1901696663/100000000000000 : ℝ)*(sp1) + (175127353/25000000000000 : ℝ)*(sp2) + (380130723/100000000000000 : ℝ)*(sp3) + (2079232611197817/100000000000000 : ℝ)*(sp4) + (3326769974211/160000000000 : ℝ)*(sp5) + (1039616217534563/50000000000000 : ℝ)*(sp6) + (10886795212881/1562500000000 : ℝ)*(sp7) + (6554759/1250000000000 : ℝ)*(sp8) + (696755273755107/100000000000000 : ℝ)*(f.failure) + (1039616567789269/50000000000000 : ℝ)*(f.sum) + (8271600585449/4351875000000000000000000000 : ℝ)*base66 + (1605412470828769/169995117187500000000000000000 : ℝ)*base67 + (84916827647310557/21759375000000000000000000000000 : ℝ)*base69 + (102301965407066807/21759375000000000000000000000000 : ℝ)*base71 + (33971401513777/34815000000000000000000000000 : ℝ)*base74 + (45311732512348733/5439843750000000000000000000000 : ℝ)*base75 + (107552757832035557/21759375000000000000000000000000 : ℝ)*base77 + (96567889386454307/21759375000000000000000000000000 : ℝ)*base79 + (555912658567477/34815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17444737/10000000000000000000000 : ℝ)*base90 + (17444737/10000000000000000000000 : ℝ)*base92 + (17444737/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5859/10000 : ℝ) ≤ (1545364649771065861547590525269/2637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10112181/50000000000000 : ℝ)*(lower0) + (17113183/50000000000000 : ℝ)*(upper2) + (8855187/100000000000000 : ℝ)*(upper3) + (13774343/100000000000000 : ℝ)*(lower5) + (1483989513300327/100000000000000 : ℝ)*(major0) + (1483989513300327/100000000000000 : ℝ)*(major1) + (1483989513300327/100000000000000 : ℝ)*(major2) + (137342448229961/6250000000000 : ℝ)*(sp0) + (2197472887329103/100000000000000 : ℝ)*(sp1) + (549369616275191/25000000000000 : ℝ)*(sp2) + (375484504784711/50000000000000 : ℝ)*(sp3) + (176644653/25000000000000 : ℝ)*(sp6) + (42618307/25000000000000 : ℝ)*(sp7) + (3142175137/50000000000000 : ℝ)*(sp9) + (15019383600853/2000000000000 : ℝ)*(f.failure) + (137342448229961/6250000000000 : ℝ)*(f.sum) + (250641255657/527500000000000000000000000 : ℝ)*base65 + (1090260221355923/5275000000000000000000000000000 : ℝ)*base67 + (18841356006294077/5275000000000000000000000000000 : ℝ)*base70 + (30572862997494077/5275000000000000000000000000000 : ℝ)*base72 + (4854102659439/1055000000000000000000000000 : ℝ)*base73 + (40139332622094077/5275000000000000000000000000000 : ℝ)*base76 + (13344639349555923/5275000000000000000000000000000 : ℝ)*base77 + (7586034142144077/5275000000000000000000000000000 : ℝ)*base80 + (160184674441/65937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (347623/200000000000000000000 : ℝ)*base90 + (347623/200000000000000000000 : ℝ)*base92 + (347623/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81737/100000 : ℝ) ≤ (11857395827064075460153248498131/14506250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36904363/100000000000000 : ℝ)*(upper2) + (1181483/10000000000000 : ℝ)*(lower3) + (29900047/50000000000000 : ℝ)*(lower4) + (92243271/100000000000000 : ℝ)*(lower5) + (1500055450216307/100000000000000 : ℝ)*(major0) + (1500055450216307/100000000000000 : ℝ)*(major1) + (1500055450216307/100000000000000 : ℝ)*(major2) + (430878593/50000000000000 : ℝ)*(sp2) + (779138043/50000000000000 : ℝ)*(sp3) + (325390013/50000000000000 : ℝ)*(sp4) + (2213764305461401/100000000000000 : ℝ)*(sp8) + (2213764956241427/100000000000000 : ℝ)*(sp9) + (2213764094484241/100000000000000 : ℝ)*(sp10) + (379548874471763/50000000000000 : ℝ)*(sp11) + (759099307219613/100000000000000 : ℝ)*(f.failure) + (2213764956241427/100000000000000 : ℝ)*(f.sum) + (153867218530991/17407500000000000000000000000 : ℝ)*base65 + (517208865175406881/174075000000000000000000000000000 : ℝ)*base68 + (1351517645198943119/174075000000000000000000000000000 : ℝ)*base69 + (1105952165195418119/174075000000000000000000000000000 : ℝ)*base71 + (1003018577299/17407500000000000000000000000 : ℝ)*base74 + (493877563993068119/174075000000000000000000000000000 : ℝ)*base75 + (1210982186010918119/174075000000000000000000000000000 : ℝ)*base77 + (812421962209893119/174075000000000000000000000000000 : ℝ)*base79 + (29362256580299/4351875000000000000000000000 : ℝ)*base81 + (67945217/10000000000000000000000 : ℝ)*base89 + (67945217/10000000000000000000000 : ℝ)*base91 + (67945217/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-11317/12500 : ℝ) ≤ (-26265959048821526854767752789621/29012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38241/20000000000000 : ℝ)*(lower0) + (43689/20000000000000 : ℝ)*(upper1) + (3996023/100000000000000 : ℝ)*(upper3) + (3486533/100000000000000 : ℝ)*(lower4) + (1550161116409529/100000000000000 : ℝ)*(major0) + (1550161116409529/100000000000000 : ℝ)*(major1) + (1550161116409529/100000000000000 : ℝ)*(major2) + (258930399/100000000000000 : ℝ)*(sp4) + (4579412661/100000000000000 : ℝ)*(sp5) + (21563039/2500000000000 : ℝ)*(sp7) + (1173022284770189/50000000000000 : ℝ)*(sp12) + (586510062264529/25000000000000 : ℝ)*(sp13) + (293255603558847/12500000000000 : ℝ)*(sp14) + (784454291703287/100000000000000 : ℝ)*(sp15) + (784455154224847/100000000000000 : ℝ)*(f.failure) + (293255603558847/12500000000000 : ℝ)*(f.sum) + (51259929625783/17407500000000000000000000000 : ℝ)*base66 + (1288960975590095707/174075000000000000000000000000000 : ℝ)*base68 + (1122359504316770707/174075000000000000000000000000000 : ℝ)*base70 + (2101393027640120707/174075000000000000000000000000000 : ℝ)*base72 + (10242170782661/2175937500000000000000000000 : ℝ)*base74 + (813945246842645707/174075000000000000000000000000000 : ℝ)*base76 + (326098338611270707/174075000000000000000000000000000 : ℝ)*base78 + (641332303986170707/174075000000000000000000000000000 : ℝ)*base80 + (1750570505059/34815000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (81208923/10000000000000000000000 : ℝ)*base89 + (81208923/10000000000000000000000 : ℝ)*base91 + (81208923/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1718_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3407/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (81737/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11317/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1718_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1718_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (81737/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11317/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1718_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1718_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5359/1024 : ℝ) ≤ p) (hpb : p ≤ (5367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (197609909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4261/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66823/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (81737/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11317/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1718_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:06.289189+00:00
-- url     : https://prove2.me/submissions/eb42d89a-120a-4269-8480-71853ae45702

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
theorem support_rectangle_w1138_s0_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-473269321/2500000000 : ℝ)*x 0 + (605525519/1000000000 : ℝ)*x 1 + (298747889/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473269321/2500000000 : ℝ)^8331 ≤ (2200821914423/20000000000000 : ℝ)^6283 := by
    have hnat : (473269321 : ℕ)^8331*20000000000000^6283 ≤ 2200821914423^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473269321 2500000000 2200821914423 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605525519/1000000000 : ℝ)^8331 ≤ (51418165263483/100000000000000 : ℝ)^6283 := by
    have hnat : (605525519 : ℕ)^8331*100000000000000^6283 ≤ 51418165263483^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605525519 1000000000 51418165263483 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298747889/625000000 : ℝ)^8331 ≤ (18788862572759/50000000000000 : ℝ)^6283 := by
    have hnat : (298747889 : ℕ)^8331*50000000000000^6283 ≤ 18788862572759^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298747889 625000000 18788862572759 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473269321/2500000000 : ℝ), (605525519/1000000000 : ℝ), (298747889/625000000 : ℝ)] ![(2200821914423/20000000000000 : ℝ), (51418165263483/100000000000000 : ℝ), (18788862572759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473269321/2500000000 : ℝ)|^8331 ≤ (2200821914423/20000000000000 : ℝ)^6283
        have hw : |(-473269321/2500000000 : ℝ)|=(473269321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605525519/1000000000 : ℝ)|^8331 ≤ (51418165263483/100000000000000 : ℝ)^6283
        have hw : |(605525519/1000000000 : ℝ)|=(605525519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298747889/625000000 : ℝ)|^8331 ≤ (18788862572759/50000000000000 : ℝ)^6283
        have hw : |(298747889/625000000 : ℝ)|=(298747889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (344813687/625000000 : ℝ)*x 0 + (-525011593/2000000000 : ℝ)*x 1 + (4779966191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344813687/625000000 : ℝ)^8331 ≤ (45447578198967/100000000000000 : ℝ)^6283 := by
    have hnat : (344813687 : ℕ)^8331*100000000000000^6283 ≤ 45447578198967^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344813687 625000000 45447578198967 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525011593/2000000000 : ℝ)^8331 ≤ (8487348490539/50000000000000 : ℝ)^6283 := by
    have hnat : (525011593 : ℕ)^8331*50000000000000^6283 ≤ 8487348490539^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525011593 2000000000 8487348490539 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4779966191/10000000000 : ℝ)^8331 ≤ (1503108992061/4000000000000 : ℝ)^6283 := by
    have hnat : (4779966191 : ℕ)^8331*4000000000000^6283 ≤ 1503108992061^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779966191 10000000000 1503108992061 4000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344813687/625000000 : ℝ), (-525011593/2000000000 : ℝ), (4779966191/10000000000 : ℝ)] ![(45447578198967/100000000000000 : ℝ), (8487348490539/50000000000000 : ℝ), (1503108992061/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344813687/625000000 : ℝ)|^8331 ≤ (45447578198967/100000000000000 : ℝ)^6283
        have hw : |(344813687/625000000 : ℝ)|=(344813687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525011593/2000000000 : ℝ)|^8331 ≤ (8487348490539/50000000000000 : ℝ)^6283
        have hw : |(-525011593/2000000000 : ℝ)|=(525011593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4779966191/10000000000 : ℝ)|^8331 ≤ (1503108992061/4000000000000 : ℝ)^6283
        have hw : |(4779966191/10000000000 : ℝ)|=(4779966191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1379254727/2500000000 : ℝ)*x 0 + (1194991551/2500000000 : ℝ)*x 1 + (-2625058057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379254727/2500000000 : ℝ)^8331 ≤ (45447577281447/100000000000000 : ℝ)^6283 := by
    have hnat : (1379254727 : ℕ)^8331*100000000000000^6283 ≤ 45447577281447^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379254727 2500000000 45447577281447 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194991551/2500000000 : ℝ)^8331 ≤ (18788862468519/50000000000000 : ℝ)^6283 := by
    have hnat : (1194991551 : ℕ)^8331*50000000000000^6283 ≤ 18788862468519^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194991551 2500000000 18788862468519 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625058057/10000000000 : ℝ)^8331 ≤ (16974697769903/100000000000000 : ℝ)^6283 := by
    have hnat : (2625058057 : ℕ)^8331*100000000000000^6283 ≤ 16974697769903^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625058057 10000000000 16974697769903 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379254727/2500000000 : ℝ), (1194991551/2500000000 : ℝ), (-2625058057/10000000000 : ℝ)] ![(45447577281447/100000000000000 : ℝ), (18788862468519/50000000000000 : ℝ), (16974697769903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379254727/2500000000 : ℝ)|^8331 ≤ (45447577281447/100000000000000 : ℝ)^6283
        have hw : |(1379254727/2500000000 : ℝ)|=(1379254727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194991551/2500000000 : ℝ)|^8331 ≤ (18788862468519/50000000000000 : ℝ)^6283
        have hw : |(1194991551/2500000000 : ℝ)|=(1194991551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2625058057/10000000000 : ℝ)|^8331 ≤ (16974697769903/100000000000000 : ℝ)^6283
        have hw : |(-2625058057/10000000000 : ℝ)|=(2625058057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050328613/2500000000 : ℝ)*x 0 + (1560632219/5000000000 : ℝ)*x 1 + (226257143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050328613/2500000000 : ℝ)^8331 ≤ (7917065408463/25000000000000 : ℝ)^6283 := by
    have hnat : (1050328613 : ℕ)^8331*25000000000000^6283 ≤ 7917065408463^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050328613 2500000000 7917065408463 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560632219/5000000000 : ℝ)^8331 ≤ (21355172930933/100000000000000 : ℝ)^6283 := by
    have hnat : (1560632219 : ℕ)^8331*100000000000000^6283 ≤ 21355172930933^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560632219 5000000000 21355172930933 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226257143/400000000 : ℝ)^8331 ≤ (23488282711899/50000000000000 : ℝ)^6283 := by
    have hnat : (226257143 : ℕ)^8331*50000000000000^6283 ≤ 23488282711899^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226257143 400000000 23488282711899 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050328613/2500000000 : ℝ), (1560632219/5000000000 : ℝ), (226257143/400000000 : ℝ)] ![(7917065408463/25000000000000 : ℝ), (21355172930933/100000000000000 : ℝ), (23488282711899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050328613/2500000000 : ℝ)|^8331 ≤ (7917065408463/25000000000000 : ℝ)^6283
        have hw : |(1050328613/2500000000 : ℝ)|=(1050328613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560632219/5000000000 : ℝ)|^8331 ≤ (21355172930933/100000000000000 : ℝ)^6283
        have hw : |(1560632219/5000000000 : ℝ)|=(1560632219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226257143/400000000 : ℝ)|^8331 ≤ (23488282711899/50000000000000 : ℝ)^6283
        have hw : |(226257143/400000000 : ℝ)|=(226257143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898234719/10000000000 : ℝ)*x 0 + (2406433503/5000000000 : ℝ)*x 1 + (3010598949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898234719/10000000000 : ℝ)^8331 ≤ (5521939212899/50000000000000 : ℝ)^6283 := by
    have hnat : (1898234719 : ℕ)^8331*50000000000000^6283 ≤ 5521939212899^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898234719 10000000000 5521939212899 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406433503/5000000000 : ℝ)^8331 ≤ (37921068084081/100000000000000 : ℝ)^6283 := by
    have hnat : (2406433503 : ℕ)^8331*100000000000000^6283 ≤ 37921068084081^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406433503 5000000000 37921068084081 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010598949/5000000000 : ℝ)^8331 ≤ (10207010693671/20000000000000 : ℝ)^6283 := by
    have hnat : (3010598949 : ℕ)^8331*20000000000000^6283 ≤ 10207010693671^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010598949 5000000000 10207010693671 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898234719/10000000000 : ℝ), (2406433503/5000000000 : ℝ), (3010598949/5000000000 : ℝ)] ![(5521939212899/50000000000000 : ℝ), (37921068084081/100000000000000 : ℝ), (10207010693671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898234719/10000000000 : ℝ)|^8331 ≤ (5521939212899/50000000000000 : ℝ)^6283
        have hw : |(-1898234719/10000000000 : ℝ)|=(1898234719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406433503/5000000000 : ℝ)|^8331 ≤ (37921068084081/100000000000000 : ℝ)^6283
        have hw : |(2406433503/5000000000 : ℝ)|=(2406433503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010598949/5000000000 : ℝ)|^8331 ≤ (10207010693671/20000000000000 : ℝ)^6283
        have hw : |(3010598949/5000000000 : ℝ)|=(3010598949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170514111/10000000000 : ℝ)*x 0 + (-27676527/200000000 : ℝ)*x 1 + (6021197783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170514111/10000000000 : ℝ)^8331 ≤ (41702057826343/100000000000000 : ℝ)^6283 := by
    have hnat : (5170514111 : ℕ)^8331*100000000000000^6283 ≤ 41702057826343^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170514111 10000000000 41702057826343 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27676527/200000000 : ℝ)^8331 ≤ (907861248979/12500000000000 : ℝ)^6283 := by
    have hnat : (27676527 : ℕ)^8331*12500000000000^6283 ≤ 907861248979^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27676527 200000000 907861248979 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6021197783/10000000000 : ℝ)^8331 ≤ (10207010435181/20000000000000 : ℝ)^6283 := by
    have hnat : (6021197783 : ℕ)^8331*20000000000000^6283 ≤ 10207010435181^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021197783 10000000000 10207010435181 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170514111/10000000000 : ℝ), (-27676527/200000000 : ℝ), (6021197783/10000000000 : ℝ)] ![(41702057826343/100000000000000 : ℝ), (907861248979/12500000000000 : ℝ), (10207010435181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170514111/10000000000 : ℝ)|^8331 ≤ (41702057826343/100000000000000 : ℝ)^6283
        have hw : |(5170514111/10000000000 : ℝ)|=(5170514111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27676527/200000000 : ℝ)|^8331 ≤ (907861248979/12500000000000 : ℝ)^6283
        have hw : |(-27676527/200000000 : ℝ)|=(27676527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6021197783/10000000000 : ℝ)|^8331 ≤ (10207010435181/20000000000000 : ℝ)^6283
        have hw : |(6021197783/10000000000 : ℝ)|=(6021197783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585257061/5000000000 : ℝ)*x 0 + (1505299449/2500000000 : ℝ)*x 1 + (-1383826311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585257061/5000000000 : ℝ)^8331 ≤ (41702057943981/100000000000000 : ℝ)^6283 := by
    have hnat : (2585257061 : ℕ)^8331*100000000000000^6283 ≤ 41702057943981^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585257061 5000000000 41702057943981 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505299449/2500000000 : ℝ)^8331 ≤ (6379381540251/12500000000000 : ℝ)^6283 := by
    have hnat : (1505299449 : ℕ)^8331*12500000000000^6283 ≤ 6379381540251^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505299449 2500000000 6379381540251 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383826311/10000000000 : ℝ)^8331 ≤ (907861215053/12500000000000 : ℝ)^6283 := by
    have hnat : (1383826311 : ℕ)^8331*12500000000000^6283 ≤ 907861215053^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383826311 10000000000 907861215053 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585257061/5000000000 : ℝ), (1505299449/2500000000 : ℝ), (-1383826311/10000000000 : ℝ)] ![(41702057943981/100000000000000 : ℝ), (6379381540251/12500000000000 : ℝ), (907861215053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585257061/5000000000 : ℝ)|^8331 ≤ (41702057943981/100000000000000 : ℝ)^6283
        have hw : |(2585257061/5000000000 : ℝ)|=(2585257061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1505299449/2500000000 : ℝ)|^8331 ≤ (6379381540251/12500000000000 : ℝ)^6283
        have hw : |(1505299449/2500000000 : ℝ)|=(1505299449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1383826311/10000000000 : ℝ)|^8331 ≤ (907861215053/12500000000000 : ℝ)^6283
        have hw : |(-1383826311/10000000000 : ℝ)|=(1383826311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s0_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (210578353/500000000 : ℝ)*x 0 + (111820487/200000000 : ℝ)*x 1 + (3188967553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210578353/500000000 : ℝ)^8331 ≤ (15885386977167/50000000000000 : ℝ)^6283 := by
    have hnat : (210578353 : ℕ)^8331*50000000000000^6283 ≤ 15885386977167^6283*500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210578353 500000000 15885386977167 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111820487/200000000 : ℝ)^8331 ≤ (46257690240823/100000000000000 : ℝ)^6283 := by
    have hnat : (111820487 : ℕ)^8331*100000000000000^6283 ≤ 46257690240823^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111820487 200000000 46257690240823 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188967553/10000000000 : ℝ)^8331 ≤ (21971535795187/100000000000000 : ℝ)^6283 := by
    have hnat : (3188967553 : ℕ)^8331*100000000000000^6283 ≤ 21971535795187^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188967553 10000000000 21971535795187 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210578353/500000000 : ℝ), (111820487/200000000 : ℝ), (3188967553/10000000000 : ℝ)] ![(15885386977167/50000000000000 : ℝ), (46257690240823/100000000000000 : ℝ), (21971535795187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210578353/500000000 : ℝ)|^8331 ≤ (15885386977167/50000000000000 : ℝ)^6283
        have hw : |(210578353/500000000 : ℝ)|=(210578353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111820487/200000000 : ℝ)|^8331 ≤ (46257690240823/100000000000000 : ℝ)^6283
        have hw : |(111820487/200000000 : ℝ)|=(111820487/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188967553/10000000000 : ℝ)|^8331 ≤ (21971535795187/100000000000000 : ℝ)^6283
        have hw : |(3188967553/10000000000 : ℝ)|=(3188967553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2783/10000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4165/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4165 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4165*1^1024 ≤ 0^1024*1^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4165/1024 : ℝ) ≤ (2406720450668484699/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4165 ≤ (2406720450668484699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4165*100000000000000000000^1024 ≤ 2406720450668484699^1024*5^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2406720450668484699 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2406720450668484699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4165 := by
      have hnat : (1 : ℕ)^1024*1^4165 ≤ 1^4165*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102406720450668484699/100000000000000000000 : ℝ) ≤ (402345667303693/400000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (102406720450668484699/100000000000000000000 : ℝ)^1024 ≤ (402345667303693/400000000000000 : ℝ)^4165 := by
      have hnat : (102406720450668484699 : ℕ)^1024*400000000000000^4165 ≤ 402345667303693^4165*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102406720450668484699 100000000000000000000 402345667303693 400000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402345667303693/400000000000000 : ℝ)) (X := (102406720450668484699/100000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52406720450668484699/50000000000000000000 : ℝ) ≤ (202345667303693/200000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (52406720450668484699/50000000000000000000 : ℝ)^1024 ≤ (202345667303693/200000000000000 : ℝ)^4165 := by
      have hnat : (52406720450668484699 : ℕ)^1024*200000000000000^4165 ≤ 202345667303693^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52406720450668484699 50000000000000000000 202345667303693 200000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202345667303693/200000000000000 : ℝ)) (X := (52406720450668484699/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2345667303693/160000000000000 : ℝ)*(0 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2345667303693/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2406720450668484699/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2345667303693/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2345667303693/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(402345667303693/400000000000000 : ℝ) by norm_num, show 1+(2406720450668484699/100000000000000000000 : ℝ)+(0 : ℝ)=(102406720450668484699/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2406720450668484699/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2345667303693/160000000000000 : ℝ)*(2/5 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2345667303693/160000000000000 : ℝ)*(2/5 : ℝ)=(202345667303693/200000000000000 : ℝ) by norm_num, show 1+2*(2406720450668484699/100000000000000000000 : ℝ)=(52406720450668484699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2345667303693/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2345667303693/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2345667303693/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2345667303693/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2345667303693/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2345667303693/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473269321/2500000000 : ℝ)*X 0 0+(605525519/1000000000 : ℝ)*X 0 1+(298747889/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((344813687/625000000 : ℝ)*X 1 0+(-525011593/2000000000 : ℝ)*X 1 1+(4779966191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379254727/2500000000 : ℝ)*X 2 0+(1194991551/2500000000 : ℝ)*X 2 1+(-2625058057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050328613/2500000000 : ℝ)*X 0 0+(1560632219/5000000000 : ℝ)*X 0 1+(226257143/400000000 : ℝ)*X 0 2+(1050328613/2500000000 : ℝ)*X 1 0+(1560632219/5000000000 : ℝ)*X 1 1+(226257143/400000000 : ℝ)*X 1 2+(1050328613/2500000000 : ℝ)*X 2 0+(1560632219/5000000000 : ℝ)*X 2 1+(226257143/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1898234719/10000000000 : ℝ)*X 0 0+(2406433503/5000000000 : ℝ)*X 0 1+(3010598949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170514111/10000000000 : ℝ)*X 1 0+(-27676527/200000000 : ℝ)*X 1 1+(6021197783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585257061/5000000000 : ℝ)*X 2 0+(1505299449/2500000000 : ℝ)*X 2 1+(-1383826311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210578353/500000000 : ℝ)*X 0 0+(111820487/200000000 : ℝ)*X 0 1+(3188967553/10000000000 : ℝ)*X 0 2+(210578353/500000000 : ℝ)*X 1 0+(111820487/200000000 : ℝ)*X 1 1+(3188967553/10000000000 : ℝ)*X 1 2+(210578353/500000000 : ℝ)*X 2 0+(111820487/200000000 : ℝ)*X 2 1+(3188967553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38130891094256578226649/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3645489/6250000000000 : ℝ)*(base1) + (70496019/6250000000000 : ℝ)*(base19) + (65442671/6250000000000 : ℝ)*(base23) + (68914539/100000000000000 : ℝ)*(base24) + (255650117/100000000000000 : ℝ)*(upper3) + (589298618071169/100000000000000 : ℝ)*(major0) + (589298618071169/100000000000000 : ℝ)*(major1) + (589298618071169/100000000000000 : ℝ)*(major2) + (392069871356231/50000000000000 : ℝ)*(sp0) + (784140994899443/100000000000000 : ℝ)*(sp1) + (784141006838471/100000000000000 : ℝ)*(sp2) + (6163327148153/1562500000000 : ℝ)*(sp3) + (609612777/25000000000000 : ℝ)*(sp4) + (1958618259/100000000000000 : ℝ)*(sp7) + (3155639635423/800000000000 : ℝ)*(f.failure) + (392071061417873/50000000000000 : ℝ)*(f.sum) + (12326386784883/8000000000000000000000000000 : ℝ)*base66 + (70692770943117/16000000000000000000000000000 : ℝ)*base67 + (84478832943117/16000000000000000000000000000 : ℝ)*base69 + (48446562847117/16000000000000000000000000000 : ℝ)*base71 + (3236562119117/8000000000000000000000000000 : ℝ)*base73 + (21368801312883/16000000000000000000000000000 : ℝ)*base76 + (54085151455117/16000000000000000000000000000 : ℝ)*base77 + (60668552447117/16000000000000000000000000000 : ℝ)*base79 + (54641355712883/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (17013/80000000000000000000 : ℝ)*base90 + (17013/80000000000000000000 : ℝ)*base92 + (17013/80000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (997700842727876192127/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33857111/100000000000000 : ℝ)*(base1) + (97046363/20000000000000 : ℝ)*(base19) + (121526889/25000000000000 : ℝ)*(base23) + (2938379/6250000000000 : ℝ)*(upper3) + (12086473/20000000000000 : ℝ)*(upper5) + (155487235711413/25000000000000 : ℝ)*(major0) + (155487235711413/25000000000000 : ℝ)*(major1) + (155487235711413/25000000000000 : ℝ)*(major2) + (935738191/100000000000000 : ℝ)*(sp1) + (461266963/50000000000000 : ℝ)*(sp2) + (827587964663589/100000000000000 : ℝ)*(sp4) + (103448313729559/12500000000000 : ℝ)*(sp5) + (206896630541249/25000000000000 : ℝ)*(sp6) + (5203873181429/1250000000000 : ℝ)*(sp7) + (416309888371431/100000000000000 : ℝ)*(f.failure) + (413793965403239/50000000000000 : ℝ)*(f.sum) + (2841671730209/2000000000000000000000000000 : ℝ)*base65 + (35652968987791/4000000000000000000000000000 : ℝ)*base68 + (41598802379791/4000000000000000000000000000 : ℝ)*base70 + (21829539107791/4000000000000000000000000000 : ℝ)*base72 + (1847249821791/2000000000000000000000000000 : ℝ)*base74 + (38168826919791/4000000000000000000000000000 : ℝ)*base76 + (24951004931791/4000000000000000000000000000 : ℝ)*base78 + (19650333731791/4000000000000000000000000000 : ℝ)*base80 + (3135037695791/2000000000000000000000000000 : ℝ)*base82 + (54732339/10000000000000000000000 : ℝ)*base89 + (54732339/10000000000000000000000 : ℝ)*base91 + (54732339/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1138_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2783/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s1_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098035547/10000000000 : ℝ)*x 0 + (57025683/100000000 : ℝ)*x 1 + (312589843/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098035547/10000000000 : ℝ)^8331 ≤ (12611062476663/100000000000000 : ℝ)^6283 := by
    have hnat : (2098035547 : ℕ)^8331*100000000000000^6283 ≤ 12611062476663^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098035547 10000000000 12611062476663 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57025683/100000000 : ℝ)^8331 ≤ (11871333405783/25000000000000 : ℝ)^6283 := by
    have hnat : (57025683 : ℕ)^8331*25000000000000^6283 ≤ 11871333405783^6283*100000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57025683 100000000 11871333405783 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312589843/625000000 : ℝ)^8331 ≤ (19951801939951/50000000000000 : ℝ)^6283 := by
    have hnat : (312589843 : ℕ)^8331*50000000000000^6283 ≤ 19951801939951^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312589843 625000000 19951801939951 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098035547/10000000000 : ℝ), (57025683/100000000 : ℝ), (312589843/625000000 : ℝ)] ![(12611062476663/100000000000000 : ℝ), (11871333405783/25000000000000 : ℝ), (19951801939951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098035547/10000000000 : ℝ)|^8331 ≤ (12611062476663/100000000000000 : ℝ)^6283
        have hw : |(-2098035547/10000000000 : ℝ)|=(2098035547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57025683/100000000 : ℝ)|^8331 ≤ (11871333405783/25000000000000 : ℝ)^6283
        have hw : |(57025683/100000000 : ℝ)|=(57025683/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312589843/625000000 : ℝ)|^8331 ≤ (19951801939951/50000000000000 : ℝ)^6283
        have hw : |(312589843/625000000 : ℝ)|=(312589843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677417441/1250000000 : ℝ)*x 0 + (-1238240399/5000000000 : ℝ)*x 1 + (5001436877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677417441/1250000000 : ℝ)^8331 ≤ (22191865109549/50000000000000 : ℝ)^6283 := by
    have hnat : (677417441 : ℕ)^8331*50000000000000^6283 ≤ 22191865109549^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677417441 1250000000 22191865109549 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238240399/5000000000 : ℝ)^8331 ≤ (15712672354451/100000000000000 : ℝ)^6283 := by
    have hnat : (1238240399 : ℕ)^8331*100000000000000^6283 ≤ 15712672354451^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238240399 5000000000 15712672354451 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001436877/10000000000 : ℝ)^8331 ≤ (39903597416093/100000000000000 : ℝ)^6283 := by
    have hnat : (5001436877 : ℕ)^8331*100000000000000^6283 ≤ 39903597416093^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001436877 10000000000 39903597416093 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677417441/1250000000 : ℝ), (-1238240399/5000000000 : ℝ), (5001436877/10000000000 : ℝ)] ![(22191865109549/50000000000000 : ℝ), (15712672354451/100000000000000 : ℝ), (39903597416093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677417441/1250000000 : ℝ)|^8331 ≤ (22191865109549/50000000000000 : ℝ)^6283
        have hw : |(677417441/1250000000 : ℝ)|=(677417441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1238240399/5000000000 : ℝ)|^8331 ≤ (15712672354451/100000000000000 : ℝ)^6283
        have hw : |(-1238240399/5000000000 : ℝ)|=(1238240399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001436877/10000000000 : ℝ)|^8331 ≤ (39903597416093/100000000000000 : ℝ)^6283
        have hw : |(5001436877/10000000000 : ℝ)|=(5001436877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419341401/10000000000 : ℝ)*x 0 + (625179401/1250000000 : ℝ)*x 1 + (-2476480479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419341401/10000000000 : ℝ)^8331 ≤ (22191875279417/50000000000000 : ℝ)^6283 := by
    have hnat : (5419341401 : ℕ)^8331*50000000000000^6283 ≤ 22191875279417^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419341401 10000000000 22191875279417 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625179401/1250000000 : ℝ)^8331 ≤ (2493973734977/6250000000000 : ℝ)^6283 := by
    have hnat : (625179401 : ℕ)^8331*6250000000000^6283 ≤ 2493973734977^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625179401 1250000000 2493973734977 6250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2476480479/10000000000 : ℝ)^8331 ≤ (15712669670739/100000000000000 : ℝ)^6283 := by
    have hnat : (2476480479 : ℕ)^8331*100000000000000^6283 ≤ 15712669670739^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476480479 10000000000 15712669670739 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419341401/10000000000 : ℝ), (625179401/1250000000 : ℝ), (-2476480479/10000000000 : ℝ)] ![(22191875279417/50000000000000 : ℝ), (2493973734977/6250000000000 : ℝ), (15712669670739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419341401/10000000000 : ℝ)|^8331 ≤ (22191875279417/50000000000000 : ℝ)^6283
        have hw : |(5419341401/10000000000 : ℝ)|=(5419341401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625179401/1250000000 : ℝ)|^8331 ≤ (2493973734977/6250000000000 : ℝ)^6283
        have hw : |(625179401/1250000000 : ℝ)|=(625179401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2476480479/10000000000 : ℝ)|^8331 ≤ (15712669670739/100000000000000 : ℝ)^6283
        have hw : |(-2476480479/10000000000 : ℝ)|=(2476480479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4317779639/10000000000 : ℝ)*x 0 + (229769007/625000000 : ℝ)*x 1 + (2535044479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317779639/10000000000 : ℝ)^8331 ≤ (2052345073851/6250000000000 : ℝ)^6283 := by
    have hnat : (4317779639 : ℕ)^8331*6250000000000^6283 ≤ 2052345073851^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317779639 10000000000 2052345073851 6250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229769007/625000000 : ℝ)^8331 ≤ (6632746673011/25000000000000 : ℝ)^6283 := by
    have hnat : (229769007 : ℕ)^8331*25000000000000^6283 ≤ 6632746673011^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229769007 625000000 6632746673011 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2535044479/5000000000 : ℝ)^8331 ≤ (406314921141/1000000000000 : ℝ)^6283 := by
    have hnat : (2535044479 : ℕ)^8331*1000000000000^6283 ≤ 406314921141^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535044479 5000000000 406314921141 1000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317779639/10000000000 : ℝ), (229769007/625000000 : ℝ), (2535044479/5000000000 : ℝ)] ![(2052345073851/6250000000000 : ℝ), (6632746673011/25000000000000 : ℝ), (406314921141/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317779639/10000000000 : ℝ)|^8331 ≤ (2052345073851/6250000000000 : ℝ)^6283
        have hw : |(4317779639/10000000000 : ℝ)|=(4317779639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229769007/625000000 : ℝ)|^8331 ≤ (6632746673011/25000000000000 : ℝ)^6283
        have hw : |(229769007/625000000 : ℝ)|=(229769007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2535044479/5000000000 : ℝ)|^8331 ≤ (406314921141/1000000000000 : ℝ)^6283
        have hw : |(2535044479/5000000000 : ℝ)|=(2535044479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049425911/5000000000 : ℝ)*x 0 + (5011025269/10000000000 : ℝ)*x 1 + (1138557401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049425911/5000000000 : ℝ)^8331 ≤ (1261756875953/10000000000000 : ℝ)^6283 := by
    have hnat : (1049425911 : ℕ)^8331*10000000000000^6283 ≤ 1261756875953^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049425911 5000000000 1261756875953 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011025269/10000000000 : ℝ)^8331 ≤ (40005065329761/100000000000000 : ℝ)^6283 := by
    have hnat : (5011025269 : ℕ)^8331*100000000000000^6283 ≤ 40005065329761^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011025269 10000000000 40005065329761 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138557401/2000000000 : ℝ)^8331 ≤ (47377365895881/100000000000000 : ℝ)^6283 := by
    have hnat : (1138557401 : ℕ)^8331*100000000000000^6283 ≤ 47377365895881^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138557401 2000000000 47377365895881 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049425911/5000000000 : ℝ), (5011025269/10000000000 : ℝ), (1138557401/2000000000 : ℝ)] ![(1261756875953/10000000000000 : ℝ), (40005065329761/100000000000000 : ℝ), (47377365895881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049425911/5000000000 : ℝ)|^8331 ≤ (1261756875953/10000000000000 : ℝ)^6283
        have hw : |(-1049425911/5000000000 : ℝ)|=(1049425911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011025269/10000000000 : ℝ)|^8331 ≤ (40005065329761/100000000000000 : ℝ)^6283
        have hw : |(5011025269/10000000000 : ℝ)|=(5011025269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138557401/2000000000 : ℝ)|^8331 ≤ (47377365895881/100000000000000 : ℝ)^6283
        have hw : |(1138557401/2000000000 : ℝ)|=(1138557401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619809189/5000000000 : ℝ)*x 0 + (-89256321/500000000 : ℝ)*x 1 + (569279067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619809189/5000000000 : ℝ)^8331 ≤ (42442687049739/100000000000000 : ℝ)^6283 := by
    have hnat : (2619809189 : ℕ)^8331*100000000000000^6283 ≤ 42442687049739^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619809189 5000000000 42442687049739 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89256321/500000000 : ℝ)^8331 ≤ (10179906595199/100000000000000 : ℝ)^6283 := by
    have hnat : (89256321 : ℕ)^8331*100000000000000^6283 ≤ 10179906595199^6283*500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89256321 500000000 10179906595199 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569279067/1000000000 : ℝ)^8331 ≤ (23688703169753/50000000000000 : ℝ)^6283 := by
    have hnat : (569279067 : ℕ)^8331*50000000000000^6283 ≤ 23688703169753^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569279067 1000000000 23688703169753 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619809189/5000000000 : ℝ), (-89256321/500000000 : ℝ), (569279067/1000000000 : ℝ)] ![(42442687049739/100000000000000 : ℝ), (10179906595199/100000000000000 : ℝ), (23688703169753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619809189/5000000000 : ℝ)|^8331 ≤ (42442687049739/100000000000000 : ℝ)^6283
        have hw : |(2619809189/5000000000 : ℝ)|=(2619809189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89256321/500000000 : ℝ)|^8331 ≤ (10179906595199/100000000000000 : ℝ)^6283
        have hw : |(-89256321/500000000 : ℝ)|=(89256321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569279067/1000000000 : ℝ)|^8331 ≤ (23688703169753/50000000000000 : ℝ)^6283
        have hw : |(569279067/1000000000 : ℝ)|=(569279067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309904199/2500000000 : ℝ)*x 0 + (5692792673/10000000000 : ℝ)*x 1 + (-111570359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309904199/2500000000 : ℝ)^8331 ≤ (1697706802317/4000000000000 : ℝ)^6283 := by
    have hnat : (1309904199 : ℕ)^8331*4000000000000^6283 ≤ 1697706802317^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309904199 2500000000 1697706802317 4000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5692792673/10000000000 : ℝ)^8331 ≤ (23688714221403/50000000000000 : ℝ)^6283 := by
    have hnat : (5692792673 : ℕ)^8331*50000000000000^6283 ≤ 23688714221403^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5692792673 10000000000 23688714221403 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111570359/625000000 : ℝ)^8331 ≤ (10179901483661/100000000000000 : ℝ)^6283 := by
    have hnat : (111570359 : ℕ)^8331*100000000000000^6283 ≤ 10179901483661^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111570359 625000000 10179901483661 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309904199/2500000000 : ℝ), (5692792673/10000000000 : ℝ), (-111570359/625000000 : ℝ)] ![(1697706802317/4000000000000 : ℝ), (23688714221403/50000000000000 : ℝ), (10179901483661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309904199/2500000000 : ℝ)|^8331 ≤ (1697706802317/4000000000000 : ℝ)^6283
        have hw : |(1309904199/2500000000 : ℝ)|=(1309904199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5692792673/10000000000 : ℝ)|^8331 ≤ (23688714221403/50000000000000 : ℝ)^6283
        have hw : |(5692792673/10000000000 : ℝ)|=(5692792673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111570359/625000000 : ℝ)|^8331 ≤ (10179901483661/100000000000000 : ℝ)^6283
        have hw : |(-111570359/625000000 : ℝ)|=(111570359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319392487/10000000000 : ℝ)*x 0 + (5051028681/10000000000 : ℝ)*x 1 + (230983777/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319392487/10000000000 : ℝ)^8331 ≤ (32853786397913/100000000000000 : ℝ)^6283 := by
    have hnat : (4319392487 : ℕ)^8331*100000000000000^6283 ≤ 32853786397913^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319392487 10000000000 32853786397913 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051028681/10000000000 : ℝ)^8331 ≤ (10107269583399/25000000000000 : ℝ)^6283 := by
    have hnat : (5051028681 : ℕ)^8331*25000000000000^6283 ≤ 10107269583399^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051028681 10000000000 10107269583399 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230983777/625000000 : ℝ)^8331 ≤ (5343427051761/20000000000000 : ℝ)^6283 := by
    have hnat : (230983777 : ℕ)^8331*20000000000000^6283 ≤ 5343427051761^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230983777 625000000 5343427051761 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319392487/10000000000 : ℝ), (5051028681/10000000000 : ℝ), (230983777/625000000 : ℝ)] ![(32853786397913/100000000000000 : ℝ), (10107269583399/25000000000000 : ℝ), (5343427051761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319392487/10000000000 : ℝ)|^8331 ≤ (32853786397913/100000000000000 : ℝ)^6283
        have hw : |(4319392487/10000000000 : ℝ)|=(4319392487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051028681/10000000000 : ℝ)|^8331 ≤ (10107269583399/25000000000000 : ℝ)^6283
        have hw : |(5051028681/10000000000 : ℝ)|=(5051028681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230983777/625000000 : ℝ)|^8331 ≤ (5343427051761/20000000000000 : ℝ)^6283
        have hw : |(230983777/625000000 : ℝ)|=(230983777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_8 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (621669/1000000000 : ℝ)*x 0 + (1372571281/2500000000 : ℝ)*x 1 + (6356622871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621669/1000000000 : ℝ)^8331 ≤ (5602620179/100000000000000 : ℝ)^6283 := by
    have hnat : (621669 : ℕ)^8331*100000000000000^6283 ≤ 5602620179^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621669 1000000000 5602620179 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372571281/2500000000 : ℝ)^8331 ≤ (9031159757199/20000000000000 : ℝ)^6283 := by
    have hnat : (1372571281 : ℕ)^8331*20000000000000^6283 ≤ 9031159757199^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372571281 2500000000 9031159757199 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6356622871/10000000000 : ℝ)^8331 ≤ (54838598584113/100000000000000 : ℝ)^6283 := by
    have hnat : (6356622871 : ℕ)^8331*100000000000000^6283 ≤ 54838598584113^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6356622871 10000000000 54838598584113 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(621669/1000000000 : ℝ), (1372571281/2500000000 : ℝ), (6356622871/10000000000 : ℝ)] ![(5602620179/100000000000000 : ℝ), (9031159757199/20000000000000 : ℝ), (54838598584113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(621669/1000000000 : ℝ)|^8331 ≤ (5602620179/100000000000000 : ℝ)^6283
        have hw : |(621669/1000000000 : ℝ)|=(621669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372571281/2500000000 : ℝ)|^8331 ≤ (9031159757199/20000000000000 : ℝ)^6283
        have hw : |(1372571281/2500000000 : ℝ)|=(1372571281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6356622871/10000000000 : ℝ)|^8331 ≤ (54838598584113/100000000000000 : ℝ)^6283
        have hw : |(6356622871/10000000000 : ℝ)|=(6356622871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_9 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (244753337/2500000000 : ℝ)*x 0 + (-4412101367/10000000000 : ℝ)*x 1 + (1388137437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244753337/2500000000 : ℝ)^8331 ≤ (4590152794867/100000000000000 : ℝ)^6283 := by
    have hnat : (244753337 : ℕ)^8331*100000000000000^6283 ≤ 4590152794867^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244753337 2500000000 4590152794867 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412101367/10000000000 : ℝ)^8331 ≤ (33792047012331/100000000000000 : ℝ)^6283 := by
    have hnat : (4412101367 : ℕ)^8331*100000000000000^6283 ≤ 33792047012331^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412101367 10000000000 33792047012331 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388137437/2000000000 : ℝ)^8331 ≤ (30808900088331/50000000000000 : ℝ)^6283 := by
    have hnat : (1388137437 : ℕ)^8331*50000000000000^6283 ≤ 30808900088331^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388137437 2000000000 30808900088331 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(244753337/2500000000 : ℝ), (-4412101367/10000000000 : ℝ), (1388137437/2000000000 : ℝ)] ![(4590152794867/100000000000000 : ℝ), (33792047012331/100000000000000 : ℝ), (30808900088331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(244753337/2500000000 : ℝ)|^8331 ≤ (4590152794867/100000000000000 : ℝ)^6283
        have hw : |(244753337/2500000000 : ℝ)|=(244753337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4412101367/10000000000 : ℝ)|^8331 ≤ (33792047012331/100000000000000 : ℝ)^6283
        have hw : |(-4412101367/10000000000 : ℝ)|=(4412101367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1388137437/2000000000 : ℝ)|^8331 ≤ (30808900088331/50000000000000 : ℝ)^6283
        have hw : |(1388137437/2000000000 : ℝ)|=(1388137437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_10 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (979005257/10000000000 : ℝ)*x 0 + (6940668311/10000000000 : ℝ)*x 1 + (-2206064099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979005257/10000000000 : ℝ)^8331 ≤ (286881405913/6250000000000 : ℝ)^6283 := by
    have hnat : (979005257 : ℕ)^8331*6250000000000^6283 ≤ 286881405913^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979005257 10000000000 286881405913 6250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6940668311/10000000000 : ℝ)^8331 ≤ (61617578000453/100000000000000 : ℝ)^6283 := by
    have hnat : (6940668311 : ℕ)^8331*100000000000000^6283 ≤ 61617578000453^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6940668311 10000000000 61617578000453 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206064099/5000000000 : ℝ)^8331 ≤ (3379231949343/10000000000000 : ℝ)^6283 := by
    have hnat : (2206064099 : ℕ)^8331*10000000000000^6283 ≤ 3379231949343^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206064099 5000000000 3379231949343 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(979005257/10000000000 : ℝ), (6940668311/10000000000 : ℝ), (-2206064099/5000000000 : ℝ)] ![(286881405913/6250000000000 : ℝ), (61617578000453/100000000000000 : ℝ), (3379231949343/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(979005257/10000000000 : ℝ)|^8331 ≤ (286881405913/6250000000000 : ℝ)^6283
        have hw : |(979005257/10000000000 : ℝ)|=(979005257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6940668311/10000000000 : ℝ)|^8331 ≤ (61617578000453/100000000000000 : ℝ)^6283
        have hw : |(6940668311/10000000000 : ℝ)|=(6940668311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206064099/5000000000 : ℝ)|^8331 ≤ (3379231949343/10000000000000 : ℝ)^6283
        have hw : |(-2206064099/5000000000 : ℝ)|=(2206064099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s1_11 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1916380631/10000000000 : ℝ)*x 0 + (1162592463/2000000000 : ℝ)*x 1 + (2510366767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916380631/10000000000 : ℝ)^8331 ≤ (11184080755451/100000000000000 : ℝ)^6283 := by
    have hnat : (1916380631 : ℕ)^8331*100000000000000^6283 ≤ 11184080755451^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916380631 10000000000 11184080755451 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162592463/2000000000 : ℝ)^8331 ≤ (48708052950909/100000000000000 : ℝ)^6283 := by
    have hnat : (1162592463 : ℕ)^8331*100000000000000^6283 ≤ 48708052950909^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162592463 2000000000 48708052950909 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510366767/5000000000 : ℝ)^8331 ≤ (40107866281897/100000000000000 : ℝ)^6283 := by
    have hnat : (2510366767 : ℕ)^8331*100000000000000^6283 ≤ 40107866281897^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510366767 5000000000 40107866281897 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1916380631/10000000000 : ℝ), (1162592463/2000000000 : ℝ), (2510366767/5000000000 : ℝ)] ![(11184080755451/100000000000000 : ℝ), (48708052950909/100000000000000 : ℝ), (40107866281897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1916380631/10000000000 : ℝ)|^8331 ≤ (11184080755451/100000000000000 : ℝ)^6283
        have hw : |(1916380631/10000000000 : ℝ)|=(1916380631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162592463/2000000000 : ℝ)|^8331 ≤ (48708052950909/100000000000000 : ℝ)^6283
        have hw : |(1162592463/2000000000 : ℝ)|=(1162592463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510366767/5000000000 : ℝ)|^8331 ≤ (40107866281897/100000000000000 : ℝ)^6283
        have hw : |(2510366767/5000000000 : ℝ)|=(2510366767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2783/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5627/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2783/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2783/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2783/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2783/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2783/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2783/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (397/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (3422880787/20000000000000000000 : ℝ) := by
    have hpowers : (397/100000 : ℝ)^4165 ≤ (3422880787/20000000000000000000 : ℝ)^1024 := by
      have hnat : (397 : ℕ)^4165*20000000000000000000^1024 ≤ 3422880787^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        397 100000 3422880787 20000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (397/100000 : ℝ)) (X := (3422880787/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2783/10000 : ℝ) ^ (4165/1024 : ℝ) ≤ (275164603898762803/50000000000000000000 : ℝ) := by
    have hpowers : (2783/10000 : ℝ)^4165 ≤ (275164603898762803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2783 : ℕ)^4165*50000000000000000000^1024 ≤ 275164603898762803^1024*10000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2783 10000 275164603898762803 50000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2783/10000 : ℝ)) (X := (275164603898762803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000003422880787/10000000000000000000 : ℝ) ≤ (1250000000105193/1250000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (10000000003422880787/10000000000000000000 : ℝ)^1024 ≤ (1250000000105193/1250000000000000 : ℝ)^4165 := by
      have hnat : (10000000003422880787 : ℕ)^1024*1250000000000000^4165 ≤ 1250000000105193^4165*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000003422880787 10000000000000000000 1250000000105193 1250000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000105193/1250000000000000 : ℝ)) (X := (10000000003422880787/10000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100550329224911929541/100000000000000000000 : ℝ) ≤ (10013502316008793/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (100550329224911929541/100000000000000000000 : ℝ)^1024 ≤ (10013502316008793/10000000000000000 : ℝ)^4165 := by
      have hnat : (100550329224911929541 : ℕ)^1024*10000000000000000^4165 ≤ 10013502316008793^4165*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100550329224911929541 100000000000000000000 10013502316008793 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013502316008793/10000000000000000 : ℝ)) (X := (100550329224911929541/100000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25275164603898762803/25000000000000000000 : ℝ) ≤ (5013502315588021/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (25275164603898762803/25000000000000000000 : ℝ)^1024 ≤ (5013502315588021/5000000000000000 : ℝ)^4165 := by
      have hnat : (25275164603898762803 : ℕ)^1024*5000000000000000^4165 ≤ 5013502315588021^4165*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25275164603898762803 25000000000000000000 5013502315588021 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013502315588021/5000000000000000 : ℝ)) (X := (25275164603898762803/25000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3422880787/20000000000000000000 : ℝ) ≤ ((137159639592421640423/137165000000000000000 : ℝ)+2*(13502315167249/2743300000000000 : ℝ)*(397/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (137159639592421640423/137165000000000000000 : ℝ)+2*(13502315167249/2743300000000000 : ℝ)*(397/100000 : ℝ)=(1250000000105193/1250000000000000 : ℝ) by norm_num, show 1+2*(3422880787/20000000000000000000 : ℝ)=(10000000003422880787/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(275164603898762803/50000000000000000000 : ℝ)+(3422880787/20000000000000000000 : ℝ) ≤ ((137159639592421640423/137165000000000000000 : ℝ)+(13502315167249/2743300000000000 : ℝ)*((2783/10000 : ℝ)+(397/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (137159639592421640423/137165000000000000000 : ℝ)+(13502315167249/2743300000000000 : ℝ)*((2783/10000 : ℝ)+(397/100000 : ℝ))=(10013502316008793/10000000000000000 : ℝ) by norm_num, show 1+(275164603898762803/50000000000000000000 : ℝ)+(3422880787/20000000000000000000 : ℝ)=(100550329224911929541/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(275164603898762803/50000000000000000000 : ℝ) ≤ ((137159639592421640423/137165000000000000000 : ℝ)+2*(13502315167249/2743300000000000 : ℝ)*(2783/10000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (137159639592421640423/137165000000000000000 : ℝ)+2*(13502315167249/2743300000000000 : ℝ)*(2783/10000 : ℝ)=(5013502315588021/5000000000000000 : ℝ) by norm_num, show 1+2*(275164603898762803/50000000000000000000 : ℝ)=(25275164603898762803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137159639592421640423/137165000000000000000 : ℝ)*(X 1 0+X 2 0)+(13502315167249/2743300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (397/100000 : ℝ)) (hi := (2783/10000 : ℝ)) (c := (137159639592421640423/137165000000000000000 : ℝ)) (alpha := (13502315167249/2743300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137159639592421640423/137165000000000000000 : ℝ)*(X 0 1+X 2 1)+(13502315167249/2743300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (397/100000 : ℝ)) (hi := (2783/10000 : ℝ)) (c := (137159639592421640423/137165000000000000000 : ℝ)) (alpha := (13502315167249/2743300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137159639592421640423/137165000000000000000 : ℝ)*(X 0 2+X 1 2)+(13502315167249/2743300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (397/100000 : ℝ)) (hi := (2783/10000 : ℝ)) (c := (137159639592421640423/137165000000000000000 : ℝ)) (alpha := (13502315167249/2743300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2098035547/10000000000 : ℝ)*X 0 0+(57025683/100000000 : ℝ)*X 0 1+(312589843/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677417441/1250000000 : ℝ)*X 1 0+(-1238240399/5000000000 : ℝ)*X 1 1+(5001436877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419341401/10000000000 : ℝ)*X 2 0+(625179401/1250000000 : ℝ)*X 2 1+(-2476480479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317779639/10000000000 : ℝ)*X 0 0+(229769007/625000000 : ℝ)*X 0 1+(2535044479/5000000000 : ℝ)*X 0 2+(4317779639/10000000000 : ℝ)*X 1 0+(229769007/625000000 : ℝ)*X 1 1+(2535044479/5000000000 : ℝ)*X 1 2+(4317779639/10000000000 : ℝ)*X 2 0+(229769007/625000000 : ℝ)*X 2 1+(2535044479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1049425911/5000000000 : ℝ)*X 0 0+(5011025269/10000000000 : ℝ)*X 0 1+(1138557401/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619809189/5000000000 : ℝ)*X 1 0+(-89256321/500000000 : ℝ)*X 1 1+(569279067/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309904199/2500000000 : ℝ)*X 2 0+(5692792673/10000000000 : ℝ)*X 2 1+(-111570359/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319392487/10000000000 : ℝ)*X 0 0+(5051028681/10000000000 : ℝ)*X 0 1+(230983777/625000000 : ℝ)*X 0 2+(4319392487/10000000000 : ℝ)*X 1 0+(5051028681/10000000000 : ℝ)*X 1 1+(230983777/625000000 : ℝ)*X 1 2+(4319392487/10000000000 : ℝ)*X 2 0+(5051028681/10000000000 : ℝ)*X 2 1+(230983777/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((621669/1000000000 : ℝ)*X 0 0+(1372571281/2500000000 : ℝ)*X 0 1+(6356622871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((244753337/2500000000 : ℝ)*X 1 0+(-4412101367/10000000000 : ℝ)*X 1 1+(1388137437/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((979005257/10000000000 : ℝ)*X 2 0+(6940668311/10000000000 : ℝ)*X 2 1+(-2206064099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1916380631/10000000000 : ℝ)*X 0 0+(1162592463/2000000000 : ℝ)*X 0 1+(2510366767/5000000000 : ℝ)*X 0 2+(1916380631/10000000000 : ℝ)*X 1 0+(1162592463/2000000000 : ℝ)*X 1 1+(2510366767/5000000000 : ℝ)*X 1 2+(1916380631/10000000000 : ℝ)*X 2 0+(1162592463/2000000000 : ℝ)*X 2 1+(2510366767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43562751371511157340386980663/3429125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (535937140314791/50000000000000 : ℝ)*(major0) + (535937140314791/50000000000000 : ℝ)*(major1) + (535937140314791/50000000000000 : ℝ)*(major2) + (356567689277481/25000000000000 : ℝ)*(sp0) + (1426270483674399/100000000000000 : ℝ)*(sp1) + (1426268547230159/100000000000000 : ℝ)*(sp2) + (17936790818553/2500000000000 : ℝ)*(sp3) + (3567031573/100000000000000 : ℝ)*(sp4) + (108048029/3125000000000 : ℝ)*(sp5) + (1212167061/25000000000000 : ℝ)*(sp6) + (350201931/100000000000000 : ℝ)*(sp8) + (7331321/1000000000000 : ℝ)*(sp9) + (51137801/4000000000000 : ℝ)*(sp10) + (57209851/3125000000000 : ℝ)*(sp11) + (89684182932169/12500000000000 : ℝ)*(f.failure) + (356568668585857/25000000000000 : ℝ)*(f.sum) + (57306731184649/68582500000000000000000000000 : ℝ)*base65 + (25733159352245096593/6858250000000000000000000000000000 : ℝ)*base67 + (16392749394388846593/6858250000000000000000000000000000 : ℝ)*base69 + (27542626130572346593/6858250000000000000000000000000000 : ℝ)*base71 + (41980458586163/34291250000000000000000000000 : ℝ)*base74 + (42399860889972596593/6858250000000000000000000000000000 : ℝ)*base75 + (8290433734618346593/6858250000000000000000000000000000 : ℝ)*base77 + (13943036996901596593/6858250000000000000000000000000000 : ℝ)*base79 + (34264903700247/137165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5623939/1250000000000000000000 : ℝ)*base90 + (5623939/1250000000000000000000 : ℝ)*base92 + (5623939/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3257413519831854651931004817/489875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (551159881807017/50000000000000 : ℝ)*(major0) + (551159881807017/50000000000000 : ℝ)*(major1) + (551159881807017/50000000000000 : ℝ)*(major2) + (2351086037/50000000000000 : ℝ)*(sp1) + (7950580669/100000000000000 : ℝ)*(sp2) + (370838967/50000000000000 : ℝ)*(sp3) + (1466782759123091/100000000000000 : ℝ)*(sp4) + (733390813499941/50000000000000 : ℝ)*(sp5) + (146677878619103/10000000000000 : ℝ)*(sp6) + (368924980145357/50000000000000 : ℝ)*(sp7) + (398955589/10000000000000 : ℝ)*(sp8) + (26219189/6250000000000 : ℝ)*(sp9) + (11907281/100000000000000 : ℝ)*(sp10) + (927465567/50000000000000 : ℝ)*(sp11) + (368926278449891/50000000000000 : ℝ)*(f.failure) + (73339337433949/5000000000000 : ℝ)*(f.sum) + (3754821280009/9797500000000000000000000000 : ℝ)*base65 + (9052060711748121687/979750000000000000000000000000000 : ℝ)*base68 + (11224192454515621687/979750000000000000000000000000000 : ℝ)*base70 + (5136422260451371687/979750000000000000000000000000000 : ℝ)*base72 + (24958999585401/9797500000000000000000000000 : ℝ)*base74 + (4945139922697371687/979750000000000000000000000000000 : ℝ)*base76 + (4114900174394871687/979750000000000000000000000000000 : ℝ)*base78 + (4676519642144621687/979750000000000000000000000000000 : ℝ)*base80 + (18187298656727/19595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (48922079/5000000000000000000000 : ℝ)*base89 + (48922079/5000000000000000000000 : ℝ)*base91 + (48922079/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1138_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2783/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s2_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215148117/1000000000 : ℝ)*x 0 + (344472921/625000000 : ℝ)*x 1 + (1289614469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215148117/1000000000 : ℝ)^8331 ≤ (3259698248729/25000000000000 : ℝ)^6283 := by
    have hnat : (215148117 : ℕ)^8331*25000000000000^6283 ≤ 3259698248729^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215148117 1000000000 3259698248729 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344472921/625000000 : ℝ)^8331 ≤ (45388033567859/100000000000000 : ℝ)^6283 := by
    have hnat : (344472921 : ℕ)^8331*100000000000000^6283 ≤ 45388033567859^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344472921 625000000 45388033567859 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289614469/2500000000 : ℝ)^8331 ≤ (10393293354839/25000000000000 : ℝ)^6283 := by
    have hnat : (1289614469 : ℕ)^8331*25000000000000^6283 ≤ 10393293354839^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289614469 2500000000 10393293354839 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215148117/1000000000 : ℝ), (344472921/625000000 : ℝ), (1289614469/2500000000 : ℝ)] ![(3259698248729/25000000000000 : ℝ), (45388033567859/100000000000000 : ℝ), (10393293354839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215148117/1000000000 : ℝ)|^8331 ≤ (3259698248729/25000000000000 : ℝ)^6283
        have hw : |(-215148117/1000000000 : ℝ)|=(215148117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344472921/625000000 : ℝ)|^8331 ≤ (45388033567859/100000000000000 : ℝ)^6283
        have hw : |(344472921/625000000 : ℝ)|=(344472921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1289614469/2500000000 : ℝ)|^8331 ≤ (10393293354839/25000000000000 : ℝ)^6283
        have hw : |(1289614469/2500000000 : ℝ)|=(1289614469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074806909/2000000000 : ℝ)*x 0 + (-1167545593/5000000000 : ℝ)*x 1 + (5158459809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074806909/2000000000 : ℝ)^8331 ≤ (21946207484759/50000000000000 : ℝ)^6283 := by
    have hnat : (1074806909 : ℕ)^8331*50000000000000^6283 ≤ 21946207484759^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074806909 2000000000 21946207484759 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167545593/5000000000 : ℝ)^8331 ≤ (2906878187051/20000000000000 : ℝ)^6283 := by
    have hnat : (1167545593 : ℕ)^8331*20000000000000^6283 ≤ 2906878187051^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167545593 5000000000 2906878187051 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5158459809/10000000000 : ℝ)^8331 ≤ (8314638815157/20000000000000 : ℝ)^6283 := by
    have hnat : (5158459809 : ℕ)^8331*20000000000000^6283 ≤ 8314638815157^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158459809 10000000000 8314638815157 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074806909/2000000000 : ℝ), (-1167545593/5000000000 : ℝ), (5158459809/10000000000 : ℝ)] ![(21946207484759/50000000000000 : ℝ), (2906878187051/20000000000000 : ℝ), (8314638815157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074806909/2000000000 : ℝ)|^8331 ≤ (21946207484759/50000000000000 : ℝ)^6283
        have hw : |(1074806909/2000000000 : ℝ)|=(1074806909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1167545593/5000000000 : ℝ)|^8331 ≤ (2906878187051/20000000000000 : ℝ)^6283
        have hw : |(-1167545593/5000000000 : ℝ)|=(1167545593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5158459809/10000000000 : ℝ)|^8331 ≤ (8314638815157/20000000000000 : ℝ)^6283
        have hw : |(5158459809/10000000000 : ℝ)|=(5158459809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374034509/10000000000 : ℝ)*x 0 + (5158459727/10000000000 : ℝ)*x 1 + (-2335091339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374034509/10000000000 : ℝ)^8331 ≤ (43892414579647/100000000000000 : ℝ)^6283 := by
    have hnat : (5374034509 : ℕ)^8331*100000000000000^6283 ≤ 43892414579647^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374034509 10000000000 43892414579647 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158459727/10000000000 : ℝ)^8331 ≤ (10393298299879/25000000000000 : ℝ)^6283 := by
    have hnat : (5158459727 : ℕ)^8331*25000000000000^6283 ≤ 10393298299879^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158459727 10000000000 10393298299879 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2335091339/10000000000 : ℝ)^8331 ≤ (3633598049499/25000000000000 : ℝ)^6283 := by
    have hnat : (2335091339 : ℕ)^8331*25000000000000^6283 ≤ 3633598049499^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335091339 10000000000 3633598049499 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374034509/10000000000 : ℝ), (5158459727/10000000000 : ℝ), (-2335091339/10000000000 : ℝ)] ![(43892414579647/100000000000000 : ℝ), (10393298299879/25000000000000 : ℝ), (3633598049499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374034509/10000000000 : ℝ)|^8331 ≤ (43892414579647/100000000000000 : ℝ)^6283
        have hw : |(5374034509/10000000000 : ℝ)|=(5374034509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158459727/10000000000 : ℝ)|^8331 ≤ (10393298299879/25000000000000 : ℝ)^6283
        have hw : |(5158459727/10000000000 : ℝ)|=(5158459727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2335091339/10000000000 : ℝ)|^8331 ≤ (3633598049499/25000000000000 : ℝ)^6283
        have hw : |(-2335091339/10000000000 : ℝ)|=(2335091339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088608723/2500000000 : ℝ)*x 0 + (4017492451/10000000000 : ℝ)*x 1 + (589929711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088608723/2500000000 : ℝ)^8331 ≤ (16603834638683/50000000000000 : ℝ)^6283 := by
    have hnat : (1088608723 : ℕ)^8331*50000000000000^6283 ≤ 16603834638683^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088608723 2500000000 16603834638683 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4017492451/10000000000 : ℝ)^8331 ≤ (1492212553351/5000000000000 : ℝ)^6283 := by
    have hnat : (4017492451 : ℕ)^8331*5000000000000^6283 ≤ 1492212553351^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017492451 10000000000 1492212553351 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589929711/1250000000 : ℝ)^8331 ≤ (7389615927659/20000000000000 : ℝ)^6283 := by
    have hnat : (589929711 : ℕ)^8331*20000000000000^6283 ≤ 7389615927659^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589929711 1250000000 7389615927659 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088608723/2500000000 : ℝ), (4017492451/10000000000 : ℝ), (589929711/1250000000 : ℝ)] ![(16603834638683/50000000000000 : ℝ), (1492212553351/5000000000000 : ℝ), (7389615927659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088608723/2500000000 : ℝ)|^8331 ≤ (16603834638683/50000000000000 : ℝ)^6283
        have hw : |(1088608723/2500000000 : ℝ)|=(1088608723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4017492451/10000000000 : ℝ)|^8331 ≤ (1492212553351/5000000000000 : ℝ)^6283
        have hw : |(4017492451/10000000000 : ℝ)|=(4017492451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(589929711/1250000000 : ℝ)|^8331 ≤ (7389615927659/20000000000000 : ℝ)^6283
        have hw : |(589929711/1250000000 : ℝ)|=(589929711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151584917/10000000000 : ℝ)*x 0 + (5160899721/10000000000 : ℝ)*x 1 + (5509100313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151584917/10000000000 : ℝ)^8331 ≤ (651981334657/5000000000000 : ℝ)^6283 := by
    have hnat : (2151584917 : ℕ)^8331*5000000000000^6283 ≤ 651981334657^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151584917 10000000000 651981334657 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160899721/10000000000 : ℝ)^8331 ≤ (4159926948023/10000000000000 : ℝ)^6283 := by
    have hnat : (5160899721 : ℕ)^8331*10000000000000^6283 ≤ 4159926948023^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160899721 10000000000 4159926948023 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5509100313/10000000000 : ℝ)^8331 ≤ (45361103822021/100000000000000 : ℝ)^6283 := by
    have hnat : (5509100313 : ℕ)^8331*100000000000000^6283 ≤ 45361103822021^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509100313 10000000000 45361103822021 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151584917/10000000000 : ℝ), (5160899721/10000000000 : ℝ), (5509100313/10000000000 : ℝ)] ![(651981334657/5000000000000 : ℝ), (4159926948023/10000000000000 : ℝ), (45361103822021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151584917/10000000000 : ℝ)|^8331 ≤ (651981334657/5000000000000 : ℝ)^6283
        have hw : |(-2151584917/10000000000 : ℝ)|=(2151584917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160899721/10000000000 : ℝ)|^8331 ≤ (4159926948023/10000000000000 : ℝ)^6283
        have hw : |(5160899721/10000000000 : ℝ)|=(5160899721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5509100313/10000000000 : ℝ)|^8331 ≤ (45361103822021/100000000000000 : ℝ)^6283
        have hw : |(5509100313/10000000000 : ℝ)|=(5509100313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660558191/1250000000 : ℝ)*x 0 + (-1984448713/10000000000 : ℝ)*x 1 + (5509100953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660558191/1250000000 : ℝ)^8331 ≤ (21462524137303/50000000000000 : ℝ)^6283 := by
    have hnat : (660558191 : ℕ)^8331*50000000000000^6283 ≤ 21462524137303^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660558191 1250000000 21462524137303 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984448713/10000000000 : ℝ)^8331 ≤ (1464230112589/12500000000000 : ℝ)^6283 := by
    have hnat : (1984448713 : ℕ)^8331*12500000000000^6283 ≤ 1464230112589^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984448713 10000000000 1464230112589 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5509100953/10000000000 : ℝ)^8331 ≤ (45361110809379/100000000000000 : ℝ)^6283 := by
    have hnat : (5509100953 : ℕ)^8331*100000000000000^6283 ≤ 45361110809379^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509100953 10000000000 45361110809379 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660558191/1250000000 : ℝ), (-1984448713/10000000000 : ℝ), (5509100953/10000000000 : ℝ)] ![(21462524137303/50000000000000 : ℝ), (1464230112589/12500000000000 : ℝ), (45361110809379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660558191/1250000000 : ℝ)|^8331 ≤ (21462524137303/50000000000000 : ℝ)^6283
        have hw : |(660558191/1250000000 : ℝ)|=(660558191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984448713/10000000000 : ℝ)|^8331 ≤ (1464230112589/12500000000000 : ℝ)^6283
        have hw : |(-1984448713/10000000000 : ℝ)|=(1984448713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5509100953/10000000000 : ℝ)|^8331 ≤ (45361110809379/100000000000000 : ℝ)^6283
        have hw : |(5509100953/10000000000 : ℝ)|=(5509100953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284464097/10000000000 : ℝ)*x 0 + (5509100769/10000000000 : ℝ)*x 1 + (-1984450939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284464097/10000000000 : ℝ)^8331 ≤ (21462516430941/50000000000000 : ℝ)^6283 := by
    have hnat : (5284464097 : ℕ)^8331*50000000000000^6283 ≤ 21462516430941^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284464097 10000000000 21462516430941 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509100769/10000000000 : ℝ)^8331 ≤ (22680554400257/50000000000000 : ℝ)^6283 := by
    have hnat : (5509100769 : ℕ)^8331*50000000000000^6283 ≤ 22680554400257^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509100769 10000000000 22680554400257 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984450939/10000000000 : ℝ)^8331 ≤ (1464232290423/12500000000000 : ℝ)^6283 := by
    have hnat : (1984450939 : ℕ)^8331*12500000000000^6283 ≤ 1464232290423^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984450939 10000000000 1464232290423 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284464097/10000000000 : ℝ), (5509100769/10000000000 : ℝ), (-1984450939/10000000000 : ℝ)] ![(21462516430941/50000000000000 : ℝ), (22680554400257/50000000000000 : ℝ), (1464232290423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284464097/10000000000 : ℝ)|^8331 ≤ (21462516430941/50000000000000 : ℝ)^6283
        have hw : |(5284464097/10000000000 : ℝ)|=(5284464097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509100769/10000000000 : ℝ)|^8331 ≤ (22680554400257/50000000000000 : ℝ)^6283
        have hw : |(5509100769/10000000000 : ℝ)|=(5509100769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984450939/10000000000 : ℝ)|^8331 ≤ (1464232290423/12500000000000 : ℝ)^6283
        have hw : |(-1984450939/10000000000 : ℝ)|=(1984450939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s2_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272165023/625000000 : ℝ)*x 0 + (4714585153/10000000000 : ℝ)*x 1 + (4022393723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272165023/625000000 : ℝ)^8331 ≤ (1660487353239/5000000000000 : ℝ)^6283 := by
    have hnat : (272165023 : ℕ)^8331*5000000000000^6283 ≤ 1660487353239^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272165023 625000000 1660487353239 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4714585153/10000000000 : ℝ)^8331 ≤ (36897714785867/100000000000000 : ℝ)^6283 := by
    have hnat : (4714585153 : ℕ)^8331*100000000000000^6283 ≤ 36897714785867^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714585153 10000000000 36897714785867 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022393723/10000000000 : ℝ)^8331 ≤ (29892538132647/100000000000000 : ℝ)^6283 := by
    have hnat : (4022393723 : ℕ)^8331*100000000000000^6283 ≤ 29892538132647^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022393723 10000000000 29892538132647 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272165023/625000000 : ℝ), (4714585153/10000000000 : ℝ), (4022393723/10000000000 : ℝ)] ![(1660487353239/5000000000000 : ℝ), (36897714785867/100000000000000 : ℝ), (29892538132647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272165023/625000000 : ℝ)|^8331 ≤ (1660487353239/5000000000000 : ℝ)^6283
        have hw : |(272165023/625000000 : ℝ)|=(272165023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4714585153/10000000000 : ℝ)|^8331 ≤ (36897714785867/100000000000000 : ℝ)^6283
        have hw : |(4714585153/10000000000 : ℝ)|=(4714585153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022393723/10000000000 : ℝ)|^8331 ≤ (29892538132647/100000000000000 : ℝ)^6283
        have hw : |(4022393723/10000000000 : ℝ)|=(4022393723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8257/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5627/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (103230449241477/12500000000000000000 : ℝ) := by
    have hpowers : (5627/100000 : ℝ)^4165 ≤ (103230449241477/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5627 : ℕ)^4165*12500000000000000000^1024 ≤ 103230449241477^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5627 100000 103230449241477 12500000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5627/100000 : ℝ)) (X := (103230449241477/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/20000 : ℝ) ^ (4165/1024 : ℝ) ≤ (157310483608867249/100000000000000000000 : ℝ) := by
    have hpowers : (4091/20000 : ℝ)^4165 ≤ (157310483608867249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4165*100000000000000000000^1024 ≤ 157310483608867249^1024*20000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 20000 157310483608867249 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/20000 : ℝ)) (X := (157310483608867249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250103230449241477/6250000000000000000 : ℝ) ≤ (5000020303927333/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (6250103230449241477/6250000000000000000 : ℝ)^1024 ≤ (5000020303927333/5000000000000000 : ℝ)^4165 := by
      have hnat : (6250103230449241477 : ℕ)^1024*5000000000000000^4165 ≤ 5000020303927333^4165*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250103230449241477 6250000000000000000 5000020303927333 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020303927333/5000000000000000 : ℝ)) (X := (6250103230449241477/6250000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20031627265440559813/20000000000000000000 : ℝ) ≤ (500194279868789/500000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (20031627265440559813/20000000000000000000 : ℝ)^1024 ≤ (500194279868789/500000000000000 : ℝ)^4165 := by
      have hnat : (20031627265440559813 : ℕ)^1024*500000000000000^4165 ≤ 500194279868789^4165*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20031627265440559813 20000000000000000000 500194279868789 500000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500194279868789/500000000000000 : ℝ)) (X := (20031627265440559813/20000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50157310483608867249/50000000000000000000 : ℝ) ≤ (5003865293448447/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50157310483608867249/50000000000000000000 : ℝ)^1024 ≤ (5003865293448447/5000000000000000 : ℝ)^4165 := by
      have hnat : (50157310483608867249 : ℕ)^1024*5000000000000000^4165 ≤ 5003865293448447^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50157310483608867249 50000000000000000000 5003865293448447 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003865293448447/5000000000000000 : ℝ)) (X := (50157310483608867249/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103230449241477/12500000000000000000 : ℝ) ≤ ((37059332655299592623/37070000000000000000 : ℝ)+2*(1922494760557/741400000000000 : ℝ)*(5627/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (37059332655299592623/37070000000000000000 : ℝ)+2*(1922494760557/741400000000000 : ℝ)*(5627/100000 : ℝ)=(5000020303927333/5000000000000000 : ℝ) by norm_num, show 1+2*(103230449241477/12500000000000000000 : ℝ)=(6250103230449241477/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157310483608867249/100000000000000000000 : ℝ)+(103230449241477/12500000000000000000 : ℝ) ≤ ((37059332655299592623/37070000000000000000 : ℝ)+(1922494760557/741400000000000 : ℝ)*((4091/20000 : ℝ)+(5627/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (37059332655299592623/37070000000000000000 : ℝ)+(1922494760557/741400000000000 : ℝ)*((4091/20000 : ℝ)+(5627/100000 : ℝ))=(500194279868789/500000000000000 : ℝ) by norm_num, show 1+(157310483608867249/100000000000000000000 : ℝ)+(103230449241477/12500000000000000000 : ℝ)=(20031627265440559813/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157310483608867249/100000000000000000000 : ℝ) ≤ ((37059332655299592623/37070000000000000000 : ℝ)+2*(1922494760557/741400000000000 : ℝ)*(4091/20000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (37059332655299592623/37070000000000000000 : ℝ)+2*(1922494760557/741400000000000 : ℝ)*(4091/20000 : ℝ)=(5003865293448447/5000000000000000 : ℝ) by norm_num, show 1+2*(157310483608867249/100000000000000000000 : ℝ)=(50157310483608867249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37059332655299592623/37070000000000000000 : ℝ)*(X 1 0+X 2 0)+(1922494760557/741400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (5627/100000 : ℝ)) (hi := (4091/20000 : ℝ)) (c := (37059332655299592623/37070000000000000000 : ℝ)) (alpha := (1922494760557/741400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37059332655299592623/37070000000000000000 : ℝ)*(X 0 1+X 2 1)+(1922494760557/741400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (5627/100000 : ℝ)) (hi := (4091/20000 : ℝ)) (c := (37059332655299592623/37070000000000000000 : ℝ)) (alpha := (1922494760557/741400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37059332655299592623/37070000000000000000 : ℝ)*(X 0 2+X 1 2)+(1922494760557/741400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (5627/100000 : ℝ)) (hi := (4091/20000 : ℝ)) (c := (37059332655299592623/37070000000000000000 : ℝ)) (alpha := (1922494760557/741400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215148117/1000000000 : ℝ)*X 0 0+(344472921/625000000 : ℝ)*X 0 1+(1289614469/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074806909/2000000000 : ℝ)*X 1 0+(-1167545593/5000000000 : ℝ)*X 1 1+(5158459809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374034509/10000000000 : ℝ)*X 2 0+(5158459727/10000000000 : ℝ)*X 2 1+(-2335091339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088608723/2500000000 : ℝ)*X 0 0+(4017492451/10000000000 : ℝ)*X 0 1+(589929711/1250000000 : ℝ)*X 0 2+(1088608723/2500000000 : ℝ)*X 1 0+(4017492451/10000000000 : ℝ)*X 1 1+(589929711/1250000000 : ℝ)*X 1 2+(1088608723/2500000000 : ℝ)*X 2 0+(4017492451/10000000000 : ℝ)*X 2 1+(589929711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151584917/10000000000 : ℝ)*X 0 0+(5160899721/10000000000 : ℝ)*X 0 1+(5509100313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660558191/1250000000 : ℝ)*X 1 0+(-1984448713/10000000000 : ℝ)*X 1 1+(5509100953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284464097/10000000000 : ℝ)*X 2 0+(5509100769/10000000000 : ℝ)*X 2 1+(-1984450939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272165023/625000000 : ℝ)*X 0 0+(4714585153/10000000000 : ℝ)*X 0 1+(4022393723/10000000000 : ℝ)*X 0 2+(272165023/625000000 : ℝ)*X 1 0+(4714585153/10000000000 : ℝ)*X 1 1+(4022393723/10000000000 : ℝ)*X 1 2+(272165023/625000000 : ℝ)*X 2 0+(4714585153/10000000000 : ℝ)*X 2 1+(4022393723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4186278590084121874210427589/463375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (930665179/100000000000000 : ℝ)*(base19) + (125023823/20000000000000 : ℝ)*(base23) + (1189009/10000000000000 : ℝ)*(upper2) + (319730819/100000000000000 : ℝ)*(upper3) + (165896293/100000000000000 : ℝ)*(upper4) + (1064163902850881/50000000000000 : ℝ)*(major0) + (1064163902850881/50000000000000 : ℝ)*(major1) + (1064163902850881/50000000000000 : ℝ)*(major2) + (2832011129351169/100000000000000 : ℝ)*(sp0) + (2832029542778073/100000000000000 : ℝ)*(sp1) + (1416014924162069/50000000000000 : ℝ)*(sp2) + (11396937471007/800000000000 : ℝ)*(sp3) + (19344092083/100000000000000 : ℝ)*(sp4) + (7652940353/100000000000000 : ℝ)*(sp7) + (356156209204057/25000000000000 : ℝ)*(f.failure) + (708007618360813/25000000000000 : ℝ)*(f.sum) + (7336533445689/2316875000000000000000000000 : ℝ)*base65 + (79745626710999137/1853500000000000000000000000000000 : ℝ)*base68 + (475539015894499137/1853500000000000000000000000000000 : ℝ)*base70 + (3117651269658999137/1853500000000000000000000000000000 : ℝ)*base72 + (24190597772757/18535000000000000000000000000 : ℝ)*base73 + (10417500809586500863/1853500000000000000000000000000000 : ℝ)*base75 + (10270579227708499137/1853500000000000000000000000000000 : ℝ)*base78 + (7195085794707499137/1853500000000000000000000000000000 : ℝ)*base80 + (40679916750461/9267500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3029133/2500000000000000000000 : ℝ)*base89 + (3029133/2500000000000000000000 : ℝ)*base91 + (3029133/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71513102328329707977095067/16850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14066473/2500000000000 : ℝ)*(base19) + (170381157/100000000000000 : ℝ)*(base23) + (162922033/50000000000000 : ℝ)*(upper2) + (14663597/12500000000000 : ℝ)*(upper3) + (46599773/100000000000000 : ℝ)*(upper5) + (215829626487409/10000000000000 : ℝ)*(major0) + (215829626487409/10000000000000 : ℝ)*(major1) + (215829626487409/10000000000000 : ℝ)*(major2) + (4537269053/100000000000000 : ℝ)*(sp0) + (6819987847/50000000000000 : ℝ)*(sp1) + (1435951611526853/50000000000000 : ℝ)*(sp4) + (1435946778844073/50000000000000 : ℝ)*(sp5) + (1435953794970801/50000000000000 : ℝ)*(sp6) + (361171156988843/25000000000000 : ℝ)*(sp7) + (361171156988843/25000000000000 : ℝ)*(f.failure) + (71797694008069/2500000000000 : ℝ)*(f.sum) + (24941634161/2696000000000000000000000 : ℝ)*base66 + (370956282974039437/33700000000000000000000000000000 : ℝ)*base67 + (661533777689639437/33700000000000000000000000000000 : ℝ)*base69 + (50334204477239437/33700000000000000000000000000000 : ℝ)*base71 + (549672217/539200000000000000000000 : ℝ)*base73 + (111483584891039437/33700000000000000000000000000000 : ℝ)*base75 + (230019804816039437/33700000000000000000000000000000 : ℝ)*base77 + (391754072709239437/33700000000000000000000000000000 : ℝ)*base79 + (1376867023497/337000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (24479033/2500000000000000000000 : ℝ)*base90 + (24479033/2500000000000000000000 : ℝ)*base92 + (24479033/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1138_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1138_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1138_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1138_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1138_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

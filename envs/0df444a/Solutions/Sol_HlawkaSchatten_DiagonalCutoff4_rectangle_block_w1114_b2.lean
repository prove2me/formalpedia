-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:06:33.439158+00:00
-- url     : https://prove2.me/submissions/321d3a0f-2fa8-4f8f-821e-1e4cba41b54a

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
theorem support_rectangle_w1114_s6_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436063069/2000000000 : ℝ)*x 0 + (674242789/1250000000 : ℝ)*x 1 + (2632445673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436063069/2000000000 : ℝ)^8307 ≤ (13245763490101/100000000000000 : ℝ)^6259 := by
    have hnat : (436063069 : ℕ)^8307*100000000000000^6259 ≤ 13245763490101^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436063069 2000000000 13245763490101 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674242789/1250000000 : ℝ)^8307 ≤ (44074122405953/100000000000000 : ℝ)^6259 := by
    have hnat : (674242789 : ℕ)^8307*100000000000000^6259 ≤ 44074122405953^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674242789 1250000000 44074122405953 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632445673/5000000000 : ℝ)^8307 ≤ (1707204563349/4000000000000 : ℝ)^6259 := by
    have hnat : (2632445673 : ℕ)^8307*4000000000000^6259 ≤ 1707204563349^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632445673 5000000000 1707204563349 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436063069/2000000000 : ℝ), (674242789/1250000000 : ℝ), (2632445673/5000000000 : ℝ)] ![(13245763490101/100000000000000 : ℝ), (44074122405953/100000000000000 : ℝ), (1707204563349/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436063069/2000000000 : ℝ)|^8307 ≤ (13245763490101/100000000000000 : ℝ)^6259
        have hw : |(-436063069/2000000000 : ℝ)|=(436063069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674242789/1250000000 : ℝ)|^8307 ≤ (44074122405953/100000000000000 : ℝ)^6259
        have hw : |(674242789/1250000000 : ℝ)|=(674242789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632445673/5000000000 : ℝ)|^8307 ≤ (1707204563349/4000000000000 : ℝ)^6259
        have hw : |(2632445673/5000000000 : ℝ)|=(2632445673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334059691/625000000 : ℝ)*x 0 + (-2245785221/10000000000 : ℝ)*x 1 + (2632445673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334059691/625000000 : ℝ)^8307 ≤ (43543662388299/100000000000000 : ℝ)^6259 := by
    have hnat : (334059691 : ℕ)^8307*100000000000000^6259 ≤ 43543662388299^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334059691 625000000 43543662388299 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245785221/10000000000 : ℝ)^8307 ≤ (6888111757499/50000000000000 : ℝ)^6259 := by
    have hnat : (2245785221 : ℕ)^8307*50000000000000^6259 ≤ 6888111757499^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245785221 10000000000 6888111757499 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632445673/5000000000 : ℝ)^8307 ≤ (1707204563349/4000000000000 : ℝ)^6259 := by
    have hnat : (2632445673 : ℕ)^8307*4000000000000^6259 ≤ 1707204563349^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632445673 5000000000 1707204563349 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334059691/625000000 : ℝ), (-2245785221/10000000000 : ℝ), (2632445673/5000000000 : ℝ)] ![(43543662388299/100000000000000 : ℝ), (6888111757499/50000000000000 : ℝ), (1707204563349/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334059691/625000000 : ℝ)|^8307 ≤ (43543662388299/100000000000000 : ℝ)^6259
        have hw : |(334059691/625000000 : ℝ)|=(334059691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245785221/10000000000 : ℝ)|^8307 ≤ (6888111757499/50000000000000 : ℝ)^6259
        have hw : |(-2245785221/10000000000 : ℝ)|=(2245785221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632445673/5000000000 : ℝ)|^8307 ≤ (1707204563349/4000000000000 : ℝ)^6259
        have hw : |(2632445673/5000000000 : ℝ)|=(2632445673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344955059/10000000000 : ℝ)*x 0 + (5264891349/10000000000 : ℝ)*x 1 + (-2245785213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344955059/10000000000 : ℝ)^8307 ≤ (170092431331/390625000000 : ℝ)^6259 := by
    have hnat : (5344955059 : ℕ)^8307*390625000000^6259 ≤ 170092431331^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344955059 10000000000 170092431331 390625000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264891349/10000000000 : ℝ)^8307 ≤ (42680114116003/100000000000000 : ℝ)^6259 := by
    have hnat : (5264891349 : ℕ)^8307*100000000000000^6259 ≤ 42680114116003^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264891349 10000000000 42680114116003 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245785213/10000000000 : ℝ)^8307 ≤ (6888111724933/50000000000000 : ℝ)^6259 := by
    have hnat : (2245785213 : ℕ)^8307*50000000000000^6259 ≤ 6888111724933^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245785213 10000000000 6888111724933 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344955059/10000000000 : ℝ), (5264891349/10000000000 : ℝ), (-2245785213/10000000000 : ℝ)] ![(170092431331/390625000000 : ℝ), (42680114116003/100000000000000 : ℝ), (6888111724933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344955059/10000000000 : ℝ)|^8307 ≤ (170092431331/390625000000 : ℝ)^6259
        have hw : |(5344955059/10000000000 : ℝ)|=(5344955059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264891349/10000000000 : ℝ)|^8307 ≤ (42680114116003/100000000000000 : ℝ)^6259
        have hw : |(5264891349/10000000000 : ℝ)|=(5264891349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245785213/10000000000 : ℝ)|^8307 ≤ (6888111724933/50000000000000 : ℝ)^6259
        have hw : |(-2245785213/10000000000 : ℝ)|=(2245785213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (349489/800000 : ℝ)*x 0 + (33942511/80000000 : ℝ)*x 1 + (89962963/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349489/800000 : ℝ)^8307 ≤ (16658303012849/50000000000000 : ℝ)^6259 := by
    have hnat : (349489 : ℕ)^8307*50000000000000^6259 ≤ 16658303012849^6259*800000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349489 800000 16658303012849 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33942511/80000000 : ℝ)^8307 ≤ (32049339157137/100000000000000 : ℝ)^6259 := by
    have hnat : (33942511 : ℕ)^8307*100000000000000^6259 ≤ 32049339157137^6259*80000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33942511 80000000 32049339157137 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89962963/200000000 : ℝ)^8307 ≤ (34634054805701/100000000000000 : ℝ)^6259 := by
    have hnat : (89962963 : ℕ)^8307*100000000000000^6259 ≤ 34634054805701^6259*200000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89962963 200000000 34634054805701 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(349489/800000 : ℝ), (33942511/80000000 : ℝ), (89962963/200000000 : ℝ)] ![(16658303012849/50000000000000 : ℝ), (32049339157137/100000000000000 : ℝ), (34634054805701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(349489/800000 : ℝ)|^8307 ≤ (16658303012849/50000000000000 : ℝ)^6259
        have hw : |(349489/800000 : ℝ)|=(349489/800000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33942511/80000000 : ℝ)|^8307 ≤ (32049339157137/100000000000000 : ℝ)^6259
        have hw : |(33942511/80000000 : ℝ)|=(33942511/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89962963/200000000 : ℝ)|^8307 ≤ (34634054805701/100000000000000 : ℝ)^6259
        have hw : |(89962963/200000000 : ℝ)|=(89962963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180320421/10000000000 : ℝ)*x 0 + (2632608597/5000000000 : ℝ)*x 1 + (674201907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180320421/10000000000 : ℝ)^8307 ≤ (13245804417931/100000000000000 : ℝ)^6259 := by
    have hnat : (2180320421 : ℕ)^8307*100000000000000^6259 ≤ 13245804417931^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180320421 10000000000 13245804417931 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632608597/5000000000 : ℝ)^8307 ≤ (42683619946191/100000000000000 : ℝ)^6259 := by
    have hnat : (2632608597 : ℕ)^8307*100000000000000^6259 ≤ 42683619946191^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632608597 5000000000 42683619946191 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674201907/1250000000 : ℝ)^8307 ≤ (22035287812173/50000000000000 : ℝ)^6259 := by
    have hnat : (674201907 : ℕ)^8307*50000000000000^6259 ≤ 22035287812173^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674201907 1250000000 22035287812173 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180320421/10000000000 : ℝ), (2632608597/5000000000 : ℝ), (674201907/1250000000 : ℝ)] ![(13245804417931/100000000000000 : ℝ), (42683619946191/100000000000000 : ℝ), (22035287812173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180320421/10000000000 : ℝ)|^8307 ≤ (13245804417931/100000000000000 : ℝ)^6259
        have hw : |(-2180320421/10000000000 : ℝ)|=(2180320421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632608597/5000000000 : ℝ)|^8307 ≤ (42683619946191/100000000000000 : ℝ)^6259
        have hw : |(2632608597/5000000000 : ℝ)|=(2632608597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674201907/1250000000 : ℝ)|^8307 ≤ (22035287812173/50000000000000 : ℝ)^6259
        have hw : |(674201907/1250000000 : ℝ)|=(674201907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328082053/2500000000 : ℝ)*x 0 + (-2117061297/10000000000 : ℝ)*x 1 + (5393615221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328082053/2500000000 : ℝ)^8307 ≤ (21595621136783/50000000000000 : ℝ)^6259 := by
    have hnat : (1328082053 : ℕ)^8307*50000000000000^6259 ≤ 21595621136783^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328082053 2500000000 21595621136783 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117061297/10000000000 : ℝ)^8307 ≤ (12738182457903/100000000000000 : ℝ)^6259 := by
    have hnat : (2117061297 : ℕ)^8307*100000000000000^6259 ≤ 12738182457903^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117061297 10000000000 12738182457903 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393615221/10000000000 : ℝ)^8307 ≤ (4407057524479/10000000000000 : ℝ)^6259 := by
    have hnat : (5393615221 : ℕ)^8307*10000000000000^6259 ≤ 4407057524479^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393615221 10000000000 4407057524479 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328082053/2500000000 : ℝ), (-2117061297/10000000000 : ℝ), (5393615221/10000000000 : ℝ)] ![(21595621136783/50000000000000 : ℝ), (12738182457903/100000000000000 : ℝ), (4407057524479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328082053/2500000000 : ℝ)|^8307 ≤ (21595621136783/50000000000000 : ℝ)^6259
        have hw : |(1328082053/2500000000 : ℝ)|=(1328082053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117061297/10000000000 : ℝ)|^8307 ≤ (12738182457903/100000000000000 : ℝ)^6259
        have hw : |(-2117061297/10000000000 : ℝ)|=(2117061297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393615221/10000000000 : ℝ)|^8307 ≤ (4407057524479/10000000000000 : ℝ)^6259
        have hw : |(5393615221/10000000000 : ℝ)|=(5393615221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312328243/10000000000 : ℝ)*x 0 + (5393615169/10000000000 : ℝ)*x 1 + (-1058530663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312328243/10000000000 : ℝ)^8307 ≤ (21595621304039/50000000000000 : ℝ)^6259 := by
    have hnat : (5312328243 : ℕ)^8307*50000000000000^6259 ≤ 21595621304039^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312328243 10000000000 21595621304039 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393615169/10000000000 : ℝ)^8307 ≤ (22035287340439/50000000000000 : ℝ)^6259 := by
    have hnat : (5393615169 : ℕ)^8307*50000000000000^6259 ≤ 22035287340439^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393615169 10000000000 22035287340439 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058530663/5000000000 : ℝ)^8307 ≤ (796136418093/6250000000000 : ℝ)^6259 := by
    have hnat : (1058530663 : ℕ)^8307*6250000000000^6259 ≤ 796136418093^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058530663 5000000000 796136418093 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312328243/10000000000 : ℝ), (5393615169/10000000000 : ℝ), (-1058530663/5000000000 : ℝ)] ![(21595621304039/50000000000000 : ℝ), (22035287340439/50000000000000 : ℝ), (796136418093/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312328243/10000000000 : ℝ)|^8307 ≤ (21595621304039/50000000000000 : ℝ)^6259
        have hw : |(5312328243/10000000000 : ℝ)|=(5312328243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393615169/10000000000 : ℝ)|^8307 ≤ (22035287340439/50000000000000 : ℝ)^6259
        have hw : |(5393615169/10000000000 : ℝ)|=(5393615169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058530663/5000000000 : ℝ)|^8307 ≤ (796136418093/6250000000000 : ℝ)^6259
        have hw : |(-1058530663/5000000000 : ℝ)|=(1058530663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s6_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368622483/10000000000 : ℝ)*x 0 + (899500667/2000000000 : ℝ)*x 1 + (1060865257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368622483/10000000000 : ℝ)^8307 ≤ (33316707071371/100000000000000 : ℝ)^6259 := by
    have hnat : (4368622483 : ℕ)^8307*100000000000000^6259 ≤ 33316707071371^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368622483 10000000000 33316707071371 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899500667/2000000000 : ℝ)^8307 ≤ (34627465589017/100000000000000 : ℝ)^6259 := by
    have hnat : (899500667 : ℕ)^8307*100000000000000^6259 ≤ 34627465589017^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899500667 2000000000 34627465589017 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060865257/2500000000 : ℝ)^8307 ≤ (16027913663141/50000000000000 : ℝ)^6259 := by
    have hnat : (1060865257 : ℕ)^8307*50000000000000^6259 ≤ 16027913663141^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060865257 2500000000 16027913663141 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368622483/10000000000 : ℝ), (899500667/2000000000 : ℝ), (1060865257/2500000000 : ℝ)] ![(33316707071371/100000000000000 : ℝ), (34627465589017/100000000000000 : ℝ), (16027913663141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368622483/10000000000 : ℝ)|^8307 ≤ (33316707071371/100000000000000 : ℝ)^6259
        have hw : |(4368622483/10000000000 : ℝ)|=(4368622483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899500667/2000000000 : ℝ)|^8307 ≤ (34627465589017/100000000000000 : ℝ)^6259
        have hw : |(899500667/2000000000 : ℝ)|=(899500667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060865257/2500000000 : ℝ)|^8307 ≤ (16027913663141/50000000000000 : ℝ)^6259
        have hw : |(1060865257/2500000000 : ℝ)|=(1060865257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14041/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11273/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (14301799848944991/100000000000000000000 : ℝ) := by
    have hpowers : (11273/100000 : ℝ)^4153 ≤ (14301799848944991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11273 : ℕ)^4153*100000000000000000000^1024 ≤ 14301799848944991^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11273 100000 14301799848944991 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11273/100000 : ℝ)) (X := (14301799848944991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (35208137856220651/100000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^4153 ≤ (35208137856220651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14077 : ℕ)^4153*100000000000000000000^1024 ≤ 35208137856220651^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 35208137856220651 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (35208137856220651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014301799848944991/50000000000000000000 : ℝ) ≤ (5000352599692843/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50014301799848944991/50000000000000000000 : ℝ)^1024 ≤ (5000352599692843/5000000000000000 : ℝ)^4153 := by
      have hnat : (50014301799848944991 : ℕ)^1024*5000000000000000^4153 ≤ 5000352599692843^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014301799848944991 50000000000000000000 5000352599692843 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000352599692843/5000000000000000 : ℝ)) (X := (50014301799848944991/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024754968852582821/50000000000000000000 : ℝ) ≤ (2500305133175679/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50024754968852582821/50000000000000000000 : ℝ)^1024 ≤ (2500305133175679/2500000000000000 : ℝ)^4153 := by
      have hnat : (50024754968852582821 : ℕ)^1024*2500000000000000^4153 ≤ 2500305133175679^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024754968852582821 50000000000000000000 2500305133175679 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500305133175679/2500000000000000 : ℝ)) (X := (50024754968852582821/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035208137856220651/50000000000000000000 : ℝ) ≤ (5000867933009873/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50035208137856220651/50000000000000000000 : ℝ)^1024 ≤ (5000867933009873/5000000000000000 : ℝ)^4153 := by
      have hnat : (50035208137856220651 : ℕ)^1024*5000000000000000^4153 ≤ 5000867933009873^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035208137856220651 50000000000000000000 5000867933009873 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000867933009873/5000000000000000 : ℝ)) (X := (50035208137856220651/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14301799848944991/100000000000000000000 : ℝ) ≤ ((7007589668527926291/7010000000000000000 : ℝ)+2*(51533331703/28040000000000 : ℝ)*(11273/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (7007589668527926291/7010000000000000000 : ℝ)+2*(51533331703/28040000000000 : ℝ)*(11273/100000 : ℝ)=(5000352599692843/5000000000000000 : ℝ) by norm_num, show 1+2*(14301799848944991/100000000000000000000 : ℝ)=(50014301799848944991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35208137856220651/100000000000000000000 : ℝ)+(14301799848944991/100000000000000000000 : ℝ) ≤ ((7007589668527926291/7010000000000000000 : ℝ)+(51533331703/28040000000000 : ℝ)*((14077/100000 : ℝ)+(11273/100000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (7007589668527926291/7010000000000000000 : ℝ)+(51533331703/28040000000000 : ℝ)*((14077/100000 : ℝ)+(11273/100000 : ℝ))=(2500305133175679/2500000000000000 : ℝ) by norm_num, show 1+(35208137856220651/100000000000000000000 : ℝ)+(14301799848944991/100000000000000000000 : ℝ)=(50024754968852582821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35208137856220651/100000000000000000000 : ℝ) ≤ ((7007589668527926291/7010000000000000000 : ℝ)+2*(51533331703/28040000000000 : ℝ)*(14077/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (7007589668527926291/7010000000000000000 : ℝ)+2*(51533331703/28040000000000 : ℝ)*(14077/100000 : ℝ)=(5000867933009873/5000000000000000 : ℝ) by norm_num, show 1+2*(35208137856220651/100000000000000000000 : ℝ)=(50035208137856220651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7007589668527926291/7010000000000000000 : ℝ)*(X 1 0+X 2 0)+(51533331703/28040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (7007589668527926291/7010000000000000000 : ℝ)) (alpha := (51533331703/28040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7007589668527926291/7010000000000000000 : ℝ)*(X 0 1+X 2 1)+(51533331703/28040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (7007589668527926291/7010000000000000000 : ℝ)) (alpha := (51533331703/28040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7007589668527926291/7010000000000000000 : ℝ)*(X 0 2+X 1 2)+(51533331703/28040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (7007589668527926291/7010000000000000000 : ℝ)) (alpha := (51533331703/28040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436063069/2000000000 : ℝ)*X 0 0+(674242789/1250000000 : ℝ)*X 0 1+(2632445673/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334059691/625000000 : ℝ)*X 1 0+(-2245785221/10000000000 : ℝ)*X 1 1+(2632445673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344955059/10000000000 : ℝ)*X 2 0+(5264891349/10000000000 : ℝ)*X 2 1+(-2245785213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((349489/800000 : ℝ)*X 0 0+(33942511/80000000 : ℝ)*X 0 1+(89962963/200000000 : ℝ)*X 0 2+(349489/800000 : ℝ)*X 1 0+(33942511/80000000 : ℝ)*X 1 1+(89962963/200000000 : ℝ)*X 1 2+(349489/800000 : ℝ)*X 2 0+(33942511/80000000 : ℝ)*X 2 1+(89962963/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180320421/10000000000 : ℝ)*X 0 0+(2632608597/5000000000 : ℝ)*X 0 1+(674201907/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328082053/2500000000 : ℝ)*X 1 0+(-2117061297/10000000000 : ℝ)*X 1 1+(5393615221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312328243/10000000000 : ℝ)*X 2 0+(5393615169/10000000000 : ℝ)*X 2 1+(-1058530663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368622483/10000000000 : ℝ)*X 0 0+(899500667/2000000000 : ℝ)*X 0 1+(1060865257/2500000000 : ℝ)*X 0 2+(4368622483/10000000000 : ℝ)*X 1 0+(899500667/2000000000 : ℝ)*X 1 1+(1060865257/2500000000 : ℝ)*X 1 2+(4368622483/10000000000 : ℝ)*X 2 0+(899500667/2000000000 : ℝ)*X 2 1+(1060865257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1875514069738328793157443981/350500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1080759237/100000000000000 : ℝ)*(base19) + (1007159189/100000000000000 : ℝ)*(base23) + (41663573/100000000000000 : ℝ)*(lower2) + (67107931/50000000000000 : ℝ)*(upper3) + (89805341/100000000000000 : ℝ)*(upper5) + (5832700455877803/100000000000000 : ℝ)*(major0) + (5832700455877803/100000000000000 : ℝ)*(major1) + (5832700455877803/100000000000000 : ℝ)*(major2) + (774890661914723/10000000000000 : ℝ)*(sp0) + (3874467433733763/50000000000000 : ℝ)*(sp1) + (3874467470533787/50000000000000 : ℝ)*(sp2) + (1958224503242233/50000000000000 : ℝ)*(sp3) + (29329079533/100000000000000 : ℝ)*(sp4) + (15778678789/100000000000000 : ℝ)*(sp7) + (783292957032651/20000000000000 : ℝ)*(f.failure) + (7748935948226763/100000000000000 : ℝ)*(f.sum) + (4431952093779/1402000000000000000000000000 : ℝ)*base66 + (6881540981687268673/701000000000000000000000000000000 : ℝ)*base67 + (4654122739794268673/701000000000000000000000000000000 : ℝ)*base69 + (8528655224171268673/701000000000000000000000000000000 : ℝ)*base71 + (7370022954271/1402000000000000000000000000 : ℝ)*base73 + (3378020259226268673/701000000000000000000000000000000 : ℝ)*base75 + (7946699208238731327/701000000000000000000000000000000 : ℝ)*base78 + (7543168164276731327/701000000000000000000000000000000 : ℝ)*base80 + (6538652512951/1402000000000000000000000000 : ℝ)*base82 + (757389/250000000000000000000 : ℝ)*base90 + (757389/250000000000000000000 : ℝ)*base92 + (757389/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357043645810684352354054199/175250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320477119/50000000000000 : ℝ)*(base19) + (676956331/100000000000000 : ℝ)*(base23) + (1519617/25000000000000 : ℝ)*(upper2) + (6171047/20000000000000 : ℝ)*(upper3) + (86515421/100000000000000 : ℝ)*(upper5) + (5862316784157463/100000000000000 : ℝ)*(major0) + (5862316784157463/100000000000000 : ℝ)*(major1) + (5862316784157463/100000000000000 : ℝ)*(major2) + (184219099/1000000000000 : ℝ)*(sp1) + (15020843759/100000000000000 : ℝ)*(sp2) + (1947070583420847/25000000000000 : ℝ)*(sp4) + (7788263270819249/100000000000000 : ℝ)*(sp5) + (3894133317941649/50000000000000 : ℝ)*(sp6) + (393635116672023/10000000000000 : ℝ)*(sp7) + (393635116672023/10000000000000 : ℝ)*(f.failure) + (1947070583420847/25000000000000 : ℝ)*(f.sum) + (1973563363759/280400000000000000000000000 : ℝ)*base66 + (8673661797348190267/701000000000000000000000000000000 : ℝ)*base68 + (2406317632994190267/701000000000000000000000000000000 : ℝ)*base70 + (9074702464504190267/701000000000000000000000000000000 : ℝ)*base72 + (1059125254541/280400000000000000000000000 : ℝ)*base74 + (10451882049204809733/701000000000000000000000000000000 : ℝ)*base75 + (14217382174411190267/701000000000000000000000000000000 : ℝ)*base78 + (6848618799029190267/701000000000000000000000000000000 : ℝ)*base80 + (3241636219239/1402000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1209103/125000000000000000000 : ℝ)*base89 + (1209103/125000000000000000000 : ℝ)*base91 + (1209103/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1114_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s7_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43606909/200000000 : ℝ)*x 0 + (5393572689/10000000000 : ℝ)*x 1 + (263262067/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43606909/200000000 : ℝ)^8307 ≤ (13246006227423/100000000000000 : ℝ)^6259 := by
    have hnat : (43606909 : ℕ)^8307*100000000000000^6259 ≤ 13246006227423^6259*200000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43606909 200000000 13246006227423 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393572689/10000000000 : ℝ)^8307 ≤ (44070114008721/100000000000000 : ℝ)^6259 := by
    have hnat : (5393572689 : ℕ)^8307*100000000000000^6259 ≤ 44070114008721^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393572689 10000000000 44070114008721 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263262067/500000000 : ℝ)^8307 ≤ (533548496757/1250000000000 : ℝ)^6259 := by
    have hnat : (263262067 : ℕ)^8307*1250000000000^6259 ≤ 533548496757^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263262067 500000000 533548496757 1250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43606909/200000000 : ℝ), (5393572689/10000000000 : ℝ), (263262067/500000000 : ℝ)] ![(13246006227423/100000000000000 : ℝ), (44070114008721/100000000000000 : ℝ), (533548496757/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43606909/200000000 : ℝ)|^8307 ≤ (13246006227423/100000000000000 : ℝ)^6259
        have hw : |(-43606909/200000000 : ℝ)|=(43606909/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393572689/10000000000 : ℝ)|^8307 ≤ (44070114008721/100000000000000 : ℝ)^6259
        have hw : |(5393572689/10000000000 : ℝ)|=(5393572689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263262067/500000000 : ℝ)|^8307 ≤ (533548496757/1250000000000 : ℝ)^6259
        have hw : |(263262067/500000000 : ℝ)|=(263262067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344862937/10000000000 : ℝ)*x 0 + (-2245445019/10000000000 : ℝ)*x 1 + (2632620671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344862937/10000000000 : ℝ)^8307 ≤ (435426663681/1000000000000 : ℝ)^6259 := by
    have hnat : (5344862937 : ℕ)^8307*1000000000000^6259 ≤ 435426663681^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344862937 10000000000 435426663681 1000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245445019/10000000000 : ℝ)^8307 ≤ (3443363462379/25000000000000 : ℝ)^6259 := by
    have hnat : (2245445019 : ℕ)^8307*25000000000000^6259 ≤ 3443363462379^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245445019 10000000000 3443363462379 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632620671/5000000000 : ℝ)^8307 ≤ (42683879762079/100000000000000 : ℝ)^6259 := by
    have hnat : (2632620671 : ℕ)^8307*100000000000000^6259 ≤ 42683879762079^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632620671 5000000000 42683879762079 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344862937/10000000000 : ℝ), (-2245445019/10000000000 : ℝ), (2632620671/5000000000 : ℝ)] ![(435426663681/1000000000000 : ℝ), (3443363462379/25000000000000 : ℝ), (42683879762079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344862937/10000000000 : ℝ)|^8307 ≤ (435426663681/1000000000000 : ℝ)^6259
        have hw : |(5344862937/10000000000 : ℝ)|=(5344862937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245445019/10000000000 : ℝ)|^8307 ≤ (3443363462379/25000000000000 : ℝ)^6259
        have hw : |(-2245445019/10000000000 : ℝ)|=(2245445019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632620671/5000000000 : ℝ)|^8307 ≤ (42683879762079/100000000000000 : ℝ)^6259
        have hw : |(2632620671/5000000000 : ℝ)|=(2632620671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672431469/5000000000 : ℝ)*x 0 + (5265241343/10000000000 : ℝ)*x 1 + (-280680627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672431469/5000000000 : ℝ)^8307 ≤ (43542666378913/100000000000000 : ℝ)^6259 := by
    have hnat : (2672431469 : ℕ)^8307*100000000000000^6259 ≤ 43542666378913^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672431469 5000000000 43542666378913 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265241343/10000000000 : ℝ)^8307 ≤ (21341939886419/50000000000000 : ℝ)^6259 := by
    have hnat : (5265241343 : ℕ)^8307*50000000000000^6259 ≤ 21341939886419^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265241343 10000000000 21341939886419 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280680627/1250000000 : ℝ)^8307 ≤ (13773453825093/100000000000000 : ℝ)^6259 := by
    have hnat : (280680627 : ℕ)^8307*100000000000000^6259 ≤ 13773453825093^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280680627 1250000000 13773453825093 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672431469/5000000000 : ℝ), (5265241343/10000000000 : ℝ), (-280680627/1250000000 : ℝ)] ![(43542666378913/100000000000000 : ℝ), (21341939886419/50000000000000 : ℝ), (13773453825093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672431469/5000000000 : ℝ)|^8307 ≤ (43542666378913/100000000000000 : ℝ)^6259
        have hw : |(2672431469/5000000000 : ℝ)|=(2672431469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265241343/10000000000 : ℝ)|^8307 ≤ (21341939886419/50000000000000 : ℝ)^6259
        have hw : |(5265241343/10000000000 : ℝ)|=(5265241343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280680627/1250000000 : ℝ)|^8307 ≤ (13773453825093/100000000000000 : ℝ)^6259
        have hw : |(-280680627/1250000000 : ℝ)|=(280680627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546078857/1250000000 : ℝ)*x 0 + (4243523393/10000000000 : ℝ)*x 1 + (4497433851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546078857/1250000000 : ℝ)^8307 ≤ (16658395910523/50000000000000 : ℝ)^6259 := by
    have hnat : (546078857 : ℕ)^8307*50000000000000^6259 ≤ 16658395910523^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546078857 1250000000 16658395910523 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243523393/10000000000 : ℝ)^8307 ≤ (4007056574609/12500000000000 : ℝ)^6259 := by
    have hnat : (4243523393 : ℕ)^8307*12500000000000^6259 ≤ 4007056574609^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243523393 10000000000 4007056574609 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497433851/10000000000 : ℝ)^8307 ≤ (8656688891599/25000000000000 : ℝ)^6259 := by
    have hnat : (4497433851 : ℕ)^8307*25000000000000^6259 ≤ 8656688891599^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497433851 10000000000 8656688891599 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546078857/1250000000 : ℝ), (4243523393/10000000000 : ℝ), (4497433851/10000000000 : ℝ)] ![(16658395910523/50000000000000 : ℝ), (4007056574609/12500000000000 : ℝ), (8656688891599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546078857/1250000000 : ℝ)|^8307 ≤ (16658395910523/50000000000000 : ℝ)^6259
        have hw : |(546078857/1250000000 : ℝ)|=(546078857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243523393/10000000000 : ℝ)|^8307 ≤ (4007056574609/12500000000000 : ℝ)^6259
        have hw : |(4243523393/10000000000 : ℝ)|=(4243523393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497433851/10000000000 : ℝ)|^8307 ≤ (8656688891599/25000000000000 : ℝ)^6259
        have hw : |(4497433851/10000000000 : ℝ)|=(4497433851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180350407/10000000000 : ℝ)*x 0 + (658195453/1250000000 : ℝ)*x 1 + (5393249243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180350407/10000000000 : ℝ)^8307 ≤ (2649209239187/20000000000000 : ℝ)^6259 := by
    have hnat : (2180350407 : ℕ)^8307*20000000000000^6259 ≤ 2649209239187^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180350407 10000000000 2649209239187 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658195453/1250000000 : ℝ)^8307 ≤ (42687347332289/100000000000000 : ℝ)^6259 := by
    have hnat : (658195453 : ℕ)^8307*100000000000000^6259 ≤ 42687347332289^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658195453 1250000000 42687347332289 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393249243/10000000000 : ℝ)^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259 := by
    have hnat : (5393249243 : ℕ)^8307*100000000000000^6259 ≤ 44066606454279^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393249243 10000000000 44066606454279 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180350407/10000000000 : ℝ), (658195453/1250000000 : ℝ), (5393249243/10000000000 : ℝ)] ![(2649209239187/20000000000000 : ℝ), (42687347332289/100000000000000 : ℝ), (44066606454279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180350407/10000000000 : ℝ)|^8307 ≤ (2649209239187/20000000000000 : ℝ)^6259
        have hw : |(-2180350407/10000000000 : ℝ)|=(2180350407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658195453/1250000000 : ℝ)|^8307 ≤ (42687347332289/100000000000000 : ℝ)^6259
        have hw : |(658195453/1250000000 : ℝ)|=(658195453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393249243/10000000000 : ℝ)|^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259
        have hw : |(5393249243/10000000000 : ℝ)|=(5393249243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656208937/5000000000 : ℝ)*x 0 + (-1058718559/5000000000 : ℝ)*x 1 + (5393249243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656208937/5000000000 : ℝ)^8307 ≤ (43192209792953/100000000000000 : ℝ)^6259 := by
    have hnat : (2656208937 : ℕ)^8307*100000000000000^6259 ≤ 43192209792953^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656208937 5000000000 43192209792953 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058718559/5000000000 : ℝ)^8307 ≤ (127411837409/1000000000000 : ℝ)^6259 := by
    have hnat : (1058718559 : ℕ)^8307*1000000000000^6259 ≤ 127411837409^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058718559 5000000000 127411837409 1000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393249243/10000000000 : ℝ)^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259 := by
    have hnat : (5393249243 : ℕ)^8307*100000000000000^6259 ≤ 44066606454279^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393249243 10000000000 44066606454279 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656208937/5000000000 : ℝ), (-1058718559/5000000000 : ℝ), (5393249243/10000000000 : ℝ)] ![(43192209792953/100000000000000 : ℝ), (127411837409/1000000000000 : ℝ), (44066606454279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656208937/5000000000 : ℝ)|^8307 ≤ (43192209792953/100000000000000 : ℝ)^6259
        have hw : |(2656208937/5000000000 : ℝ)|=(2656208937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058718559/5000000000 : ℝ)|^8307 ≤ (127411837409/1000000000000 : ℝ)^6259
        have hw : |(-1058718559/5000000000 : ℝ)|=(1058718559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393249243/10000000000 : ℝ)|^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259
        have hw : |(5393249243/10000000000 : ℝ)|=(5393249243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656208937/5000000000 : ℝ)*x 0 + (5393249243/10000000000 : ℝ)*x 1 + (-1058718559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656208937/5000000000 : ℝ)^8307 ≤ (43192209792953/100000000000000 : ℝ)^6259 := by
    have hnat : (2656208937 : ℕ)^8307*100000000000000^6259 ≤ 43192209792953^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656208937 5000000000 43192209792953 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393249243/10000000000 : ℝ)^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259 := by
    have hnat : (5393249243 : ℕ)^8307*100000000000000^6259 ≤ 44066606454279^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393249243 10000000000 44066606454279 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058718559/5000000000 : ℝ)^8307 ≤ (127411837409/1000000000000 : ℝ)^6259 := by
    have hnat : (1058718559 : ℕ)^8307*1000000000000^6259 ≤ 127411837409^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058718559 5000000000 127411837409 1000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656208937/5000000000 : ℝ), (5393249243/10000000000 : ℝ), (-1058718559/5000000000 : ℝ)] ![(43192209792953/100000000000000 : ℝ), (44066606454279/100000000000000 : ℝ), (127411837409/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656208937/5000000000 : ℝ)|^8307 ≤ (43192209792953/100000000000000 : ℝ)^6259
        have hw : |(2656208937/5000000000 : ℝ)|=(2656208937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393249243/10000000000 : ℝ)|^8307 ≤ (44066606454279/100000000000000 : ℝ)^6259
        have hw : |(5393249243/10000000000 : ℝ)|=(5393249243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058718559/5000000000 : ℝ)|^8307 ≤ (127411837409/1000000000000 : ℝ)^6259
        have hw : |(-1058718559/5000000000 : ℝ)|=(1058718559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s7_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092160167/2500000000 : ℝ)*x 0 + (899359241/2000000000 : ℝ)*x 1 + (265260209/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092160167/2500000000 : ℝ)^8307 ≤ (33316891136031/100000000000000 : ℝ)^6259 := by
    have hnat : (1092160167 : ℕ)^8307*100000000000000^6259 ≤ 33316891136031^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092160167 2500000000 33316891136031 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899359241/2000000000 : ℝ)^8307 ≤ (17310119972497/50000000000000 : ℝ)^6259 := by
    have hnat : (899359241 : ℕ)^8307*50000000000000^6259 ≤ 17310119972497^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899359241 2000000000 17310119972497 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265260209/625000000 : ℝ)^8307 ≤ (32062868910089/100000000000000 : ℝ)^6259 := by
    have hnat : (265260209 : ℕ)^8307*100000000000000^6259 ≤ 32062868910089^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265260209 625000000 32062868910089 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092160167/2500000000 : ℝ), (899359241/2000000000 : ℝ), (265260209/625000000 : ℝ)] ![(33316891136031/100000000000000 : ℝ), (17310119972497/50000000000000 : ℝ), (32062868910089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092160167/2500000000 : ℝ)|^8307 ≤ (33316891136031/100000000000000 : ℝ)^6259
        have hw : |(1092160167/2500000000 : ℝ)|=(1092160167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899359241/2000000000 : ℝ)|^8307 ≤ (17310119972497/50000000000000 : ℝ)^6259
        have hw : |(899359241/2000000000 : ℝ)|=(899359241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265260209/625000000 : ℝ)|^8307 ≤ (32062868910089/100000000000000 : ℝ)^6259
        have hw : |(265260209/625000000 : ℝ)|=(265260209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/25000 : ℝ) ^ (4153/1024 : ℝ) ≤ (7241371219653969/50000000000000000000 : ℝ) := by
    have hpowers : (2827/25000 : ℝ)^4153 ≤ (7241371219653969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2827 : ℕ)^4153*50000000000000000000^1024 ≤ 7241371219653969^1024*25000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 25000 7241371219653969 50000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/25000 : ℝ)) (X := (7241371219653969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14041/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (8711097551706151/25000000000000000000 : ℝ) := by
    have hpowers : (14041/100000 : ℝ)^4153 ≤ (8711097551706151/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14041 : ℕ)^4153*25000000000000000000^1024 ≤ 8711097551706151^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14041 100000 8711097551706151 25000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14041/100000 : ℝ)) (X := (8711097551706151/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007241371219653969/25000000000000000000 : ℝ) ≤ (10000714120408539/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (25007241371219653969/25000000000000000000 : ℝ)^1024 ≤ (10000714120408539/10000000000000000 : ℝ)^4153 := by
      have hnat : (25007241371219653969 : ℕ)^1024*10000000000000000^4153 ≤ 10000714120408539^4153*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007241371219653969 25000000000000000000 10000714120408539 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714120408539/10000000000000000 : ℝ)) (X := (25007241371219653969/25000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024663566323066271/50000000000000000000 : ℝ) ≤ (2500304006744711/2500000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50024663566323066271/50000000000000000000 : ℝ)^1024 ≤ (2500304006744711/2500000000000000 : ℝ)^4153 := by
      have hnat : (50024663566323066271 : ℕ)^1024*2500000000000000^4153 ≤ 2500304006744711^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024663566323066271 50000000000000000000 2500304006744711 2500000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500304006744711/2500000000000000 : ℝ)) (X := (50024663566323066271/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508711097551706151/12500000000000000000 : ℝ) ≤ (10001717933549149/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (12508711097551706151/12500000000000000000 : ℝ)^1024 ≤ (10001717933549149/10000000000000000 : ℝ)^4153 := by
      have hnat : (12508711097551706151 : ℕ)^1024*10000000000000000^4153 ≤ 10001717933549149^4153*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508711097551706151 12500000000000000000 10001717933549149 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001717933549149/10000000000000000 : ℝ)) (X := (12508711097551706151/12500000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7241371219653969/50000000000000000000 : ℝ) ≤ ((27320600572082519207/27330000000000000000 : ℝ)+2*(100381314061/54660000000000 : ℝ)*(2827/25000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (27320600572082519207/27330000000000000000 : ℝ)+2*(100381314061/54660000000000 : ℝ)*(2827/25000 : ℝ)=(10000714120408539/10000000000000000 : ℝ) by norm_num, show 1+2*(7241371219653969/50000000000000000000 : ℝ)=(25007241371219653969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8711097551706151/25000000000000000000 : ℝ)+(7241371219653969/50000000000000000000 : ℝ) ≤ ((27320600572082519207/27330000000000000000 : ℝ)+(100381314061/54660000000000 : ℝ)*((14041/100000 : ℝ)+(2827/25000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (27320600572082519207/27330000000000000000 : ℝ)+(100381314061/54660000000000 : ℝ)*((14041/100000 : ℝ)+(2827/25000 : ℝ))=(2500304006744711/2500000000000000 : ℝ) by norm_num, show 1+(8711097551706151/25000000000000000000 : ℝ)+(7241371219653969/50000000000000000000 : ℝ)=(50024663566323066271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8711097551706151/25000000000000000000 : ℝ) ≤ ((27320600572082519207/27330000000000000000 : ℝ)+2*(100381314061/54660000000000 : ℝ)*(14041/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (27320600572082519207/27330000000000000000 : ℝ)+2*(100381314061/54660000000000 : ℝ)*(14041/100000 : ℝ)=(10001717933549149/10000000000000000 : ℝ) by norm_num, show 1+2*(8711097551706151/25000000000000000000 : ℝ)=(12508711097551706151/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27320600572082519207/27330000000000000000 : ℝ)*(X 1 0+X 2 0)+(100381314061/54660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (27320600572082519207/27330000000000000000 : ℝ)) (alpha := (100381314061/54660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27320600572082519207/27330000000000000000 : ℝ)*(X 0 1+X 2 1)+(100381314061/54660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (27320600572082519207/27330000000000000000 : ℝ)) (alpha := (100381314061/54660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27320600572082519207/27330000000000000000 : ℝ)*(X 0 2+X 1 2)+(100381314061/54660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (27320600572082519207/27330000000000000000 : ℝ)) (alpha := (100381314061/54660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43606909/200000000 : ℝ)*X 0 0+(5393572689/10000000000 : ℝ)*X 0 1+(263262067/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344862937/10000000000 : ℝ)*X 1 0+(-2245445019/10000000000 : ℝ)*X 1 1+(2632620671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672431469/5000000000 : ℝ)*X 2 0+(5265241343/10000000000 : ℝ)*X 2 1+(-280680627/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546078857/1250000000 : ℝ)*X 0 0+(4243523393/10000000000 : ℝ)*X 0 1+(4497433851/10000000000 : ℝ)*X 0 2+(546078857/1250000000 : ℝ)*X 1 0+(4243523393/10000000000 : ℝ)*X 1 1+(4497433851/10000000000 : ℝ)*X 1 2+(546078857/1250000000 : ℝ)*X 2 0+(4243523393/10000000000 : ℝ)*X 2 1+(4497433851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2180350407/10000000000 : ℝ)*X 0 0+(658195453/1250000000 : ℝ)*X 0 1+(5393249243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656208937/5000000000 : ℝ)*X 1 0+(-1058718559/5000000000 : ℝ)*X 1 1+(5393249243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656208937/5000000000 : ℝ)*X 2 0+(5393249243/10000000000 : ℝ)*X 2 1+(-1058718559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092160167/2500000000 : ℝ)*X 0 0+(899359241/2000000000 : ℝ)*X 0 1+(265260209/625000000 : ℝ)*X 0 2+(1092160167/2500000000 : ℝ)*X 1 0+(899359241/2000000000 : ℝ)*X 1 1+(265260209/625000000 : ℝ)*X 1 2+(1092160167/2500000000 : ℝ)*X 2 0+(899359241/2000000000 : ℝ)*X 2 1+(265260209/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2179473393530849635688232253/227750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (955361977/50000000000000 : ℝ)*(base19) + (1785183203/100000000000000 : ℝ)*(base23) + (67879053/100000000000000 : ℝ)*(lower2) + (15003051/6250000000000 : ℝ)*(upper3) + (150660547/100000000000000 : ℝ)*(upper5) + (2932721174139221/50000000000000 : ℝ)*(major0) + (2932721174139221/50000000000000 : ℝ)*(major1) + (2932721174139221/50000000000000 : ℝ)*(major2) + (7792382455286261/100000000000000 : ℝ)*(sp0) + (1948108146886981/25000000000000 : ℝ)*(sp1) + (311697308523547/4000000000000 : ℝ)*(sp2) + (393842175134327/10000000000000 : ℝ)*(sp3) + (3252686601/6250000000000 : ℝ)*(sp4) + (5625591099/20000000000000 : ℝ)*(sp7) + (1969224939649383/50000000000000 : ℝ)*(f.failure) + (3896217249135939/50000000000000 : ℝ)*(f.sum) + (401195893871/341625000000000000000000000 : ℝ)*base65 + (14009097403698017747/1366500000000000000000000000000000 : ℝ)*base67 + (12204420050478017747/1366500000000000000000000000000000 : ℝ)*base69 + (23139049073493017747/1366500000000000000000000000000000 : ℝ)*base71 + (2056503620141/546600000000000000000000000 : ℝ)*base73 + (47850461249591982253/1366500000000000000000000000000000 : ℝ)*base76 + (9725301467820017747/1366500000000000000000000000000000 : ℝ)*base77 + (18600692800649982253/1366500000000000000000000000000000 : ℝ)*base80 + (92016293077/10675781250000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5102063/625000000000000000000 : ℝ)*base89 + (5102063/625000000000000000000 : ℝ)*base91 + (5102063/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2217224028165761408545657593/227750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1791702107/100000000000000 : ℝ)*(base19) + (1947241749/100000000000000 : ℝ)*(base23) + (97722721/50000000000000 : ℝ)*(upper3) + (70779291/100000000000000 : ℝ)*(lower4) + (1243927/625000000000 : ℝ)*(upper5) + (2947511687442399/50000000000000 : ℝ)*(major0) + (2947511687442399/50000000000000 : ℝ)*(major1) + (2947511687442399/50000000000000 : ℝ)*(major2) + (2460578831/5000000000000 : ℝ)*(sp1) + (13215965441/25000000000000 : ℝ)*(sp2) + (313269354732181/4000000000000 : ℝ)*(sp4) + (7831682865025799/100000000000000 : ℝ)*(sp5) + (1957919764300253/25000000000000 : ℝ)*(sp6) + (3958312556953679/100000000000000 : ℝ)*(sp7) + (3958312556953679/100000000000000 : ℝ)*(f.failure) + (313269354732181/4000000000000 : ℝ)*(f.sum) + (1463889643941/911000000000000000000000000 : ℝ)*base66 + (5024107595808552531/455500000000000000000000000000000 : ℝ)*base67 + (3014501906349447469/455500000000000000000000000000000 : ℝ)*base70 + (238600496277947469/455500000000000000000000000000000 : ℝ)*base72 + (400017052063/911000000000000000000000000 : ℝ)*base73 + (785794894170447469/455500000000000000000000000000000 : ℝ)*base76 + (2455121278274947469/455500000000000000000000000000000 : ℝ)*base78 + (5605806436184552531/455500000000000000000000000000000 : ℝ)*base79 + (278218411447/91100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7929481/1250000000000000000000 : ℝ)*base90 + (7929481/1250000000000000000000 : ℝ)*base92 + (7929481/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1114_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1114_s8_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2180350631/10000000000 : ℝ)*x 0 + (337093817/625000000 : ℝ)*x 1 + (5265309641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180350631/10000000000 : ℝ)^8307 ≤ (6623024001029/50000000000000 : ℝ)^6259 := by
    have hnat : (2180350631 : ℕ)^8307*50000000000000^6259 ≤ 6623024001029^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180350631 10000000000 6623024001029 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337093817/625000000 : ℝ)^8307 ≤ (22034668682283/50000000000000 : ℝ)^6259 := by
    have hnat : (337093817 : ℕ)^8307*50000000000000^6259 ≤ 22034668682283^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337093817 625000000 22034668682283 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265309641/10000000000 : ℝ)^8307 ≤ (42684614614503/100000000000000 : ℝ)^6259 := by
    have hnat : (5265309641 : ℕ)^8307*100000000000000^6259 ≤ 42684614614503^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265309641 10000000000 42684614614503 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2180350631/10000000000 : ℝ), (337093817/625000000 : ℝ), (5265309641/10000000000 : ℝ)] ![(6623024001029/50000000000000 : ℝ), (22034668682283/50000000000000 : ℝ), (42684614614503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2180350631/10000000000 : ℝ)|^8307 ≤ (6623024001029/50000000000000 : ℝ)^6259
        have hw : |(-2180350631/10000000000 : ℝ)|=(2180350631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337093817/625000000 : ℝ)|^8307 ≤ (22034668682283/50000000000000 : ℝ)^6259
        have hw : |(337093817/625000000 : ℝ)|=(337093817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265309641/10000000000 : ℝ)|^8307 ≤ (42684614614503/100000000000000 : ℝ)^6259
        have hw : |(5265309641/10000000000 : ℝ)|=(5265309641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344845213/10000000000 : ℝ)*x 0 + (-2245378193/10000000000 : ℝ)*x 1 + (5265309717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344845213/10000000000 : ℝ)^8307 ≤ (43542474731167/100000000000000 : ℝ)^6259 := by
    have hnat : (5344845213 : ℕ)^8307*100000000000000^6259 ≤ 43542474731167^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344845213 10000000000 43542474731167 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245378193/10000000000 : ℝ)^8307 ≤ (13772909819273/100000000000000 : ℝ)^6259 := by
    have hnat : (2245378193 : ℕ)^8307*100000000000000^6259 ≤ 13772909819273^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245378193 10000000000 13772909819273 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265309717/10000000000 : ℝ)^8307 ≤ (21342307716107/50000000000000 : ℝ)^6259 := by
    have hnat : (5265309717 : ℕ)^8307*50000000000000^6259 ≤ 21342307716107^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265309717 10000000000 21342307716107 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344845213/10000000000 : ℝ), (-2245378193/10000000000 : ℝ), (5265309717/10000000000 : ℝ)] ![(43542474731167/100000000000000 : ℝ), (13772909819273/100000000000000 : ℝ), (21342307716107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344845213/10000000000 : ℝ)|^8307 ≤ (43542474731167/100000000000000 : ℝ)^6259
        have hw : |(5344845213/10000000000 : ℝ)|=(5344845213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245378193/10000000000 : ℝ)|^8307 ≤ (13772909819273/100000000000000 : ℝ)^6259
        have hw : |(-2245378193/10000000000 : ℝ)|=(2245378193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265309717/10000000000 : ℝ)|^8307 ≤ (21342307716107/50000000000000 : ℝ)^6259
        have hw : |(5265309717/10000000000 : ℝ)|=(5265309717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068969061/2000000000 : ℝ)*x 0 + (263265481/500000000 : ℝ)*x 1 + (-2245378199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068969061/2000000000 : ℝ)^8307 ≤ (43542475725897/100000000000000 : ℝ)^6259 := by
    have hnat : (1068969061 : ℕ)^8307*100000000000000^6259 ≤ 43542475725897^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068969061 2000000000 43542475725897 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263265481/500000000 : ℝ)^8307 ≤ (10671153597139/25000000000000 : ℝ)^6259 := by
    have hnat : (263265481 : ℕ)^8307*25000000000000^6259 ≤ 10671153597139^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263265481 500000000 10671153597139 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245378199/10000000000 : ℝ)^8307 ≤ (6886454934059/50000000000000 : ℝ)^6259 := by
    have hnat : (2245378199 : ℕ)^8307*50000000000000^6259 ≤ 6886454934059^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245378199 10000000000 6886454934059 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068969061/2000000000 : ℝ), (263265481/500000000 : ℝ), (-2245378199/10000000000 : ℝ)] ![(43542475725897/100000000000000 : ℝ), (10671153597139/25000000000000 : ℝ), (6886454934059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068969061/2000000000 : ℝ)|^8307 ≤ (43542475725897/100000000000000 : ℝ)^6259
        have hw : |(1068969061/2000000000 : ℝ)|=(1068969061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263265481/500000000 : ℝ)|^8307 ≤ (10671153597139/25000000000000 : ℝ)^6259
        have hw : |(263265481/500000000 : ℝ)|=(263265481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245378199/10000000000 : ℝ)|^8307 ≤ (6886454934059/50000000000000 : ℝ)^6259
        have hw : |(-2245378199/10000000000 : ℝ)|=(2245378199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184317211/5000000000 : ℝ)*x 0 + (33949291/80000000 : ℝ)*x 1 + (2248647467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184317211/5000000000 : ℝ)^8307 ≤ (16658413957667/50000000000000 : ℝ)^6259 := by
    have hnat : (2184317211 : ℕ)^8307*50000000000000^6259 ≤ 16658413957667^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184317211 5000000000 16658413957667 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33949291/80000000 : ℝ)^8307 ≤ (32057836013099/100000000000000 : ℝ)^6259 := by
    have hnat : (33949291 : ℕ)^8307*100000000000000^6259 ≤ 32057836013099^6259*80000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33949291 80000000 32057836013099 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248647467/5000000000 : ℝ)^8307 ≤ (34625336053061/100000000000000 : ℝ)^6259 := by
    have hnat : (2248647467 : ℕ)^8307*100000000000000^6259 ≤ 34625336053061^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248647467 5000000000 34625336053061 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184317211/5000000000 : ℝ), (33949291/80000000 : ℝ), (2248647467/5000000000 : ℝ)] ![(16658413957667/50000000000000 : ℝ), (32057836013099/100000000000000 : ℝ), (34625336053061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184317211/5000000000 : ℝ)|^8307 ≤ (16658413957667/50000000000000 : ℝ)^6259
        have hw : |(2184317211/5000000000 : ℝ)|=(2184317211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33949291/80000000 : ℝ)|^8307 ≤ (32057836013099/100000000000000 : ℝ)^6259
        have hw : |(33949291/80000000 : ℝ)|=(33949291/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248647467/5000000000 : ℝ)|^8307 ≤ (34625336053061/100000000000000 : ℝ)^6259
        have hw : |(2248647467/5000000000 : ℝ)|=(2248647467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090177707/5000000000 : ℝ)*x 0 + (1316407833/2500000000 : ℝ)*x 1 + (5393178341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090177707/5000000000 : ℝ)^8307 ≤ (1324608656763/10000000000000 : ℝ)^6259 := by
    have hnat : (1090177707 : ℕ)^8307*10000000000000^6259 ≤ 1324608656763^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090177707 5000000000 1324608656763 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316407833/2500000000 : ℝ)^8307 ≤ (42688075840517/100000000000000 : ℝ)^6259 := by
    have hnat : (1316407833 : ℕ)^8307*100000000000000^6259 ≤ 42688075840517^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316407833 2500000000 42688075840517 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393178341/10000000000 : ℝ)^8307 ≤ (44065837578949/100000000000000 : ℝ)^6259 := by
    have hnat : (5393178341 : ℕ)^8307*100000000000000^6259 ≤ 44065837578949^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393178341 10000000000 44065837578949 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090177707/5000000000 : ℝ), (1316407833/2500000000 : ℝ), (5393178341/10000000000 : ℝ)] ![(1324608656763/10000000000000 : ℝ), (42688075840517/100000000000000 : ℝ), (44065837578949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090177707/5000000000 : ℝ)|^8307 ≤ (1324608656763/10000000000000 : ℝ)^6259
        have hw : |(-1090177707/5000000000 : ℝ)|=(1090177707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316407833/2500000000 : ℝ)|^8307 ≤ (42688075840517/100000000000000 : ℝ)^6259
        have hw : |(1316407833/2500000000 : ℝ)|=(1316407833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393178341/10000000000 : ℝ)|^8307 ≤ (44065837578949/100000000000000 : ℝ)^6259
        have hw : |(5393178341/10000000000 : ℝ)|=(5393178341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328108833/2500000000 : ℝ)*x 0 + (-1058755077/5000000000 : ℝ)*x 1 + (1348294521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328108833/2500000000 : ℝ)^8307 ≤ (1727695927133/4000000000000 : ℝ)^6259 := by
    have hnat : (1328108833 : ℕ)^8307*4000000000000^6259 ≤ 1727695927133^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328108833 2500000000 1727695927133 4000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058755077/5000000000 : ℝ)^8307 ≤ (12741767022057/100000000000000 : ℝ)^6259 := by
    have hnat : (1058755077 : ℕ)^8307*100000000000000^6259 ≤ 12741767022057^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058755077 5000000000 12741767022057 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348294521/2500000000 : ℝ)^8307 ≤ (11016458697999/25000000000000 : ℝ)^6259 := by
    have hnat : (1348294521 : ℕ)^8307*25000000000000^6259 ≤ 11016458697999^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348294521 2500000000 11016458697999 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328108833/2500000000 : ℝ), (-1058755077/5000000000 : ℝ), (1348294521/2500000000 : ℝ)] ![(1727695927133/4000000000000 : ℝ), (12741767022057/100000000000000 : ℝ), (11016458697999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328108833/2500000000 : ℝ)|^8307 ≤ (1727695927133/4000000000000 : ℝ)^6259
        have hw : |(1328108833/2500000000 : ℝ)|=(1328108833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058755077/5000000000 : ℝ)|^8307 ≤ (12741767022057/100000000000000 : ℝ)^6259
        have hw : |(-1058755077/5000000000 : ℝ)|=(1058755077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348294521/2500000000 : ℝ)|^8307 ≤ (11016458697999/25000000000000 : ℝ)^6259
        have hw : |(1348294521/2500000000 : ℝ)|=(1348294521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312436047/10000000000 : ℝ)*x 0 + (1348294531/2500000000 : ℝ)*x 1 + (-2117509133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312436047/10000000000 : ℝ)^8307 ≤ (21596202946867/50000000000000 : ℝ)^6259 := by
    have hnat : (5312436047 : ℕ)^8307*50000000000000^6259 ≤ 21596202946867^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312436047 10000000000 21596202946867 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348294531/2500000000 : ℝ)^8307 ≤ (44065835225763/100000000000000 : ℝ)^6259 := by
    have hnat : (1348294531 : ℕ)^8307*100000000000000^6259 ≤ 44065835225763^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348294531 2500000000 44065835225763 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117509133/10000000000 : ℝ)^8307 ≤ (12741758868087/100000000000000 : ℝ)^6259 := by
    have hnat : (2117509133 : ℕ)^8307*100000000000000^6259 ≤ 12741758868087^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117509133 10000000000 12741758868087 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312436047/10000000000 : ℝ), (1348294531/2500000000 : ℝ), (-2117509133/10000000000 : ℝ)] ![(21596202946867/50000000000000 : ℝ), (44065835225763/100000000000000 : ℝ), (12741758868087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312436047/10000000000 : ℝ)|^8307 ≤ (21596202946867/50000000000000 : ℝ)^6259
        have hw : |(5312436047/10000000000 : ℝ)|=(5312436047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348294531/2500000000 : ℝ)|^8307 ≤ (44065835225763/100000000000000 : ℝ)^6259
        have hw : |(1348294531/2500000000 : ℝ)|=(1348294531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117509133/10000000000 : ℝ)|^8307 ≤ (12741758868087/100000000000000 : ℝ)^6259
        have hw : |(-2117509133/10000000000 : ℝ)|=(2117509133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_s8_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184322371/5000000000 : ℝ)*x 0 + (4496658547/10000000000 : ℝ)*x 1 + (4244299517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184322371/5000000000 : ℝ)^8307 ≤ (16658466186109/50000000000000 : ℝ)^6259 := by
    have hnat : (2184322371 : ℕ)^8307*50000000000000^6259 ≤ 16658466186109^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184322371 5000000000 16658466186109 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496658547/10000000000 : ℝ)^8307 ≤ (540919271279/1562500000000 : ℝ)^6259 := by
    have hnat : (4496658547 : ℕ)^8307*1562500000000^6259 ≤ 540919271279^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496658547 10000000000 540919271279 1562500000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244299517/10000000000 : ℝ)^8307 ≤ (16032117128219/50000000000000 : ℝ)^6259 := by
    have hnat : (4244299517 : ℕ)^8307*50000000000000^6259 ≤ 16032117128219^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244299517 10000000000 16032117128219 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184322371/5000000000 : ℝ), (4496658547/10000000000 : ℝ), (4244299517/10000000000 : ℝ)] ![(16658466186109/50000000000000 : ℝ), (540919271279/1562500000000 : ℝ), (16032117128219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184322371/5000000000 : ℝ)|^8307 ≤ (16658466186109/50000000000000 : ℝ)^6259
        have hw : |(2184322371/5000000000 : ℝ)|=(2184322371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496658547/10000000000 : ℝ)|^8307 ≤ (540919271279/1562500000000 : ℝ)^6259
        have hw : |(4496658547/10000000000 : ℝ)|=(4496658547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244299517/10000000000 : ℝ)|^8307 ≤ (16032117128219/50000000000000 : ℝ)^6259
        have hw : |(4244299517/10000000000 : ℝ)|=(4244299517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11317/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (877/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/20000 : ℝ) ^ (4153/1024 : ℝ) ≤ (290382738768599/2000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^4153 ≤ (290382738768599/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^4153*2000000000000000000^1024 ≤ 290382738768599^1024*20000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 290382738768599 2000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (290382738768599/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (4153/1024 : ℝ) ≤ (34773991604804571/100000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^4153 ≤ (34773991604804571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7017 : ℕ)^4153*100000000000000000000^1024 ≤ 34773991604804571^1024*50000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 34773991604804571 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (34773991604804571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000290382738768599/1000000000000000000 : ℝ) ≤ (10000715914765667/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (1000290382738768599/1000000000000000000 : ℝ)^1024 ≤ (10000715914765667/10000000000000000 : ℝ)^4153 := by
      have hnat : (1000290382738768599 : ℕ)^1024*10000000000000000^4153 ≤ 10000715914765667^4153*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000290382738768599 1000000000000000000 10000715914765667 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000715914765667/10000000000000000 : ℝ)) (X := (1000290382738768599/1000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049293128543234521/100000000000000000000 : ℝ) ≤ (1250151898606913/1250000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (100049293128543234521/100000000000000000000 : ℝ)^1024 ≤ (1250151898606913/1250000000000000 : ℝ)^4153 := by
      have hnat : (100049293128543234521 : ℕ)^1024*1250000000000000^4153 ≤ 1250151898606913^4153*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049293128543234521 100000000000000000000 1250151898606913 1250000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151898606913/1250000000000000 : ℝ)) (X := (100049293128543234521/100000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034773991604804571/50000000000000000000 : ℝ) ≤ (10001714462944941/10000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50034773991604804571/50000000000000000000 : ℝ)^1024 ≤ (10001714462944941/10000000000000000 : ℝ)^4153 := by
      have hnat : (50034773991604804571 : ℕ)^1024*10000000000000000^4153 ≤ 10001714462944941^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034773991604804571 50000000000000000000 10001714462944941 10000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001714462944941/10000000000000000 : ℝ)) (X := (50034773991604804571/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(290382738768599/2000000000000000000 : ℝ) ≤ ((27180647999599363263/27190000000000000000 : ℝ)+2*(499274089637/271900000000000 : ℝ)*(2263/20000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (27180647999599363263/27190000000000000000 : ℝ)+2*(499274089637/271900000000000 : ℝ)*(2263/20000 : ℝ)=(10000715914765667/10000000000000000 : ℝ) by norm_num, show 1+2*(290382738768599/2000000000000000000 : ℝ)=(1000290382738768599/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34773991604804571/100000000000000000000 : ℝ)+(290382738768599/2000000000000000000 : ℝ) ≤ ((27180647999599363263/27190000000000000000 : ℝ)+(499274089637/271900000000000 : ℝ)*((7017/50000 : ℝ)+(2263/20000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (27180647999599363263/27190000000000000000 : ℝ)+(499274089637/271900000000000 : ℝ)*((7017/50000 : ℝ)+(2263/20000 : ℝ))=(1250151898606913/1250000000000000 : ℝ) by norm_num, show 1+(34773991604804571/100000000000000000000 : ℝ)+(290382738768599/2000000000000000000 : ℝ)=(100049293128543234521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34773991604804571/100000000000000000000 : ℝ) ≤ ((27180647999599363263/27190000000000000000 : ℝ)+2*(499274089637/271900000000000 : ℝ)*(7017/50000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (27180647999599363263/27190000000000000000 : ℝ)+2*(499274089637/271900000000000 : ℝ)*(7017/50000 : ℝ)=(10001714462944941/10000000000000000 : ℝ) by norm_num, show 1+2*(34773991604804571/100000000000000000000 : ℝ)=(50034773991604804571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27180647999599363263/27190000000000000000 : ℝ)*(X 1 0+X 2 0)+(499274089637/271900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27180647999599363263/27190000000000000000 : ℝ)) (alpha := (499274089637/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27180647999599363263/27190000000000000000 : ℝ)*(X 0 1+X 2 1)+(499274089637/271900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27180647999599363263/27190000000000000000 : ℝ)) (alpha := (499274089637/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27180647999599363263/27190000000000000000 : ℝ)*(X 0 2+X 1 2)+(499274089637/271900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27180647999599363263/27190000000000000000 : ℝ)) (alpha := (499274089637/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2180350631/10000000000 : ℝ)*X 0 0+(337093817/625000000 : ℝ)*X 0 1+(5265309641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344845213/10000000000 : ℝ)*X 1 0+(-2245378193/10000000000 : ℝ)*X 1 1+(5265309717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068969061/2000000000 : ℝ)*X 2 0+(263265481/500000000 : ℝ)*X 2 1+(-2245378199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184317211/5000000000 : ℝ)*X 0 0+(33949291/80000000 : ℝ)*X 0 1+(2248647467/5000000000 : ℝ)*X 0 2+(2184317211/5000000000 : ℝ)*X 1 0+(33949291/80000000 : ℝ)*X 1 1+(2248647467/5000000000 : ℝ)*X 1 2+(2184317211/5000000000 : ℝ)*X 2 0+(33949291/80000000 : ℝ)*X 2 1+(2248647467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090177707/5000000000 : ℝ)*X 0 0+(1316407833/2500000000 : ℝ)*X 0 1+(5393178341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328108833/2500000000 : ℝ)*X 1 0+(-1058755077/5000000000 : ℝ)*X 1 1+(1348294521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312436047/10000000000 : ℝ)*X 2 0+(1348294531/2500000000 : ℝ)*X 2 1+(-2117509133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184322371/5000000000 : ℝ)*X 0 0+(4496658547/10000000000 : ℝ)*X 0 1+(4244299517/10000000000 : ℝ)*X 0 2+(2184322371/5000000000 : ℝ)*X 1 0+(4496658547/10000000000 : ℝ)*X 1 1+(4244299517/10000000000 : ℝ)*X 1 2+(2184322371/5000000000 : ℝ)*X 2 0+(4496658547/10000000000 : ℝ)*X 2 1+(4244299517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48989991800185737263319327/10621093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (207959467/25000000000000 : ℝ)*(base19) + (873993241/100000000000000 : ℝ)*(base23) + (49236747/100000000000000 : ℝ)*(lower2) + (115057261/100000000000000 : ℝ)*(upper3) + (31150041/50000000000000 : ℝ)*(upper5) + (91746932959387/1562500000000 : ℝ)*(major0) + (91746932959387/1562500000000 : ℝ)*(major1) + (91746932959387/1562500000000 : ℝ)*(major2) + (1560171900667219/20000000000000 : ℝ)*(sp0) + (3900442555518177/50000000000000 : ℝ)*(sp1) + (390044253444049/5000000000000 : ℝ)*(sp2) + (3942707455352837/100000000000000 : ℝ)*(sp3) + (26439538127/100000000000000 : ℝ)*(sp4) + (1733352981/12500000000000 : ℝ)*(sp7) + (788544264435337/20000000000000 : ℝ)*(f.failure) + (7800885942874221/100000000000000 : ℝ)*(f.sum) + (25374657459449/13595000000000000000000000000 : ℝ)*base66 + (171374083696328961/10621093750000000000000000000000 : ℝ)*base68 + (605341898908425219/42484375000000000000000000000000 : ℝ)*base70 + (105879759109425219/42484375000000000000000000000000 : ℝ)*base72 + (36897840664139/13595000000000000000000000000 : ℝ)*base74 + (1599882110828800219/42484375000000000000000000000000 : ℝ)*base76 + (420728297063518969/42484375000000000000000000000000 : ℝ)*base78 + (15487806625382917/1327636718750000000000000000000 : ℝ)*base80 + (13696574458793/6797500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (613857/250000000000000000000 : ℝ)*base89 + (613857/250000000000000000000 : ℝ)*base91 + (613857/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2683388445593945390147770569/679750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890673607/100000000000000 : ℝ)*(base19) + (788775361/50000000000000 : ℝ)*(base23) + (47988891/12500000000000 : ℝ)*(lower2) + (52205671/25000000000000 : ℝ)*(upper3) + (9124413/25000000000000 : ℝ)*(upper5) + (2950721978905007/50000000000000 : ℝ)*(major0) + (2950721978905007/50000000000000 : ℝ)*(major1) + (2950721978905007/50000000000000 : ℝ)*(major2) + (29039755591/50000000000000 : ℝ)*(sp2) + (264061367/100000000000000 : ℝ)*(sp3) + (3920132009363079/50000000000000 : ℝ)*(sp4) + (7840263128052551/100000000000000 : ℝ)*(sp5) + (3920102180832127/50000000000000 : ℝ)*(sp6) + (1981311750622733/50000000000000 : ℝ)*(sp7) + (1981311882653417/50000000000000 : ℝ)*(f.failure) + (3920132009363079/50000000000000 : ℝ)*(f.sum) + (1555728359959/424843750000000000000000000 : ℝ)*base65 + (23266758510480042159/1359500000000000000000000000000000 : ℝ)*base68 + (2513608440382542159/1359500000000000000000000000000000 : ℝ)*base70 + (40496064446382542159/1359500000000000000000000000000000 : ℝ)*base72 + (81006951645483/13595000000000000000000000000 : ℝ)*base73 + (2401787398339542159/1359500000000000000000000000000000 : ℝ)*base76 + (4310976901884542159/1359500000000000000000000000000000 : ℝ)*base78 + (20676867343340042159/1359500000000000000000000000000000 : ℝ)*base80 + (12369255306709/6797500000000000000000000000 : ℝ)*base81 + (111263/625000000000000000000 : ℝ)*base90 + (111263/625000000000000000000 : ℝ)*base92 + (111263/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1114_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1114_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1114_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1114_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1114_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1114_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (877/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

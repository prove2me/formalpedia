-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:41.8697+00:00
-- url     : https://prove2.me/submissions/95415723-138b-4e59-8a41-4fc770997a77

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
theorem support_rectangle_w1582_s0_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1614041121/10000000000 : ℝ)*x 0 + (1465231891/2500000000 : ℝ)*x 1 + (195365307/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614041121/10000000000 : ℝ)^4661 ≤ (4829168693337/50000000000000 : ℝ)^3637 := by
    have hnat : (1614041121 : ℕ)^4661*50000000000000^3637 ≤ 4829168693337^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614041121 10000000000 4829168693337 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1465231891/2500000000 : ℝ)^4661 ≤ (50423978830623/100000000000000 : ℝ)^3637 := by
    have hnat : (1465231891 : ℕ)^4661*100000000000000^3637 ≤ 50423978830623^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465231891 2500000000 50423978830623 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195365307/400000000 : ℝ)^4661 ≤ (9979420944111/25000000000000 : ℝ)^3637 := by
    have hnat : (195365307 : ℕ)^4661*25000000000000^3637 ≤ 9979420944111^3637*400000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195365307 400000000 9979420944111 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1614041121/10000000000 : ℝ), (1465231891/2500000000 : ℝ), (195365307/400000000 : ℝ)] ![(4829168693337/50000000000000 : ℝ), (50423978830623/100000000000000 : ℝ), (9979420944111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1614041121/10000000000 : ℝ)|^4661 ≤ (4829168693337/50000000000000 : ℝ)^3637
        have hw : |(-1614041121/10000000000 : ℝ)|=(1614041121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1465231891/2500000000 : ℝ)|^4661 ≤ (50423978830623/100000000000000 : ℝ)^3637
        have hw : |(1465231891/2500000000 : ℝ)|=(1465231891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(195365307/400000000 : ℝ)|^4661 ≤ (9979420944111/25000000000000 : ℝ)^3637
        have hw : |(195365307/400000000 : ℝ)|=(195365307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462924517/10000000000 : ℝ)*x 0 + (-107841357/500000000 : ℝ)*x 1 + (305258289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462924517/10000000000 : ℝ)^4661 ≤ (4607836636239/10000000000000 : ℝ)^3637 := by
    have hnat : (5462924517 : ℕ)^4661*10000000000000^3637 ≤ 4607836636239^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462924517 10000000000 4607836636239 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107841357/500000000 : ℝ)^4661 ≤ (280079007593/2000000000000 : ℝ)^3637 := by
    have hnat : (107841357 : ℕ)^4661*2000000000000^3637 ≤ 280079007593^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107841357 500000000 280079007593 2000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305258289/625000000 : ℝ)^4661 ≤ (39917683242269/100000000000000 : ℝ)^3637 := by
    have hnat : (305258289 : ℕ)^4661*100000000000000^3637 ≤ 39917683242269^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305258289 625000000 39917683242269 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462924517/10000000000 : ℝ), (-107841357/500000000 : ℝ), (305258289/625000000 : ℝ)] ![(4607836636239/10000000000000 : ℝ), (280079007593/2000000000000 : ℝ), (39917683242269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462924517/10000000000 : ℝ)|^4661 ≤ (4607836636239/10000000000000 : ℝ)^3637
        have hw : |(5462924517/10000000000 : ℝ)|=(5462924517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107841357/500000000 : ℝ)|^4661 ≤ (280079007593/2000000000000 : ℝ)^3637
        have hw : |(-107841357/500000000 : ℝ)|=(107841357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305258289/625000000 : ℝ)|^4661 ≤ (39917683242269/100000000000000 : ℝ)^3637
        have hw : |(305258289/625000000 : ℝ)|=(305258289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462924587/10000000000 : ℝ)*x 0 + (1221033131/2500000000 : ℝ)*x 1 + (-1078413587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462924587/10000000000 : ℝ)^4661 ≤ (23039183559529/50000000000000 : ℝ)^3637 := by
    have hnat : (5462924587 : ℕ)^4661*50000000000000^3637 ≤ 23039183559529^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462924587 10000000000 23039183559529 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221033131/2500000000 : ℝ)^4661 ≤ (19958841097433/50000000000000 : ℝ)^3637 := by
    have hnat : (1221033131 : ℕ)^4661*50000000000000^3637 ≤ 19958841097433^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221033131 2500000000 19958841097433 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078413587/5000000000 : ℝ)^4661 ≤ (14003950662561/100000000000000 : ℝ)^3637 := by
    have hnat : (1078413587 : ℕ)^4661*100000000000000^3637 ≤ 14003950662561^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078413587 5000000000 14003950662561 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462924587/10000000000 : ℝ), (1221033131/2500000000 : ℝ), (-1078413587/5000000000 : ℝ)] ![(23039183559529/50000000000000 : ℝ), (19958841097433/50000000000000 : ℝ), (14003950662561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462924587/10000000000 : ℝ)|^4661 ≤ (23039183559529/50000000000000 : ℝ)^3637
        have hw : |(5462924587/10000000000 : ℝ)|=(5462924587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221033131/2500000000 : ℝ)|^4661 ≤ (19958841097433/50000000000000 : ℝ)^3637
        have hw : |(1221033131/2500000000 : ℝ)|=(1221033131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078413587/5000000000 : ℝ)|^4661 ≤ (14003950662561/100000000000000 : ℝ)^3637
        have hw : |(-1078413587/5000000000 : ℝ)|=(1078413587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063383711/5000000000 : ℝ)*x 0 + (3093882123/10000000000 : ℝ)*x 1 + (338658023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063383711/5000000000 : ℝ)^4661 ≤ (8041271316433/25000000000000 : ℝ)^3637 := by
    have hnat : (2063383711 : ℕ)^4661*25000000000000^3637 ≤ 8041271316433^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063383711 5000000000 8041271316433 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093882123/10000000000 : ℝ)^4661 ≤ (2223590071953/10000000000000 : ℝ)^3637 := by
    have hnat : (3093882123 : ℕ)^4661*10000000000000^3637 ≤ 2223590071953^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093882123 10000000000 2223590071953 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338658023/625000000 : ℝ)^4661 ≤ (2279950700483/5000000000000 : ℝ)^3637 := by
    have hnat : (338658023 : ℕ)^4661*5000000000000^3637 ≤ 2279950700483^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338658023 625000000 2279950700483 5000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063383711/5000000000 : ℝ), (3093882123/10000000000 : ℝ), (338658023/625000000 : ℝ)] ![(8041271316433/25000000000000 : ℝ), (2223590071953/10000000000000 : ℝ), (2279950700483/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063383711/5000000000 : ℝ)|^4661 ≤ (8041271316433/25000000000000 : ℝ)^3637
        have hw : |(2063383711/5000000000 : ℝ)|=(2063383711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093882123/10000000000 : ℝ)|^4661 ≤ (2223590071953/10000000000000 : ℝ)^3637
        have hw : |(3093882123/10000000000 : ℝ)|=(3093882123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338658023/625000000 : ℝ)|^4661 ≤ (2279950700483/5000000000000 : ℝ)^3637
        have hw : |(338658023/625000000 : ℝ)|=(338658023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-808502967/5000000000 : ℝ)*x 0 + (4908682601/10000000000 : ℝ)*x 1 + (5835511349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808502967/5000000000 : ℝ)^4661 ≤ (9681079620737/100000000000000 : ℝ)^3637 := by
    have hnat : (808502967 : ℕ)^4661*100000000000000^3637 ≤ 9681079620737^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808502967 5000000000 9681079620737 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908682601/10000000000 : ℝ)^4661 ≤ (10043750523061/25000000000000 : ℝ)^3637 := by
    have hnat : (4908682601 : ℕ)^4661*25000000000000^3637 ≤ 10043750523061^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908682601 10000000000 10043750523061 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5835511349/10000000000 : ℝ)^4661 ≤ (25071959136099/50000000000000 : ℝ)^3637 := by
    have hnat : (5835511349 : ℕ)^4661*50000000000000^3637 ≤ 25071959136099^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835511349 10000000000 25071959136099 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-808502967/5000000000 : ℝ), (4908682601/10000000000 : ℝ), (5835511349/10000000000 : ℝ)] ![(9681079620737/100000000000000 : ℝ), (10043750523061/25000000000000 : ℝ), (25071959136099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-808502967/5000000000 : ℝ)|^4661 ≤ (9681079620737/100000000000000 : ℝ)^3637
        have hw : |(-808502967/5000000000 : ℝ)|=(808502967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908682601/10000000000 : ℝ)|^4661 ≤ (10043750523061/25000000000000 : ℝ)^3637
        have hw : |(4908682601/10000000000 : ℝ)|=(4908682601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5835511349/10000000000 : ℝ)|^4661 ≤ (25071959136099/50000000000000 : ℝ)^3637
        have hw : |(5835511349/10000000000 : ℝ)|=(5835511349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597940287/5000000000 : ℝ)*x 0 + (-1205447993/10000000000 : ℝ)*x 1 + (5835511437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597940287/5000000000 : ℝ)^4661 ≤ (5401480378427/12500000000000 : ℝ)^3637 := by
    have hnat : (2597940287 : ℕ)^4661*12500000000000^3637 ≤ 5401480378427^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597940287 5000000000 5401480378427 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205447993/10000000000 : ℝ)^4661 ≤ (166105943139/2500000000000 : ℝ)^3637 := by
    have hnat : (1205447993 : ℕ)^4661*2500000000000^3637 ≤ 166105943139^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205447993 10000000000 166105943139 2500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5835511437/10000000000 : ℝ)^4661 ≤ (50143919241273/100000000000000 : ℝ)^3637 := by
    have hnat : (5835511437 : ℕ)^4661*100000000000000^3637 ≤ 50143919241273^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835511437 10000000000 50143919241273 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597940287/5000000000 : ℝ), (-1205447993/10000000000 : ℝ), (5835511437/10000000000 : ℝ)] ![(5401480378427/12500000000000 : ℝ), (166105943139/2500000000000 : ℝ), (50143919241273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597940287/5000000000 : ℝ)|^4661 ≤ (5401480378427/12500000000000 : ℝ)^3637
        have hw : |(2597940287/5000000000 : ℝ)|=(2597940287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1205447993/10000000000 : ℝ)|^4661 ≤ (166105943139/2500000000000 : ℝ)^3637
        have hw : |(-1205447993/10000000000 : ℝ)|=(1205447993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5835511437/10000000000 : ℝ)|^4661 ≤ (50143919241273/100000000000000 : ℝ)^3637
        have hw : |(5835511437/10000000000 : ℝ)|=(5835511437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597940269/5000000000 : ℝ)*x 0 + (5835511321/10000000000 : ℝ)*x 1 + (-1205448227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597940269/5000000000 : ℝ)^4661 ≤ (10802960660931/25000000000000 : ℝ)^3637 := by
    have hnat : (2597940269 : ℕ)^4661*25000000000000^3637 ≤ 10802960660931^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597940269 5000000000 10802960660931 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5835511321/10000000000 : ℝ)^4661 ≤ (10028783592771/20000000000000 : ℝ)^3637 := by
    have hnat : (5835511321 : ℕ)^4661*20000000000000^3637 ≤ 10028783592771^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835511321 10000000000 10028783592771 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205448227/10000000000 : ℝ)^4661 ≤ (3322119689233/50000000000000 : ℝ)^3637 := by
    have hnat : (1205448227 : ℕ)^4661*50000000000000^3637 ≤ 3322119689233^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205448227 10000000000 3322119689233 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597940269/5000000000 : ℝ), (5835511321/10000000000 : ℝ), (-1205448227/10000000000 : ℝ)] ![(10802960660931/25000000000000 : ℝ), (10028783592771/20000000000000 : ℝ), (3322119689233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597940269/5000000000 : ℝ)|^4661 ≤ (10802960660931/25000000000000 : ℝ)^3637
        have hw : |(2597940269/5000000000 : ℝ)|=(2597940269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5835511321/10000000000 : ℝ)|^4661 ≤ (10028783592771/20000000000000 : ℝ)^3637
        have hw : |(5835511321/10000000000 : ℝ)|=(5835511321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205448227/10000000000 : ℝ)|^4661 ≤ (3322119689233/50000000000000 : ℝ)^3637
        have hw : |(-1205448227/10000000000 : ℝ)|=(1205448227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s0_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3307059/8000000 : ℝ)*x 0 + (5360102683/10000000000 : ℝ)*x 1 + (157718457/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3307059/8000000 : ℝ)^4661 ≤ (32235586019347/100000000000000 : ℝ)^3637 := by
    have hnat : (3307059 : ℕ)^4661*100000000000000^3637 ≤ 32235586019347^3637*8000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3307059 8000000 32235586019347 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5360102683/10000000000 : ℝ)^4661 ≤ (5621233349589/12500000000000 : ℝ)^3637 := by
    have hnat : (5360102683 : ℕ)^4661*12500000000000^3637 ≤ 5621233349589^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360102683 10000000000 5621233349589 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157718457/500000000 : ℝ)^4661 ≤ (5698636789749/25000000000000 : ℝ)^3637 := by
    have hnat : (157718457 : ℕ)^4661*25000000000000^3637 ≤ 5698636789749^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157718457 500000000 5698636789749 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3307059/8000000 : ℝ), (5360102683/10000000000 : ℝ), (157718457/500000000 : ℝ)] ![(32235586019347/100000000000000 : ℝ), (5621233349589/12500000000000 : ℝ), (5698636789749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3307059/8000000 : ℝ)|^4661 ≤ (32235586019347/100000000000000 : ℝ)^3637
        have hw : |(3307059/8000000 : ℝ)|=(3307059/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5360102683/10000000000 : ℝ)|^4661 ≤ (5621233349589/12500000000000 : ℝ)^3637
        have hw : |(5360102683/10000000000 : ℝ)|=(5360102683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157718457/500000000 : ℝ)|^4661 ≤ (5698636789749/25000000000000 : ℝ)^3637
        have hw : |(157718457/500000000 : ℝ)|=(157718457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (737/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24609/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4659/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4659 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4659*1^1024 ≤ 0^1024*1^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4659/1024 : ℝ) ≤ (309371767734742389/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4659 ≤ (309371767734742389/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4659*20000000000000000000^1024 ≤ 309371767734742389^1024*5^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 309371767734742389 20000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (309371767734742389/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4659 := by
      have hnat : (1 : ℕ)^1024*1^4659 ≤ 1^4659*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20309371767734742389/20000000000000000000 : ℝ) ≤ (2508448765310849/2500000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (20309371767734742389/20000000000000000000 : ℝ)^1024 ≤ (2508448765310849/2500000000000000 : ℝ)^4659 := by
      have hnat : (20309371767734742389 : ℕ)^1024*2500000000000000^4659 ≤ 2508448765310849^4659*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20309371767734742389 20000000000000000000 2508448765310849 2500000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508448765310849/2500000000000000 : ℝ)) (X := (20309371767734742389/20000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10309371767734742389/10000000000000000000 : ℝ) ≤ (1258448765310849/1250000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (10309371767734742389/10000000000000000000 : ℝ)^1024 ≤ (1258448765310849/1250000000000000 : ℝ)^4659 := by
      have hnat : (10309371767734742389 : ℕ)^1024*1250000000000000^4659 ≤ 1258448765310849^4659*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10309371767734742389 10000000000000000000 1258448765310849 1250000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258448765310849/1250000000000000 : ℝ)) (X := (10309371767734742389/10000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8448765310849/1000000000000000 : ℝ)*(0 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8448765310849/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(309371767734742389/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8448765310849/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8448765310849/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2508448765310849/2500000000000000 : ℝ) by norm_num, show 1+(309371767734742389/20000000000000000000 : ℝ)+(0 : ℝ)=(20309371767734742389/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(309371767734742389/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8448765310849/1000000000000000 : ℝ)*(2/5 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8448765310849/1000000000000000 : ℝ)*(2/5 : ℝ)=(1258448765310849/1250000000000000 : ℝ) by norm_num, show 1+2*(309371767734742389/20000000000000000000 : ℝ)=(10309371767734742389/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8448765310849/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8448765310849/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8448765310849/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8448765310849/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8448765310849/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8448765310849/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1614041121/10000000000 : ℝ)*X 0 0+(1465231891/2500000000 : ℝ)*X 0 1+(195365307/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5462924517/10000000000 : ℝ)*X 1 0+(-107841357/500000000 : ℝ)*X 1 1+(305258289/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5462924587/10000000000 : ℝ)*X 2 0+(1221033131/2500000000 : ℝ)*X 2 1+(-1078413587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2063383711/5000000000 : ℝ)*X 0 0+(3093882123/10000000000 : ℝ)*X 0 1+(338658023/625000000 : ℝ)*X 0 2+(2063383711/5000000000 : ℝ)*X 1 0+(3093882123/10000000000 : ℝ)*X 1 1+(338658023/625000000 : ℝ)*X 1 2+(2063383711/5000000000 : ℝ)*X 2 0+(3093882123/10000000000 : ℝ)*X 2 1+(338658023/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-808502967/5000000000 : ℝ)*X 0 0+(4908682601/10000000000 : ℝ)*X 0 1+(5835511349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597940287/5000000000 : ℝ)*X 1 0+(-1205447993/10000000000 : ℝ)*X 1 1+(5835511437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597940269/5000000000 : ℝ)*X 2 0+(5835511321/10000000000 : ℝ)*X 2 1+(-1205448227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3307059/8000000 : ℝ)*X 0 0+(5360102683/10000000000 : ℝ)*X 0 1+(157718457/500000000 : ℝ)*X 0 2+(3307059/8000000 : ℝ)*X 1 0+(5360102683/10000000000 : ℝ)*X 1 1+(157718457/500000000 : ℝ)*X 1 2+(3307059/8000000 : ℝ)*X 2 0+(5360102683/10000000000 : ℝ)*X 2 1+(157718457/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56043589232729109985281/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41635107/50000000000000 : ℝ)*(base1) + (224721653/12500000000000 : ℝ)*(base19) + (1810891423/100000000000000 : ℝ)*(base23) + (59093109/25000000000000 : ℝ)*(upper3) + (229409069/100000000000000 : ℝ)*(upper5) + (363487073431123/50000000000000 : ℝ)*(major0) + (363487073431123/50000000000000 : ℝ)*(major1) + (363487073431123/50000000000000 : ℝ)*(major2) + (1023762773195499/100000000000000 : ℝ)*(sp0) + (127970949057491/12500000000000 : ℝ)*(sp1) + (1023767579341729/100000000000000 : ℝ)*(sp2) + (430175663418083/100000000000000 : ℝ)*(sp3) + (6700307867/100000000000000 : ℝ)*(sp4) + (1428951949/50000000000000 : ℝ)*(sp7) + (86035720918439/20000000000000 : ℝ)*(f.failure) + (15996396722393/1562500000000 : ℝ)*(f.sum) + (63199723071573/25000000000000000000000000000 : ℝ)*base66 + (6335166146573/50000000000000000000000000000 : ℝ)*base68 + (5692847446573/50000000000000000000000000000 : ℝ)*base70 + (101635871053427/50000000000000000000000000000 : ℝ)*base71 + (140341479421573/25000000000000000000000000000 : ℝ)*base74 + (18501780646573/50000000000000000000000000000 : ℝ)*base76 + (120739063703427/50000000000000000000000000000 : ℝ)*base77 + (35492040796573/50000000000000000000000000000 : ℝ)*base80 + (139228974296573/25000000000000000000000000000 : ℝ)*base82 + (955141/1000000000000000000000 : ℝ)*base90 + (955141/1000000000000000000000 : ℝ)*base92 + (955141/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117062814286270215179943/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2004083521/100000000000000 : ℝ)*(base19) + (1004091203/50000000000000 : ℝ)*(base23) + (4269771/2500000000000 : ℝ)*(base32) + (315663437/100000000000000 : ℝ)*(upper3) + (92488151/50000000000000 : ℝ)*(upper5) + (191538865141223/25000000000000 : ℝ)*(major0) + (191538865141223/25000000000000 : ℝ)*(major1) + (191538865141223/25000000000000 : ℝ)*(major2) + (694294401/12500000000000 : ℝ)*(sp1) + (2889778391/50000000000000 : ℝ)*(sp2) + (1078946911850019/100000000000000 : ℝ)*(sp4) + (107893935341129/10000000000000 : ℝ)*(sp5) + (67433695256927/6250000000000 : ℝ)*(sp6) + (56670440790177/12500000000000 : ℝ)*(sp7) + (7083807767379/1562500000000 : ℝ)*(f.failure) + (1078946911850019/100000000000000 : ℝ)*(f.sum) + (212163353327/12500000000000000000000000000 : ℝ)*base65 + (50589584646673/25000000000000000000000000000 : ℝ)*base68 + (20666817746673/25000000000000000000000000000 : ℝ)*base70 + (46558745871673/25000000000000000000000000000 : ℝ)*base72 + (50034783946673/12500000000000000000000000000 : ℝ)*base74 + (79916584978327/25000000000000000000000000000 : ℝ)*base75 + (62585537221673/25000000000000000000000000000 : ℝ)*base78 + (262561770171673/25000000000000000000000000000 : ℝ)*base80 + (23770287321673/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (431999/78125000000000000000 : ℝ)*base89 + (431999/78125000000000000000 : ℝ)*base91 + (431999/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1582_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (737/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24609/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1582_s1_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1749636539/10000000000 : ℝ)*x 0 + (552813837/1000000000 : ℝ)*x 1 + (320591687/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1749636539/10000000000 : ℝ)^4661 ≤ (2677560306509/25000000000000 : ℝ)^3637 := by
    have hnat : (1749636539 : ℕ)^4661*25000000000000^3637 ≤ 2677560306509^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749636539 10000000000 2677560306509 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552813837/1000000000 : ℝ)^4661 ≤ (9356896028621/20000000000000 : ℝ)^3637 := by
    have hnat : (552813837 : ℕ)^4661*20000000000000^3637 ≤ 9356896028621^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552813837 1000000000 9356896028621 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320591687/625000000 : ℝ)^4661 ≤ (42505278616469/100000000000000 : ℝ)^3637 := by
    have hnat : (320591687 : ℕ)^4661*100000000000000^3637 ≤ 42505278616469^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320591687 625000000 42505278616469 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1749636539/10000000000 : ℝ), (552813837/1000000000 : ℝ), (320591687/625000000 : ℝ)] ![(2677560306509/25000000000000 : ℝ), (9356896028621/20000000000000 : ℝ), (42505278616469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1749636539/10000000000 : ℝ)|^4661 ≤ (2677560306509/25000000000000 : ℝ)^3637
        have hw : |(-1749636539/10000000000 : ℝ)|=(1749636539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552813837/1000000000 : ℝ)|^4661 ≤ (9356896028621/20000000000000 : ℝ)^3637
        have hw : |(552813837/1000000000 : ℝ)|=(552813837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320591687/625000000 : ℝ)|^4661 ≤ (42505278616469/100000000000000 : ℝ)^3637
        have hw : |(320591687/625000000 : ℝ)|=(320591687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374428803/10000000000 : ℝ)*x 0 + (-1957910733/10000000000 : ℝ)*x 1 + (5129466623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374428803/10000000000 : ℝ)^4661 ≤ (45123957397483/100000000000000 : ℝ)^3637 := by
    have hnat : (5374428803 : ℕ)^4661*100000000000000^3637 ≤ 45123957397483^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374428803 10000000000 45123957397483 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957910733/10000000000 : ℝ)^4661 ≤ (12370767892547/100000000000000 : ℝ)^3637 := by
    have hnat : (1957910733 : ℕ)^4661*100000000000000^3637 ≤ 12370767892547^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957910733 10000000000 12370767892547 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129466623/10000000000 : ℝ)^4661 ≤ (10626318674463/25000000000000 : ℝ)^3637 := by
    have hnat : (5129466623 : ℕ)^4661*25000000000000^3637 ≤ 10626318674463^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129466623 10000000000 10626318674463 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374428803/10000000000 : ℝ), (-1957910733/10000000000 : ℝ), (5129466623/10000000000 : ℝ)] ![(45123957397483/100000000000000 : ℝ), (12370767892547/100000000000000 : ℝ), (10626318674463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374428803/10000000000 : ℝ)|^4661 ≤ (45123957397483/100000000000000 : ℝ)^3637
        have hw : |(5374428803/10000000000 : ℝ)|=(5374428803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957910733/10000000000 : ℝ)|^4661 ≤ (12370767892547/100000000000000 : ℝ)^3637
        have hw : |(-1957910733/10000000000 : ℝ)|=(1957910733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129466623/10000000000 : ℝ)|^4661 ≤ (10626318674463/25000000000000 : ℝ)^3637
        have hw : |(5129466623/10000000000 : ℝ)|=(5129466623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214977139/400000000 : ℝ)*x 0 + (2564733461/5000000000 : ℝ)*x 1 + (-244738847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214977139/400000000 : ℝ)^4661 ≤ (45123953868217/100000000000000 : ℝ)^3637 := by
    have hnat : (214977139 : ℕ)^4661*100000000000000^3637 ≤ 45123953868217^3637*400000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214977139 400000000 45123953868217 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564733461/5000000000 : ℝ)^4661 ≤ (425052778731/1000000000000 : ℝ)^3637 := by
    have hnat : (2564733461 : ℕ)^4661*1000000000000^3637 ≤ 425052778731^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564733461 5000000000 425052778731 1000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244738847/1250000000 : ℝ)^4661 ≤ (1237076824073/10000000000000 : ℝ)^3637 := by
    have hnat : (244738847 : ℕ)^4661*10000000000000^3637 ≤ 1237076824073^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244738847 1250000000 1237076824073 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214977139/400000000 : ℝ), (2564733461/5000000000 : ℝ), (-244738847/1250000000 : ℝ)] ![(45123953868217/100000000000000 : ℝ), (425052778731/1000000000000 : ℝ), (1237076824073/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214977139/400000000 : ℝ)|^4661 ≤ (45123953868217/100000000000000 : ℝ)^3637
        have hw : |(214977139/400000000 : ℝ)|=(214977139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564733461/5000000000 : ℝ)|^4661 ≤ (425052778731/1000000000000 : ℝ)^3637
        have hw : |(2564733461/5000000000 : ℝ)|=(2564733461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244738847/1250000000 : ℝ)|^4661 ≤ (1237076824073/10000000000000 : ℝ)^3637
        have hw : |(-244738847/1250000000 : ℝ)|=(244738847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211204737/500000000 : ℝ)*x 0 + (3770975607/10000000000 : ℝ)*x 1 + (4719762969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211204737/500000000 : ℝ)^4661 ≤ (6628094357067/20000000000000 : ℝ)^3637 := by
    have hnat : (211204737 : ℕ)^4661*20000000000000^3637 ≤ 6628094357067^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211204737 500000000 6628094357067 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3770975607/10000000000 : ℝ)^4661 ≤ (1432761703279/5000000000000 : ℝ)^3637 := by
    have hnat : (3770975607 : ℕ)^4661*5000000000000^3637 ≤ 1432761703279^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3770975607 10000000000 1432761703279 5000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4719762969/10000000000 : ℝ)^4661 ≤ (4775536766221/12500000000000 : ℝ)^3637 := by
    have hnat : (4719762969 : ℕ)^4661*12500000000000^3637 ≤ 4775536766221^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719762969 10000000000 4775536766221 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211204737/500000000 : ℝ), (3770975607/10000000000 : ℝ), (4719762969/10000000000 : ℝ)] ![(6628094357067/20000000000000 : ℝ), (1432761703279/5000000000000 : ℝ), (4775536766221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211204737/500000000 : ℝ)|^4661 ≤ (6628094357067/20000000000000 : ℝ)^3637
        have hw : |(211204737/500000000 : ℝ)|=(211204737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3770975607/10000000000 : ℝ)|^4661 ≤ (1432761703279/5000000000000 : ℝ)^3637
        have hw : |(3770975607/10000000000 : ℝ)|=(3770975607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4719762969/10000000000 : ℝ)|^4661 ≤ (4775536766221/12500000000000 : ℝ)^3637
        have hw : |(4719762969/10000000000 : ℝ)|=(4719762969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1749833101/10000000000 : ℝ)*x 0 + (80211149/156250000 : ℝ)*x 1 + (2762016581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1749833101/10000000000 : ℝ)^4661 ≤ (2677945814739/25000000000000 : ℝ)^3637 := by
    have hnat : (1749833101 : ℕ)^4661*25000000000000^3637 ≤ 2677945814739^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749833101 10000000000 2677945814739 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80211149/156250000 : ℝ)^4661 ≤ (850965117909/2000000000000 : ℝ)^3637 := by
    have hnat : (80211149 : ℕ)^4661*2000000000000^3637 ≤ 850965117909^3637*156250000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80211149 156250000 850965117909 2000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762016581/5000000000 : ℝ)^4661 ≤ (46739960829487/100000000000000 : ℝ)^3637 := by
    have hnat : (2762016581 : ℕ)^4661*100000000000000^3637 ≤ 46739960829487^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762016581 5000000000 46739960829487 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1749833101/10000000000 : ℝ), (80211149/156250000 : ℝ), (2762016581/5000000000 : ℝ)] ![(2677945814739/25000000000000 : ℝ), (850965117909/2000000000000 : ℝ), (46739960829487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1749833101/10000000000 : ℝ)|^4661 ≤ (2677945814739/25000000000000 : ℝ)^3637
        have hw : |(-1749833101/10000000000 : ℝ)|=(1749833101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80211149/156250000 : ℝ)|^4661 ≤ (850965117909/2000000000000 : ℝ)^3637
        have hw : |(80211149/156250000 : ℝ)|=(80211149/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762016581/5000000000 : ℝ)|^4661 ≤ (46739960829487/100000000000000 : ℝ)^3637
        have hw : |(2762016581/5000000000 : ℝ)|=(2762016581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268630621/10000000000 : ℝ)*x 0 + (-312668849/2000000000 : ℝ)*x 1 + (110480677/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268630621/10000000000 : ℝ)^4661 ≤ (43988742884791/100000000000000 : ℝ)^3637 := by
    have hnat : (5268630621 : ℕ)^4661*100000000000000^3637 ≤ 43988742884791^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268630621 10000000000 43988742884791 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312668849/2000000000 : ℝ)^4661 ≤ (1854257762301/20000000000000 : ℝ)^3637 := by
    have hnat : (312668849 : ℕ)^4661*20000000000000^3637 ≤ 1854257762301^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312668849 2000000000 1854257762301 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110480677/200000000 : ℝ)^4661 ≤ (46739968289787/100000000000000 : ℝ)^3637 := by
    have hnat : (110480677 : ℕ)^4661*100000000000000^3637 ≤ 46739968289787^3637*200000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110480677 200000000 46739968289787 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268630621/10000000000 : ℝ), (-312668849/2000000000 : ℝ), (110480677/200000000 : ℝ)] ![(43988742884791/100000000000000 : ℝ), (1854257762301/20000000000000 : ℝ), (46739968289787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268630621/10000000000 : ℝ)|^4661 ≤ (43988742884791/100000000000000 : ℝ)^3637
        have hw : |(5268630621/10000000000 : ℝ)|=(5268630621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312668849/2000000000 : ℝ)|^4661 ≤ (1854257762301/20000000000000 : ℝ)^3637
        have hw : |(-312668849/2000000000 : ℝ)|=(312668849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110480677/200000000 : ℝ)|^4661 ≤ (46739968289787/100000000000000 : ℝ)^3637
        have hw : |(110480677/200000000 : ℝ)|=(110480677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268629777/10000000000 : ℝ)*x 0 + (2762017091/5000000000 : ℝ)*x 1 + (-4885453/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268629777/10000000000 : ℝ)^4661 ≤ (21994366927039/50000000000000 : ℝ)^3637 := by
    have hnat : (5268629777 : ℕ)^4661*50000000000000^3637 ≤ 21994366927039^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268629777 10000000000 21994366927039 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762017091/5000000000 : ℝ)^4661 ≤ (5842496486227/12500000000000 : ℝ)^3637 := by
    have hnat : (2762017091 : ℕ)^4661*12500000000000^3637 ≤ 5842496486227^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762017091 5000000000 5842496486227 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885453/31250000 : ℝ)^4661 ≤ (4635647122801/50000000000000 : ℝ)^3637 := by
    have hnat : (4885453 : ℕ)^4661*50000000000000^3637 ≤ 4635647122801^3637*31250000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885453 31250000 4635647122801 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268629777/10000000000 : ℝ), (2762017091/5000000000 : ℝ), (-4885453/31250000 : ℝ)] ![(21994366927039/50000000000000 : ℝ), (5842496486227/12500000000000 : ℝ), (4635647122801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268629777/10000000000 : ℝ)|^4661 ≤ (21994366927039/50000000000000 : ℝ)^3637
        have hw : |(5268629777/10000000000 : ℝ)|=(5268629777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762017091/5000000000 : ℝ)|^4661 ≤ (5842496486227/12500000000000 : ℝ)^3637
        have hw : |(2762017091/5000000000 : ℝ)|=(2762017091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4885453/31250000 : ℝ)|^4661 ≤ (4635647122801/50000000000000 : ℝ)^3637
        have hw : |(-4885453/31250000 : ℝ)|=(4885453/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s1_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2112280843/5000000000 : ℝ)*x 0 + (588766697/1250000000 : ℝ)*x 1 + (3780744467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112280843/5000000000 : ℝ)^4661 ≤ (33145166770843/100000000000000 : ℝ)^3637 := by
    have hnat : (2112280843 : ℕ)^4661*100000000000000^3637 ≤ 33145166770843^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112280843 5000000000 33145166770843 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588766697/1250000000 : ℝ)^4661 ≤ (19052215877359/50000000000000 : ℝ)^3637 := by
    have hnat : (588766697 : ℕ)^4661*50000000000000^3637 ≤ 19052215877359^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588766697 1250000000 19052215877359 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3780744467/10000000000 : ℝ)^4661 ≤ (28750401459787/100000000000000 : ℝ)^3637 := by
    have hnat : (3780744467 : ℕ)^4661*100000000000000^3637 ≤ 28750401459787^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780744467 10000000000 28750401459787 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112280843/5000000000 : ℝ), (588766697/1250000000 : ℝ), (3780744467/10000000000 : ℝ)] ![(33145166770843/100000000000000 : ℝ), (19052215877359/50000000000000 : ℝ), (28750401459787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112280843/5000000000 : ℝ)|^4661 ≤ (33145166770843/100000000000000 : ℝ)^3637
        have hw : |(2112280843/5000000000 : ℝ)|=(2112280843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588766697/1250000000 : ℝ)|^4661 ≤ (19052215877359/50000000000000 : ℝ)^3637
        have hw : |(588766697/1250000000 : ℝ)|=(588766697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3780744467/10000000000 : ℝ)|^4661 ≤ (28750401459787/100000000000000 : ℝ)^3637
        have hw : |(3780744467/10000000000 : ℝ)|=(3780744467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1103/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (737/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (737/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (737/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (737/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (737/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (737/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (737/20000 : ℝ) ^ (4659/1024 : ℝ) ≤ (30031054502269/100000000000000000000 : ℝ) := by
    have hpowers : (737/20000 : ℝ)^4659 ≤ (30031054502269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (737 : ℕ)^4659*100000000000000000000^1024 ≤ 30031054502269^1024*20000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 20000 30031054502269 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/20000 : ℝ)) (X := (30031054502269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24609/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (169666645521158297/100000000000000000000 : ℝ) := by
    have hpowers : (24609/100000 : ℝ)^4659 ≤ (169666645521158297/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24609 : ℕ)^4659*100000000000000000000^1024 ≤ 169666645521158297^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24609 100000 169666645521158297 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24609/100000 : ℝ)) (X := (169666645521158297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000030031054502269/50000000000000000000 : ℝ) ≤ (10000001320102709/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50000030031054502269/50000000000000000000 : ℝ)^1024 ≤ (10000001320102709/10000000000000000 : ℝ)^4659 := by
      have hnat : (50000030031054502269 : ℕ)^1024*10000000000000000^4659 ≤ 10000001320102709^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000030031054502269 50000000000000000000 10000001320102709 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001320102709/10000000000000000 : ℝ)) (X := (50000030031054502269/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50084848338287830283/50000000000000000000 : ℝ) ≤ (1250465911348879/1250000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50084848338287830283/50000000000000000000 : ℝ)^1024 ≤ (1250465911348879/1250000000000000 : ℝ)^4659 := by
      have hnat : (50084848338287830283 : ℕ)^1024*1250000000000000^4659 ≤ 1250465911348879^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50084848338287830283 50000000000000000000 1250465911348879 1250000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250465911348879/1250000000000000 : ℝ)) (X := (50084848338287830283/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50169666645521158297/50000000000000000000 : ℝ) ≤ (2001490652295871/2000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50169666645521158297/50000000000000000000 : ℝ)^1024 ≤ (2001490652295871/2000000000000000 : ℝ)^4659 := by
      have hnat : (50169666645521158297 : ℕ)^1024*2000000000000000^4659 ≤ 2001490652295871^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50169666645521158297 50000000000000000000 2001490652295871 2000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001490652295871/2000000000000000 : ℝ)) (X := (50169666645521158297/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30031054502269/100000000000000000000 : ℝ) ≤ ((104606283608928071303/104620000000000000000 : ℝ)+2*(3725970688323/2092400000000000 : ℝ)*(737/20000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (104606283608928071303/104620000000000000000 : ℝ)+2*(3725970688323/2092400000000000 : ℝ)*(737/20000 : ℝ)=(10000001320102709/10000000000000000 : ℝ) by norm_num, show 1+2*(30031054502269/100000000000000000000 : ℝ)=(50000030031054502269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(169666645521158297/100000000000000000000 : ℝ)+(30031054502269/100000000000000000000 : ℝ) ≤ ((104606283608928071303/104620000000000000000 : ℝ)+(3725970688323/2092400000000000 : ℝ)*((24609/100000 : ℝ)+(737/20000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (104606283608928071303/104620000000000000000 : ℝ)+(3725970688323/2092400000000000 : ℝ)*((24609/100000 : ℝ)+(737/20000 : ℝ))=(1250465911348879/1250000000000000 : ℝ) by norm_num, show 1+(169666645521158297/100000000000000000000 : ℝ)+(30031054502269/100000000000000000000 : ℝ)=(50084848338287830283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(169666645521158297/100000000000000000000 : ℝ) ≤ ((104606283608928071303/104620000000000000000 : ℝ)+2*(3725970688323/2092400000000000 : ℝ)*(24609/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (104606283608928071303/104620000000000000000 : ℝ)+2*(3725970688323/2092400000000000 : ℝ)*(24609/100000 : ℝ)=(2001490652295871/2000000000000000 : ℝ) by norm_num, show 1+2*(169666645521158297/100000000000000000000 : ℝ)=(50169666645521158297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104606283608928071303/104620000000000000000 : ℝ)*(X 1 0+X 2 0)+(3725970688323/2092400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (737/20000 : ℝ)) (hi := (24609/100000 : ℝ)) (c := (104606283608928071303/104620000000000000000 : ℝ)) (alpha := (3725970688323/2092400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104606283608928071303/104620000000000000000 : ℝ)*(X 0 1+X 2 1)+(3725970688323/2092400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (737/20000 : ℝ)) (hi := (24609/100000 : ℝ)) (c := (104606283608928071303/104620000000000000000 : ℝ)) (alpha := (3725970688323/2092400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104606283608928071303/104620000000000000000 : ℝ)*(X 0 2+X 1 2)+(3725970688323/2092400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (737/20000 : ℝ)) (hi := (24609/100000 : ℝ)) (c := (104606283608928071303/104620000000000000000 : ℝ)) (alpha := (3725970688323/2092400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1749636539/10000000000 : ℝ)*X 0 0+(552813837/1000000000 : ℝ)*X 0 1+(320591687/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374428803/10000000000 : ℝ)*X 1 0+(-1957910733/10000000000 : ℝ)*X 1 1+(5129466623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214977139/400000000 : ℝ)*X 2 0+(2564733461/5000000000 : ℝ)*X 2 1+(-244738847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((211204737/500000000 : ℝ)*X 0 0+(3770975607/10000000000 : ℝ)*X 0 1+(4719762969/10000000000 : ℝ)*X 0 2+(211204737/500000000 : ℝ)*X 1 0+(3770975607/10000000000 : ℝ)*X 1 1+(4719762969/10000000000 : ℝ)*X 1 2+(211204737/500000000 : ℝ)*X 2 0+(3770975607/10000000000 : ℝ)*X 2 1+(4719762969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1749833101/10000000000 : ℝ)*X 0 0+(80211149/156250000 : ℝ)*X 0 1+(2762016581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268630621/10000000000 : ℝ)*X 1 0+(-312668849/2000000000 : ℝ)*X 1 1+(110480677/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268629777/10000000000 : ℝ)*X 2 0+(2762017091/5000000000 : ℝ)*X 2 1+(-4885453/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2112280843/5000000000 : ℝ)*X 0 0+(588766697/1250000000 : ℝ)*X 0 1+(3780744467/10000000000 : ℝ)*X 0 2+(2112280843/5000000000 : ℝ)*X 1 0+(588766697/1250000000 : ℝ)*X 1 1+(3780744467/10000000000 : ℝ)*X 1 2+(2112280843/5000000000 : ℝ)*X 2 0+(588766697/1250000000 : ℝ)*X 2 1+(3780744467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46844512659734963102068715079/5231000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (598549129/25000000000000 : ℝ)*(base19) + (13565571/625000000000 : ℝ)*(base23) + (270536417/100000000000000 : ℝ)*(upper3) + (474427/1250000000000 : ℝ)*(upper4) + (41370569/25000000000000 : ℝ)*(upper5) + (1781184789207623/100000000000000 : ℝ)*(major0) + (1781184789207623/100000000000000 : ℝ)*(major1) + (1781184789207623/100000000000000 : ℝ)*(major2) + (627088320024399/25000000000000 : ℝ)*(sp0) + (1254185618759587/50000000000000 : ℝ)*(sp1) + (250837146122433/10000000000000 : ℝ)*(sp2) + (65874120531389/6250000000000 : ℝ)*(sp3) + (4070323619/20000000000000 : ℝ)*(sp4) + (607480721/6250000000000 : ℝ)*(sp7) + (1053995648193759/100000000000000 : ℝ)*(f.failure) + (2508373631715691/100000000000000 : ℝ)*(f.sum) + (622323240024311/104620000000000000000000000000 : ℝ)*base66 + (39394674200798592769/10462000000000000000000000000000000 : ℝ)*base67 + (29481543717946592769/10462000000000000000000000000000000 : ℝ)*base69 + (18437143135090592769/10462000000000000000000000000000000 : ℝ)*base71 + (156387560422211/104620000000000000000000000000 : ℝ)*base74 + (113222407075586592769/10462000000000000000000000000000000 : ℝ)*base75 + (75931817106154592769/10462000000000000000000000000000000 : ℝ)*base77 + (56351276443958592769/10462000000000000000000000000000000 : ℝ)*base79 + (211807507724331/104620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (50210221/5000000000000000000000 : ℝ)*base90 + (50210221/5000000000000000000000 : ℝ)*base92 + (50210221/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27161264675662569179051095149/2615500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (917171203/50000000000000 : ℝ)*(base19) + (408880211/25000000000000 : ℝ)*(base23) + (122600183/100000000000000 : ℝ)*(upper2) + (192531929/50000000000000 : ℝ)*(upper3) + (41701247/25000000000000 : ℝ)*(upper5) + (909165160513639/50000000000000 : ℝ)*(major0) + (909165160513639/50000000000000 : ℝ)*(major1) + (909165160513639/50000000000000 : ℝ)*(major2) + (3102927079/20000000000000 : ℝ)*(sp1) + (14453080633/100000000000000 : ℝ)*(sp2) + (640171051434571/25000000000000 : ℝ)*(sp4) + (2560666856760483/100000000000000 : ℝ)*(sp5) + (1280334058568403/50000000000000 : ℝ)*(sp6) + (537988045079279/50000000000000 : ℝ)*(sp7) + (537988045079279/50000000000000 : ℝ)*(f.failure) + (640171051434571/25000000000000 : ℝ)*(f.sum) + (339424543602843/52310000000000000000000000000 : ℝ)*base66 + (16734061574973851617/5231000000000000000000000000000000 : ℝ)*base67 + (20077104946751851617/5231000000000000000000000000000000 : ℝ)*base69 + (3298499045630148383/5231000000000000000000000000000000 : ℝ)*base72 + (130195446785383/52310000000000000000000000000 : ℝ)*base74 + (3945198709085148383/5231000000000000000000000000000000 : ℝ)*base76 + (1866251338490851617/5231000000000000000000000000000000 : ℝ)*base77 + (45508683111259851617/5231000000000000000000000000000000 : ℝ)*base79 + (128475550480183/52310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15300899/2500000000000000000000 : ℝ)*base89 + (15300899/2500000000000000000000 : ℝ)*base91 + (15300899/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1582_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1582_s2_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-883591157/5000000000 : ℝ)*x 0 + (5438500991/10000000000 : ℝ)*x 1 + (5207656767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883591157/5000000000 : ℝ)^4661 ≤ (1356009983283/12500000000000 : ℝ)^3637 := by
    have hnat : (883591157 : ℕ)^4661*12500000000000^3637 ≤ 1356009983283^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883591157 5000000000 1356009983283 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438500991/10000000000 : ℝ)^4661 ≤ (22907262668969/50000000000000 : ℝ)^3637 := by
    have hnat : (5438500991 : ℕ)^4661*50000000000000^3637 ≤ 22907262668969^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438500991 10000000000 22907262668969 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207656767/10000000000 : ℝ)^4661 ≤ (21668697395113/50000000000000 : ℝ)^3637 := by
    have hnat : (5207656767 : ℕ)^4661*50000000000000^3637 ≤ 21668697395113^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207656767 10000000000 21668697395113 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883591157/5000000000 : ℝ), (5438500991/10000000000 : ℝ), (5207656767/10000000000 : ℝ)] ![(1356009983283/12500000000000 : ℝ), (22907262668969/50000000000000 : ℝ), (21668697395113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883591157/5000000000 : ℝ)|^4661 ≤ (1356009983283/12500000000000 : ℝ)^3637
        have hw : |(-883591157/5000000000 : ℝ)|=(883591157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438500991/10000000000 : ℝ)|^4661 ≤ (22907262668969/50000000000000 : ℝ)^3637
        have hw : |(5438500991/10000000000 : ℝ)|=(5438500991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207656767/10000000000 : ℝ)|^4661 ≤ (21668697395113/50000000000000 : ℝ)^3637
        have hw : |(5207656767/10000000000 : ℝ)|=(5207656767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070241503/2000000000 : ℝ)*x 0 + (-235700443/1250000000 : ℝ)*x 1 + (1041531517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070241503/2000000000 : ℝ)^4661 ≤ (44874249395273/100000000000000 : ℝ)^3637 := by
    have hnat : (1070241503 : ℕ)^4661*100000000000000^3637 ≤ 44874249395273^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070241503 2000000000 44874249395273 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235700443/1250000000 : ℝ)^4661 ≤ (736771692207/6250000000000 : ℝ)^3637 := by
    have hnat : (235700443 : ℕ)^4661*6250000000000^3637 ≤ 736771692207^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235700443 1250000000 736771692207 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041531517/2000000000 : ℝ)^4661 ≤ (43337403514103/100000000000000 : ℝ)^3637 := by
    have hnat : (1041531517 : ℕ)^4661*100000000000000^3637 ≤ 43337403514103^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041531517 2000000000 43337403514103 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070241503/2000000000 : ℝ), (-235700443/1250000000 : ℝ), (1041531517/2000000000 : ℝ)] ![(44874249395273/100000000000000 : ℝ), (736771692207/6250000000000 : ℝ), (43337403514103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070241503/2000000000 : ℝ)|^4661 ≤ (44874249395273/100000000000000 : ℝ)^3637
        have hw : |(1070241503/2000000000 : ℝ)|=(1070241503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235700443/1250000000 : ℝ)|^4661 ≤ (736771692207/6250000000000 : ℝ)^3637
        have hw : |(-235700443/1250000000 : ℝ)|=(235700443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041531517/2000000000 : ℝ)|^4661 ≤ (43337403514103/100000000000000 : ℝ)^3637
        have hw : |(1041531517/2000000000 : ℝ)|=(1041531517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351208023/10000000000 : ℝ)*x 0 + (5207656469/10000000000 : ℝ)*x 1 + (-471401087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351208023/10000000000 : ℝ)^4661 ≤ (44874254854673/100000000000000 : ℝ)^3637 := by
    have hnat : (5351208023 : ℕ)^4661*100000000000000^3637 ≤ 44874254854673^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351208023 10000000000 44874254854673 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207656469/10000000000 : ℝ)^4661 ≤ (43337391612089/100000000000000 : ℝ)^3637 := by
    have hnat : (5207656469 : ℕ)^4661*100000000000000^3637 ≤ 43337391612089^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207656469 10000000000 43337391612089 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471401087/2500000000 : ℝ)^4661 ≤ (5894176758461/50000000000000 : ℝ)^3637 := by
    have hnat : (471401087 : ℕ)^4661*50000000000000^3637 ≤ 5894176758461^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471401087 2500000000 5894176758461 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351208023/10000000000 : ℝ), (5207656469/10000000000 : ℝ), (-471401087/2500000000 : ℝ)] ![(44874254854673/100000000000000 : ℝ), (43337391612089/100000000000000 : ℝ), (5894176758461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351208023/10000000000 : ℝ)|^4661 ≤ (44874254854673/100000000000000 : ℝ)^3637
        have hw : |(5351208023/10000000000 : ℝ)|=(5351208023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207656469/10000000000 : ℝ)|^4661 ≤ (43337391612089/100000000000000 : ℝ)^3637
        have hw : |(5207656469/10000000000 : ℝ)|=(5207656469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471401087/2500000000 : ℝ)|^4661 ≤ (5894176758461/50000000000000 : ℝ)^3637
        have hw : |(-471401087/2500000000 : ℝ)|=(471401087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423683407/1000000000 : ℝ)*x 0 + (3969285321/10000000000 : ℝ)*x 1 + (4518663403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423683407/1000000000 : ℝ)^4661 ≤ (8317153456683/25000000000000 : ℝ)^3637 := by
    have hnat : (423683407 : ℕ)^4661*25000000000000^3637 ≤ 8317153456683^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423683407 1000000000 8317153456683 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3969285321/10000000000 : ℝ)^4661 ≤ (30600567367459/100000000000000 : ℝ)^3637 := by
    have hnat : (3969285321 : ℕ)^4661*100000000000000^3637 ≤ 30600567367459^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3969285321 10000000000 30600567367459 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518663403/10000000000 : ℝ)^4661 ≤ (2258176174399/6250000000000 : ℝ)^3637 := by
    have hnat : (4518663403 : ℕ)^4661*6250000000000^3637 ≤ 2258176174399^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518663403 10000000000 2258176174399 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423683407/1000000000 : ℝ), (3969285321/10000000000 : ℝ), (4518663403/10000000000 : ℝ)] ![(8317153456683/25000000000000 : ℝ), (30600567367459/100000000000000 : ℝ), (2258176174399/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423683407/1000000000 : ℝ)|^4661 ≤ (8317153456683/25000000000000 : ℝ)^3637
        have hw : |(423683407/1000000000 : ℝ)|=(423683407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3969285321/10000000000 : ℝ)|^4661 ≤ (30600567367459/100000000000000 : ℝ)^3637
        have hw : |(3969285321/10000000000 : ℝ)|=(3969285321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518663403/10000000000 : ℝ)|^4661 ≤ (2258176174399/6250000000000 : ℝ)^3637
        have hw : |(4518663403/10000000000 : ℝ)|=(4518663403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1767220101/10000000000 : ℝ)*x 0 + (1302255429/2500000000 : ℝ)*x 1 + (2718562487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767220101/10000000000 : ℝ)^4661 ≤ (5424188568117/50000000000000 : ℝ)^3637 := by
    have hnat : (1767220101 : ℕ)^4661*50000000000000^3637 ≤ 5424188568117^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767220101 10000000000 5424188568117 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302255429/2500000000 : ℝ)^4661 ≤ (10837988088469/25000000000000 : ℝ)^3637 := by
    have hnat : (1302255429 : ℕ)^4661*25000000000000^3637 ≤ 10837988088469^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302255429 2500000000 10837988088469 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718562487/5000000000 : ℝ)^4661 ≤ (45799670493413/100000000000000 : ℝ)^3637 := by
    have hnat : (2718562487 : ℕ)^4661*100000000000000^3637 ≤ 45799670493413^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718562487 5000000000 45799670493413 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1767220101/10000000000 : ℝ), (1302255429/2500000000 : ℝ), (2718562487/5000000000 : ℝ)] ![(5424188568117/50000000000000 : ℝ), (10837988088469/25000000000000 : ℝ), (45799670493413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1767220101/10000000000 : ℝ)|^4661 ≤ (5424188568117/50000000000000 : ℝ)^3637
        have hw : |(-1767220101/10000000000 : ℝ)|=(1767220101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302255429/2500000000 : ℝ)|^4661 ≤ (10837988088469/25000000000000 : ℝ)^3637
        have hw : |(1302255429/2500000000 : ℝ)|=(1302255429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718562487/5000000000 : ℝ)|^4661 ≤ (45799670493413/100000000000000 : ℝ)^3637
        have hw : |(2718562487/5000000000 : ℝ)|=(2718562487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645021511/5000000000 : ℝ)*x 0 + (-1656136507/10000000000 : ℝ)*x 1 + (108742521/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645021511/5000000000 : ℝ)^4661 ≤ (2763624020351/6250000000000 : ℝ)^3637 := by
    have hnat : (2645021511 : ℕ)^4661*6250000000000^3637 ≤ 2763624020351^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645021511 5000000000 2763624020351 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1656136507/10000000000 : ℝ)^4661 ≤ (998233354833/10000000000000 : ℝ)^3637 := by
    have hnat : (1656136507 : ℕ)^4661*10000000000000^3637 ≤ 998233354833^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656136507 10000000000 998233354833 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108742521/200000000 : ℝ)^4661 ≤ (45799682108999/100000000000000 : ℝ)^3637 := by
    have hnat : (108742521 : ℕ)^4661*100000000000000^3637 ≤ 45799682108999^3637*200000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108742521 200000000 45799682108999 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645021511/5000000000 : ℝ), (-1656136507/10000000000 : ℝ), (108742521/200000000 : ℝ)] ![(2763624020351/6250000000000 : ℝ), (998233354833/10000000000000 : ℝ), (45799682108999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645021511/5000000000 : ℝ)|^4661 ≤ (2763624020351/6250000000000 : ℝ)^3637
        have hw : |(2645021511/5000000000 : ℝ)|=(2645021511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1656136507/10000000000 : ℝ)|^4661 ≤ (998233354833/10000000000000 : ℝ)^3637
        have hw : |(-1656136507/10000000000 : ℝ)|=(1656136507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108742521/200000000 : ℝ)|^4661 ≤ (45799682108999/100000000000000 : ℝ)^3637
        have hw : |(108742521/200000000 : ℝ)|=(108742521/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645021791/5000000000 : ℝ)*x 0 + (1087425443/2000000000 : ℝ)*x 1 + (-1656134103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645021791/5000000000 : ℝ)^4661 ≤ (8843598064881/20000000000000 : ℝ)^3637 := by
    have hnat : (2645021791 : ℕ)^4661*20000000000000^3637 ≤ 8843598064881^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645021791 5000000000 8843598064881 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087425443/2000000000 : ℝ)^4661 ≤ (22899847342677/50000000000000 : ℝ)^3637 := by
    have hnat : (1087425443 : ℕ)^4661*50000000000000^3637 ≤ 22899847342677^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087425443 2000000000 22899847342677 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656134103/10000000000 : ℝ)^4661 ≤ (4991157489289/50000000000000 : ℝ)^3637 := by
    have hnat : (1656134103 : ℕ)^4661*50000000000000^3637 ≤ 4991157489289^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656134103 10000000000 4991157489289 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645021791/5000000000 : ℝ), (1087425443/2000000000 : ℝ), (-1656134103/10000000000 : ℝ)] ![(8843598064881/20000000000000 : ℝ), (22899847342677/50000000000000 : ℝ), (4991157489289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645021791/5000000000 : ℝ)|^4661 ≤ (8843598064881/20000000000000 : ℝ)^3637
        have hw : |(2645021791/5000000000 : ℝ)|=(2645021791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087425443/2000000000 : ℝ)|^4661 ≤ (22899847342677/50000000000000 : ℝ)^3637
        have hw : |(1087425443/2000000000 : ℝ)|=(1087425443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656134103/10000000000 : ℝ)|^4661 ≤ (4991157489289/50000000000000 : ℝ)^3637
        have hw : |(-1656134103/10000000000 : ℝ)|=(1656134103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s2_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118462913/5000000000 : ℝ)*x 0 + (2257708257/5000000000 : ℝ)*x 1 + (158902349/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118462913/5000000000 : ℝ)^4661 ≤ (33269537173533/100000000000000 : ℝ)^3637 := by
    have hnat : (2118462913 : ℕ)^4661*100000000000000^3637 ≤ 33269537173533^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118462913 5000000000 33269537173533 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257708257/5000000000 : ℝ)^4661 ≤ (18048775379021/50000000000000 : ℝ)^3637 := by
    have hnat : (2257708257 : ℕ)^4661*50000000000000^3637 ≤ 18048775379021^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257708257 5000000000 18048775379021 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158902349/400000000 : ℝ)^4661 ≤ (6126582411267/20000000000000 : ℝ)^3637 := by
    have hnat : (158902349 : ℕ)^4661*20000000000000^3637 ≤ 6126582411267^3637*400000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158902349 400000000 6126582411267 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118462913/5000000000 : ℝ), (2257708257/5000000000 : ℝ), (158902349/400000000 : ℝ)] ![(33269537173533/100000000000000 : ℝ), (18048775379021/50000000000000 : ℝ), (6126582411267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118462913/5000000000 : ℝ)|^4661 ≤ (33269537173533/100000000000000 : ℝ)^3637
        have hw : |(2118462913/5000000000 : ℝ)|=(2118462913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257708257/5000000000 : ℝ)|^4661 ≤ (18048775379021/50000000000000 : ℝ)^3637
        have hw : |(2257708257/5000000000 : ℝ)|=(2257708257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158902349/400000000 : ℝ)|^4661 ≤ (6126582411267/20000000000000 : ℝ)^3637
        have hw : |(158902349/400000000 : ℝ)|=(158902349/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2177/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1103/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1103/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1103/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1103/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1103/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1103/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9201/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (965209905010201/50000000000000000000 : ℝ) := by
    have hpowers : (9201/100000 : ℝ)^4659 ≤ (965209905010201/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9201 : ℕ)^4659*50000000000000000000^1024 ≤ 965209905010201^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9201 100000 965209905010201 50000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9201/100000 : ℝ)) (X := (965209905010201/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1103/6250 : ℝ) ^ (4659/1024 : ℝ) ≤ (18688809484450243/50000000000000000000 : ℝ) := by
    have hpowers : (1103/6250 : ℝ)^4659 ≤ (18688809484450243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1103 : ℕ)^4659*50000000000000000000^1024 ≤ 18688809484450243^1024*6250^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 6250 18688809484450243 50000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/6250 : ℝ)) (X := (18688809484450243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000965209905010201/25000000000000000000 : ℝ) ≤ (10000084855982557/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (25000965209905010201/25000000000000000000 : ℝ)^1024 ≤ (10000084855982557/10000000000000000 : ℝ)^4659 := by
      have hnat : (25000965209905010201 : ℕ)^1024*10000000000000000^4659 ≤ 10000084855982557^4659*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000965209905010201 25000000000000000000 10000084855982557 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084855982557/10000000000000000 : ℝ)) (X := (25000965209905010201/25000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504913504847365111/12500000000000000000 : ℝ) ≤ (5000431908788217/5000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (12504913504847365111/12500000000000000000 : ℝ)^1024 ≤ (5000431908788217/5000000000000000 : ℝ)^4659 := by
      have hnat : (12504913504847365111 : ℕ)^1024*5000000000000000^4659 ≤ 5000431908788217^4659*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504913504847365111 12500000000000000000 5000431908788217 5000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000431908788217/5000000000000000 : ℝ)) (X := (12504913504847365111/12500000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018688809484450243/25000000000000000000 : ℝ) ≤ (10001642779170311/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (25018688809484450243/25000000000000000000 : ℝ)^1024 ≤ (10001642779170311/10000000000000000 : ℝ)^4659 := by
      have hnat : (25018688809484450243 : ℕ)^1024*10000000000000000^4659 ≤ 10001642779170311^4659*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018688809484450243 25000000000000000000 10001642779170311 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001642779170311/10000000000000000 : ℝ)) (X := (25018688809484450243/25000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(965209905010201/50000000000000000000 : ℝ) ≤ ((3378255293089365377/3378800000000000000 : ℝ)+2*(778961593877/844700000000000 : ℝ)*(9201/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (3378255293089365377/3378800000000000000 : ℝ)+2*(778961593877/844700000000000 : ℝ)*(9201/100000 : ℝ)=(10000084855982557/10000000000000000 : ℝ) by norm_num, show 1+2*(965209905010201/50000000000000000000 : ℝ)=(25000965209905010201/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18688809484450243/50000000000000000000 : ℝ)+(965209905010201/50000000000000000000 : ℝ) ≤ ((3378255293089365377/3378800000000000000 : ℝ)+(778961593877/844700000000000 : ℝ)*((1103/6250 : ℝ)+(9201/100000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (3378255293089365377/3378800000000000000 : ℝ)+(778961593877/844700000000000 : ℝ)*((1103/6250 : ℝ)+(9201/100000 : ℝ))=(5000431908788217/5000000000000000 : ℝ) by norm_num, show 1+(18688809484450243/50000000000000000000 : ℝ)+(965209905010201/50000000000000000000 : ℝ)=(12504913504847365111/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18688809484450243/50000000000000000000 : ℝ) ≤ ((3378255293089365377/3378800000000000000 : ℝ)+2*(778961593877/844700000000000 : ℝ)*(1103/6250 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (3378255293089365377/3378800000000000000 : ℝ)+2*(778961593877/844700000000000 : ℝ)*(1103/6250 : ℝ)=(10001642779170311/10000000000000000 : ℝ) by norm_num, show 1+2*(18688809484450243/50000000000000000000 : ℝ)=(25018688809484450243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3378255293089365377/3378800000000000000 : ℝ)*(X 1 0+X 2 0)+(778961593877/844700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (3378255293089365377/3378800000000000000 : ℝ)) (alpha := (778961593877/844700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3378255293089365377/3378800000000000000 : ℝ)*(X 0 1+X 2 1)+(778961593877/844700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (3378255293089365377/3378800000000000000 : ℝ)) (alpha := (778961593877/844700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3378255293089365377/3378800000000000000 : ℝ)*(X 0 2+X 1 2)+(778961593877/844700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (9201/100000 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (3378255293089365377/3378800000000000000 : ℝ)) (alpha := (778961593877/844700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-883591157/5000000000 : ℝ)*X 0 0+(5438500991/10000000000 : ℝ)*X 0 1+(5207656767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070241503/2000000000 : ℝ)*X 1 0+(-235700443/1250000000 : ℝ)*X 1 1+(1041531517/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351208023/10000000000 : ℝ)*X 2 0+(5207656469/10000000000 : ℝ)*X 2 1+(-471401087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((423683407/1000000000 : ℝ)*X 0 0+(3969285321/10000000000 : ℝ)*X 0 1+(4518663403/10000000000 : ℝ)*X 0 2+(423683407/1000000000 : ℝ)*X 1 0+(3969285321/10000000000 : ℝ)*X 1 1+(4518663403/10000000000 : ℝ)*X 1 2+(423683407/1000000000 : ℝ)*X 2 0+(3969285321/10000000000 : ℝ)*X 2 1+(4518663403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1767220101/10000000000 : ℝ)*X 0 0+(1302255429/2500000000 : ℝ)*X 0 1+(2718562487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645021511/5000000000 : ℝ)*X 1 0+(-1656136507/10000000000 : ℝ)*X 1 1+(108742521/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645021791/5000000000 : ℝ)*X 2 0+(1087425443/2000000000 : ℝ)*X 2 1+(-1656134103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118462913/5000000000 : ℝ)*X 0 0+(2257708257/5000000000 : ℝ)*X 0 1+(158902349/400000000 : ℝ)*X 0 2+(2118462913/5000000000 : ℝ)*X 1 0+(2257708257/5000000000 : ℝ)*X 1 1+(158902349/400000000 : ℝ)*X 1 2+(2118462913/5000000000 : ℝ)*X 2 0+(2257708257/5000000000 : ℝ)*X 2 1+(158902349/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (922747749398110104512804397/84470000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (936967499/100000000000000 : ℝ)*(base19) + (266997611/20000000000000 : ℝ)*(base23) + (51675621/100000000000000 : ℝ)*(upper2) + (40748893/25000000000000 : ℝ)*(upper3) + (1538061439010971/50000000000000 : ℝ)*(major0) + (1538061439010971/50000000000000 : ℝ)*(major1) + (1538061439010971/50000000000000 : ℝ)*(major2) + (4331957090130229/100000000000000 : ℝ)*(sp0) + (2165992030316361/50000000000000 : ℝ)*(sp1) + (4331974057140073/100000000000000 : ℝ)*(sp2) + (227531145529949/12500000000000 : ℝ)*(sp3) + (3488433749/12500000000000 : ℝ)*(sp4) + (4802736047/50000000000000 : ℝ)*(sp6) + (5615035863/50000000000000 : ℝ)*(sp7) + (910130197155659/50000000000000 : ℝ)*(f.failure) + (2165992498800111/50000000000000 : ℝ)*(f.sum) + (22581555291113/5279375000000000000000000000 : ℝ)*base65 + (1498927655770239067/168940000000000000000000000000000 : ℝ)*base67 + (1346875680362439067/168940000000000000000000000000000 : ℝ)*base69 + (1083574214811579067/168940000000000000000000000000000 : ℝ)*base71 + (6617941848777/21117500000000000000000000000 : ℝ)*base73 + (2360413215042579067/168940000000000000000000000000000 : ℝ)*base75 + (2030330774711999067/168940000000000000000000000000000 : ℝ)*base77 + (92313409920399067/168940000000000000000000000000000 : ℝ)*base79 + (28377058681633/21117500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8566321/2500000000000000000000 : ℝ)*base90 + (8566321/2500000000000000000000 : ℝ)*base92 + (8566321/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (381679349175609547756742367/42235000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97797/5000000000000 : ℝ)*(base8) + (176571923/25000000000000 : ℝ)*(base15) + (214897703/100000000000000 : ℝ)*(lower2) + (55990227/100000000000000 : ℝ)*(lower4) + (778261188581319/25000000000000 : ℝ)*(major0) + (778261188581319/25000000000000 : ℝ)*(major1) + (778261188581319/25000000000000 : ℝ)*(major2) + (193408433/5000000000000 : ℝ)*(sp1) + (17639169/40000000000 : ℝ)*(sp2) + (2567685669/100000000000000 : ℝ)*(sp3) + (136999397336491/3125000000000 : ℝ)*(sp4) + (43839761422673/1000000000000 : ℝ)*(sp5) + (2140594052149/48828125000 : ℝ)*(sp6) + (230263240375823/12500000000000 : ℝ)*(sp7) + (1842108490692253/100000000000000 : ℝ)*(f.failure) + (1095995179180913/25000000000000 : ℝ)*(f.sum) + (95652925855041/21117500000000000000000000000 : ℝ)*base65 + (1915653224182345737/84470000000000000000000000000000 : ℝ)*base68 + (626998313530005737/84470000000000000000000000000000 : ℝ)*base70 + (397627226978935737/84470000000000000000000000000000 : ℝ)*base72 + (70317845380577/42235000000000000000000000000 : ℝ)*base73 + (1275509272395645737/84470000000000000000000000000000 : ℝ)*base76 + (566631716783015737/84470000000000000000000000000000 : ℝ)*base78 + (825531584856705737/84470000000000000000000000000000 : ℝ)*base80 + (30605202889433/42235000000000000000000000000 : ℝ)*base82 + (40137593/5000000000000000000000 : ℝ)*base89 + (40137593/5000000000000000000000 : ℝ)*base91 + (40137593/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1582_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1582_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1582_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1582_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1582_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

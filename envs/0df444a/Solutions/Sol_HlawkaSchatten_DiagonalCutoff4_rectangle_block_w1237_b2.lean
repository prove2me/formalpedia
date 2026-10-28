-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:20.487985+00:00
-- url     : https://prove2.me/submissions/f047383e-44cd-4514-8aa6-5e9e511cac3f

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
theorem support_rectangle_w1237_s6_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122250279/10000000000 : ℝ)*x 0 + (5391489799/10000000000 : ℝ)*x 1 + (658369859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122250279/10000000000 : ℝ)^4215 ≤ (1613146953291/12500000000000 : ℝ)^3191 := by
    have hnat : (2122250279 : ℕ)^4215*12500000000000^3191 ≤ 1613146953291^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122250279 10000000000 1613146953291 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391489799/10000000000 : ℝ)^4215 ≤ (44219462247789/100000000000000 : ℝ)^3191 := by
    have hnat : (5391489799 : ℕ)^4215*100000000000000^3191 ≤ 44219462247789^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391489799 10000000000 44219462247789 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658369859/1250000000 : ℝ)^4215 ≤ (42875362106019/100000000000000 : ℝ)^3191 := by
    have hnat : (658369859 : ℕ)^4215*100000000000000^3191 ≤ 42875362106019^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658369859 1250000000 42875362106019 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122250279/10000000000 : ℝ), (5391489799/10000000000 : ℝ), (658369859/1250000000 : ℝ)] ![(1613146953291/12500000000000 : ℝ), (44219462247789/100000000000000 : ℝ), (42875362106019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122250279/10000000000 : ℝ)|^4215 ≤ (1613146953291/12500000000000 : ℝ)^3191
        have hw : |(-2122250279/10000000000 : ℝ)|=(2122250279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391489799/10000000000 : ℝ)|^4215 ≤ (44219462247789/100000000000000 : ℝ)^3191
        have hw : |(5391489799/10000000000 : ℝ)|=(5391489799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658369859/1250000000 : ℝ)|^4215 ≤ (42875362106019/100000000000000 : ℝ)^3191
        have hw : |(658369859/1250000000 : ℝ)|=(658369859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334024087/625000000 : ℝ)*x 0 + (-2185394493/10000000000 : ℝ)*x 1 + (2633479449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334024087/625000000 : ℝ)^4215 ≤ (4370986562703/10000000000000 : ℝ)^3191 := by
    have hnat : (334024087 : ℕ)^4215*10000000000000^3191 ≤ 4370986562703^3191*625000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334024087 625000000 4370986562703 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185394493/10000000000 : ℝ)^4215 ≤ (6707385987077/50000000000000 : ℝ)^3191 := by
    have hnat : (2185394493 : ℕ)^4215*50000000000000^3191 ≤ 6707385987077^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185394493 10000000000 6707385987077 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633479449/5000000000 : ℝ)^4215 ≤ (4287536238559/10000000000000 : ℝ)^3191 := by
    have hnat : (2633479449 : ℕ)^4215*10000000000000^3191 ≤ 4287536238559^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633479449 5000000000 4287536238559 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334024087/625000000 : ℝ), (-2185394493/10000000000 : ℝ), (2633479449/5000000000 : ℝ)] ![(4370986562703/10000000000000 : ℝ), (6707385987077/50000000000000 : ℝ), (4287536238559/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334024087/625000000 : ℝ)|^4215 ≤ (4370986562703/10000000000000 : ℝ)^3191
        have hw : |(334024087/625000000 : ℝ)|=(334024087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185394493/10000000000 : ℝ)|^4215 ≤ (6707385987077/50000000000000 : ℝ)^3191
        have hw : |(-2185394493/10000000000 : ℝ)|=(2185394493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633479449/5000000000 : ℝ)|^4215 ≤ (4287536238559/10000000000000 : ℝ)^3191
        have hw : |(2633479449/5000000000 : ℝ)|=(2633479449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344385403/10000000000 : ℝ)*x 0 + (526695889/1000000000 : ℝ)*x 1 + (-2185394489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344385403/10000000000 : ℝ)^4215 ≤ (8741973149173/20000000000000 : ℝ)^3191 := by
    have hnat : (5344385403 : ℕ)^4215*20000000000000^3191 ≤ 8741973149173^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344385403 10000000000 8741973149173 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526695889/1000000000 : ℝ)^4215 ≤ (2679710143723/6250000000000 : ℝ)^3191 := by
    have hnat : (526695889 : ℕ)^4215*6250000000000^3191 ≤ 2679710143723^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526695889 1000000000 2679710143723 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185394489/10000000000 : ℝ)^4215 ≤ (13414771941721/100000000000000 : ℝ)^3191 := by
    have hnat : (2185394489 : ℕ)^4215*100000000000000^3191 ≤ 13414771941721^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185394489 10000000000 13414771941721 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344385403/10000000000 : ℝ), (526695889/1000000000 : ℝ), (-2185394489/10000000000 : ℝ)] ![(8741973149173/20000000000000 : ℝ), (2679710143723/6250000000000 : ℝ), (13414771941721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344385403/10000000000 : ℝ)|^4215 ≤ (8741973149173/20000000000000 : ℝ)^3191
        have hw : |(5344385403/10000000000 : ℝ)|=(5344385403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526695889/1000000000 : ℝ)|^4215 ≤ (2679710143723/6250000000000 : ℝ)^3191
        have hw : |(526695889/1000000000 : ℝ)|=(526695889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185394489/10000000000 : ℝ)|^4215 ≤ (13414771941721/100000000000000 : ℝ)^3191
        have hw : |(-2185394489/10000000000 : ℝ)|=(2185394489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870289911/2000000000 : ℝ)*x 0 + (4227042533/10000000000 : ℝ)*x 1 + (4479418391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870289911/2000000000 : ℝ)^4215 ≤ (33317366909927/100000000000000 : ℝ)^3191 := by
    have hnat : (870289911 : ℕ)^4215*100000000000000^3191 ≤ 33317366909927^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870289911 2000000000 33317366909927 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227042533/10000000000 : ℝ)^4215 ≤ (32064968613779/100000000000000 : ℝ)^3191 := by
    have hnat : (4227042533 : ℕ)^4215*100000000000000^3191 ≤ 32064968613779^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227042533 10000000000 32064968613779 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479418391/10000000000 : ℝ)^4215 ≤ (3461766445637/10000000000000 : ℝ)^3191 := by
    have hnat : (4479418391 : ℕ)^4215*10000000000000^3191 ≤ 3461766445637^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479418391 10000000000 3461766445637 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870289911/2000000000 : ℝ), (4227042533/10000000000 : ℝ), (4479418391/10000000000 : ℝ)] ![(33317366909927/100000000000000 : ℝ), (32064968613779/100000000000000 : ℝ), (3461766445637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870289911/2000000000 : ℝ)|^4215 ≤ (33317366909927/100000000000000 : ℝ)^3191
        have hw : |(870289911/2000000000 : ℝ)|=(870289911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227042533/10000000000 : ℝ)|^4215 ≤ (32064968613779/100000000000000 : ℝ)^3191
        have hw : |(4227042533/10000000000 : ℝ)|=(4227042533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479418391/10000000000 : ℝ)|^4215 ≤ (3461766445637/10000000000000 : ℝ)^3191
        have hw : |(4479418391/10000000000 : ℝ)|=(4479418391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-424450979/2000000000 : ℝ)*x 0 + (5267273947/10000000000 : ℝ)*x 1 + (107823473/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424450979/2000000000 : ℝ)^4215 ≤ (12905212703281/100000000000000 : ℝ)^3191 := by
    have hnat : (424450979 : ℕ)^4215*100000000000000^3191 ≤ 12905212703281^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424450979 2000000000 12905212703281 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267273947/10000000000 : ℝ)^4215 ≤ (21439375027111/50000000000000 : ℝ)^3191 := by
    have hnat : (5267273947 : ℕ)^4215*50000000000000^3191 ≤ 21439375027111^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267273947 10000000000 21439375027111 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107823473/200000000 : ℝ)^4215 ≤ (44216037227331/100000000000000 : ℝ)^3191 := by
    have hnat : (107823473 : ℕ)^4215*100000000000000^3191 ≤ 44216037227331^3191*200000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107823473 200000000 44216037227331 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424450979/2000000000 : ℝ), (5267273947/10000000000 : ℝ), (107823473/200000000 : ℝ)] ![(12905212703281/100000000000000 : ℝ), (21439375027111/50000000000000 : ℝ), (44216037227331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424450979/2000000000 : ℝ)|^4215 ≤ (12905212703281/100000000000000 : ℝ)^3191
        have hw : |(-424450979/2000000000 : ℝ)|=(424450979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267273947/10000000000 : ℝ)|^4215 ≤ (21439375027111/50000000000000 : ℝ)^3191
        have hw : |(5267273947/10000000000 : ℝ)|=(5267273947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107823473/200000000 : ℝ)|^4215 ≤ (44216037227331/100000000000000 : ℝ)^3191
        have hw : |(107823473/200000000 : ℝ)|=(107823473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656310707/5000000000 : ℝ)*x 0 + (-1030589833/5000000000 : ℝ)*x 1 + (5391173841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656310707/5000000000 : ℝ)^4215 ≤ (43367040653523/100000000000000 : ℝ)^3191 := by
    have hnat : (2656310707 : ℕ)^4215*100000000000000^3191 ≤ 43367040653523^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656310707 5000000000 43367040653523 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030589833/5000000000 : ℝ)^4215 ≤ (310423000987/2500000000000 : ℝ)^3191 := by
    have hnat : (1030589833 : ℕ)^4215*2500000000000^3191 ≤ 310423000987^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030589833 5000000000 310423000987 2500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391173841/10000000000 : ℝ)^4215 ≤ (22108019648261/50000000000000 : ℝ)^3191 := by
    have hnat : (5391173841 : ℕ)^4215*50000000000000^3191 ≤ 22108019648261^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391173841 10000000000 22108019648261 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656310707/5000000000 : ℝ), (-1030589833/5000000000 : ℝ), (5391173841/10000000000 : ℝ)] ![(43367040653523/100000000000000 : ℝ), (310423000987/2500000000000 : ℝ), (22108019648261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656310707/5000000000 : ℝ)|^4215 ≤ (43367040653523/100000000000000 : ℝ)^3191
        have hw : |(2656310707/5000000000 : ℝ)|=(2656310707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030589833/5000000000 : ℝ)|^4215 ≤ (310423000987/2500000000000 : ℝ)^3191
        have hw : |(-1030589833/5000000000 : ℝ)|=(1030589833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391173841/10000000000 : ℝ)|^4215 ≤ (22108019648261/50000000000000 : ℝ)^3191
        have hw : |(5391173841/10000000000 : ℝ)|=(5391173841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312621419/10000000000 : ℝ)*x 0 + (539117379/1000000000 : ℝ)*x 1 + (-128823733/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312621419/10000000000 : ℝ)^4215 ≤ (10841760176859/25000000000000 : ℝ)^3191 := by
    have hnat : (5312621419 : ℕ)^4215*25000000000000^3191 ≤ 10841760176859^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312621419 10000000000 10841760176859 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539117379/1000000000 : ℝ)^4215 ≤ (8843207748803/20000000000000 : ℝ)^3191 := by
    have hnat : (539117379 : ℕ)^4215*20000000000000^3191 ≤ 8843207748803^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539117379 1000000000 8843207748803 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128823733/625000000 : ℝ)^4215 ≤ (3104230133209/25000000000000 : ℝ)^3191 := by
    have hnat : (128823733 : ℕ)^4215*25000000000000^3191 ≤ 3104230133209^3191*625000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128823733 625000000 3104230133209 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312621419/10000000000 : ℝ), (539117379/1000000000 : ℝ), (-128823733/625000000 : ℝ)] ![(10841760176859/25000000000000 : ℝ), (8843207748803/20000000000000 : ℝ), (3104230133209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312621419/10000000000 : ℝ)|^4215 ≤ (10841760176859/25000000000000 : ℝ)^3191
        have hw : |(5312621419/10000000000 : ℝ)|=(5312621419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539117379/1000000000 : ℝ)|^4215 ≤ (8843207748803/20000000000000 : ℝ)^3191
        have hw : |(539117379/1000000000 : ℝ)|=(539117379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128823733/625000000 : ℝ)|^4215 ≤ (3104230133209/25000000000000 : ℝ)^3191
        have hw : |(-128823733/625000000 : ℝ)|=(128823733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s6_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351458901/10000000000 : ℝ)*x 0 + (4478780147/10000000000 : ℝ)*x 1 + (2113841651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351458901/10000000000 : ℝ)^4215 ≤ (832936535801/2500000000000 : ℝ)^3191 := by
    have hnat : (4351458901 : ℕ)^4215*2500000000000^3191 ≤ 832936535801^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351458901 10000000000 832936535801 2500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478780147/10000000000 : ℝ)^4215 ≤ (34611149316831/100000000000000 : ℝ)^3191 := by
    have hnat : (4478780147 : ℕ)^4215*100000000000000^3191 ≤ 34611149316831^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478780147 10000000000 34611149316831 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113841651/5000000000 : ℝ)^4215 ≤ (4008923654341/12500000000000 : ℝ)^3191 := by
    have hnat : (2113841651 : ℕ)^4215*12500000000000^3191 ≤ 4008923654341^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113841651 5000000000 4008923654341 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351458901/10000000000 : ℝ), (4478780147/10000000000 : ℝ), (2113841651/5000000000 : ℝ)] ![(832936535801/2500000000000 : ℝ), (34611149316831/100000000000000 : ℝ), (4008923654341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351458901/10000000000 : ℝ)|^4215 ≤ (832936535801/2500000000000 : ℝ)^3191
        have hw : |(4351458901/10000000000 : ℝ)|=(4351458901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478780147/10000000000 : ℝ)|^4215 ≤ (34611149316831/100000000000000 : ℝ)^3191
        have hw : |(4478780147/10000000000 : ℝ)|=(4478780147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113841651/5000000000 : ℝ)|^4215 ≤ (4008923654341/12500000000000 : ℝ)^3191
        have hw : |(2113841651/5000000000 : ℝ)|=(2113841651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (883/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2867/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (883/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (883/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (883/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (883/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (883/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (883/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11447/100000 : ℝ) ^ (8429/2048 : ℝ) ≤ (13360909812178957/100000000000000000000 : ℝ) := by
    have hpowers : (11447/100000 : ℝ)^8429 ≤ (13360909812178957/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11447 : ℕ)^8429*100000000000000000000^2048 ≤ 13360909812178957^2048*100000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11447 100000 13360909812178957 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11447/100000 : ℝ)) (X := (13360909812178957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (883/6250 : ℝ) ^ (8429/2048 : ℝ) ≤ (3970798392160779/12500000000000000000 : ℝ) := by
    have hpowers : (883/6250 : ℝ)^8429 ≤ (3970798392160779/12500000000000000000 : ℝ)^2048 := by
      have hnat : (883 : ℕ)^8429*12500000000000000000^2048 ≤ 3970798392160779^2048*6250^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        883 6250 3970798392160779 12500000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (883/6250 : ℝ)) (X := (3970798392160779/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013360909812178957/50000000000000000000 : ℝ) ≤ (2500162299063091/2500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50013360909812178957/50000000000000000000 : ℝ)^2048 ≤ (2500162299063091/2500000000000000 : ℝ)^8429 := by
      have hnat : (50013360909812178957 : ℕ)^2048*2500000000000000^8429 ≤ 2500162299063091^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013360909812178957 50000000000000000000 2500162299063091 2500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162299063091/2500000000000000 : ℝ)) (X := (50013360909812178957/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045127296949465189/100000000000000000000 : ℝ) ≤ (10001096273835877/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (100045127296949465189/100000000000000000000 : ℝ)^2048 ≤ (10001096273835877/10000000000000000 : ℝ)^8429 := by
      have hnat : (100045127296949465189 : ℕ)^2048*10000000000000000^8429 ≤ 10001096273835877^8429*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045127296949465189 100000000000000000000 10001096273835877 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001096273835877/10000000000000000 : ℝ)) (X := (100045127296949465189/100000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253970798392160779/6250000000000000000 : ℝ) ≤ (1000154335141939/1000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (6253970798392160779/6250000000000000000 : ℝ)^2048 ≤ (1000154335141939/1000000000000000 : ℝ)^8429 := by
      have hnat : (6253970798392160779 : ℕ)^2048*1000000000000000^8429 ≤ 1000154335141939^8429*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253970798392160779 6250000000000000000 1000154335141939 1000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000154335141939/1000000000000000 : ℝ)) (X := (6253970798392160779/6250000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13360909812178957/100000000000000000000 : ℝ) ≤ ((13400752550477820631/13405000000000000000 : ℝ)+2*(447077583513/268100000000000 : ℝ)*(11447/100000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13400752550477820631/13405000000000000000 : ℝ)+2*(447077583513/268100000000000 : ℝ)*(11447/100000 : ℝ)=(2500162299063091/2500000000000000 : ℝ) by norm_num, show 1+2*(13360909812178957/100000000000000000000 : ℝ)=(50013360909812178957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3970798392160779/12500000000000000000 : ℝ)+(13360909812178957/100000000000000000000 : ℝ) ≤ ((13400752550477820631/13405000000000000000 : ℝ)+(447077583513/268100000000000 : ℝ)*((883/6250 : ℝ)+(11447/100000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (13400752550477820631/13405000000000000000 : ℝ)+(447077583513/268100000000000 : ℝ)*((883/6250 : ℝ)+(11447/100000 : ℝ))=(10001096273835877/10000000000000000 : ℝ) by norm_num, show 1+(3970798392160779/12500000000000000000 : ℝ)+(13360909812178957/100000000000000000000 : ℝ)=(100045127296949465189/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3970798392160779/12500000000000000000 : ℝ) ≤ ((13400752550477820631/13405000000000000000 : ℝ)+2*(447077583513/268100000000000 : ℝ)*(883/6250 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13400752550477820631/13405000000000000000 : ℝ)+2*(447077583513/268100000000000 : ℝ)*(883/6250 : ℝ)=(1000154335141939/1000000000000000 : ℝ) by norm_num, show 1+2*(3970798392160779/12500000000000000000 : ℝ)=(6253970798392160779/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13400752550477820631/13405000000000000000 : ℝ)*(X 1 0+X 2 0)+(447077583513/268100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (883/6250 : ℝ)) (c := (13400752550477820631/13405000000000000000 : ℝ)) (alpha := (447077583513/268100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13400752550477820631/13405000000000000000 : ℝ)*(X 0 1+X 2 1)+(447077583513/268100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (883/6250 : ℝ)) (c := (13400752550477820631/13405000000000000000 : ℝ)) (alpha := (447077583513/268100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13400752550477820631/13405000000000000000 : ℝ)*(X 0 2+X 1 2)+(447077583513/268100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (883/6250 : ℝ)) (c := (13400752550477820631/13405000000000000000 : ℝ)) (alpha := (447077583513/268100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122250279/10000000000 : ℝ)*X 0 0+(5391489799/10000000000 : ℝ)*X 0 1+(658369859/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334024087/625000000 : ℝ)*X 1 0+(-2185394493/10000000000 : ℝ)*X 1 1+(2633479449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344385403/10000000000 : ℝ)*X 2 0+(526695889/1000000000 : ℝ)*X 2 1+(-2185394489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870289911/2000000000 : ℝ)*X 0 0+(4227042533/10000000000 : ℝ)*X 0 1+(4479418391/10000000000 : ℝ)*X 0 2+(870289911/2000000000 : ℝ)*X 1 0+(4227042533/10000000000 : ℝ)*X 1 1+(4479418391/10000000000 : ℝ)*X 1 2+(870289911/2000000000 : ℝ)*X 2 0+(4227042533/10000000000 : ℝ)*X 2 1+(4479418391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424450979/2000000000 : ℝ)*X 0 0+(5267273947/10000000000 : ℝ)*X 0 1+(107823473/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656310707/5000000000 : ℝ)*X 1 0+(-1030589833/5000000000 : ℝ)*X 1 1+(5391173841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312621419/10000000000 : ℝ)*X 2 0+(539117379/1000000000 : ℝ)*X 2 1+(-128823733/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351458901/10000000000 : ℝ)*X 0 0+(4478780147/10000000000 : ℝ)*X 0 1+(2113841651/5000000000 : ℝ)*X 0 2+(4351458901/10000000000 : ℝ)*X 1 0+(4478780147/10000000000 : ℝ)*X 1 1+(2113841651/5000000000 : ℝ)*X 1 2+(4351458901/10000000000 : ℝ)*X 2 0+(4478780147/10000000000 : ℝ)*X 2 1+(2113841651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5349660221127881917927757421/670250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (801737889/50000000000000 : ℝ)*(base19) + (376839283/25000000000000 : ℝ)*(base23) + (60202757/100000000000000 : ℝ)*(lower2) + (208573409/100000000000000 : ℝ)*(upper3) + (135418309/100000000000000 : ℝ)*(upper5) + (5996308563123303/100000000000000 : ℝ)*(major0) + (5996308563123303/100000000000000 : ℝ)*(major1) + (5996308563123303/100000000000000 : ℝ)*(major2) + (2007545302892219/25000000000000 : ℝ)*(sp0) + (1606045119185413/20000000000000 : ℝ)*(sp1) + (8030225692045711/100000000000000 : ℝ)*(sp2) + (990591434740821/25000000000000 : ℝ)*(sp3) + (45987833967/100000000000000 : ℝ)*(sp4) + (23921827493/100000000000000 : ℝ)*(sp7) + (495298707598847/12500000000000 : ℝ)*(f.failure) + (8030227199402843/100000000000000 : ℝ)*(f.sum) + (73028468790881/13405000000000000000000000000 : ℝ)*base66 + (4165420616944214193/1340500000000000000000000000000000 : ℝ)*base67 + (8297482595786214193/1340500000000000000000000000000000 : ℝ)*base69 + (4714111406624285807/1340500000000000000000000000000000 : ℝ)*base72 + (28486016376249/13405000000000000000000000000 : ℝ)*base73 + (16865775016992214193/1340500000000000000000000000000000 : ℝ)*base75 + (4973795818670785807/1340500000000000000000000000000000 : ℝ)*base78 + (3150438096605714193/1340500000000000000000000000000000 : ℝ)*base79 + (10550446710473/1675625000000000000000000000 : ℝ)*base81 + (12896789/1250000000000000000000 : ℝ)*base90 + (12896789/1250000000000000000000 : ℝ)*base92 + (12896789/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (473429685817685351716435197/95750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187626107/100000000000000 : ℝ)*(base19) + (131574229/50000000000000 : ℝ)*(base23) + (240759/400000000000 : ℝ)*(upper3) + (35213863/100000000000000 : ℝ)*(lower4) + (6026784327949903/100000000000000 : ℝ)*(major0) + (6026784327949903/100000000000000 : ℝ)*(major1) + (6026784327949903/100000000000000 : ℝ)*(major2) + (1815811433/12500000000000 : ℝ)*(sp1) + (3700315049/25000000000000 : ℝ)*(sp2) + (82336469/100000000000000 : ℝ)*(sp3) + (8071040297698597/100000000000000 : ℝ)*(sp4) + (8071025583581027/100000000000000 : ℝ)*(sp5) + (1008878154161243/12500000000000 : ℝ)*(sp6) + (199126405552511/5000000000000 : ℝ)*(sp7) + (398252819338669/10000000000000 : ℝ)*(f.failure) + (8071040297698597/100000000000000 : ℝ)*(f.sum) + (3492682423823/1915000000000000000000000000 : ℝ)*base66 + (1741645467161171601/191500000000000000000000000000000 : ℝ)*base68 + (335638333120671601/191500000000000000000000000000000 : ℝ)*base70 + (680185153531328399/191500000000000000000000000000000 : ℝ)*base71 + (1121461613183/478750000000000000000000000 : ℝ)*base73 + (931929564124171601/191500000000000000000000000000000 : ℝ)*base76 + (809765938675671601/191500000000000000000000000000000 : ℝ)*base78 + (163366306287328399/191500000000000000000000000000000 : ℝ)*base79 + (3242133015333/478750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4374097/1000000000000000000000 : ℝ)*base89 + (4374097/1000000000000000000000 : ℝ)*base91 + (4374097/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1237_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (883/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s7_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-212226767/1000000000 : ℝ)*x 0 + (5391286701/10000000000 : ℝ)*x 1 + (2633575253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212226767/1000000000 : ℝ)^4215 ≤ (12905315315653/100000000000000 : ℝ)^3191 := by
    have hnat : (212226767 : ℕ)^4215*100000000000000^3191 ≤ 12905315315653^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212226767 1000000000 12905315315653 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391286701/10000000000 : ℝ)^4215 ≤ (345447359103/781250000000 : ℝ)^3191 := by
    have hnat : (5391286701 : ℕ)^4215*781250000000^3191 ≤ 345447359103^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391286701 10000000000 345447359103 781250000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633575253/5000000000 : ℝ)^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191 := by
    have hnat : (2633575253 : ℕ)^4215*100000000000000^3191 ≤ 42877422706271^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633575253 5000000000 42877422706271 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212226767/1000000000 : ℝ), (5391286701/10000000000 : ℝ), (2633575253/5000000000 : ℝ)] ![(12905315315653/100000000000000 : ℝ), (345447359103/781250000000 : ℝ), (42877422706271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212226767/1000000000 : ℝ)|^4215 ≤ (12905315315653/100000000000000 : ℝ)^3191
        have hw : |(-212226767/1000000000 : ℝ)|=(212226767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391286701/10000000000 : ℝ)|^4215 ≤ (345447359103/781250000000 : ℝ)^3191
        have hw : |(5391286701/10000000000 : ℝ)|=(5391286701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633575253/5000000000 : ℝ)|^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191
        have hw : |(2633575253/5000000000 : ℝ)|=(2633575253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344333901/10000000000 : ℝ)*x 0 + (-2185208993/10000000000 : ℝ)*x 1 + (2633575253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344333901/10000000000 : ℝ)^4215 ≤ (546366367003/1250000000000 : ℝ)^3191 := by
    have hnat : (5344333901 : ℕ)^4215*1250000000000^3191 ≤ 546366367003^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344333901 10000000000 546366367003 1250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185208993/10000000000 : ℝ)^4215 ≤ (6706633962163/50000000000000 : ℝ)^3191 := by
    have hnat : (2185208993 : ℕ)^4215*50000000000000^3191 ≤ 6706633962163^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185208993 10000000000 6706633962163 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633575253/5000000000 : ℝ)^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191 := by
    have hnat : (2633575253 : ℕ)^4215*100000000000000^3191 ≤ 42877422706271^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633575253 5000000000 42877422706271 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344333901/10000000000 : ℝ), (-2185208993/10000000000 : ℝ), (2633575253/5000000000 : ℝ)] ![(546366367003/1250000000000 : ℝ), (6706633962163/50000000000000 : ℝ), (42877422706271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344333901/10000000000 : ℝ)|^4215 ≤ (546366367003/1250000000000 : ℝ)^3191
        have hw : |(5344333901/10000000000 : ℝ)|=(5344333901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185208993/10000000000 : ℝ)|^4215 ≤ (6706633962163/50000000000000 : ℝ)^3191
        have hw : |(-2185208993/10000000000 : ℝ)|=(2185208993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633575253/5000000000 : ℝ)|^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191
        have hw : |(2633575253/5000000000 : ℝ)|=(2633575253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344333901/10000000000 : ℝ)*x 0 + (2633575253/5000000000 : ℝ)*x 1 + (-2185208993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344333901/10000000000 : ℝ)^4215 ≤ (546366367003/1250000000000 : ℝ)^3191 := by
    have hnat : (5344333901 : ℕ)^4215*1250000000000^3191 ≤ 546366367003^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344333901 10000000000 546366367003 1250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633575253/5000000000 : ℝ)^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191 := by
    have hnat : (2633575253 : ℕ)^4215*100000000000000^3191 ≤ 42877422706271^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633575253 5000000000 42877422706271 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185208993/10000000000 : ℝ)^4215 ≤ (6706633962163/50000000000000 : ℝ)^3191 := by
    have hnat : (2185208993 : ℕ)^4215*50000000000000^3191 ≤ 6706633962163^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185208993 10000000000 6706633962163 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344333901/10000000000 : ℝ), (2633575253/5000000000 : ℝ), (-2185208993/10000000000 : ℝ)] ![(546366367003/1250000000000 : ℝ), (42877422706271/100000000000000 : ℝ), (6706633962163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344333901/10000000000 : ℝ)|^4215 ≤ (546366367003/1250000000000 : ℝ)^3191
        have hw : |(5344333901/10000000000 : ℝ)|=(5344333901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633575253/5000000000 : ℝ)|^4215 ≤ (42877422706271/100000000000000 : ℝ)^3191
        have hw : |(2633575253/5000000000 : ℝ)|=(2633575253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185208993/10000000000 : ℝ)|^4215 ≤ (6706633962163/50000000000000 : ℝ)^3191
        have hw : |(-2185208993/10000000000 : ℝ)|=(2185208993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351459511/10000000000 : ℝ)*x 0 + (4227441233/10000000000 : ℝ)*x 1 + (4479017167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351459511/10000000000 : ℝ)^4215 ≤ (6663493520273/20000000000000 : ℝ)^3191 := by
    have hnat : (4351459511 : ℕ)^4215*20000000000000^3191 ≤ 6663493520273^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351459511 10000000000 6663493520273 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227441233/10000000000 : ℝ)^4215 ≤ (32068963622983/100000000000000 : ℝ)^3191 := by
    have hnat : (4227441233 : ℕ)^4215*100000000000000^3191 ≤ 32068963622983^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227441233 10000000000 32068963622983 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479017167/10000000000 : ℝ)^4215 ≤ (2163348047607/6250000000000 : ℝ)^3191 := by
    have hnat : (4479017167 : ℕ)^4215*6250000000000^3191 ≤ 2163348047607^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479017167 10000000000 2163348047607 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351459511/10000000000 : ℝ), (4227441233/10000000000 : ℝ), (4479017167/10000000000 : ℝ)] ![(6663493520273/20000000000000 : ℝ), (32068963622983/100000000000000 : ℝ), (2163348047607/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351459511/10000000000 : ℝ)|^4215 ≤ (6663493520273/20000000000000 : ℝ)^3191
        have hw : |(4351459511/10000000000 : ℝ)|=(4351459511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227441233/10000000000 : ℝ)|^4215 ≤ (32068963622983/100000000000000 : ℝ)^3191
        have hw : |(4227441233/10000000000 : ℝ)|=(4227441233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479017167/10000000000 : ℝ)|^4215 ≤ (2163348047607/6250000000000 : ℝ)^3191
        have hw : |(4479017167/10000000000 : ℝ)|=(4479017167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-530568123/2500000000 : ℝ)*x 0 + (2633731683/5000000000 : ℝ)*x 1 + (539097259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530568123/2500000000 : ℝ)^4215 ≤ (12905354047357/100000000000000 : ℝ)^3191 := by
    have hnat : (530568123 : ℕ)^4215*100000000000000^3191 ≤ 12905354047357^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530568123 2500000000 12905354047357 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633731683/5000000000 : ℝ)^4215 ≤ (10720196719001/25000000000000 : ℝ)^3191 := by
    have hnat : (2633731683 : ℕ)^4215*25000000000000^3191 ≤ 10720196719001^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633731683 5000000000 10720196719001 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539097259/1000000000 : ℝ)^4215 ≤ (2210692953223/5000000000000 : ℝ)^3191 := by
    have hnat : (539097259 : ℕ)^4215*5000000000000^3191 ≤ 2210692953223^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539097259 1000000000 2210692953223 5000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530568123/2500000000 : ℝ), (2633731683/5000000000 : ℝ), (539097259/1000000000 : ℝ)] ![(12905354047357/100000000000000 : ℝ), (10720196719001/25000000000000 : ℝ), (2210692953223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530568123/2500000000 : ℝ)|^4215 ≤ (12905354047357/100000000000000 : ℝ)^3191
        have hw : |(-530568123/2500000000 : ℝ)|=(530568123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633731683/5000000000 : ℝ)|^4215 ≤ (10720196719001/25000000000000 : ℝ)^3191
        have hw : |(2633731683/5000000000 : ℝ)|=(2633731683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539097259/1000000000 : ℝ)|^4215 ≤ (2210692953223/5000000000000 : ℝ)^3191
        have hw : |(539097259/1000000000 : ℝ)|=(539097259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42501367/80000000 : ℝ)*x 0 + (-5153467/25000000 : ℝ)*x 1 + (1078194493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42501367/80000000 : ℝ)^4215 ≤ (21683786985143/50000000000000 : ℝ)^3191 := by
    have hnat : (42501367 : ℕ)^4215*50000000000000^3191 ≤ 21683786985143^3191*80000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42501367 80000000 21683786985143 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153467/25000000 : ℝ)^4215 ≤ (2483713661023/20000000000000 : ℝ)^3191 := by
    have hnat : (5153467 : ℕ)^4215*20000000000000^3191 ≤ 2483713661023^3191*25000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153467 25000000 2483713661023 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078194493/2000000000 : ℝ)^4215 ≤ (44213857710293/100000000000000 : ℝ)^3191 := by
    have hnat : (1078194493 : ℕ)^4215*100000000000000^3191 ≤ 44213857710293^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078194493 2000000000 44213857710293 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42501367/80000000 : ℝ), (-5153467/25000000 : ℝ), (1078194493/2000000000 : ℝ)] ![(21683786985143/50000000000000 : ℝ), (2483713661023/20000000000000 : ℝ), (44213857710293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42501367/80000000 : ℝ)|^4215 ≤ (21683786985143/50000000000000 : ℝ)^3191
        have hw : |(42501367/80000000 : ℝ)|=(42501367/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5153467/25000000 : ℝ)|^4215 ≤ (2483713661023/20000000000000 : ℝ)^3191
        have hw : |(-5153467/25000000 : ℝ)|=(5153467/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078194493/2000000000 : ℝ)|^4215 ≤ (44213857710293/100000000000000 : ℝ)^3191
        have hw : |(1078194493/2000000000 : ℝ)|=(1078194493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41505241/78125000 : ℝ)*x 0 + (5390972473/10000000000 : ℝ)*x 1 + (-1030693413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41505241/78125000 : ℝ)^4215 ≤ (43367573679157/100000000000000 : ℝ)^3191 := by
    have hnat : (41505241 : ℕ)^4215*100000000000000^3191 ≤ 43367573679157^3191*78125000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41505241 78125000 43367573679157 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390972473/10000000000 : ℝ)^4215 ≤ (276336611231/625000000000 : ℝ)^3191 := by
    have hnat : (5390972473 : ℕ)^4215*625000000000^3191 ≤ 276336611231^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390972473 10000000000 276336611231 625000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030693413/5000000000 : ℝ)^4215 ≤ (12418568512013/100000000000000 : ℝ)^3191 := by
    have hnat : (1030693413 : ℕ)^4215*100000000000000^3191 ≤ 12418568512013^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030693413 5000000000 12418568512013 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41505241/78125000 : ℝ), (5390972473/10000000000 : ℝ), (-1030693413/5000000000 : ℝ)] ![(43367573679157/100000000000000 : ℝ), (276336611231/625000000000 : ℝ), (12418568512013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41505241/78125000 : ℝ)|^4215 ≤ (43367573679157/100000000000000 : ℝ)^3191
        have hw : |(41505241/78125000 : ℝ)|=(41505241/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390972473/10000000000 : ℝ)|^4215 ≤ (276336611231/625000000000 : ℝ)^3191
        have hw : |(5390972473/10000000000 : ℝ)|=(5390972473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030693413/5000000000 : ℝ)|^4215 ≤ (12418568512013/100000000000000 : ℝ)^3191
        have hw : |(-1030693413/5000000000 : ℝ)|=(1030693413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s7_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175734491/5000000000 : ℝ)*x 0 + (4478382891/10000000000 : ℝ)*x 1 + (1057019449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175734491/5000000000 : ℝ)^4215 ≤ (33317563387753/100000000000000 : ℝ)^3191 := by
    have hnat : (2175734491 : ℕ)^4215*100000000000000^3191 ≤ 33317563387753^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175734491 5000000000 33317563387753 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478382891/10000000000 : ℝ)^4215 ≤ (276856754499/800000000000 : ℝ)^3191 := by
    have hnat : (4478382891 : ℕ)^4215*800000000000^3191 ≤ 276856754499^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478382891 10000000000 276856754499 800000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057019449/2500000000 : ℝ)^4215 ≤ (16037671145539/50000000000000 : ℝ)^3191 := by
    have hnat : (1057019449 : ℕ)^4215*50000000000000^3191 ≤ 16037671145539^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057019449 2500000000 16037671145539 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175734491/5000000000 : ℝ), (4478382891/10000000000 : ℝ), (1057019449/2500000000 : ℝ)] ![(33317563387753/100000000000000 : ℝ), (276856754499/800000000000 : ℝ), (16037671145539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175734491/5000000000 : ℝ)|^4215 ≤ (33317563387753/100000000000000 : ℝ)^3191
        have hw : |(2175734491/5000000000 : ℝ)|=(2175734491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478382891/10000000000 : ℝ)|^4215 ≤ (276856754499/800000000000 : ℝ)^3191
        have hw : |(4478382891/10000000000 : ℝ)|=(4478382891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057019449/2500000000 : ℝ)|^4215 ≤ (16037671145539/50000000000000 : ℝ)^3191
        have hw : |(1057019449/2500000000 : ℝ)|=(1057019449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (717/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2867/25000 : ℝ) ^ (8429/2048 : ℝ) ≤ (673103979249523/5000000000000000000 : ℝ) := by
    have hpowers : (2867/25000 : ℝ)^8429 ≤ (673103979249523/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2867 : ℕ)^8429*5000000000000000000^2048 ≤ 673103979249523^2048*25000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2867 25000 673103979249523 5000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2867/25000 : ℝ)) (X := (673103979249523/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7053/50000 : ℝ) ^ (8429/2048 : ℝ) ≤ (3156329072579319/10000000000000000000 : ℝ) := by
    have hpowers : (7053/50000 : ℝ)^8429 ≤ (3156329072579319/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7053 : ℕ)^8429*10000000000000000000^2048 ≤ 3156329072579319^2048*50000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7053 50000 3156329072579319 10000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7053/50000 : ℝ)) (X := (3156329072579319/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500673103979249523/2500000000000000000 : ℝ) ≤ (2000130822302469/2000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (2500673103979249523/2500000000000000000 : ℝ)^2048 ≤ (2000130822302469/2000000000000000 : ℝ)^8429 := by
      have hnat : (2500673103979249523 : ℕ)^2048*2000000000000000^8429 ≤ 2000130822302469^8429*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500673103979249523 2500000000000000000 2000130822302469 2000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130822302469/2000000000000000 : ℝ)) (X := (2500673103979249523/2500000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000900507406215673/2000000000000000000 : ℝ) ≤ (5000546899080997/5000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (2000900507406215673/2000000000000000000 : ℝ)^2048 ≤ (5000546899080997/5000000000000000 : ℝ)^8429 := by
      have hnat : (2000900507406215673 : ℕ)^2048*5000000000000000^8429 ≤ 5000546899080997^8429*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000900507406215673 2000000000000000000 5000546899080997 5000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546899080997/5000000000000000 : ℝ)) (X := (2000900507406215673/2000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003156329072579319/5000000000000000000 : ℝ) ≤ (10001533484811643/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (5003156329072579319/5000000000000000000 : ℝ)^2048 ≤ (10001533484811643/10000000000000000 : ℝ)^8429 := by
      have hnat : (5003156329072579319 : ℕ)^2048*10000000000000000^8429 ≤ 10001533484811643^8429*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003156329072579319 5000000000000000000 10001533484811643 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001533484811643/10000000000000000 : ℝ)) (X := (5003156329072579319/5000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(673103979249523/5000000000000000000 : ℝ) ≤ ((13185820446586608323/13190000000000000000 : ℝ)+2*(439686649649/263800000000000 : ℝ)*(2867/25000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13185820446586608323/13190000000000000000 : ℝ)+2*(439686649649/263800000000000 : ℝ)*(2867/25000 : ℝ)=(2000130822302469/2000000000000000 : ℝ) by norm_num, show 1+2*(673103979249523/5000000000000000000 : ℝ)=(2500673103979249523/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3156329072579319/10000000000000000000 : ℝ)+(673103979249523/5000000000000000000 : ℝ) ≤ ((13185820446586608323/13190000000000000000 : ℝ)+(439686649649/263800000000000 : ℝ)*((7053/50000 : ℝ)+(2867/25000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (13185820446586608323/13190000000000000000 : ℝ)+(439686649649/263800000000000 : ℝ)*((7053/50000 : ℝ)+(2867/25000 : ℝ))=(5000546899080997/5000000000000000 : ℝ) by norm_num, show 1+(3156329072579319/10000000000000000000 : ℝ)+(673103979249523/5000000000000000000 : ℝ)=(2000900507406215673/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3156329072579319/10000000000000000000 : ℝ) ≤ ((13185820446586608323/13190000000000000000 : ℝ)+2*(439686649649/263800000000000 : ℝ)*(7053/50000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13185820446586608323/13190000000000000000 : ℝ)+2*(439686649649/263800000000000 : ℝ)*(7053/50000 : ℝ)=(10001533484811643/10000000000000000 : ℝ) by norm_num, show 1+2*(3156329072579319/10000000000000000000 : ℝ)=(5003156329072579319/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13185820446586608323/13190000000000000000 : ℝ)*(X 1 0+X 2 0)+(439686649649/263800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (13185820446586608323/13190000000000000000 : ℝ)) (alpha := (439686649649/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13185820446586608323/13190000000000000000 : ℝ)*(X 0 1+X 2 1)+(439686649649/263800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (13185820446586608323/13190000000000000000 : ℝ)) (alpha := (439686649649/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13185820446586608323/13190000000000000000 : ℝ)*(X 0 2+X 1 2)+(439686649649/263800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (13185820446586608323/13190000000000000000 : ℝ)) (alpha := (439686649649/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212226767/1000000000 : ℝ)*X 0 0+(5391286701/10000000000 : ℝ)*X 0 1+(2633575253/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344333901/10000000000 : ℝ)*X 1 0+(-2185208993/10000000000 : ℝ)*X 1 1+(2633575253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344333901/10000000000 : ℝ)*X 2 0+(2633575253/5000000000 : ℝ)*X 2 1+(-2185208993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351459511/10000000000 : ℝ)*X 0 0+(4227441233/10000000000 : ℝ)*X 0 1+(4479017167/10000000000 : ℝ)*X 0 2+(4351459511/10000000000 : ℝ)*X 1 0+(4227441233/10000000000 : ℝ)*X 1 1+(4479017167/10000000000 : ℝ)*X 1 2+(4351459511/10000000000 : ℝ)*X 2 0+(4227441233/10000000000 : ℝ)*X 2 1+(4479017167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-530568123/2500000000 : ℝ)*X 0 0+(2633731683/5000000000 : ℝ)*X 0 1+(539097259/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42501367/80000000 : ℝ)*X 1 0+(-5153467/25000000 : ℝ)*X 1 1+(1078194493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41505241/78125000 : ℝ)*X 2 0+(5390972473/10000000000 : ℝ)*X 2 1+(-1030693413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175734491/5000000000 : ℝ)*X 0 0+(4478382891/10000000000 : ℝ)*X 0 1+(1057019449/2500000000 : ℝ)*X 0 2+(2175734491/5000000000 : ℝ)*X 1 0+(4478382891/10000000000 : ℝ)*X 1 1+(1057019449/2500000000 : ℝ)*X 1 2+(2175734491/5000000000 : ℝ)*X 2 0+(4478382891/10000000000 : ℝ)*X 2 1+(1057019449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5882452480212407794161541833/659500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1724786229/100000000000000 : ℝ)*(base19) + (321100087/20000000000000 : ℝ)*(base23) + (7968789/12500000000000 : ℝ)*(lower2) + (224103669/100000000000000 : ℝ)*(upper3) + (136540249/100000000000000 : ℝ)*(upper5) + (6015378944999457/100000000000000 : ℝ)*(major0) + (6015378944999457/100000000000000 : ℝ)*(major1) + (6015378944999457/100000000000000 : ℝ)*(major2) + (4027859151902049/50000000000000 : ℝ)*(sp0) + (8055764406649043/100000000000000 : ℝ)*(sp1) + (2013941131483709/25000000000000 : ℝ)*(sp2) + (1987482974138547/50000000000000 : ℝ)*(sp3) + (23913815587/50000000000000 : ℝ)*(sp4) + (5102593547/20000000000000 : ℝ)*(sp7) + (397499146124483/10000000000000 : ℝ)*(f.failure) + (8055766131435271/100000000000000 : ℝ)*(f.sum) + (53819889039247/13190000000000000000000000000 : ℝ)*base66 + (1794603057174669389/1319000000000000000000000000000000 : ℝ)*base68 + (18586749634177669389/1319000000000000000000000000000000 : ℝ)*base70 + (17579910163756669389/1319000000000000000000000000000000 : ℝ)*base72 + (94998455029873/13190000000000000000000000000 : ℝ)*base73 + (12498424744132330611/1319000000000000000000000000000000 : ℝ)*base75 + (1010063006023669389/1319000000000000000000000000000000 : ℝ)*base78 + (26301211980579330611/1319000000000000000000000000000000 : ℝ)*base79 + (24141649434693/13190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (16698079/1000000000000000000000 : ℝ)*base89 + (16698079/1000000000000000000000 : ℝ)*base91 + (16698079/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2449410048372694642839/659500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1651444023/100000000000000 : ℝ)*(base19) + (1783176363/100000000000000 : ℝ)*(base23) + (93455209/100000000000000 : ℝ)*(upper2) + (10001627/10000000000000 : ℝ)*(upper3) + (92329581/50000000000000 : ℝ)*(upper5) + (75573024029051/1250000000000 : ℝ)*(major0) + (75573024029051/1250000000000 : ℝ)*(major1) + (75573024029051/1250000000000 : ℝ)*(major2) + (45220718883/100000000000000 : ℝ)*(sp1) + (22356189151/50000000000000 : ℝ)*(sp2) + (8096562177049117/100000000000000 : ℝ)*(sp4) + (8096515304886211/100000000000000 : ℝ)*(sp5) + (2024128920373613/25000000000000 : ℝ)*(sp6) + (499390192974709/12500000000000 : ℝ)*(sp7) + (499390192974709/12500000000000 : ℝ)*(f.failure) + (8096562177049117/100000000000000 : ℝ)*(f.sum) + (247708350917/329750000000000000000000000 : ℝ)*base66 + (24997698714016473/16487500000000000000000000000000 : ℝ)*base67 + (50388178846616473/16487500000000000000000000000000 : ℝ)*base69 + (199482738793758527/16487500000000000000000000000000 : ℝ)*base72 + (306567189873/263800000000000000000000000 : ℝ)*base73 + (2480748800653973/16487500000000000000000000000000 : ℝ)*base75 + (192112730501383527/16487500000000000000000000000000 : ℝ)*base78 + (45845672345158527/16487500000000000000000000000000 : ℝ)*base80 + (334835926607/659500000000000000000000000 : ℝ)*base82 + (6466617/1250000000000000000000 : ℝ)*base89 + (6466617/1250000000000000000000 : ℝ)*base91 + (6466617/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s8_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061135151/5000000000 : ℝ)*x 0 + (269562473/500000000 : ℝ)*x 1 + (263359303/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061135151/5000000000 : ℝ)^4215 ≤ (6452668228319/50000000000000 : ℝ)^3191 := by
    have hnat : (1061135151 : ℕ)^4215*50000000000000^3191 ≤ 6452668228319^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061135151 5000000000 6452668228319 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269562473/500000000 : ℝ)^4215 ≤ (44216858513951/100000000000000 : ℝ)^3191 := by
    have hnat : (269562473 : ℕ)^4215*100000000000000^3191 ≤ 44216858513951^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269562473 500000000 44216858513951 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263359303/500000000 : ℝ)^4215 ≤ (4287780501363/10000000000000 : ℝ)^3191 := by
    have hnat : (263359303 : ℕ)^4215*10000000000000^3191 ≤ 4287780501363^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263359303 500000000 4287780501363 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061135151/5000000000 : ℝ), (269562473/500000000 : ℝ), (263359303/500000000 : ℝ)] ![(6452668228319/50000000000000 : ℝ), (44216858513951/100000000000000 : ℝ), (4287780501363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061135151/5000000000 : ℝ)|^4215 ≤ (6452668228319/50000000000000 : ℝ)^3191
        have hw : |(-1061135151/5000000000 : ℝ)|=(1061135151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269562473/500000000 : ℝ)|^4215 ≤ (44216858513951/100000000000000 : ℝ)^3191
        have hw : |(269562473/500000000 : ℝ)|=(269562473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263359303/500000000 : ℝ)|^4215 ≤ (4287780501363/10000000000000 : ℝ)^3191
        have hw : |(263359303/500000000 : ℝ)|=(263359303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668040579/1250000000 : ℝ)*x 0 + (-2185174281/10000000000 : ℝ)*x 1 + (658398249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668040579/1250000000 : ℝ)^4215 ≤ (21854604612851/50000000000000 : ℝ)^3191 := by
    have hnat : (668040579 : ℕ)^4215*50000000000000^3191 ≤ 21854604612851^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668040579 1250000000 21854604612851 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185174281/10000000000 : ℝ)^4215 ≤ (13412986481019/100000000000000 : ℝ)^3191 := by
    have hnat : (2185174281 : ℕ)^4215*100000000000000^3191 ≤ 13412986481019^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185174281 10000000000 13412986481019 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658398249/1250000000 : ℝ)^4215 ≤ (8575560856487/20000000000000 : ℝ)^3191 := by
    have hnat : (658398249 : ℕ)^4215*20000000000000^3191 ≤ 8575560856487^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658398249 1250000000 8575560856487 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668040579/1250000000 : ℝ), (-2185174281/10000000000 : ℝ), (658398249/1250000000 : ℝ)] ![(21854604612851/50000000000000 : ℝ), (13412986481019/100000000000000 : ℝ), (8575560856487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668040579/1250000000 : ℝ)|^4215 ≤ (21854604612851/50000000000000 : ℝ)^3191
        have hw : |(668040579/1250000000 : ℝ)|=(668040579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185174281/10000000000 : ℝ)|^4215 ≤ (13412986481019/100000000000000 : ℝ)^3191
        have hw : |(-2185174281/10000000000 : ℝ)|=(2185174281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658398249/1250000000 : ℝ)|^4215 ≤ (8575560856487/20000000000000 : ℝ)^3191
        have hw : |(658398249/1250000000 : ℝ)|=(658398249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534432467/1000000000 : ℝ)*x 0 + (1053437197/2000000000 : ℝ)*x 1 + (-2185174239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534432467/1000000000 : ℝ)^4215 ≤ (21854604818111/50000000000000 : ℝ)^3191 := by
    have hnat : (534432467 : ℕ)^4215*50000000000000^3191 ≤ 21854604818111^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534432467 1000000000 21854604818111 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053437197/2000000000 : ℝ)^4215 ≤ (10719451051791/25000000000000 : ℝ)^3191 := by
    have hnat : (1053437197 : ℕ)^4215*25000000000000^3191 ≤ 10719451051791^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053437197 2000000000 10719451051791 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185174239/10000000000 : ℝ)^4215 ≤ (6706493070243/50000000000000 : ℝ)^3191 := by
    have hnat : (2185174239 : ℕ)^4215*50000000000000^3191 ≤ 6706493070243^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185174239 10000000000 6706493070243 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534432467/1000000000 : ℝ), (1053437197/2000000000 : ℝ), (-2185174239/10000000000 : ℝ)] ![(21854604818111/50000000000000 : ℝ), (10719451051791/25000000000000 : ℝ), (6706493070243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534432467/1000000000 : ℝ)|^4215 ≤ (21854604818111/50000000000000 : ℝ)^3191
        have hw : |(534432467/1000000000 : ℝ)|=(534432467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053437197/2000000000 : ℝ)|^4215 ≤ (10719451051791/25000000000000 : ℝ)^3191
        have hw : |(1053437197/2000000000 : ℝ)|=(1053437197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185174239/10000000000 : ℝ)|^4215 ≤ (6706493070243/50000000000000 : ℝ)^3191
        have hw : |(-2185174239/10000000000 : ℝ)|=(2185174239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175730663/5000000000 : ℝ)*x 0 + (4227514671/10000000000 : ℝ)*x 1 + (4478943281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175730663/5000000000 : ℝ)^4215 ≤ (8329371489409/25000000000000 : ℝ)^3191 := by
    have hnat : (2175730663 : ℕ)^4215*25000000000000^3191 ≤ 8329371489409^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175730663 5000000000 8329371489409 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227514671/10000000000 : ℝ)^4215 ≤ (16034849745707/50000000000000 : ℝ)^3191 := by
    have hnat : (4227514671 : ℕ)^4215*50000000000000^3191 ≤ 16034849745707^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227514671 10000000000 16034849745707 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478943281/10000000000 : ℝ)^4215 ≤ (4326601818281/12500000000000 : ℝ)^3191 := by
    have hnat : (4478943281 : ℕ)^4215*12500000000000^3191 ≤ 4326601818281^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478943281 10000000000 4326601818281 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175730663/5000000000 : ℝ), (4227514671/10000000000 : ℝ), (4478943281/10000000000 : ℝ)] ![(8329371489409/25000000000000 : ℝ), (16034849745707/50000000000000 : ℝ), (4326601818281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175730663/5000000000 : ℝ)|^4215 ≤ (8329371489409/25000000000000 : ℝ)^3191
        have hw : |(2175730663/5000000000 : ℝ)|=(2175730663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227514671/10000000000 : ℝ)|^4215 ≤ (16034849745707/50000000000000 : ℝ)^3191
        have hw : |(4227514671/10000000000 : ℝ)|=(4227514671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478943281/10000000000 : ℝ)|^4215 ≤ (4326601818281/12500000000000 : ℝ)^3191
        have hw : |(4478943281/10000000000 : ℝ)|=(4478943281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061137591/5000000000 : ℝ)*x 0 + (5267498553/10000000000 : ℝ)*x 1 + (5390935669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061137591/5000000000 : ℝ)^4215 ≤ (1290537565423/10000000000000 : ℝ)^3191 := by
    have hnat : (1061137591 : ℕ)^4215*10000000000000^3191 ≤ 1290537565423^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061137591 5000000000 1290537565423 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267498553/10000000000 : ℝ)^4215 ≤ (42881165244269/100000000000000 : ℝ)^3191 := by
    have hnat : (5267498553 : ℕ)^4215*100000000000000^3191 ≤ 42881165244269^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267498553 10000000000 42881165244269 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390935669/10000000000 : ℝ)^4215 ≤ (4421345908743/10000000000000 : ℝ)^3191 := by
    have hnat : (5390935669 : ℕ)^4215*10000000000000^3191 ≤ 4421345908743^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390935669 10000000000 4421345908743 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061137591/5000000000 : ℝ), (5267498553/10000000000 : ℝ), (5390935669/10000000000 : ℝ)] ![(1290537565423/10000000000000 : ℝ), (42881165244269/100000000000000 : ℝ), (4421345908743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061137591/5000000000 : ℝ)|^4215 ≤ (1290537565423/10000000000000 : ℝ)^3191
        have hw : |(-1061137591/5000000000 : ℝ)|=(1061137591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267498553/10000000000 : ℝ)|^4215 ≤ (42881165244269/100000000000000 : ℝ)^3191
        have hw : |(5267498553/10000000000 : ℝ)|=(5267498553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390935669/10000000000 : ℝ)|^4215 ≤ (4421345908743/10000000000000 : ℝ)^3191
        have hw : |(5390935669/10000000000 : ℝ)|=(5390935669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340087/5000000000 : ℝ)*x 0 + (-82456971/400000000 : ℝ)*x 1 + (5390935683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340087/5000000000 : ℝ)^4215 ≤ (10841918559399/25000000000000 : ℝ)^3191 := by
    have hnat : (2656340087 : ℕ)^4215*25000000000000^3191 ≤ 10841918559399^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340087 5000000000 10841918559399 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82456971/400000000 : ℝ)^4215 ≤ (3104716629383/25000000000000 : ℝ)^3191 := by
    have hnat : (82456971 : ℕ)^4215*25000000000000^3191 ≤ 3104716629383^3191*400000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82456971 400000000 3104716629383 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390935683/10000000000 : ℝ)^4215 ≤ (5526682404887/12500000000000 : ℝ)^3191 := by
    have hnat : (5390935683 : ℕ)^4215*12500000000000^3191 ≤ 5526682404887^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390935683 10000000000 5526682404887 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340087/5000000000 : ℝ), (-82456971/400000000 : ℝ), (5390935683/10000000000 : ℝ)] ![(10841918559399/25000000000000 : ℝ), (3104716629383/25000000000000 : ℝ), (5526682404887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340087/5000000000 : ℝ)|^4215 ≤ (10841918559399/25000000000000 : ℝ)^3191
        have hw : |(2656340087/5000000000 : ℝ)|=(2656340087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82456971/400000000 : ℝ)|^4215 ≤ (3104716629383/25000000000000 : ℝ)^3191
        have hw : |(-82456971/400000000 : ℝ)|=(82456971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390935683/10000000000 : ℝ)|^4215 ≤ (5526682404887/12500000000000 : ℝ)^3191
        have hw : |(5390935683/10000000000 : ℝ)|=(5390935683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340111/5000000000 : ℝ)*x 0 + (336933467/625000000 : ℝ)*x 1 + (-2061424497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340111/5000000000 : ℝ)^4215 ≤ (1084191868879/2500000000000 : ℝ)^3191 := by
    have hnat : (2656340111 : ℕ)^4215*2500000000000^3191 ≤ 1084191868879^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340111 5000000000 1084191868879 2500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336933467/625000000 : ℝ)^4215 ≤ (11053364238317/25000000000000 : ℝ)^3191 := by
    have hnat : (336933467 : ℕ)^4215*25000000000000^3191 ≤ 11053364238317^3191*625000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336933467 625000000 11053364238317 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061424497/10000000000 : ℝ)^4215 ≤ (12418868284133/100000000000000 : ℝ)^3191 := by
    have hnat : (2061424497 : ℕ)^4215*100000000000000^3191 ≤ 12418868284133^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061424497 10000000000 12418868284133 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340111/5000000000 : ℝ), (336933467/625000000 : ℝ), (-2061424497/10000000000 : ℝ)] ![(1084191868879/2500000000000 : ℝ), (11053364238317/25000000000000 : ℝ), (12418868284133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340111/5000000000 : ℝ)|^4215 ≤ (1084191868879/2500000000000 : ℝ)^3191
        have hw : |(2656340111/5000000000 : ℝ)|=(2656340111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336933467/625000000 : ℝ)|^4215 ≤ (11053364238317/25000000000000 : ℝ)^3191
        have hw : |(336933467/625000000 : ℝ)|=(336933467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061424497/10000000000 : ℝ)|^4215 ≤ (12418868284133/100000000000000 : ℝ)^3191
        have hw : |(-2061424497/10000000000 : ℝ)|=(2061424497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s8_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870294151/2000000000 : ℝ)*x 0 + (1119577433/2500000000 : ℝ)*x 1 + (4228150527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870294151/2000000000 : ℝ)^4215 ≤ (1041174416227/3125000000000 : ℝ)^3191 := by
    have hnat : (870294151 : ℕ)^4215*3125000000000^3191 ≤ 1041174416227^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870294151 2000000000 1041174416227 3125000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119577433/2500000000 : ℝ)^4215 ≤ (432579344399/1250000000000 : ℝ)^3191 := by
    have hnat : (1119577433 : ℕ)^4215*1250000000000^3191 ≤ 432579344399^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119577433 2500000000 432579344399 1250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228150527/10000000000 : ℝ)^4215 ≤ (16038035555187/50000000000000 : ℝ)^3191 := by
    have hnat : (4228150527 : ℕ)^4215*50000000000000^3191 ≤ 16038035555187^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228150527 10000000000 16038035555187 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870294151/2000000000 : ℝ), (1119577433/2500000000 : ℝ), (4228150527/10000000000 : ℝ)] ![(1041174416227/3125000000000 : ℝ), (432579344399/1250000000000 : ℝ), (16038035555187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870294151/2000000000 : ℝ)|^4215 ≤ (1041174416227/3125000000000 : ℝ)^3191
        have hw : |(870294151/2000000000 : ℝ)|=(870294151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119577433/2500000000 : ℝ)|^4215 ≤ (432579344399/1250000000000 : ℝ)^3191
        have hw : |(1119577433/2500000000 : ℝ)|=(1119577433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228150527/10000000000 : ℝ)|^4215 ≤ (16038035555187/50000000000000 : ℝ)^3191
        have hw : |(4228150527/10000000000 : ℝ)|=(4228150527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11473/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (717/6250 : ℝ) ^ (8429/2048 : ℝ) ≤ (13481415580732177/100000000000000000000 : ℝ) := by
    have hpowers : (717/6250 : ℝ)^8429 ≤ (13481415580732177/100000000000000000000 : ℝ)^2048 := by
      have hnat : (717 : ℕ)^8429*100000000000000000000^2048 ≤ 13481415580732177^2048*6250^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 6250 13481415580732177 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/6250 : ℝ)) (X := (13481415580732177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (8429/2048 : ℝ) ≤ (15763234987843043/50000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^8429 ≤ (15763234987843043/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7051 : ℕ)^8429*50000000000000000000^2048 ≤ 15763234987843043^2048*50000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 15763234987843043 50000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (15763234987843043/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013481415580732177/50000000000000000000 : ℝ) ≤ (10000655050936807/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50013481415580732177/50000000000000000000 : ℝ)^2048 ≤ (10000655050936807/10000000000000000 : ℝ)^8429 := by
      have hnat : (50013481415580732177 : ℕ)^2048*10000000000000000^8429 ≤ 10000655050936807^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013481415580732177 50000000000000000000 10000655050936807 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000655050936807/10000000000000000 : ℝ)) (X := (50013481415580732177/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045007885556418263/100000000000000000000 : ℝ) ≤ (500054668673921/500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (100045007885556418263/100000000000000000000 : ℝ)^2048 ≤ (500054668673921/500000000000000 : ℝ)^8429 := by
      have hnat : (100045007885556418263 : ℕ)^2048*500000000000000^8429 ≤ 500054668673921^8429*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045007885556418263 100000000000000000000 500054668673921 500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500054668673921/500000000000000 : ℝ)) (X := (100045007885556418263/100000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015763234987843043/25000000000000000000 : ℝ) ≤ (10001531696020033/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (25015763234987843043/25000000000000000000 : ℝ)^2048 ≤ (10001531696020033/10000000000000000 : ℝ)^8429 := by
      have hnat : (25015763234987843043 : ℕ)^2048*10000000000000000^8429 ≤ 10001531696020033^8429*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015763234987843043 25000000000000000000 10001531696020033 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001531696020033/10000000000000000 : ℝ)) (X := (25015763234987843043/25000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13481415580732177/100000000000000000000 : ℝ) ≤ ((13145832955784516869/13150000000000000000 : ℝ)+2*(438322541613/263000000000000 : ℝ)*(717/6250 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13145832955784516869/13150000000000000000 : ℝ)+2*(438322541613/263000000000000 : ℝ)*(717/6250 : ℝ)=(10000655050936807/10000000000000000 : ℝ) by norm_num, show 1+2*(13481415580732177/100000000000000000000 : ℝ)=(50013481415580732177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15763234987843043/50000000000000000000 : ℝ)+(13481415580732177/100000000000000000000 : ℝ) ≤ ((13145832955784516869/13150000000000000000 : ℝ)+(438322541613/263000000000000 : ℝ)*((7051/50000 : ℝ)+(717/6250 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (13145832955784516869/13150000000000000000 : ℝ)+(438322541613/263000000000000 : ℝ)*((7051/50000 : ℝ)+(717/6250 : ℝ))=(500054668673921/500000000000000 : ℝ) by norm_num, show 1+(15763234987843043/50000000000000000000 : ℝ)+(13481415580732177/100000000000000000000 : ℝ)=(100045007885556418263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15763234987843043/50000000000000000000 : ℝ) ≤ ((13145832955784516869/13150000000000000000 : ℝ)+2*(438322541613/263000000000000 : ℝ)*(7051/50000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (13145832955784516869/13150000000000000000 : ℝ)+2*(438322541613/263000000000000 : ℝ)*(7051/50000 : ℝ)=(10001531696020033/10000000000000000 : ℝ) by norm_num, show 1+2*(15763234987843043/50000000000000000000 : ℝ)=(25015763234987843043/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13145832955784516869/13150000000000000000 : ℝ)*(X 1 0+X 2 0)+(438322541613/263000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13145832955784516869/13150000000000000000 : ℝ)) (alpha := (438322541613/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13145832955784516869/13150000000000000000 : ℝ)*(X 0 1+X 2 1)+(438322541613/263000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13145832955784516869/13150000000000000000 : ℝ)) (alpha := (438322541613/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13145832955784516869/13150000000000000000 : ℝ)*(X 0 2+X 1 2)+(438322541613/263000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13145832955784516869/13150000000000000000 : ℝ)) (alpha := (438322541613/263000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061135151/5000000000 : ℝ)*X 0 0+(269562473/500000000 : ℝ)*X 0 1+(263359303/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668040579/1250000000 : ℝ)*X 1 0+(-2185174281/10000000000 : ℝ)*X 1 1+(658398249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534432467/1000000000 : ℝ)*X 2 0+(1053437197/2000000000 : ℝ)*X 2 1+(-2185174239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175730663/5000000000 : ℝ)*X 0 0+(4227514671/10000000000 : ℝ)*X 0 1+(4478943281/10000000000 : ℝ)*X 0 2+(2175730663/5000000000 : ℝ)*X 1 0+(4227514671/10000000000 : ℝ)*X 1 1+(4478943281/10000000000 : ℝ)*X 1 2+(2175730663/5000000000 : ℝ)*X 2 0+(4227514671/10000000000 : ℝ)*X 2 1+(4478943281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061137591/5000000000 : ℝ)*X 0 0+(5267498553/10000000000 : ℝ)*X 0 1+(5390935669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656340087/5000000000 : ℝ)*X 1 0+(-82456971/400000000 : ℝ)*X 1 1+(5390935683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656340111/5000000000 : ℝ)*X 2 0+(336933467/625000000 : ℝ)*X 2 1+(-2061424497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870294151/2000000000 : ℝ)*X 0 0+(1119577433/2500000000 : ℝ)*X 0 1+(4228150527/10000000000 : ℝ)*X 0 2+(870294151/2000000000 : ℝ)*X 1 0+(1119577433/2500000000 : ℝ)*X 1 1+(4228150527/10000000000 : ℝ)*X 1 2+(870294151/2000000000 : ℝ)*X 2 0+(1119577433/2500000000 : ℝ)*X 2 1+(4228150527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (428993202012575993632537083/65750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (637671579/50000000000000 : ℝ)*(base19) + (1233502999/100000000000000 : ℝ)*(base23) + (52990489/100000000000000 : ℝ)*(lower2) + (14627583/12500000000000 : ℝ)*(upper3) + (123243987/100000000000000 : ℝ)*(upper5) + (601888535511223/10000000000000 : ℝ)*(major0) + (601888535511223/10000000000000 : ℝ)*(major1) + (601888535511223/10000000000000 : ℝ)*(major2) + (2015106772148009/25000000000000 : ℝ)*(sp0) + (8060460703410871/100000000000000 : ℝ)*(sp1) + (8060460745251029/100000000000000 : ℝ)*(sp2) + (3977289900911431/100000000000000 : ℝ)*(sp3) + (34890161993/100000000000000 : ℝ)*(sp4) + (18613071943/100000000000000 : ℝ)*(sp7) + (1988654256991687/50000000000000 : ℝ)*(f.failure) + (8060461978754029/100000000000000 : ℝ)*(f.sum) + (1192938713/164375000000000000000000000 : ℝ)*base65 + (924199320711729213/131500000000000000000000000000000 : ℝ)*base68 + (2748762528576229213/131500000000000000000000000000000 : ℝ)*base70 + (481263764887229213/131500000000000000000000000000000 : ℝ)*base72 + (1527524291991/1315000000000000000000000000 : ℝ)*base74 + (3281820469558729213/131500000000000000000000000000000 : ℝ)*base76 + (1181594755864229213/131500000000000000000000000000000 : ℝ)*base78 + (522760312405729213/131500000000000000000000000000000 : ℝ)*base80 + (1396641066929/328750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (29614131/5000000000000000000000 : ℝ)*base89 + (29614131/5000000000000000000000 : ℝ)*base91 + (29614131/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (512034020325166872450834057/657500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1362826733/100000000000000 : ℝ)*(base19) + (215684009/12500000000000 : ℝ)*(base23) + (239710037/50000000000000 : ℝ)*(lower1) + (85925899/50000000000000 : ℝ)*(upper2) + (44684569/50000000000000 : ℝ)*(upper3) + (98985343/100000000000000 : ℝ)*(upper5) + (6049340494046649/100000000000000 : ℝ)*(major0) + (6049340494046649/100000000000000 : ℝ)*(major1) + (6049340494046649/100000000000000 : ℝ)*(major2) + (89252921/1562500000000 : ℝ)*(sp1) + (405062377262227/5000000000000 : ℝ)*(sp4) + (506327529389429/6250000000000 : ℝ)*(sp5) + (2025311454943117/25000000000000 : ℝ)*(sp6) + (399743341689011/10000000000000 : ℝ)*(sp7) + (399743341689011/10000000000000 : ℝ)*(f.failure) + (405062377262227/5000000000000 : ℝ)*(f.sum) + (43376991320663/13150000000000000000000000000 : ℝ)*base66 + (13761901471355271981/1315000000000000000000000000000000 : ℝ)*base67 + (33104257393005271981/1315000000000000000000000000000000 : ℝ)*base69 + (5781525658345271981/1315000000000000000000000000000000 : ℝ)*base71 + (33385790771563/13150000000000000000000000000 : ℝ)*base74 + (28824498966494728019/1315000000000000000000000000000000 : ℝ)*base76 + (9341017673534728019/1315000000000000000000000000000000 : ℝ)*base78 + (26610721398415271981/1315000000000000000000000000000000 : ℝ)*base79 + (693585482063263/13150000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6257/1000000000000000000000 : ℝ)*base90 + (6257/1000000000000000000000 : ℝ)*base92 + (6257/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1237_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1237_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (883/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1237_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1237_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1237_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (883/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11473/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

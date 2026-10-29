-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1324_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:49.813084+00:00
-- url     : https://prove2.me/submissions/a959e97f-0329-4dfd-bfec-bfd22777aae4

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
theorem support_rectangle_w1324_s6_0 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029809117/5000000000 : ℝ)*x 0 + (270682741/500000000 : ℝ)*x 1 + (5244022701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029809117/5000000000 : ℝ)^1071 ≤ (12538338271199/100000000000000 : ℝ)^815 := by
    have hnat : (1029809117 : ℕ)^1071*100000000000000^815 ≤ 12538338271199^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029809117 5000000000 12538338271199 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270682741/500000000 : ℝ)^1071 ≤ (11161361530141/25000000000000 : ℝ)^815 := by
    have hnat : (270682741 : ℕ)^1071*25000000000000^815 ≤ 11161361530141^815*500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270682741 500000000 11161361530141 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244022701/10000000000 : ℝ)^1071 ≤ (21408107796369/50000000000000 : ℝ)^815 := by
    have hnat : (5244022701 : ℕ)^1071*50000000000000^815 ≤ 21408107796369^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244022701 10000000000 21408107796369 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029809117/5000000000 : ℝ), (270682741/500000000 : ℝ), (5244022701/10000000000 : ℝ)] ![(12538338271199/100000000000000 : ℝ), (11161361530141/25000000000000 : ℝ), (21408107796369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029809117/5000000000 : ℝ)|^1071 ≤ (12538338271199/100000000000000 : ℝ)^815
        have hw : |(-1029809117/5000000000 : ℝ)|=(1029809117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270682741/500000000 : ℝ)|^1071 ≤ (11161361530141/25000000000000 : ℝ)^815
        have hw : |(270682741/500000000 : ℝ)|=(270682741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244022701/10000000000 : ℝ)|^1071 ≤ (21408107796369/50000000000000 : ℝ)^815
        have hw : |(5244022701/10000000000 : ℝ)|=(5244022701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_1 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674653003/5000000000 : ℝ)*x 0 + (-2146061941/10000000000 : ℝ)*x 1 + (5244022739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674653003/5000000000 : ℝ)^1071 ≤ (8789877669063/20000000000000 : ℝ)^815 := by
    have hnat : (2674653003 : ℕ)^1071*20000000000000^815 ≤ 8789877669063^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674653003 5000000000 8789877669063 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146061941/10000000000 : ℝ)^1071 ≤ (13234395640033/100000000000000 : ℝ)^815 := by
    have hnat : (2146061941 : ℕ)^1071*100000000000000^815 ≤ 13234395640033^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146061941 10000000000 13234395640033 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244022739/10000000000 : ℝ)^1071 ≤ (8563243200091/20000000000000 : ℝ)^815 := by
    have hnat : (5244022739 : ℕ)^1071*20000000000000^815 ≤ 8563243200091^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244022739 10000000000 8563243200091 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674653003/5000000000 : ℝ), (-2146061941/10000000000 : ℝ), (5244022739/10000000000 : ℝ)] ![(8789877669063/20000000000000 : ℝ), (13234395640033/100000000000000 : ℝ), (8563243200091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674653003/5000000000 : ℝ)|^1071 ≤ (8789877669063/20000000000000 : ℝ)^815
        have hw : |(2674653003/5000000000 : ℝ)|=(2674653003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146061941/10000000000 : ℝ)|^1071 ≤ (13234395640033/100000000000000 : ℝ)^815
        have hw : |(-2146061941/10000000000 : ℝ)|=(2146061941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244022739/10000000000 : ℝ)|^1071 ≤ (8563243200091/20000000000000 : ℝ)^815
        have hw : |(5244022739/10000000000 : ℝ)|=(5244022739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_2 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668663249/1250000000 : ℝ)*x 0 + (1311005693/2500000000 : ℝ)*x 1 + (-429212383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668663249/1250000000 : ℝ)^1071 ≤ (21974694097081/50000000000000 : ℝ)^815 := by
    have hnat : (668663249 : ℕ)^1071*50000000000000^815 ≤ 21974694097081^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668663249 1250000000 21974694097081 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311005693/2500000000 : ℝ)^1071 ≤ (1712648654181/4000000000000 : ℝ)^815 := by
    have hnat : (1311005693 : ℕ)^1071*4000000000000^815 ≤ 1712648654181^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311005693 2500000000 1712648654181 4000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429212383/2000000000 : ℝ)^1071 ≤ (3308598857333/25000000000000 : ℝ)^815 := by
    have hnat : (429212383 : ℕ)^1071*25000000000000^815 ≤ 3308598857333^815*2000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429212383 2000000000 3308598857333 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668663249/1250000000 : ℝ), (1311005693/2500000000 : ℝ), (-429212383/2000000000 : ℝ)] ![(21974694097081/50000000000000 : ℝ), (1712648654181/4000000000000 : ℝ), (3308598857333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668663249/1250000000 : ℝ)|^1071 ≤ (21974694097081/50000000000000 : ℝ)^815
        have hw : |(668663249/1250000000 : ℝ)|=(668663249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311005693/2500000000 : ℝ)|^1071 ≤ (1712648654181/4000000000000 : ℝ)^815
        have hw : |(1311005693/2500000000 : ℝ)|=(1311005693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429212383/2000000000 : ℝ)|^1071 ≤ (3308598857333/25000000000000 : ℝ)^815
        have hw : |(-429212383/2000000000 : ℝ)|=(429212383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_3 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4331345681/10000000000 : ℝ)*x 0 + (2079140549/5000000000 : ℝ)*x 1 + (4511183003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331345681/10000000000 : ℝ)^1071 ≤ (16651459145257/50000000000000 : ℝ)^815 := by
    have hnat : (4331345681 : ℕ)^1071*50000000000000^815 ≤ 16651459145257^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331345681 10000000000 16651459145257 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079140549/5000000000 : ℝ)^1071 ≤ (31565357183021/100000000000000 : ℝ)^815 := by
    have hnat : (2079140549 : ℕ)^1071*100000000000000^815 ≤ 31565357183021^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079140549 5000000000 31565357183021 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511183003/10000000000 : ℝ)^1071 ≤ (17565862257209/50000000000000 : ℝ)^815 := by
    have hnat : (4511183003 : ℕ)^1071*50000000000000^815 ≤ 17565862257209^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511183003 10000000000 17565862257209 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331345681/10000000000 : ℝ), (2079140549/5000000000 : ℝ), (4511183003/10000000000 : ℝ)] ![(16651459145257/50000000000000 : ℝ), (31565357183021/100000000000000 : ℝ), (17565862257209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331345681/10000000000 : ℝ)|^1071 ≤ (16651459145257/50000000000000 : ℝ)^815
        have hw : |(4331345681/10000000000 : ℝ)|=(4331345681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079140549/5000000000 : ℝ)|^1071 ≤ (31565357183021/100000000000000 : ℝ)^815
        have hw : |(2079140549/5000000000 : ℝ)|=(2079140549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511183003/10000000000 : ℝ)|^1071 ≤ (17565862257209/50000000000000 : ℝ)^815
        have hw : |(4511183003/10000000000 : ℝ)|=(4511183003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_4 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059631257/10000000000 : ℝ)*x 0 + (2622314483/5000000000 : ℝ)*x 1 + (5413044953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059631257/10000000000 : ℝ)^1071 ≤ (6269221227067/50000000000000 : ℝ)^815 := by
    have hnat : (2059631257 : ℕ)^1071*50000000000000^815 ≤ 6269221227067^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059631257 10000000000 6269221227067 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622314483/5000000000 : ℝ)^1071 ≤ (42822720572651/100000000000000 : ℝ)^815 := by
    have hnat : (2622314483 : ℕ)^1071*100000000000000^815 ≤ 42822720572651^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622314483 5000000000 42822720572651 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413044953/10000000000 : ℝ)^1071 ≤ (44638836965857/100000000000000 : ℝ)^815 := by
    have hnat : (5413044953 : ℕ)^1071*100000000000000^815 ≤ 44638836965857^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413044953 10000000000 44638836965857 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059631257/10000000000 : ℝ), (2622314483/5000000000 : ℝ), (5413044953/10000000000 : ℝ)] ![(6269221227067/50000000000000 : ℝ), (42822720572651/100000000000000 : ℝ), (44638836965857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059631257/10000000000 : ℝ)|^1071 ≤ (6269221227067/50000000000000 : ℝ)^815
        have hw : |(-2059631257/10000000000 : ℝ)|=(2059631257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622314483/5000000000 : ℝ)|^1071 ≤ (42822720572651/100000000000000 : ℝ)^815
        have hw : |(2622314483/5000000000 : ℝ)|=(2622314483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413044953/10000000000 : ℝ)|^1071 ≤ (44638836965857/100000000000000 : ℝ)^815
        have hw : |(5413044953/10000000000 : ℝ)|=(5413044953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_5 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (26528527/50000000 : ℝ)*x 0 + (-1977039397/10000000000 : ℝ)*x 1 + (1353261141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26528527/50000000 : ℝ)^1071 ≤ (10869813375731/25000000000000 : ℝ)^815 := by
    have hnat : (26528527 : ℕ)^1071*25000000000000^815 ≤ 10869813375731^815*50000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26528527 50000000 10869813375731 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977039397/10000000000 : ℝ)^1071 ≤ (11881913727279/100000000000000 : ℝ)^815 := by
    have hnat : (1977039397 : ℕ)^1071*100000000000000^815 ≤ 11881913727279^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977039397 10000000000 11881913727279 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353261141/2500000000 : ℝ)^1071 ≤ (22319416375161/50000000000000 : ℝ)^815 := by
    have hnat : (1353261141 : ℕ)^1071*50000000000000^815 ≤ 22319416375161^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353261141 2500000000 22319416375161 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26528527/50000000 : ℝ), (-1977039397/10000000000 : ℝ), (1353261141/2500000000 : ℝ)] ![(10869813375731/25000000000000 : ℝ), (11881913727279/100000000000000 : ℝ), (22319416375161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26528527/50000000 : ℝ)|^1071 ≤ (10869813375731/25000000000000 : ℝ)^815
        have hw : |(26528527/50000000 : ℝ)|=(26528527/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1977039397/10000000000 : ℝ)|^1071 ≤ (11881913727279/100000000000000 : ℝ)^815
        have hw : |(-1977039397/10000000000 : ℝ)|=(1977039397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353261141/2500000000 : ℝ)|^1071 ≤ (22319416375161/50000000000000 : ℝ)^815
        have hw : |(1353261141/2500000000 : ℝ)|=(1353261141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_6 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (10611411/20000000 : ℝ)*x 0 + (2706522213/5000000000 : ℝ)*x 1 + (-39540789/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10611411/20000000 : ℝ)^1071 ≤ (10869813644953/25000000000000 : ℝ)^815 := by
    have hnat : (10611411 : ℕ)^1071*25000000000000^815 ≤ 10869813644953^815*20000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10611411 20000000 10869813644953 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706522213/5000000000 : ℝ)^1071 ≤ (44638831254837/100000000000000 : ℝ)^815 := by
    have hnat : (2706522213 : ℕ)^1071*100000000000000^815 ≤ 44638831254837^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706522213 5000000000 44638831254837 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39540789/200000000 : ℝ)^1071 ≤ (11881914145859/100000000000000 : ℝ)^815 := by
    have hnat : (39540789 : ℕ)^1071*100000000000000^815 ≤ 11881914145859^815*200000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39540789 200000000 11881914145859 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10611411/20000000 : ℝ), (2706522213/5000000000 : ℝ), (-39540789/200000000 : ℝ)] ![(10869813644953/25000000000000 : ℝ), (44638831254837/100000000000000 : ℝ), (11881914145859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10611411/20000000 : ℝ)|^1071 ≤ (10869813644953/25000000000000 : ℝ)^815
        have hw : |(10611411/20000000 : ℝ)|=(10611411/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706522213/5000000000 : ℝ)|^1071 ≤ (44638831254837/100000000000000 : ℝ)^815
        have hw : |(2706522213/5000000000 : ℝ)|=(2706522213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39540789/200000000 : ℝ)|^1071 ≤ (11881914145859/100000000000000 : ℝ)^815
        have hw : |(-39540789/200000000 : ℝ)|=(39540789/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_7 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4331371557/10000000000 : ℝ)*x 0 + (1127480259/2500000000 : ℝ)*x 1 + (4159549443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331371557/10000000000 : ℝ)^1071 ≤ (16651589870321/50000000000000 : ℝ)^815 := by
    have hnat : (4331371557 : ℕ)^1071*50000000000000^815 ≤ 16651589870321^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331371557 10000000000 16651589870321 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127480259/2500000000 : ℝ)^1071 ≤ (17559405123109/50000000000000 : ℝ)^815 := by
    have hnat : (1127480259 : ℕ)^1071*50000000000000^815 ≤ 17559405123109^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127480259 2500000000 17559405123109 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159549443/10000000000 : ℝ)^1071 ≤ (3157800999137/10000000000000 : ℝ)^815 := by
    have hnat : (4159549443 : ℕ)^1071*10000000000000^815 ≤ 3157800999137^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159549443 10000000000 3157800999137 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331371557/10000000000 : ℝ), (1127480259/2500000000 : ℝ), (4159549443/10000000000 : ℝ)] ![(16651589870321/50000000000000 : ℝ), (17559405123109/50000000000000 : ℝ), (3157800999137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331371557/10000000000 : ℝ)|^1071 ≤ (16651589870321/50000000000000 : ℝ)^815
        have hw : |(4331371557/10000000000 : ℝ)|=(4331371557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127480259/2500000000 : ℝ)|^1071 ≤ (17559405123109/50000000000000 : ℝ)^815
        have hw : |(1127480259/2500000000 : ℝ)|=(1127480259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159549443/10000000000 : ℝ)|^1071 ≤ (3157800999137/10000000000000 : ℝ)^815
        have hw : |(4159549443/10000000000 : ℝ)|=(4159549443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_8 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-31948831/10000000000 : ℝ)*x 0 + (5751164241/10000000000 : ℝ)*x 1 + (6044946947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31948831/10000000000 : ℝ)^1071 ≤ (52550669291/100000000000000 : ℝ)^815 := by
    have hnat : (31948831 : ℕ)^1071*100000000000000^815 ≤ 52550669291^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31948831 10000000000 52550669291 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5751164241/10000000000 : ℝ)^1071 ≤ (48338431272359/100000000000000 : ℝ)^815 := by
    have hnat : (5751164241 : ℕ)^1071*100000000000000^815 ≤ 48338431272359^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751164241 10000000000 48338431272359 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6044946947/10000000000 : ℝ)^1071 ≤ (12902254512919/25000000000000 : ℝ)^815 := by
    have hnat : (6044946947 : ℕ)^1071*25000000000000^815 ≤ 12902254512919^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044946947 10000000000 12902254512919 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31948831/10000000000 : ℝ), (5751164241/10000000000 : ℝ), (6044946947/10000000000 : ℝ)] ![(52550669291/100000000000000 : ℝ), (48338431272359/100000000000000 : ℝ), (12902254512919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31948831/10000000000 : ℝ)|^1071 ≤ (52550669291/100000000000000 : ℝ)^815
        have hw : |(-31948831/10000000000 : ℝ)|=(31948831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5751164241/10000000000 : ℝ)|^1071 ≤ (48338431272359/100000000000000 : ℝ)^815
        have hw : |(5751164241/10000000000 : ℝ)|=(5751164241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6044946947/10000000000 : ℝ)|^1071 ≤ (12902254512919/25000000000000 : ℝ)^815
        have hw : |(6044946947/10000000000 : ℝ)|=(6044946947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_9 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1003520063/10000000000 : ℝ)*x 0 + (-4300855319/10000000000 : ℝ)*x 1 + (870206033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003520063/10000000000 : ℝ)^1071 ≤ (2437053064981/50000000000000 : ℝ)^815 := by
    have hnat : (1003520063 : ℕ)^1071*50000000000000^815 ≤ 2437053064981^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003520063 10000000000 2437053064981 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300855319/10000000000 : ℝ)^1071 ≤ (1319807450533/4000000000000 : ℝ)^815 := by
    have hnat : (4300855319 : ℕ)^1071*4000000000000^815 ≤ 1319807450533^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300855319 10000000000 1319807450533 4000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870206033/1250000000 : ℝ)^1071 ≤ (62130707598909/100000000000000 : ℝ)^815 := by
    have hnat : (870206033 : ℕ)^1071*100000000000000^815 ≤ 62130707598909^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870206033 1250000000 62130707598909 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1003520063/10000000000 : ℝ), (-4300855319/10000000000 : ℝ), (870206033/1250000000 : ℝ)] ![(2437053064981/50000000000000 : ℝ), (1319807450533/4000000000000 : ℝ), (62130707598909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1003520063/10000000000 : ℝ)|^1071 ≤ (2437053064981/50000000000000 : ℝ)^815
        have hw : |(1003520063/10000000000 : ℝ)|=(1003520063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4300855319/10000000000 : ℝ)|^1071 ≤ (1319807450533/4000000000000 : ℝ)^815
        have hw : |(-4300855319/10000000000 : ℝ)|=(4300855319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(870206033/1250000000 : ℝ)|^1071 ≤ (62130707598909/100000000000000 : ℝ)^815
        have hw : |(870206033/1250000000 : ℝ)|=(870206033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s6_10 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1413618847/10000000000 : ℝ)*x 0 + (711522433/1250000000 : ℝ)*x 1 + (5415538163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1413618847/10000000000 : ℝ)^1071 ≤ (7646150622893/100000000000000 : ℝ)^815 := by
    have hnat : (1413618847 : ℕ)^1071*100000000000000^815 ≤ 7646150622893^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413618847 10000000000 7646150622893 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711522433/1250000000 : ℝ)^1071 ≤ (11921997976429/25000000000000 : ℝ)^815 := by
    have hnat : (711522433 : ℕ)^1071*25000000000000^815 ≤ 11921997976429^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711522433 1250000000 11921997976429 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415538163/10000000000 : ℝ)^1071 ≤ (2791616091577/6250000000000 : ℝ)^815 := by
    have hnat : (5415538163 : ℕ)^1071*6250000000000^815 ≤ 2791616091577^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415538163 10000000000 2791616091577 6250000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1413618847/10000000000 : ℝ), (711522433/1250000000 : ℝ), (5415538163/10000000000 : ℝ)] ![(7646150622893/100000000000000 : ℝ), (11921997976429/25000000000000 : ℝ), (2791616091577/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1413618847/10000000000 : ℝ)|^1071 ≤ (7646150622893/100000000000000 : ℝ)^815
        have hw : |(1413618847/10000000000 : ℝ)|=(1413618847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(711522433/1250000000 : ℝ)|^1071 ≤ (11921997976429/25000000000000 : ℝ)^815
        have hw : |(711522433/1250000000 : ℝ)|=(711522433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415538163/10000000000 : ℝ)|^1071 ≤ (2791616091577/6250000000000 : ℝ)^815
        have hw : |(5415538163/10000000000 : ℝ)|=(5415538163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1324_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2221/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1837/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11097/100000 : ℝ) ^ (4283/1024 : ℝ) ≤ (10149869855100323/100000000000000000000 : ℝ) := by
    have hpowers : (11097/100000 : ℝ)^4283 ≤ (10149869855100323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11097 : ℕ)^4283*100000000000000000000^1024 ≤ 10149869855100323^1024*100000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11097 100000 10149869855100323 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11097/100000 : ℝ)) (X := (10149869855100323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (4283/1024 : ℝ) ≤ (8236921538919799/25000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^4283 ≤ (8236921538919799/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2941 : ℕ)^4283*25000000000000000000^1024 ≤ 8236921538919799^1024*20000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 8236921538919799 25000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (8236921538919799/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010149869855100323/50000000000000000000 : ℝ) ≤ (10000485298347887/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50010149869855100323/50000000000000000000 : ℝ)^1024 ≤ (10000485298347887/10000000000000000 : ℝ)^4283 := by
      have hnat : (50010149869855100323 : ℕ)^1024*10000000000000000^4283 ≤ 10000485298347887^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010149869855100323 50000000000000000000 10000485298347887 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000485298347887/10000000000000000 : ℝ)) (X := (50010149869855100323/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043097556010779519/100000000000000000000 : ℝ) ≤ (5000515113973487/5000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (100043097556010779519/100000000000000000000 : ℝ)^1024 ≤ (5000515113973487/5000000000000000 : ℝ)^4283 := by
      have hnat : (100043097556010779519 : ℕ)^1024*5000000000000000^4283 ≤ 5000515113973487^4283*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043097556010779519 100000000000000000000 5000515113973487 5000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000515113973487/5000000000000000 : ℝ)) (X := (100043097556010779519/100000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508236921538919799/12500000000000000000 : ℝ) ≤ (10001575157546061/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (12508236921538919799/12500000000000000000 : ℝ)^1024 ≤ (10001575157546061/10000000000000000 : ℝ)^4283 := by
      have hnat : (12508236921538919799 : ℕ)^1024*10000000000000000^4283 ≤ 10001575157546061^4283*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508236921538919799 12500000000000000000 10001575157546061 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001575157546061/10000000000000000 : ℝ)) (X := (12508236921538919799/12500000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10149869855100323/100000000000000000000 : ℝ) ≤ ((18034828394458519709/18040000000000000000 : ℝ)+2*(544929599087/360800000000000 : ℝ)*(11097/100000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (18034828394458519709/18040000000000000000 : ℝ)+2*(544929599087/360800000000000 : ℝ)*(11097/100000 : ℝ)=(10000485298347887/10000000000000000 : ℝ) by norm_num, show 1+2*(10149869855100323/100000000000000000000 : ℝ)=(50010149869855100323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8236921538919799/25000000000000000000 : ℝ)+(10149869855100323/100000000000000000000 : ℝ) ≤ ((18034828394458519709/18040000000000000000 : ℝ)+(544929599087/360800000000000 : ℝ)*((2941/20000 : ℝ)+(11097/100000 : ℝ)))^(4283/1024 : ℝ) := by
    rw [show (18034828394458519709/18040000000000000000 : ℝ)+(544929599087/360800000000000 : ℝ)*((2941/20000 : ℝ)+(11097/100000 : ℝ))=(5000515113973487/5000000000000000 : ℝ) by norm_num, show 1+(8236921538919799/25000000000000000000 : ℝ)+(10149869855100323/100000000000000000000 : ℝ)=(100043097556010779519/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8236921538919799/25000000000000000000 : ℝ) ≤ ((18034828394458519709/18040000000000000000 : ℝ)+2*(544929599087/360800000000000 : ℝ)*(2941/20000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (18034828394458519709/18040000000000000000 : ℝ)+2*(544929599087/360800000000000 : ℝ)*(2941/20000 : ℝ)=(10001575157546061/10000000000000000 : ℝ) by norm_num, show 1+2*(8236921538919799/25000000000000000000 : ℝ)=(12508236921538919799/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18034828394458519709/18040000000000000000 : ℝ)*(X 1 0+X 2 0)+(544929599087/360800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (18034828394458519709/18040000000000000000 : ℝ)) (alpha := (544929599087/360800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18034828394458519709/18040000000000000000 : ℝ)*(X 0 1+X 2 1)+(544929599087/360800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (18034828394458519709/18040000000000000000 : ℝ)) (alpha := (544929599087/360800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18034828394458519709/18040000000000000000 : ℝ)*(X 0 2+X 1 2)+(544929599087/360800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11097/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (18034828394458519709/18040000000000000000 : ℝ)) (alpha := (544929599087/360800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1029809117/5000000000 : ℝ)*X 0 0+(270682741/500000000 : ℝ)*X 0 1+(5244022701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674653003/5000000000 : ℝ)*X 1 0+(-2146061941/10000000000 : ℝ)*X 1 1+(5244022739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668663249/1250000000 : ℝ)*X 2 0+(1311005693/2500000000 : ℝ)*X 2 1+(-429212383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331345681/10000000000 : ℝ)*X 0 0+(2079140549/5000000000 : ℝ)*X 0 1+(4511183003/10000000000 : ℝ)*X 0 2+(4331345681/10000000000 : ℝ)*X 1 0+(2079140549/5000000000 : ℝ)*X 1 1+(4511183003/10000000000 : ℝ)*X 1 2+(4331345681/10000000000 : ℝ)*X 2 0+(2079140549/5000000000 : ℝ)*X 2 1+(4511183003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2059631257/10000000000 : ℝ)*X 0 0+(2622314483/5000000000 : ℝ)*X 0 1+(5413044953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26528527/50000000 : ℝ)*X 1 0+(-1977039397/10000000000 : ℝ)*X 1 1+(1353261141/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10611411/20000000 : ℝ)*X 2 0+(2706522213/5000000000 : ℝ)*X 2 1+(-39540789/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331371557/10000000000 : ℝ)*X 0 0+(1127480259/2500000000 : ℝ)*X 0 1+(4159549443/10000000000 : ℝ)*X 0 2+(4331371557/10000000000 : ℝ)*X 1 0+(1127480259/2500000000 : ℝ)*X 1 1+(4159549443/10000000000 : ℝ)*X 1 2+(4331371557/10000000000 : ℝ)*X 2 0+(1127480259/2500000000 : ℝ)*X 2 1+(4159549443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-31948831/10000000000 : ℝ)*X 0 0+(5751164241/10000000000 : ℝ)*X 0 1+(6044946947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1003520063/10000000000 : ℝ)*X 1 0+(-4300855319/10000000000 : ℝ)*X 1 1+(870206033/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1413618847/10000000000 : ℝ)*X 0 0+(711522433/1250000000 : ℝ)*X 0 1+(5415538163/10000000000 : ℝ)*X 0 2+(1413618847/10000000000 : ℝ)*X 1 0+(711522433/1250000000 : ℝ)*X 1 1+(5415538163/10000000000 : ℝ)*X 1 2+(1413618847/10000000000 : ℝ)*X 2 0+(711522433/1250000000 : ℝ)*X 2 1+(5415538163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s6_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55667844591041505147681/3608000000000000000000000000 : ℝ) := by norm_num
    linear_combination (402443487/50000000000000 : ℝ)*(lower2) + (41111639/25000000000000 : ℝ)*(lower3) + (293657779/100000000000000 : ℝ)*(lower4) + (3337539/20000000000000 : ℝ)*(lower5) + (872874936109131/20000000000000 : ℝ)*(major0) + (872874936109131/20000000000000 : ℝ)*(major1) + (872874936109131/20000000000000 : ℝ)*(major2) + (5895098601078023/100000000000000 : ℝ)*(sp0) + (368443875756683/6250000000000 : ℝ)*(sp1) + (5895103566189943/100000000000000 : ℝ)*(sp2) + (1416822640300619/50000000000000 : ℝ)*(sp3) + (22646757/6250000000000 : ℝ)*(sp5) + (62063899/1250000000000 : ℝ)*(sp8) + (595867451/50000000000000 : ℝ)*(sp9) + (1416822640300619/50000000000000 : ℝ)*(f.failure) + (5895103566189943/100000000000000 : ℝ)*(f.sum) + (100191900400389/3608000000000000000000000000 : ℝ)*base65 + (2367237919254987121/360800000000000000000000000000000 : ℝ)*base68 + (713689056073387121/360800000000000000000000000000000 : ℝ)*base70 + (3822995641570612879/360800000000000000000000000000000 : ℝ)*base71 + (4677461692399/721600000000000000000000000 : ℝ)*base74 + (973519722346612879/360800000000000000000000000000000 : ℝ)*base75 + (8303090639041012879/360800000000000000000000000000000 : ℝ)*base77 + (1318214955747787121/360800000000000000000000000000000 : ℝ)*base80 + (757862588009/721600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8236569/1250000000000000000000 : ℝ)*base90 + (8236569/1250000000000000000000 : ℝ)*base92 + (8236569/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1367842385378685314243435397/225500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54542951/100000000000000 : ℝ)*(lower2) + (4099477/800000000000 : ℝ)*(lower3) + (591035669/100000000000000 : ℝ)*(lower5) + (879180482034009/20000000000000 : ℝ)*(major0) + (879180482034009/20000000000000 : ℝ)*(major1) + (2197951205085023/50000000000000 : ℝ)*(major2) + (8206220239/100000000000000 : ℝ)*(sp0) + (138585919/12500000000000 : ℝ)*(sp1) + (5937674858326293/100000000000000 : ℝ)*(sp4) + (742211038558571/12500000000000 : ℝ)*(sp5) + (74221117714449/1250000000000 : ℝ)*(sp6) + (1427056034853773/50000000000000 : ℝ)*(sp7) + (1588152347/25000000000000 : ℝ)*(sp8) + (1565641311/50000000000000 : ℝ)*(sp10) + (356764400123771/12500000000000 : ℝ)*(f.failure) + (74221117714449/1250000000000 : ℝ)*(f.sum) + (5487774625167/3280000000000000000000000000 : ℝ)*base65 + (1712194510817196619/360800000000000000000000000000000 : ℝ)*base68 + (1686972726653093307/902000000000000000000000000000000 : ℝ)*base69 + (4528793232879596619/360800000000000000000000000000000 : ℝ)*base72 + (4080399425633/3280000000000000000000000000 : ℝ)*base74 + (8036756621701093307/902000000000000000000000000000000 : ℝ)*base75 + (1396674021900866619/360800000000000000000000000000000 : ℝ)*base78 + (4903977710563266619/360800000000000000000000000000000 : ℝ)*base80 + (2167020050729/3608000000000000000000000000 : ℝ)*base82 + (5417679/312500000000000000000 : ℝ)*base89 + (5417679/312500000000000000000 : ℝ)*base91 + (2292679/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1324_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1324_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1324_s7_0 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029813991/5000000000 : ℝ)*x 0 + (1082716239/2000000000 : ℝ)*x 1 + (2622044899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029813991/5000000000 : ℝ)^1071 ≤ (6269208127191/50000000000000 : ℝ)^815 := by
    have hnat : (1029813991 : ℕ)^1071*50000000000000^815 ≤ 6269208127191^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029813991 5000000000 6269208127191 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082716239/2000000000 : ℝ)^1071 ≤ (44644648230883/100000000000000 : ℝ)^815 := by
    have hnat : (1082716239 : ℕ)^1071*100000000000000^815 ≤ 44644648230883^815*2000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082716239 2000000000 44644648230883 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622044899/5000000000 : ℝ)^1071 ≤ (4281693550497/10000000000000 : ℝ)^815 := by
    have hnat : (2622044899 : ℕ)^1071*10000000000000^815 ≤ 4281693550497^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622044899 5000000000 4281693550497 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029813991/5000000000 : ℝ), (1082716239/2000000000 : ℝ), (2622044899/5000000000 : ℝ)] ![(6269208127191/50000000000000 : ℝ), (44644648230883/100000000000000 : ℝ), (4281693550497/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029813991/5000000000 : ℝ)|^1071 ≤ (6269208127191/50000000000000 : ℝ)^815
        have hw : |(-1029813991/5000000000 : ℝ)|=(1029813991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082716239/2000000000 : ℝ)|^1071 ≤ (44644648230883/100000000000000 : ℝ)^815
        have hw : |(1082716239/2000000000 : ℝ)|=(1082716239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622044899/5000000000 : ℝ)|^1071 ≤ (4281693550497/10000000000000 : ℝ)^815
        have hw : |(2622044899/5000000000 : ℝ)|=(2622044899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_1 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674643909/5000000000 : ℝ)*x 0 + (-2145996817/10000000000 : ℝ)*x 1 + (1311022557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674643909/5000000000 : ℝ)^1071 ≤ (43949191976749/100000000000000 : ℝ)^815 := by
    have hnat : (2674643909 : ℕ)^1071*100000000000000^815 ≤ 43949191976749^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674643909 5000000000 43949191976749 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145996817/10000000000 : ℝ)^1071 ≤ (13233867884591/100000000000000 : ℝ)^815 := by
    have hnat : (2145996817 : ℕ)^1071*100000000000000^815 ≤ 13233867884591^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145996817 10000000000 13233867884591 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311022557/2500000000 : ℝ)^1071 ≤ (5352117514829/12500000000000 : ℝ)^815 := by
    have hnat : (1311022557 : ℕ)^1071*12500000000000^815 ≤ 5352117514829^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311022557 2500000000 5352117514829 12500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674643909/5000000000 : ℝ), (-2145996817/10000000000 : ℝ), (1311022557/2500000000 : ℝ)] ![(43949191976749/100000000000000 : ℝ), (13233867884591/100000000000000 : ℝ), (5352117514829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674643909/5000000000 : ℝ)|^1071 ≤ (43949191976749/100000000000000 : ℝ)^815
        have hw : |(2674643909/5000000000 : ℝ)|=(2674643909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145996817/10000000000 : ℝ)|^1071 ≤ (13233867884591/100000000000000 : ℝ)^815
        have hw : |(-2145996817/10000000000 : ℝ)|=(2145996817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311022557/2500000000 : ℝ)|^1071 ≤ (5352117514829/12500000000000 : ℝ)^815
        have hw : |(1311022557/2500000000 : ℝ)|=(1311022557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_2 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674643143/5000000000 : ℝ)*x 0 + (5244089843/10000000000 : ℝ)*x 1 + (-268249921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674643143/5000000000 : ℝ)^1071 ≤ (43949175436367/100000000000000 : ℝ)^815 := by
    have hnat : (2674643143 : ℕ)^1071*100000000000000^815 ≤ 43949175436367^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674643143 5000000000 43949175436367 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244089843/10000000000 : ℝ)^1071 ≤ (8563387197559/20000000000000 : ℝ)^815 := by
    have hnat : (5244089843 : ℕ)^1071*20000000000000^815 ≤ 8563387197559^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244089843 10000000000 8563387197559 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268249921/1250000000 : ℝ)^1071 ≤ (1323388855743/10000000000000 : ℝ)^815 := by
    have hnat : (268249921 : ℕ)^1071*10000000000000^815 ≤ 1323388855743^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268249921 1250000000 1323388855743 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674643143/5000000000 : ℝ), (5244089843/10000000000 : ℝ), (-268249921/1250000000 : ℝ)] ![(43949175436367/100000000000000 : ℝ), (8563387197559/20000000000000 : ℝ), (1323388855743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674643143/5000000000 : ℝ)|^1071 ≤ (43949175436367/100000000000000 : ℝ)^815
        have hw : |(2674643143/5000000000 : ℝ)|=(2674643143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244089843/10000000000 : ℝ)|^1071 ≤ (8563387197559/20000000000000 : ℝ)^815
        have hw : |(5244089843/10000000000 : ℝ)|=(5244089843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268249921/1250000000 : ℝ)|^1071 ≤ (1323388855743/10000000000000 : ℝ)^815
        have hw : |(-268249921/1250000000 : ℝ)|=(268249921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_3 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (866269977/2000000000 : ℝ)*x 0 + (1039606699/2500000000 : ℝ)*x 1 + (4511036833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866269977/2000000000 : ℝ)^1071 ≤ (16651480383769/50000000000000 : ℝ)^815 := by
    have hnat : (866269977 : ℕ)^1071*50000000000000^815 ≤ 16651480383769^815*2000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866269977 2000000000 16651480383769 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039606699/2500000000 : ℝ)^1071 ≤ (6313362116303/20000000000000 : ℝ)^815 := by
    have hnat : (1039606699 : ℕ)^1071*20000000000000^815 ≤ 6313362116303^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039606699 2500000000 6313362116303 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511036833/10000000000 : ℝ)^1071 ≤ (8782557158461/25000000000000 : ℝ)^815 := by
    have hnat : (4511036833 : ℕ)^1071*25000000000000^815 ≤ 8782557158461^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511036833 10000000000 8782557158461 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866269977/2000000000 : ℝ), (1039606699/2500000000 : ℝ), (4511036833/10000000000 : ℝ)] ![(16651480383769/50000000000000 : ℝ), (6313362116303/20000000000000 : ℝ), (8782557158461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866269977/2000000000 : ℝ)|^1071 ≤ (16651480383769/50000000000000 : ℝ)^815
        have hw : |(866269977/2000000000 : ℝ)|=(866269977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039606699/2500000000 : ℝ)|^1071 ≤ (6313362116303/20000000000000 : ℝ)^815
        have hw : |(1039606699/2500000000 : ℝ)|=(1039606699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511036833/10000000000 : ℝ)|^1071 ≤ (8782557158461/25000000000000 : ℝ)^815
        have hw : |(4511036833/10000000000 : ℝ)|=(4511036833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_4 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-128727523/625000000 : ℝ)*x 0 + (5244695457/10000000000 : ℝ)*x 1 + (676621549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128727523/625000000 : ℝ)^1071 ≤ (1567314417689/12500000000000 : ℝ)^815 := by
    have hnat : (128727523 : ℕ)^1071*12500000000000^815 ≤ 1567314417689^815*625000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128727523 625000000 1567314417689 12500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244695457/10000000000 : ℝ)^1071 ≤ (8564686801749/20000000000000 : ℝ)^815 := by
    have hnat : (5244695457 : ℕ)^1071*20000000000000^815 ≤ 8564686801749^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244695457 10000000000 8564686801749 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676621549/1250000000 : ℝ)^1071 ≤ (11159512658693/25000000000000 : ℝ)^815 := by
    have hnat : (676621549 : ℕ)^1071*25000000000000^815 ≤ 11159512658693^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676621549 1250000000 11159512658693 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128727523/625000000 : ℝ), (5244695457/10000000000 : ℝ), (676621549/1250000000 : ℝ)] ![(1567314417689/12500000000000 : ℝ), (8564686801749/20000000000000 : ℝ), (11159512658693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128727523/625000000 : ℝ)|^1071 ≤ (1567314417689/12500000000000 : ℝ)^815
        have hw : |(-128727523/625000000 : ℝ)|=(128727523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244695457/10000000000 : ℝ)|^1071 ≤ (8564686801749/20000000000000 : ℝ)^815
        have hw : |(5244695457/10000000000 : ℝ)|=(5244695457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676621549/1250000000 : ℝ)|^1071 ≤ (11159512658693/25000000000000 : ℝ)^815
        have hw : |(676621549/1250000000 : ℝ)|=(676621549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_5 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326430441/2500000000 : ℝ)*x 0 + (-395423223/2000000000 : ℝ)*x 1 + (676621549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326430441/2500000000 : ℝ)^1071 ≤ (2717464357817/6250000000000 : ℝ)^815 := by
    have hnat : (1326430441 : ℕ)^1071*6250000000000^815 ≤ 2717464357817^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326430441 2500000000 2717464357817 6250000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395423223/2000000000 : ℝ)^1071 ≤ (1188251962993/10000000000000 : ℝ)^815 := by
    have hnat : (395423223 : ℕ)^1071*10000000000000^815 ≤ 1188251962993^815*2000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395423223 2000000000 1188251962993 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676621549/1250000000 : ℝ)^1071 ≤ (11159512658693/25000000000000 : ℝ)^815 := by
    have hnat : (676621549 : ℕ)^1071*25000000000000^815 ≤ 11159512658693^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676621549 1250000000 11159512658693 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326430441/2500000000 : ℝ), (-395423223/2000000000 : ℝ), (676621549/1250000000 : ℝ)] ![(2717464357817/6250000000000 : ℝ), (1188251962993/10000000000000 : ℝ), (11159512658693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326430441/2500000000 : ℝ)|^1071 ≤ (2717464357817/6250000000000 : ℝ)^815
        have hw : |(1326430441/2500000000 : ℝ)|=(1326430441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395423223/2000000000 : ℝ)|^1071 ≤ (1188251962993/10000000000000 : ℝ)^815
        have hw : |(-395423223/2000000000 : ℝ)|=(395423223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676621549/1250000000 : ℝ)|^1071 ≤ (11159512658693/25000000000000 : ℝ)^815
        have hw : |(676621549/1250000000 : ℝ)|=(676621549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_6 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326430441/2500000000 : ℝ)*x 0 + (676621549/1250000000 : ℝ)*x 1 + (-395423223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326430441/2500000000 : ℝ)^1071 ≤ (2717464357817/6250000000000 : ℝ)^815 := by
    have hnat : (1326430441 : ℕ)^1071*6250000000000^815 ≤ 2717464357817^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326430441 2500000000 2717464357817 6250000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676621549/1250000000 : ℝ)^1071 ≤ (11159512658693/25000000000000 : ℝ)^815 := by
    have hnat : (676621549 : ℕ)^1071*25000000000000^815 ≤ 11159512658693^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676621549 1250000000 11159512658693 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395423223/2000000000 : ℝ)^1071 ≤ (1188251962993/10000000000000 : ℝ)^815 := by
    have hnat : (395423223 : ℕ)^1071*10000000000000^815 ≤ 1188251962993^815*2000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395423223 2000000000 1188251962993 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326430441/2500000000 : ℝ), (676621549/1250000000 : ℝ), (-395423223/2000000000 : ℝ)] ![(2717464357817/6250000000000 : ℝ), (11159512658693/25000000000000 : ℝ), (1188251962993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326430441/2500000000 : ℝ)|^1071 ≤ (2717464357817/6250000000000 : ℝ)^815
        have hw : |(1326430441/2500000000 : ℝ)|=(1326430441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676621549/1250000000 : ℝ)|^1071 ≤ (11159512658693/25000000000000 : ℝ)^815
        have hw : |(676621549/1250000000 : ℝ)|=(676621549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395423223/2000000000 : ℝ)|^1071 ≤ (1188251962993/10000000000000 : ℝ)^815
        have hw : |(-395423223/2000000000 : ℝ)|=(395423223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s7_7 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4331376433/10000000000 : ℝ)*x 0 + (4509775961/10000000000 : ℝ)*x 1 + (4159693311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331376433/10000000000 : ℝ)^1071 ≤ (130090738311/390625000000 : ℝ)^815 := by
    have hnat : (4331376433 : ℕ)^1071*390625000000^815 ≤ 130090738311^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331376433 10000000000 130090738311 390625000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509775961/10000000000 : ℝ)^1071 ≤ (8779331425529/25000000000000 : ℝ)^815 := by
    have hnat : (4509775961 : ℕ)^1071*25000000000000^815 ≤ 8779331425529^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509775961 10000000000 8779331425529 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159693311/10000000000 : ℝ)^1071 ≤ (31579445272233/100000000000000 : ℝ)^815 := by
    have hnat : (4159693311 : ℕ)^1071*100000000000000^815 ≤ 31579445272233^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159693311 10000000000 31579445272233 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331376433/10000000000 : ℝ), (4509775961/10000000000 : ℝ), (4159693311/10000000000 : ℝ)] ![(130090738311/390625000000 : ℝ), (8779331425529/25000000000000 : ℝ), (31579445272233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331376433/10000000000 : ℝ)|^1071 ≤ (130090738311/390625000000 : ℝ)^815
        have hw : |(4331376433/10000000000 : ℝ)|=(4331376433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509775961/10000000000 : ℝ)|^1071 ≤ (8779331425529/25000000000000 : ℝ)^815
        have hw : |(4509775961/10000000000 : ℝ)|=(4509775961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159693311/10000000000 : ℝ)|^1071 ≤ (31579445272233/100000000000000 : ℝ)^815
        have hw : |(4159693311/10000000000 : ℝ)|=(4159693311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1324_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/20000 : ℝ) ^ (4283/1024 : ℝ) ≤ (10180510026479239/100000000000000000000 : ℝ) := by
    have hpowers : (2221/20000 : ℝ)^4283 ≤ (10180510026479239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2221 : ℕ)^4283*100000000000000000000^1024 ≤ 10180510026479239^1024*20000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 20000 10180510026479239 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/20000 : ℝ)) (X := (10180510026479239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (4283/1024 : ℝ) ≤ (32863424978009151/100000000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^4283 ≤ (32863424978009151/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1837 : ℕ)^4283*100000000000000000000^1024 ≤ 32863424978009151^1024*12500^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 32863424978009151 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (32863424978009151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010180510026479239/50000000000000000000 : ℝ) ≤ (2500121690810211/2500000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50010180510026479239/50000000000000000000 : ℝ)^1024 ≤ (2500121690810211/2500000000000000 : ℝ)^4283 := by
      have hnat : (50010180510026479239 : ℕ)^1024*2500000000000000^4283 ≤ 2500121690810211^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010180510026479239 50000000000000000000 2500121690810211 2500000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500121690810211/2500000000000000 : ℝ)) (X := (50010180510026479239/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004304393500448839/10000000000000000000 : ℝ) ≤ (5000514473185229/5000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (10004304393500448839/10000000000000000000 : ℝ)^1024 ≤ (5000514473185229/5000000000000000 : ℝ)^4283 := by
      have hnat : (10004304393500448839 : ℕ)^1024*5000000000000000^4283 ≤ 5000514473185229^4283*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004304393500448839 10000000000000000000 5000514473185229 5000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000514473185229/5000000000000000 : ℝ)) (X := (10004304393500448839/10000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032863424978009151/50000000000000000000 : ℝ) ≤ (1250196391187509/1250000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50032863424978009151/50000000000000000000 : ℝ)^1024 ≤ (1250196391187509/1250000000000000 : ℝ)^4283 := by
      have hnat : (50032863424978009151 : ℕ)^1024*1250000000000000^4283 ≤ 1250196391187509^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032863424978009151 50000000000000000000 1250196391187509 1250000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250196391187509/1250000000000000 : ℝ)) (X := (50032863424978009151/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10180510026479239/100000000000000000000 : ℝ) ≤ ((641066179990877569/641250000000000000 : ℝ)+2*(38727366401/25650000000000 : ℝ)*(2221/20000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (641066179990877569/641250000000000000 : ℝ)+2*(38727366401/25650000000000 : ℝ)*(2221/20000 : ℝ)=(2500121690810211/2500000000000000 : ℝ) by norm_num, show 1+2*(10180510026479239/100000000000000000000 : ℝ)=(50010180510026479239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32863424978009151/100000000000000000000 : ℝ)+(10180510026479239/100000000000000000000 : ℝ) ≤ ((641066179990877569/641250000000000000 : ℝ)+(38727366401/25650000000000 : ℝ)*((1837/12500 : ℝ)+(2221/20000 : ℝ)))^(4283/1024 : ℝ) := by
    rw [show (641066179990877569/641250000000000000 : ℝ)+(38727366401/25650000000000 : ℝ)*((1837/12500 : ℝ)+(2221/20000 : ℝ))=(5000514473185229/5000000000000000 : ℝ) by norm_num, show 1+(32863424978009151/100000000000000000000 : ℝ)+(10180510026479239/100000000000000000000 : ℝ)=(10004304393500448839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32863424978009151/100000000000000000000 : ℝ) ≤ ((641066179990877569/641250000000000000 : ℝ)+2*(38727366401/25650000000000 : ℝ)*(1837/12500 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (641066179990877569/641250000000000000 : ℝ)+2*(38727366401/25650000000000 : ℝ)*(1837/12500 : ℝ)=(1250196391187509/1250000000000000 : ℝ) by norm_num, show 1+2*(32863424978009151/100000000000000000000 : ℝ)=(50032863424978009151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (641066179990877569/641250000000000000 : ℝ)*(X 1 0+X 2 0)+(38727366401/25650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (641066179990877569/641250000000000000 : ℝ)) (alpha := (38727366401/25650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (641066179990877569/641250000000000000 : ℝ)*(X 0 1+X 2 1)+(38727366401/25650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (641066179990877569/641250000000000000 : ℝ)) (alpha := (38727366401/25650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (641066179990877569/641250000000000000 : ℝ)*(X 0 2+X 1 2)+(38727366401/25650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (641066179990877569/641250000000000000 : ℝ)) (alpha := (38727366401/25650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1029813991/5000000000 : ℝ)*X 0 0+(1082716239/2000000000 : ℝ)*X 0 1+(2622044899/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674643909/5000000000 : ℝ)*X 1 0+(-2145996817/10000000000 : ℝ)*X 1 1+(1311022557/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674643143/5000000000 : ℝ)*X 2 0+(5244089843/10000000000 : ℝ)*X 2 1+(-268249921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866269977/2000000000 : ℝ)*X 0 0+(1039606699/2500000000 : ℝ)*X 0 1+(4511036833/10000000000 : ℝ)*X 0 2+(866269977/2000000000 : ℝ)*X 1 0+(1039606699/2500000000 : ℝ)*X 1 1+(4511036833/10000000000 : ℝ)*X 1 2+(866269977/2000000000 : ℝ)*X 2 0+(1039606699/2500000000 : ℝ)*X 2 1+(4511036833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-128727523/625000000 : ℝ)*X 0 0+(5244695457/10000000000 : ℝ)*X 0 1+(676621549/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326430441/2500000000 : ℝ)*X 1 0+(-395423223/2000000000 : ℝ)*X 1 1+(676621549/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326430441/2500000000 : ℝ)*X 2 0+(676621549/1250000000 : ℝ)*X 2 1+(-395423223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331376433/10000000000 : ℝ)*X 0 0+(4509775961/10000000000 : ℝ)*X 0 1+(4159693311/10000000000 : ℝ)*X 0 2+(4331376433/10000000000 : ℝ)*X 1 0+(4509775961/10000000000 : ℝ)*X 1 1+(4159693311/10000000000 : ℝ)*X 1 2+(4331376433/10000000000 : ℝ)*X 2 0+(4509775961/10000000000 : ℝ)*X 2 1+(4159693311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2734926723190146571228991/667968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073631603/50000000000000 : ℝ)*(base19) + (33377653/50000000000000 : ℝ)*(base23) + (24124789/12500000000000 : ℝ)*(upper2) + (44824673/50000000000000 : ℝ)*(lower5) + (4368132956187941/100000000000000 : ℝ)*(major0) + (4368132956187941/100000000000000 : ℝ)*(major1) + (2184066478093971/50000000000000 : ℝ)*(major2) + (1180020975666963/20000000000000 : ℝ)*(sp0) + (2950089111484939/50000000000000 : ℝ)*(sp1) + (5900088023285983/100000000000000 : ℝ)*(sp2) + (567208785962981/20000000000000 : ℝ)*(sp3) + (7549189827/10000000000000 : ℝ)*(sp4) + (23070047949/25000000000000 : ℝ)*(sp6) + (20737924053/50000000000000 : ℝ)*(sp7) + (283608540566301/10000000000000 : ℝ)*(f.failure) + (1180036074046617/20000000000000 : ℝ)*(f.sum) + (4526084329531/1282500000000000000000000000 : ℝ)*base66 + (889329788195379571/64125000000000000000000000000000 : ℝ)*base68 + (13575650822263501/32062500000000000000000000000000 : ℝ)*base70 + (130688104327629571/64125000000000000000000000000000 : ℝ)*base72 + (16348390127717/2565000000000000000000000000 : ℝ)*base74 + (417751453051138501/32062500000000000000000000000000 : ℝ)*base76 + (460335218788134857/21375000000000000000000000000000 : ℝ)*base78 + (227821000660884857/21375000000000000000000000000000 : ℝ)*base80 + (23616957373/2565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1376351/250000000000000000000 : ℝ)*base90 + (1376351/250000000000000000000 : ℝ)*base92 + (3876351/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29967250180500898470770747/2671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (392899703/20000000000000 : ℝ)*(base19) + (426923689/20000000000000 : ℝ)*(base23) + (84101943/12500000000000 : ℝ)*(lower1) + (228305343/100000000000000 : ℝ)*(upper3) + (602767/781250000000 : ℝ)*(lower4) + (115021179/50000000000000 : ℝ)*(upper5) + (2199748125226913/50000000000000 : ℝ)*(major0) + (2199748125226913/50000000000000 : ℝ)*(major1) + (2199748125226913/50000000000000 : ℝ)*(major2) + (1504288727/50000000000000 : ℝ)*(sp2) + (5942543563478253/100000000000000 : ℝ)*(sp4) + (2971270799489869/50000000000000 : ℝ)*(sp5) + (5942538420282353/100000000000000 : ℝ)*(sp6) + (57128971271379/2000000000000 : ℝ)*(sp7) + (57128971271379/2000000000000 : ℝ)*(f.failure) + (5942543563478253/100000000000000 : ℝ)*(f.sum) + (10198541750269/1282500000000000000000000000 : ℝ)*base66 + (190577217211483999/10687500000000000000000000000000 : ℝ)*base67 + (152323493813828501/10687500000000000000000000000000 : ℝ)*base70 + (306215890256078501/10687500000000000000000000000000 : ℝ)*base72 + (360270812563/641250000000000000000000000 : ℝ)*base73 + (731372266471328501/10687500000000000000000000000000 : ℝ)*base76 + (74154020780078501/10687500000000000000000000000000 : ℝ)*base78 + (59580836073953501/10687500000000000000000000000000 : ℝ)*base80 + (19733229532943/2565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (554671/50000000000000000000 : ℝ)*base89 + (554671/50000000000000000000 : ℝ)*base91 + (554671/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1324_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1324_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1324_s8_0 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349284737/10000000000 : ℝ)*x 0 + (-2145984719/10000000000 : ℝ)*x 1 + (2622051233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349284737/10000000000 : ℝ)^1071 ≤ (10987289678111/25000000000000 : ℝ)^815 := by
    have hnat : (5349284737 : ℕ)^1071*25000000000000^815 ≤ 10987289678111^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349284737 10000000000 10987289678111 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145984719/10000000000 : ℝ)^1071 ≤ (13233769844709/100000000000000 : ℝ)^815 := by
    have hnat : (2145984719 : ℕ)^1071*100000000000000^815 ≤ 13233769844709^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145984719 10000000000 13233769844709 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622051233/5000000000 : ℝ)^1071 ≤ (42817071425651/100000000000000 : ℝ)^815 := by
    have hnat : (2622051233 : ℕ)^1071*100000000000000^815 ≤ 42817071425651^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622051233 5000000000 42817071425651 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349284737/10000000000 : ℝ), (-2145984719/10000000000 : ℝ), (2622051233/5000000000 : ℝ)] ![(10987289678111/25000000000000 : ℝ), (13233769844709/100000000000000 : ℝ), (42817071425651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349284737/10000000000 : ℝ)|^1071 ≤ (10987289678111/25000000000000 : ℝ)^815
        have hw : |(5349284737/10000000000 : ℝ)|=(5349284737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145984719/10000000000 : ℝ)|^1071 ≤ (13233769844709/100000000000000 : ℝ)^815
        have hw : |(-2145984719/10000000000 : ℝ)|=(2145984719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622051233/5000000000 : ℝ)|^1071 ≤ (42817071425651/100000000000000 : ℝ)^815
        have hw : |(2622051233/5000000000 : ℝ)|=(2622051233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s8_1 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029819411/5000000000 : ℝ)*x 0 + (2622353863/5000000000 : ℝ)*x 1 + (2706480693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029819411/5000000000 : ℝ)^1071 ≤ (1253850297361/10000000000000 : ℝ)^815 := by
    have hnat : (1029819411 : ℕ)^1071*10000000000000^815 ≤ 1253850297361^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029819411 5000000000 1253850297361 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622353863/5000000000 : ℝ)^1071 ≤ (42823565653149/100000000000000 : ℝ)^815 := by
    have hnat : (2622353863 : ℕ)^1071*100000000000000^815 ≤ 42823565653149^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622353863 5000000000 42823565653149 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706480693/5000000000 : ℝ)^1071 ≤ (44637931364931/100000000000000 : ℝ)^815 := by
    have hnat : (2706480693 : ℕ)^1071*100000000000000^815 ≤ 44637931364931^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706480693 5000000000 44637931364931 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029819411/5000000000 : ℝ), (2622353863/5000000000 : ℝ), (2706480693/5000000000 : ℝ)] ![(1253850297361/10000000000000 : ℝ), (42823565653149/100000000000000 : ℝ), (44637931364931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029819411/5000000000 : ℝ)|^1071 ≤ (1253850297361/10000000000000 : ℝ)^815
        have hw : |(-1029819411/5000000000 : ℝ)|=(1029819411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622353863/5000000000 : ℝ)|^1071 ≤ (42823565653149/100000000000000 : ℝ)^815
        have hw : |(2622353863/5000000000 : ℝ)|=(2622353863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706480693/5000000000 : ℝ)|^1071 ≤ (44637931364931/100000000000000 : ℝ)^815
        have hw : |(2706480693/5000000000 : ℝ)|=(2706480693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s8_2 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305725891/10000000000 : ℝ)*x 0 + (-12357037/62500000 : ℝ)*x 1 + (676620143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305725891/10000000000 : ℝ)^1071 ≤ (10869868542079/25000000000000 : ℝ)^815 := by
    have hnat : (5305725891 : ℕ)^1071*25000000000000^815 ≤ 10869868542079^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305725891 10000000000 10869868542079 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12357037/62500000 : ℝ)^1071 ≤ (2970649267073/25000000000000 : ℝ)^815 := by
    have hnat : (12357037 : ℕ)^1071*25000000000000^815 ≤ 2970649267073^815*62500000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12357037 62500000 2970649267073 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676620143/1250000000 : ℝ)^1071 ≤ (22318964371213/50000000000000 : ℝ)^815 := by
    have hnat : (676620143 : ℕ)^1071*50000000000000^815 ≤ 22318964371213^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676620143 1250000000 22318964371213 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305725891/10000000000 : ℝ), (-12357037/62500000 : ℝ), (676620143/1250000000 : ℝ)] ![(10869868542079/25000000000000 : ℝ), (2970649267073/25000000000000 : ℝ), (22318964371213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305725891/10000000000 : ℝ)|^1071 ≤ (10869868542079/25000000000000 : ℝ)^815
        have hw : |(5305725891/10000000000 : ℝ)|=(5305725891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12357037/62500000 : ℝ)|^1071 ≤ (2970649267073/25000000000000 : ℝ)^815
        have hw : |(-12357037/62500000 : ℝ)|=(12357037/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676620143/1250000000 : ℝ)|^1071 ≤ (22318964371213/50000000000000 : ℝ)^815
        have hw : |(676620143/1250000000 : ℝ)|=(676620143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s8_3 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305725743/10000000000 : ℝ)*x 0 + (5412961233/10000000000 : ℝ)*x 1 + (-988563/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305725743/10000000000 : ℝ)^1071 ≤ (43479472574519/100000000000000 : ℝ)^815 := by
    have hnat : (5305725743 : ℕ)^1071*100000000000000^815 ≤ 43479472574519^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305725743 10000000000 43479472574519 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412961233/10000000000 : ℝ)^1071 ≤ (44637929706901/100000000000000 : ℝ)^815 := by
    have hnat : (5412961233 : ℕ)^1071*100000000000000^815 ≤ 44637929706901^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412961233 10000000000 44637929706901 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988563/5000000 : ℝ)^1071 ≤ (11882597700121/100000000000000 : ℝ)^815 := by
    have hnat : (988563 : ℕ)^1071*100000000000000^815 ≤ 11882597700121^815*5000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988563 5000000 11882597700121 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305725743/10000000000 : ℝ), (5412961233/10000000000 : ℝ), (-988563/5000000 : ℝ)] ![(43479472574519/100000000000000 : ℝ), (44637929706901/100000000000000 : ℝ), (11882597700121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305725743/10000000000 : ℝ)|^1071 ≤ (43479472574519/100000000000000 : ℝ)^815
        have hw : |(5305725743/10000000000 : ℝ)|=(5305725743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412961233/10000000000 : ℝ)|^1071 ≤ (44637929706901/100000000000000 : ℝ)^815
        have hw : |(5412961233/10000000000 : ℝ)|=(5412961233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988563/5000000 : ℝ)|^1071 ≤ (11882597700121/100000000000000 : ℝ)^815
        have hw : |(-988563/5000000 : ℝ)|=(988563/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_s8_4 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4331377243/10000000000 : ℝ)*x 0 + (2254875711/5000000000 : ℝ)*x 1 + (4159717661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331377243/10000000000 : ℝ)^1071 ≤ (33303237191837/100000000000000 : ℝ)^815 := by
    have hnat : (4331377243 : ℕ)^1071*100000000000000^815 ≤ 33303237191837^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331377243 10000000000 33303237191837 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254875711/5000000000 : ℝ)^1071 ≤ (35117074597429/100000000000000 : ℝ)^815 := by
    have hnat : (2254875711 : ℕ)^1071*100000000000000^815 ≤ 35117074597429^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254875711 5000000000 35117074597429 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159717661/10000000000 : ℝ)^1071 ≤ (493432628101/1562500000000 : ℝ)^815 := by
    have hnat : (4159717661 : ℕ)^1071*1562500000000^815 ≤ 493432628101^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159717661 10000000000 493432628101 1562500000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331377243/10000000000 : ℝ), (2254875711/5000000000 : ℝ), (4159717661/10000000000 : ℝ)] ![(33303237191837/100000000000000 : ℝ), (35117074597429/100000000000000 : ℝ), (493432628101/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331377243/10000000000 : ℝ)|^1071 ≤ (33303237191837/100000000000000 : ℝ)^815
        have hw : |(4331377243/10000000000 : ℝ)|=(4331377243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254875711/5000000000 : ℝ)|^1071 ≤ (35117074597429/100000000000000 : ℝ)^815
        have hw : |(2254875711/5000000000 : ℝ)|=(2254875711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159717661/10000000000 : ℝ)|^1071 ≤ (493432628101/1562500000000 : ℝ)^815
        have hw : |(4159717661/10000000000 : ℝ)|=(4159717661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1324_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11107/100000 : ℝ) ^ (4283/1024 : ℝ) ≤ (10188181054176271/100000000000000000000 : ℝ) := by
    have hpowers : (11107/100000 : ℝ)^4283 ≤ (10188181054176271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11107 : ℕ)^4283*100000000000000000000^1024 ≤ 10188181054176271^1024*100000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11107 100000 10188181054176271 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11107/100000 : ℝ)) (X := (10188181054176271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2939/20000 : ℝ) ^ (4283/1024 : ℝ) ≤ (16427036378395961/50000000000000000000 : ℝ) := by
    have hpowers : (2939/20000 : ℝ)^4283 ≤ (16427036378395961/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2939 : ℕ)^4283*50000000000000000000^1024 ≤ 16427036378395961^1024*20000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2939 20000 16427036378395961 50000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2939/20000 : ℝ)) (X := (16427036378395961/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010188181054176271/50000000000000000000 : ℝ) ≤ (10000487129989157/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50010188181054176271/50000000000000000000 : ℝ)^1024 ≤ (10000487129989157/10000000000000000 : ℝ)^4283 := by
      have hnat : (50010188181054176271 : ℕ)^1024*10000000000000000^4283 ≤ 10000487129989157^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010188181054176271 50000000000000000000 10000487129989157 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000487129989157/10000000000000000 : ℝ)) (X := (50010188181054176271/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043042253810968193/100000000000000000000 : ℝ) ≤ (10001028906188843/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (100043042253810968193/100000000000000000000 : ℝ)^1024 ≤ (10001028906188843/10000000000000000 : ℝ)^4283 := by
      have hnat : (100043042253810968193 : ℕ)^1024*10000000000000000^4283 ≤ 10001028906188843^4283*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043042253810968193 100000000000000000000 10001028906188843 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001028906188843/10000000000000000 : ℝ)) (X := (100043042253810968193/100000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016427036378395961/25000000000000000000 : ℝ) ≤ (10001570682388529/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (25016427036378395961/25000000000000000000 : ℝ)^1024 ≤ (10001570682388529/10000000000000000 : ℝ)^4283 := by
      have hnat : (25016427036378395961 : ℕ)^1024*10000000000000000^4283 ≤ 10001570682388529^4283*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016427036378395961 25000000000000000000 10001570682388529 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001570682388529/10000000000000000 : ℝ)) (X := (25016427036378395961/25000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10188181054176271/100000000000000000000 : ℝ) ≤ ((747285683456276469/747500000000000000 : ℝ)+2*(90296033281/59800000000000 : ℝ)*(11107/100000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (747285683456276469/747500000000000000 : ℝ)+2*(90296033281/59800000000000 : ℝ)*(11107/100000 : ℝ)=(10000487129989157/10000000000000000 : ℝ) by norm_num, show 1+2*(10188181054176271/100000000000000000000 : ℝ)=(50010188181054176271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16427036378395961/50000000000000000000 : ℝ)+(10188181054176271/100000000000000000000 : ℝ) ≤ ((747285683456276469/747500000000000000 : ℝ)+(90296033281/59800000000000 : ℝ)*((2939/20000 : ℝ)+(11107/100000 : ℝ)))^(4283/1024 : ℝ) := by
    rw [show (747285683456276469/747500000000000000 : ℝ)+(90296033281/59800000000000 : ℝ)*((2939/20000 : ℝ)+(11107/100000 : ℝ))=(10001028906188843/10000000000000000 : ℝ) by norm_num, show 1+(16427036378395961/50000000000000000000 : ℝ)+(10188181054176271/100000000000000000000 : ℝ)=(100043042253810968193/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16427036378395961/50000000000000000000 : ℝ) ≤ ((747285683456276469/747500000000000000 : ℝ)+2*(90296033281/59800000000000 : ℝ)*(2939/20000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (747285683456276469/747500000000000000 : ℝ)+2*(90296033281/59800000000000 : ℝ)*(2939/20000 : ℝ)=(10001570682388529/10000000000000000 : ℝ) by norm_num, show 1+2*(16427036378395961/50000000000000000000 : ℝ)=(25016427036378395961/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (747285683456276469/747500000000000000 : ℝ)*(X 1 0+X 2 0)+(90296033281/59800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (747285683456276469/747500000000000000 : ℝ)) (alpha := (90296033281/59800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (747285683456276469/747500000000000000 : ℝ)*(X 0 1+X 2 1)+(90296033281/59800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (747285683456276469/747500000000000000 : ℝ)) (alpha := (90296033281/59800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (747285683456276469/747500000000000000 : ℝ)*(X 0 2+X 1 2)+(90296033281/59800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (747285683456276469/747500000000000000 : ℝ)) (alpha := (90296033281/59800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349284737/10000000000 : ℝ)*X 1 0+(-2145984719/10000000000 : ℝ)*X 1 1+(2622051233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1029819411/5000000000 : ℝ)*X 0 0+(2622353863/5000000000 : ℝ)*X 0 1+(2706480693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305725891/10000000000 : ℝ)*X 1 0+(-12357037/62500000 : ℝ)*X 1 1+(676620143/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305725743/10000000000 : ℝ)*X 2 0+(5412961233/10000000000 : ℝ)*X 2 1+(-988563/5000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4331377243/10000000000 : ℝ)*X 0 0+(2254875711/5000000000 : ℝ)*X 0 1+(4159717661/10000000000 : ℝ)*X 0 2+(4331377243/10000000000 : ℝ)*X 1 0+(2254875711/5000000000 : ℝ)*X 1 1+(4159717661/10000000000 : ℝ)*X 1 2+(4331377243/10000000000 : ℝ)*X 2 0+(2254875711/5000000000 : ℝ)*X 2 1+(4159717661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35685426268288865171342079/9343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364627221/50000000000000 : ℝ)*(base19) + (609950921/100000000000000 : ℝ)*(base23) + (24816431/25000000000000 : ℝ)*(lower1) + (1469/97656250000 : ℝ)*(upper3) + (2991049/6250000000000 : ℝ)*(lower4) + (15067567/12500000000000 : ℝ)*(upper5) + (2200066191490853/50000000000000 : ℝ)*(major0) + (2200066191490853/50000000000000 : ℝ)*(major1) + (2200066191490853/50000000000000 : ℝ)*(major2) + (5324660347/100000000000000 : ℝ)*(sp0) + (1485850763777593/25000000000000 : ℝ)*(sp1) + (92865578143681/1562500000000 : ℝ)*(sp2) + (5943402445159451/100000000000000 : ℝ)*(sp3) + (71421539588679/2500000000000 : ℝ)*(sp4) + (71421539588679/2500000000000 : ℝ)*(f.failure) + (1485850763777593/25000000000000 : ℝ)*(f.sum) + (2859455974827/1495000000000000000000000000 : ℝ)*base66 + (13470883760230459/1625000000000000000000000000000 : ℝ)*base67 + (29418483025230459/1625000000000000000000000000000 : ℝ)*base69 + (14519377032355459/1625000000000000000000000000000 : ℝ)*base71 + (839377423991/186875000000000000000000000 : ℝ)*base73 + (3808555309519541/1625000000000000000000000000000 : ℝ)*base76 + (25877220266105459/1625000000000000000000000000000 : ℝ)*base77 + (21668311617355459/1625000000000000000000000000000 : ℝ)*base79 + (1940552227507/1495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (377629/62500000000000000000 : ℝ)*base90 + (377629/62500000000000000000 : ℝ)*base92 + (377629/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1324_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1324_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1324_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1324_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1324_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1324_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1324_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

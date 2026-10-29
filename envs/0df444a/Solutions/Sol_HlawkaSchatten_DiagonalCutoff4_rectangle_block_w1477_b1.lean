-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:27.641216+00:00
-- url     : https://prove2.me/submissions/eb0a6553-81ef-43a6-8b6e-f196c5e8b059

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
theorem support_rectangle_w1477_s3_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920236011/10000000000 : ℝ)*x 0 + (5442696663/10000000000 : ℝ)*x 1 + (2605644287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920236011/10000000000 : ℝ)^4451 ≤ (11727849234663/100000000000000 : ℝ)^3427 := by
    have hnat : (1920236011 : ℕ)^4451*100000000000000^3427 ≤ 11727849234663^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920236011 10000000000 11727849234663 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442696663/10000000000 : ℝ)^4451 ≤ (45381039205451/100000000000000 : ℝ)^3427 := by
    have hnat : (5442696663 : ℕ)^4451*100000000000000^3427 ≤ 45381039205451^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442696663 10000000000 45381039205451 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605644287/5000000000 : ℝ)^4451 ≤ (21445555770389/50000000000000 : ℝ)^3427 := by
    have hnat : (2605644287 : ℕ)^4451*50000000000000^3427 ≤ 21445555770389^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605644287 5000000000 21445555770389 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920236011/10000000000 : ℝ), (5442696663/10000000000 : ℝ), (2605644287/5000000000 : ℝ)] ![(11727849234663/100000000000000 : ℝ), (45381039205451/100000000000000 : ℝ), (21445555770389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920236011/10000000000 : ℝ)|^4451 ≤ (11727849234663/100000000000000 : ℝ)^3427
        have hw : |(-1920236011/10000000000 : ℝ)|=(1920236011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442696663/10000000000 : ℝ)|^4451 ≤ (45381039205451/100000000000000 : ℝ)^3427
        have hw : |(5442696663/10000000000 : ℝ)|=(5442696663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605644287/5000000000 : ℝ)|^4451 ≤ (21445555770389/50000000000000 : ℝ)^3427
        have hw : |(2605644287/5000000000 : ℝ)|=(2605644287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338681853/2500000000 : ℝ)*x 0 + (-2038959349/10000000000 : ℝ)*x 1 + (5211288599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338681853/2500000000 : ℝ)^4451 ≤ (8886139096933/20000000000000 : ℝ)^3427 := by
    have hnat : (1338681853 : ℕ)^4451*20000000000000^3427 ≤ 8886139096933^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338681853 2500000000 8886139096933 20000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2038959349/10000000000 : ℝ)^4451 ≤ (1584774087233/12500000000000 : ℝ)^3427 := by
    have hnat : (2038959349 : ℕ)^4451*12500000000000^3427 ≤ 1584774087233^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038959349 10000000000 1584774087233 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5211288599/10000000000 : ℝ)^4451 ≤ (2144555590401/5000000000000 : ℝ)^3427 := by
    have hnat : (5211288599 : ℕ)^4451*5000000000000^3427 ≤ 2144555590401^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211288599 10000000000 2144555590401 5000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338681853/2500000000 : ℝ), (-2038959349/10000000000 : ℝ), (5211288599/10000000000 : ℝ)] ![(8886139096933/20000000000000 : ℝ), (1584774087233/12500000000000 : ℝ), (2144555590401/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338681853/2500000000 : ℝ)|^4451 ≤ (8886139096933/20000000000000 : ℝ)^3427
        have hw : |(1338681853/2500000000 : ℝ)|=(1338681853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2038959349/10000000000 : ℝ)|^4451 ≤ (1584774087233/12500000000000 : ℝ)^3427
        have hw : |(-2038959349/10000000000 : ℝ)|=(2038959349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5211288599/10000000000 : ℝ)|^4451 ≤ (2144555590401/5000000000000 : ℝ)^3427
        have hw : |(5211288599/10000000000 : ℝ)|=(5211288599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354727433/10000000000 : ℝ)*x 0 + (5211288441/10000000000 : ℝ)*x 1 + (-2038959529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354727433/10000000000 : ℝ)^4451 ≤ (44430695710977/100000000000000 : ℝ)^3427 := by
    have hnat : (5354727433 : ℕ)^4451*100000000000000^3427 ≤ 44430695710977^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354727433 10000000000 44430695710977 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211288441/10000000000 : ℝ)^4451 ≤ (42891110119047/100000000000000 : ℝ)^3427 := by
    have hnat : (5211288441 : ℕ)^4451*100000000000000^3427 ≤ 42891110119047^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211288441 10000000000 42891110119047 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038959529/10000000000 : ℝ)^4451 ≤ (1267819415153/10000000000000 : ℝ)^3427 := by
    have hnat : (2038959529 : ℕ)^4451*10000000000000^3427 ≤ 1267819415153^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038959529 10000000000 1267819415153 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354727433/10000000000 : ℝ), (5211288441/10000000000 : ℝ), (-2038959529/10000000000 : ℝ)] ![(44430695710977/100000000000000 : ℝ), (42891110119047/100000000000000 : ℝ), (1267819415153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354727433/10000000000 : ℝ)|^4451 ≤ (44430695710977/100000000000000 : ℝ)^3427
        have hw : |(5354727433/10000000000 : ℝ)|=(5354727433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211288441/10000000000 : ℝ)|^4451 ≤ (42891110119047/100000000000000 : ℝ)^3427
        have hw : |(5211288441/10000000000 : ℝ)|=(5211288441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038959529/10000000000 : ℝ)|^4451 ≤ (1267819415153/10000000000000 : ℝ)^3427
        have hw : |(-2038959529/10000000000 : ℝ)|=(2038959529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285887123/10000000000 : ℝ)*x 0 + (4036655041/10000000000 : ℝ)*x 1 + (1137119209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285887123/10000000000 : ℝ)^4451 ≤ (33273092493503/100000000000000 : ℝ)^3427 := by
    have hnat : (4285887123 : ℕ)^4451*100000000000000^3427 ≤ 33273092493503^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285887123 10000000000 33273092493503 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4036655041/10000000000 : ℝ)^4451 ≤ (30782187373401/100000000000000 : ℝ)^3427 := by
    have hnat : (4036655041 : ℕ)^4451*100000000000000^3427 ≤ 30782187373401^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036655041 10000000000 30782187373401 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137119209/2500000000 : ℝ)^4451 ≤ (898618003029/2500000000000 : ℝ)^3427 := by
    have hnat : (1137119209 : ℕ)^4451*2500000000000^3427 ≤ 898618003029^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137119209 2500000000 898618003029 2500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285887123/10000000000 : ℝ), (4036655041/10000000000 : ℝ), (1137119209/2500000000 : ℝ)] ![(33273092493503/100000000000000 : ℝ), (30782187373401/100000000000000 : ℝ), (898618003029/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285887123/10000000000 : ℝ)|^4451 ≤ (33273092493503/100000000000000 : ℝ)^3427
        have hw : |(4285887123/10000000000 : ℝ)|=(4285887123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4036655041/10000000000 : ℝ)|^4451 ≤ (30782187373401/100000000000000 : ℝ)^3427
        have hw : |(4036655041/10000000000 : ℝ)|=(4036655041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137119209/2500000000 : ℝ)|^4451 ≤ (898618003029/2500000000000 : ℝ)^3427
        have hw : |(1137119209/2500000000 : ℝ)|=(1137119209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480067603/2500000000 : ℝ)*x 0 + (2606260389/5000000000 : ℝ)*x 1 + (5441455069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480067603/2500000000 : ℝ)^4451 ≤ (234562442391/2000000000000 : ℝ)^3427 := by
    have hnat : (480067603 : ℕ)^4451*2000000000000^3427 ≤ 234562442391^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480067603 2500000000 234562442391 2000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606260389/5000000000 : ℝ)^4451 ≤ (21452141950873/50000000000000 : ℝ)^3427 := by
    have hnat : (2606260389 : ℕ)^4451*50000000000000^3427 ≤ 21452141950873^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606260389 5000000000 21452141950873 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441455069/10000000000 : ℝ)^4451 ≤ (9073518792843/20000000000000 : ℝ)^3427 := by
    have hnat : (5441455069 : ℕ)^4451*20000000000000^3427 ≤ 9073518792843^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441455069 10000000000 9073518792843 20000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480067603/2500000000 : ℝ), (2606260389/5000000000 : ℝ), (5441455069/10000000000 : ℝ)] ![(234562442391/2000000000000 : ℝ), (21452141950873/50000000000000 : ℝ), (9073518792843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480067603/2500000000 : ℝ)|^4451 ≤ (234562442391/2000000000000 : ℝ)^3427
        have hw : |(-480067603/2500000000 : ℝ)|=(480067603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606260389/5000000000 : ℝ)|^4451 ≤ (21452141950873/50000000000000 : ℝ)^3427
        have hw : |(2606260389/5000000000 : ℝ)|=(2606260389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441455069/10000000000 : ℝ)|^4451 ≤ (9073518792843/20000000000000 : ℝ)^3427
        have hw : |(5441455069/10000000000 : ℝ)|=(5441455069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647160031/5000000000 : ℝ)*x 0 + (-904396637/5000000000 : ℝ)*x 1 + (5313921/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647160031/5000000000 : ℝ)^4451 ≤ (43780798549449/100000000000000 : ℝ)^3427 := by
    have hnat : (2647160031 : ℕ)^4451*100000000000000^3427 ≤ 43780798549449^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647160031 5000000000 43780798549449 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904396637/5000000000 : ℝ)^4451 ≤ (5425803549643/50000000000000 : ℝ)^3427 := by
    have hnat : (904396637 : ℕ)^4451*50000000000000^3427 ≤ 5425803549643^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904396637 5000000000 5425803549643 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5313921/9765625 : ℝ)^4451 ≤ (45367594343217/100000000000000 : ℝ)^3427 := by
    have hnat : (5313921 : ℕ)^4451*100000000000000^3427 ≤ 45367594343217^3427*9765625^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5313921 9765625 45367594343217 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647160031/5000000000 : ℝ), (-904396637/5000000000 : ℝ), (5313921/9765625 : ℝ)] ![(43780798549449/100000000000000 : ℝ), (5425803549643/50000000000000 : ℝ), (45367594343217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647160031/5000000000 : ℝ)|^4451 ≤ (43780798549449/100000000000000 : ℝ)^3427
        have hw : |(2647160031/5000000000 : ℝ)|=(2647160031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-904396637/5000000000 : ℝ)|^4451 ≤ (5425803549643/50000000000000 : ℝ)^3427
        have hw : |(-904396637/5000000000 : ℝ)|=(904396637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5313921/9765625 : ℝ)|^4451 ≤ (45367594343217/100000000000000 : ℝ)^3427
        have hw : |(5313921/9765625 : ℝ)|=(5313921/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058864017/2000000000 : ℝ)*x 0 + (5441455117/10000000000 : ℝ)*x 1 + (-1808793223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058864017/2000000000 : ℝ)^4451 ≤ (10945199699119/25000000000000 : ℝ)^3427 := by
    have hnat : (1058864017 : ℕ)^4451*25000000000000^3427 ≤ 10945199699119^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058864017 2000000000 10945199699119 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441455117/10000000000 : ℝ)^4451 ≤ (4536759448399/10000000000000 : ℝ)^3427 := by
    have hnat : (5441455117 : ℕ)^4451*10000000000000^3427 ≤ 4536759448399^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441455117 10000000000 4536759448399 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1808793223/10000000000 : ℝ)^4451 ≤ (5425803350947/50000000000000 : ℝ)^3427 := by
    have hnat : (1808793223 : ℕ)^4451*50000000000000^3427 ≤ 5425803350947^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808793223 10000000000 5425803350947 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058864017/2000000000 : ℝ), (5441455117/10000000000 : ℝ), (-1808793223/10000000000 : ℝ)] ![(10945199699119/25000000000000 : ℝ), (4536759448399/10000000000000 : ℝ), (5425803350947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058864017/2000000000 : ℝ)|^4451 ≤ (10945199699119/25000000000000 : ℝ)^3427
        have hw : |(1058864017/2000000000 : ℝ)|=(1058864017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441455117/10000000000 : ℝ)|^4451 ≤ (4536759448399/10000000000000 : ℝ)^3427
        have hw : |(5441455117/10000000000 : ℝ)|=(5441455117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1808793223/10000000000 : ℝ)|^4451 ≤ (5425803350947/50000000000000 : ℝ)^3427
        have hw : |(-1808793223/10000000000 : ℝ)|=(1808793223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s3_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285963257/10000000000 : ℝ)*x 0 + (142054751/312500000 : ℝ)*x 1 + (4039400751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285963257/10000000000 : ℝ)^4451 ≤ (33273860165553/100000000000000 : ℝ)^3427 := by
    have hnat : (4285963257 : ℕ)^4451*100000000000000^3427 ≤ 33273860165553^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285963257 10000000000 33273860165553 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142054751/312500000 : ℝ)^4451 ≤ (8979188874033/25000000000000 : ℝ)^3427 := by
    have hnat : (142054751 : ℕ)^4451*25000000000000^3427 ≤ 8979188874033^3427*312500000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142054751 312500000 8979188874033 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4039400751/10000000000 : ℝ)^4451 ≤ (15404692159101/50000000000000 : ℝ)^3427 := by
    have hnat : (4039400751 : ℕ)^4451*50000000000000^3427 ≤ 15404692159101^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039400751 10000000000 15404692159101 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285963257/10000000000 : ℝ), (142054751/312500000 : ℝ), (4039400751/10000000000 : ℝ)] ![(33273860165553/100000000000000 : ℝ), (8979188874033/25000000000000 : ℝ), (15404692159101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285963257/10000000000 : ℝ)|^4451 ≤ (33273860165553/100000000000000 : ℝ)^3427
        have hw : |(4285963257/10000000000 : ℝ)|=(4285963257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142054751/312500000 : ℝ)|^4451 ≤ (8979188874033/25000000000000 : ℝ)^3427
        have hw : |(142054751/312500000 : ℝ)|=(142054751/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4039400751/10000000000 : ℝ)|^4451 ≤ (15404692159101/50000000000000 : ℝ)^3427
        have hw : |(4039400751/10000000000 : ℝ)|=(4039400751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10679/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1947/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3229/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5079/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3229/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5079/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3229/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5079/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3229/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5079/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3229/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5079/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3229/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5079/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5079/50000 : ℝ) ^ (4449/1024 : ℝ) ≤ (968017564213897/20000000000000000000 : ℝ) := by
    have hpowers : (5079/50000 : ℝ)^4449 ≤ (968017564213897/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5079 : ℕ)^4449*20000000000000000000^1024 ≤ 968017564213897^1024*50000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5079 50000 968017564213897 20000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5079/50000 : ℝ)) (X := (968017564213897/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3229/20000 : ℝ) ^ (4449/1024 : ℝ) ≤ (7247227126075747/20000000000000000000 : ℝ) := by
    have hpowers : (3229/20000 : ℝ)^4449 ≤ (7247227126075747/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3229 : ℕ)^4449*20000000000000000000^1024 ≤ 7247227126075747^1024*20000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3229 20000 7247227126075747 20000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3229/20000 : ℝ)) (X := (7247227126075747/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000968017564213897/10000000000000000000 : ℝ) ≤ (400008911782901/400000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (10000968017564213897/10000000000000000000 : ℝ)^1024 ≤ (400008911782901/400000000000000 : ℝ)^4449 := by
      have hnat : (10000968017564213897 : ℕ)^1024*400000000000000^4449 ≤ 400008911782901^4449*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000968017564213897 10000000000000000000 400008911782901 400000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400008911782901/400000000000000 : ℝ)) (X := (10000968017564213897/10000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002053811172572411/5000000000000000000 : ℝ) ≤ (5000472638840237/5000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (5002053811172572411/5000000000000000000 : ℝ)^1024 ≤ (5000472638840237/5000000000000000 : ℝ)^4449 := by
      have hnat : (5002053811172572411 : ℕ)^1024*5000000000000000^4449 ≤ 5000472638840237^4449*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002053811172572411 5000000000000000000 5000472638840237 5000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000472638840237/5000000000000000 : ℝ)) (X := (5002053811172572411/5000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007247227126075747/10000000000000000000 : ℝ) ≤ (10001667760788423/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (10007247227126075747/10000000000000000000 : ℝ)^1024 ≤ (10001667760788423/10000000000000000 : ℝ)^4449 := by
      have hnat : (10007247227126075747 : ℕ)^1024*10000000000000000^4449 ≤ 10001667760788423^4449*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007247227126075747 10000000000000000000 10001667760788423 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001667760788423/10000000000000000 : ℝ)) (X := (10007247227126075747/10000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(968017564213897/20000000000000000000 : ℝ) ≤ ((59856655904284615291/59870000000000000000 : ℝ)+2*(722483107949/598700000000000 : ℝ)*(5079/50000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (59856655904284615291/59870000000000000000 : ℝ)+2*(722483107949/598700000000000 : ℝ)*(5079/50000 : ℝ)=(400008911782901/400000000000000 : ℝ) by norm_num, show 1+2*(968017564213897/20000000000000000000 : ℝ)=(10000968017564213897/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7247227126075747/20000000000000000000 : ℝ)+(968017564213897/20000000000000000000 : ℝ) ≤ ((59856655904284615291/59870000000000000000 : ℝ)+(722483107949/598700000000000 : ℝ)*((3229/20000 : ℝ)+(5079/50000 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (59856655904284615291/59870000000000000000 : ℝ)+(722483107949/598700000000000 : ℝ)*((3229/20000 : ℝ)+(5079/50000 : ℝ))=(5000472638840237/5000000000000000 : ℝ) by norm_num, show 1+(7247227126075747/20000000000000000000 : ℝ)+(968017564213897/20000000000000000000 : ℝ)=(5002053811172572411/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7247227126075747/20000000000000000000 : ℝ) ≤ ((59856655904284615291/59870000000000000000 : ℝ)+2*(722483107949/598700000000000 : ℝ)*(3229/20000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (59856655904284615291/59870000000000000000 : ℝ)+2*(722483107949/598700000000000 : ℝ)*(3229/20000 : ℝ)=(10001667760788423/10000000000000000 : ℝ) by norm_num, show 1+2*(7247227126075747/20000000000000000000 : ℝ)=(10007247227126075747/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59856655904284615291/59870000000000000000 : ℝ)*(X 1 0+X 2 0)+(722483107949/598700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (5079/50000 : ℝ)) (hi := (3229/20000 : ℝ)) (c := (59856655904284615291/59870000000000000000 : ℝ)) (alpha := (722483107949/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59856655904284615291/59870000000000000000 : ℝ)*(X 0 1+X 2 1)+(722483107949/598700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (5079/50000 : ℝ)) (hi := (3229/20000 : ℝ)) (c := (59856655904284615291/59870000000000000000 : ℝ)) (alpha := (722483107949/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59856655904284615291/59870000000000000000 : ℝ)*(X 0 2+X 1 2)+(722483107949/598700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (5079/50000 : ℝ)) (hi := (3229/20000 : ℝ)) (c := (59856655904284615291/59870000000000000000 : ℝ)) (alpha := (722483107949/598700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1920236011/10000000000 : ℝ)*X 0 0+(5442696663/10000000000 : ℝ)*X 0 1+(2605644287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338681853/2500000000 : ℝ)*X 1 0+(-2038959349/10000000000 : ℝ)*X 1 1+(5211288599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354727433/10000000000 : ℝ)*X 2 0+(5211288441/10000000000 : ℝ)*X 2 1+(-2038959529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4285887123/10000000000 : ℝ)*X 0 0+(4036655041/10000000000 : ℝ)*X 0 1+(1137119209/2500000000 : ℝ)*X 0 2+(4285887123/10000000000 : ℝ)*X 1 0+(4036655041/10000000000 : ℝ)*X 1 1+(1137119209/2500000000 : ℝ)*X 1 2+(4285887123/10000000000 : ℝ)*X 2 0+(4036655041/10000000000 : ℝ)*X 2 1+(1137119209/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-480067603/2500000000 : ℝ)*X 0 0+(2606260389/5000000000 : ℝ)*X 0 1+(5441455069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647160031/5000000000 : ℝ)*X 1 0+(-904396637/5000000000 : ℝ)*X 1 1+(5313921/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058864017/2000000000 : ℝ)*X 2 0+(5441455117/10000000000 : ℝ)*X 2 1+(-1808793223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4285963257/10000000000 : ℝ)*X 0 0+(142054751/312500000 : ℝ)*X 0 1+(4039400751/10000000000 : ℝ)*X 0 2+(4285963257/10000000000 : ℝ)*X 1 0+(142054751/312500000 : ℝ)*X 1 1+(4039400751/10000000000 : ℝ)*X 1 2+(4285963257/10000000000 : ℝ)*X 2 0+(142054751/312500000 : ℝ)*X 2 1+(4039400751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7879672483626683856617455599/748375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2491964703/100000000000000 : ℝ)*(base19) + (1169259677/50000000000000 : ℝ)*(base23) + (45620421/50000000000000 : ℝ)*(lower2) + (179078291/50000000000000 : ℝ)*(upper3) + (35041499/50000000000000 : ℝ)*(upper5) + (1568822097667263/50000000000000 : ℝ)*(major0) + (1568822097667263/50000000000000 : ℝ)*(major1) + (1568822097667263/50000000000000 : ℝ)*(major2) + (2160706399555079/50000000000000 : ℝ)*(sp0) + (2160723531074199/50000000000000 : ℝ)*(sp1) + (4321447215593747/100000000000000 : ℝ)*(sp2) + (195381991228179/10000000000000 : ℝ)*(sp3) + (36755002943/100000000000000 : ℝ)*(sp4) + (18573306059/100000000000000 : ℝ)*(sp7) + (1953838485587849/100000000000000 : ℝ)*(f.failure) + (4321449554113101/100000000000000 : ℝ)*(f.sum) + (137955207612309/29935000000000000000000000000 : ℝ)*base65 + (7806115555202381467/2993500000000000000000000000000000 : ℝ)*base68 + (19431827284359381467/2993500000000000000000000000000000 : ℝ)*base70 + (24832941862152881467/2993500000000000000000000000000000 : ℝ)*base72 + (79287961735807/14967500000000000000000000000 : ℝ)*base73 + (25100054387679881467/2993500000000000000000000000000000 : ℝ)*base76 + (10904432603434618533/2993500000000000000000000000000000 : ℝ)*base77 + (27378594493078881467/2993500000000000000000000000000000 : ℝ)*base80 + (315935783783/3741875000000000000000000000 : ℝ)*base81 + (32875431/10000000000000000000000 : ℝ)*base89 + (32875431/10000000000000000000000 : ℝ)*base91 + (32875431/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (942254346228010405466692389/187093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82697453/12500000000000 : ℝ)*(base19) + (212156059/25000000000000 : ℝ)*(base23) + (52931693/50000000000000 : ℝ)*(upper3) + (32779037/50000000000000 : ℝ)*(lower4) + (60428521/100000000000000 : ℝ)*(upper5) + (396436092824493/12500000000000 : ℝ)*(major0) + (396436092824493/12500000000000 : ℝ)*(major1) + (396436092824493/12500000000000 : ℝ)*(major2) + (9167662253/100000000000000 : ℝ)*(sp1) + (3261283861/25000000000000 : ℝ)*(sp2) + (4265687046981/97656250000 : ℝ)*(sp4) + (2184026853433333/50000000000000 : ℝ)*(sp5) + (68250775661701/1562500000000 : ℝ)*(sp6) + (987456890603861/50000000000000 : ℝ)*(sp7) + (987456890603861/50000000000000 : ℝ)*(f.failure) + (4265687046981/97656250000 : ℝ)*(f.sum) + (75940339178273/14967500000000000000000000000 : ℝ)*base65 + (479308702868822463/748375000000000000000000000000000 : ℝ)*base67 + (6832008529195427537/748375000000000000000000000000000 : ℝ)*base70 + (1596971481418927537/748375000000000000000000000000000 : ℝ)*base72 + (137566872034851/29935000000000000000000000000 : ℝ)*base73 + (4445969961123552537/748375000000000000000000000000000 : ℝ)*base76 + (1132931208152427537/748375000000000000000000000000000 : ℝ)*base78 + (5242177321558677537/748375000000000000000000000000000 : ℝ)*base80 + (85275056321333/14967500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (25555941/5000000000000000000000 : ℝ)*base90 + (25555941/5000000000000000000000 : ℝ)*base92 + (25555941/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1477_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1947/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1477_s4_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920889217/10000000000 : ℝ)*x 0 + (5438486653/10000000000 : ℝ)*x 1 + (5215067949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920889217/10000000000 : ℝ)^4451 ≤ (11733031020849/100000000000000 : ℝ)^3427 := by
    have hnat : (1920889217 : ℕ)^4451*100000000000000^3427 ≤ 11733031020849^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920889217 10000000000 11733031020849 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438486653/10000000000 : ℝ)^4451 ≤ (11333863163953/25000000000000 : ℝ)^3427 := by
    have hnat : (5438486653 : ℕ)^4451*25000000000000^3427 ≤ 11333863163953^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438486653 10000000000 11333863163953 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215067949/10000000000 : ℝ)^4451 ≤ (1073287907911/2500000000000 : ℝ)^3427 := by
    have hnat : (5215067949 : ℕ)^4451*2500000000000^3427 ≤ 1073287907911^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215067949 10000000000 1073287907911 2500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920889217/10000000000 : ℝ), (5438486653/10000000000 : ℝ), (5215067949/10000000000 : ℝ)] ![(11733031020849/100000000000000 : ℝ), (11333863163953/25000000000000 : ℝ), (1073287907911/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920889217/10000000000 : ℝ)|^4451 ≤ (11733031020849/100000000000000 : ℝ)^3427
        have hw : |(-1920889217/10000000000 : ℝ)|=(1920889217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438486653/10000000000 : ℝ)|^4451 ≤ (11333863163953/25000000000000 : ℝ)^3427
        have hw : |(5438486653/10000000000 : ℝ)|=(5438486653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215067949/10000000000 : ℝ)|^4451 ≤ (1073287907911/2500000000000 : ℝ)^3427
        have hw : |(5215067949/10000000000 : ℝ)|=(5215067949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334602187/625000000 : ℝ)*x 0 + (-1017707099/5000000000 : ℝ)*x 1 + (5215067091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334602187/625000000 : ℝ)^4451 ≤ (44418923067631/100000000000000 : ℝ)^3427 := by
    have hnat : (334602187 : ℕ)^4451*100000000000000^3427 ≤ 44418923067631^3427*625000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334602187 625000000 44418923067631 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017707099/5000000000 : ℝ)^4451 ≤ (12649569764893/100000000000000 : ℝ)^3427 := by
    have hnat : (1017707099 : ℕ)^4451*100000000000000^3427 ≤ 12649569764893^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017707099 5000000000 12649569764893 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215067091/10000000000 : ℝ)^4451 ≤ (42931507142687/100000000000000 : ℝ)^3427 := by
    have hnat : (5215067091 : ℕ)^4451*100000000000000^3427 ≤ 42931507142687^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215067091 10000000000 42931507142687 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334602187/625000000 : ℝ), (-1017707099/5000000000 : ℝ), (5215067091/10000000000 : ℝ)] ![(44418923067631/100000000000000 : ℝ), (12649569764893/100000000000000 : ℝ), (42931507142687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334602187/625000000 : ℝ)|^4451 ≤ (44418923067631/100000000000000 : ℝ)^3427
        have hw : |(334602187/625000000 : ℝ)|=(334602187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017707099/5000000000 : ℝ)|^4451 ≤ (12649569764893/100000000000000 : ℝ)^3427
        have hw : |(-1017707099/5000000000 : ℝ)|=(1017707099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215067091/10000000000 : ℝ)|^4451 ≤ (42931507142687/100000000000000 : ℝ)^3427
        have hw : |(5215067091/10000000000 : ℝ)|=(5215067091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353634567/10000000000 : ℝ)*x 0 + (5215067819/10000000000 : ℝ)*x 1 + (-1017706901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353634567/10000000000 : ℝ)^4451 ≤ (44418918487777/100000000000000 : ℝ)^3427 := by
    have hnat : (5353634567 : ℕ)^4451*100000000000000^3427 ≤ 44418918487777^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353634567 10000000000 44418918487777 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215067819/10000000000 : ℝ)^4451 ≤ (42931514926477/100000000000000 : ℝ)^3427 := by
    have hnat : (5215067819 : ℕ)^4451*100000000000000^3427 ≤ 42931514926477^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215067819 10000000000 42931514926477 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017706901/5000000000 : ℝ)^4451 ≤ (12649566568489/100000000000000 : ℝ)^3427 := by
    have hnat : (1017706901 : ℕ)^4451*100000000000000^3427 ≤ 12649566568489^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017706901 5000000000 12649566568489 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353634567/10000000000 : ℝ), (5215067819/10000000000 : ℝ), (-1017706901/5000000000 : ℝ)] ![(44418918487777/100000000000000 : ℝ), (42931514926477/100000000000000 : ℝ), (12649566568489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353634567/10000000000 : ℝ)|^4451 ≤ (44418918487777/100000000000000 : ℝ)^3427
        have hw : |(5353634567/10000000000 : ℝ)|=(5353634567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215067819/10000000000 : ℝ)|^4451 ≤ (42931514926477/100000000000000 : ℝ)^3427
        have hw : |(5215067819/10000000000 : ℝ)|=(5215067819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017706901/5000000000 : ℝ)|^4451 ≤ (12649566568489/100000000000000 : ℝ)^3427
        have hw : |(-1017706901/5000000000 : ℝ)|=(1017706901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133946607/312500000 : ℝ)*x 0 + (809088367/2000000000 : ℝ)*x 1 + (283724713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133946607/312500000 : ℝ)^4451 ≤ (33277169175771/100000000000000 : ℝ)^3427 := by
    have hnat : (133946607 : ℕ)^4451*100000000000000^3427 ≤ 33277169175771^3427*312500000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133946607 312500000 33277169175771 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809088367/2000000000 : ℝ)^4451 ≤ (15434621106221/50000000000000 : ℝ)^3427 := by
    have hnat : (809088367 : ℕ)^4451*50000000000000^3427 ≤ 15434621106221^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809088367 2000000000 15434621106221 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283724713/625000000 : ℝ)^4451 ≤ (17926794298097/50000000000000 : ℝ)^3427 := by
    have hnat : (283724713 : ℕ)^4451*50000000000000^3427 ≤ 17926794298097^3427*625000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283724713 625000000 17926794298097 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133946607/312500000 : ℝ), (809088367/2000000000 : ℝ), (283724713/625000000 : ℝ)] ![(33277169175771/100000000000000 : ℝ), (15434621106221/50000000000000 : ℝ), (17926794298097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133946607/312500000 : ℝ)|^4451 ≤ (33277169175771/100000000000000 : ℝ)^3427
        have hw : |(133946607/312500000 : ℝ)|=(133946607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(809088367/2000000000 : ℝ)|^4451 ≤ (15434621106221/50000000000000 : ℝ)^3427
        have hw : |(809088367/2000000000 : ℝ)|=(809088367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283724713/625000000 : ℝ)|^4451 ≤ (17926794298097/50000000000000 : ℝ)^3427
        have hw : |(283724713/625000000 : ℝ)|=(283724713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480230103/2500000000 : ℝ)*x 0 + (2608108113/5000000000 : ℝ)*x 1 + (2718664873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480230103/2500000000 : ℝ)^4451 ≤ (5866639249663/50000000000000 : ℝ)^3427 := by
    have hnat : (480230103 : ℕ)^4451*50000000000000^3427 ≤ 5866639249663^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480230103 2500000000 5866639249663 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608108113/5000000000 : ℝ)^4451 ≤ (42943794120487/100000000000000 : ℝ)^3427 := by
    have hnat : (2608108113 : ℕ)^4451*100000000000000^3427 ≤ 42943794120487^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608108113 5000000000 42943794120487 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718664873/5000000000 : ℝ)^4451 ≤ (5665365919881/12500000000000 : ℝ)^3427 := by
    have hnat : (2718664873 : ℕ)^4451*12500000000000^3427 ≤ 5665365919881^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718664873 5000000000 5665365919881 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480230103/2500000000 : ℝ), (2608108113/5000000000 : ℝ), (2718664873/5000000000 : ℝ)] ![(5866639249663/50000000000000 : ℝ), (42943794120487/100000000000000 : ℝ), (5665365919881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480230103/2500000000 : ℝ)|^4451 ≤ (5866639249663/50000000000000 : ℝ)^3427
        have hw : |(-480230103/2500000000 : ℝ)|=(480230103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608108113/5000000000 : ℝ)|^4451 ≤ (42943794120487/100000000000000 : ℝ)^3427
        have hw : |(2608108113/5000000000 : ℝ)|=(2608108113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718664873/5000000000 : ℝ)|^4451 ≤ (5665365919881/12500000000000 : ℝ)^3427
        have hw : |(2718664873/5000000000 : ℝ)|=(2718664873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661914451/1250000000 : ℝ)*x 0 + (-453287979/2500000000 : ℝ)*x 1 + (5437329697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661914451/1250000000 : ℝ)^4451 ≤ (5473936415801/12500000000000 : ℝ)^3427 := by
    have hnat : (661914451 : ℕ)^4451*12500000000000^3427 ≤ 5473936415801^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661914451 1250000000 5473936415801 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453287979/2500000000 : ℝ)^4451 ≤ (1088558183221/10000000000000 : ℝ)^3427 := by
    have hnat : (453287979 : ℕ)^4451*10000000000000^3427 ≤ 1088558183221^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453287979 2500000000 1088558183221 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437329697/10000000000 : ℝ)^4451 ≤ (11330731707141/25000000000000 : ℝ)^3427 := by
    have hnat : (5437329697 : ℕ)^4451*25000000000000^3427 ≤ 11330731707141^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437329697 10000000000 11330731707141 25000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661914451/1250000000 : ℝ), (-453287979/2500000000 : ℝ), (5437329697/10000000000 : ℝ)] ![(5473936415801/12500000000000 : ℝ), (1088558183221/10000000000000 : ℝ), (11330731707141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661914451/1250000000 : ℝ)|^4451 ≤ (5473936415801/12500000000000 : ℝ)^3427
        have hw : |(661914451/1250000000 : ℝ)|=(661914451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453287979/2500000000 : ℝ)|^4451 ≤ (1088558183221/10000000000000 : ℝ)^3427
        have hw : |(-453287979/2500000000 : ℝ)|=(453287979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437329697/10000000000 : ℝ)|^4451 ≤ (11330731707141/25000000000000 : ℝ)^3427
        have hw : |(5437329697/10000000000 : ℝ)|=(5437329697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295315537/10000000000 : ℝ)*x 0 + (1359332433/2500000000 : ℝ)*x 1 + (-906575983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295315537/10000000000 : ℝ)^4451 ≤ (43791490563803/100000000000000 : ℝ)^3427 := by
    have hnat : (5295315537 : ℕ)^4451*100000000000000^3427 ≤ 43791490563803^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295315537 10000000000 43791490563803 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359332433/2500000000 : ℝ)^4451 ≤ (45322927207481/100000000000000 : ℝ)^3427 := by
    have hnat : (1359332433 : ℕ)^4451*100000000000000^3427 ≤ 45322927207481^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359332433 2500000000 45322927207481 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906575983/5000000000 : ℝ)^4451 ≤ (1088558222209/10000000000000 : ℝ)^3427 := by
    have hnat : (906575983 : ℕ)^4451*10000000000000^3427 ≤ 1088558222209^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906575983 5000000000 1088558222209 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295315537/10000000000 : ℝ), (1359332433/2500000000 : ℝ), (-906575983/5000000000 : ℝ)] ![(43791490563803/100000000000000 : ℝ), (45322927207481/100000000000000 : ℝ), (1088558222209/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295315537/10000000000 : ℝ)|^4451 ≤ (43791490563803/100000000000000 : ℝ)^3427
        have hw : |(5295315537/10000000000 : ℝ)|=(5295315537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359332433/2500000000 : ℝ)|^4451 ≤ (45322927207481/100000000000000 : ℝ)^3427
        have hw : |(1359332433/2500000000 : ℝ)|=(1359332433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-906575983/5000000000 : ℝ)|^4451 ≤ (1088558222209/10000000000000 : ℝ)^3427
        have hw : |(-906575983/5000000000 : ℝ)|=(906575983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s4_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857272141/2000000000 : ℝ)*x 0 + (453705419/1000000000 : ℝ)*x 1 + (253000071/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857272141/2000000000 : ℝ)^4451 ≤ (33277867767381/100000000000000 : ℝ)^3427 := by
    have hnat : (857272141 : ℕ)^4451*100000000000000^3427 ≤ 33277867767381^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857272141 2000000000 33277867767381 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453705419/1000000000 : ℝ)^4451 ≤ (35827523185771/100000000000000 : ℝ)^3427 := by
    have hnat : (453705419 : ℕ)^4451*100000000000000^3427 ≤ 35827523185771^3427*1000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453705419 1000000000 35827523185771 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253000071/625000000 : ℝ)^4451 ≤ (15447304512613/50000000000000 : ℝ)^3427 := by
    have hnat : (253000071 : ℕ)^4451*50000000000000^3427 ≤ 15447304512613^3427*625000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253000071 625000000 15447304512613 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857272141/2000000000 : ℝ), (453705419/1000000000 : ℝ), (253000071/625000000 : ℝ)] ![(33277867767381/100000000000000 : ℝ), (35827523185771/100000000000000 : ℝ), (15447304512613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857272141/2000000000 : ℝ)|^4451 ≤ (33277867767381/100000000000000 : ℝ)^3427
        have hw : |(857272141/2000000000 : ℝ)|=(857272141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453705419/1000000000 : ℝ)|^4451 ≤ (35827523185771/100000000000000 : ℝ)^3427
        have hw : |(453705419/1000000000 : ℝ)|=(453705419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253000071/625000000 : ℝ)|^4451 ≤ (15447304512613/50000000000000 : ℝ)^3427
        have hw : |(253000071/625000000 : ℝ)|=(253000071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1947/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (269/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1947/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1947/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1947/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1947/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1947/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1947/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10679/100000 : ℝ) ^ (4449/1024 : ℝ) ≤ (6014936330048191/100000000000000000000 : ℝ) := by
    have hpowers : (10679/100000 : ℝ)^4449 ≤ (6014936330048191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10679 : ℕ)^4449*100000000000000000000^1024 ≤ 6014936330048191^1024*100000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10679 100000 6014936330048191 100000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10679/100000 : ℝ)) (X := (6014936330048191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1947/12500 : ℝ) ^ (4449/1024 : ℝ) ≤ (15502861602245897/50000000000000000000 : ℝ) := by
    have hpowers : (1947/12500 : ℝ)^4449 ≤ (15502861602245897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1947 : ℕ)^4449*50000000000000000000^1024 ≤ 15502861602245897^1024*12500^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1947 12500 15502861602245897 50000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1947/12500 : ℝ)) (X := (15502861602245897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006014936330048191/50000000000000000000 : ℝ) ≤ (5000138435819627/5000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (50006014936330048191/50000000000000000000 : ℝ)^1024 ≤ (5000138435819627/5000000000000000 : ℝ)^4449 := by
      have hnat : (50006014936330048191 : ℕ)^1024*5000000000000000^4449 ≤ 5000138435819627^4449*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006014936330048191 50000000000000000000 5000138435819627 5000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138435819627/5000000000000000 : ℝ)) (X := (50006014936330048191/50000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007404131906907997/20000000000000000000 : ℝ) ≤ (10000851961216449/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (20007404131906907997/20000000000000000000 : ℝ)^1024 ≤ (10000851961216449/10000000000000000 : ℝ)^4449 := by
      have hnat : (20007404131906907997 : ℕ)^1024*10000000000000000^4449 ≤ 10000851961216449^4449*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007404131906907997 20000000000000000000 10000851961216449 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000851961216449/10000000000000000 : ℝ)) (X := (20007404131906907997/20000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015502861602245897/25000000000000000000 : ℝ) ≤ (2500356762698411/2500000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (25015502861602245897/25000000000000000000 : ℝ)^1024 ≤ (2500356762698411/2500000000000000 : ℝ)^4449 := by
      have hnat : (25015502861602245897 : ℕ)^1024*2500000000000000^4449 ≤ 2500356762698411^4449*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015502861602245897 25000000000000000000 2500356762698411 2500000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500356762698411/2500000000000000 : ℝ)) (X := (25015502861602245897/25000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6014936330048191/100000000000000000000 : ℝ) ≤ ((207453699479778373/207500000000000000 : ℝ)+2*(115017915439/97940000000000 : ℝ)*(10679/100000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (207453699479778373/207500000000000000 : ℝ)+2*(115017915439/97940000000000 : ℝ)*(10679/100000 : ℝ)=(5000138435819627/5000000000000000 : ℝ) by norm_num, show 1+2*(6014936330048191/100000000000000000000 : ℝ)=(50006014936330048191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15502861602245897/50000000000000000000 : ℝ)+(6014936330048191/100000000000000000000 : ℝ) ≤ ((207453699479778373/207500000000000000 : ℝ)+(115017915439/97940000000000 : ℝ)*((1947/12500 : ℝ)+(10679/100000 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (207453699479778373/207500000000000000 : ℝ)+(115017915439/97940000000000 : ℝ)*((1947/12500 : ℝ)+(10679/100000 : ℝ))=(10000851961216449/10000000000000000 : ℝ) by norm_num, show 1+(15502861602245897/50000000000000000000 : ℝ)+(6014936330048191/100000000000000000000 : ℝ)=(20007404131906907997/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15502861602245897/50000000000000000000 : ℝ) ≤ ((207453699479778373/207500000000000000 : ℝ)+2*(115017915439/97940000000000 : ℝ)*(1947/12500 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (207453699479778373/207500000000000000 : ℝ)+2*(115017915439/97940000000000 : ℝ)*(1947/12500 : ℝ)=(2500356762698411/2500000000000000 : ℝ) by norm_num, show 1+2*(15502861602245897/50000000000000000000 : ℝ)=(25015502861602245897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (207453699479778373/207500000000000000 : ℝ)*(X 1 0+X 2 0)+(115017915439/97940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (1947/12500 : ℝ)) (c := (207453699479778373/207500000000000000 : ℝ)) (alpha := (115017915439/97940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (207453699479778373/207500000000000000 : ℝ)*(X 0 1+X 2 1)+(115017915439/97940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (1947/12500 : ℝ)) (c := (207453699479778373/207500000000000000 : ℝ)) (alpha := (115017915439/97940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (207453699479778373/207500000000000000 : ℝ)*(X 0 2+X 1 2)+(115017915439/97940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (10679/100000 : ℝ)) (hi := (1947/12500 : ℝ)) (c := (207453699479778373/207500000000000000 : ℝ)) (alpha := (115017915439/97940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1920889217/10000000000 : ℝ)*X 0 0+(5438486653/10000000000 : ℝ)*X 0 1+(5215067949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334602187/625000000 : ℝ)*X 1 0+(-1017707099/5000000000 : ℝ)*X 1 1+(5215067091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353634567/10000000000 : ℝ)*X 2 0+(5215067819/10000000000 : ℝ)*X 2 1+(-1017706901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((133946607/312500000 : ℝ)*X 0 0+(809088367/2000000000 : ℝ)*X 0 1+(283724713/625000000 : ℝ)*X 0 2+(133946607/312500000 : ℝ)*X 1 0+(809088367/2000000000 : ℝ)*X 1 1+(283724713/625000000 : ℝ)*X 1 2+(133946607/312500000 : ℝ)*X 2 0+(809088367/2000000000 : ℝ)*X 2 1+(283724713/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-480230103/2500000000 : ℝ)*X 0 0+(2608108113/5000000000 : ℝ)*X 0 1+(2718664873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661914451/1250000000 : ℝ)*X 1 0+(-453287979/2500000000 : ℝ)*X 1 1+(5437329697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295315537/10000000000 : ℝ)*X 2 0+(1359332433/2500000000 : ℝ)*X 2 1+(-906575983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857272141/2000000000 : ℝ)*X 0 0+(453705419/1000000000 : ℝ)*X 0 1+(253000071/625000000 : ℝ)*X 0 2+(857272141/2000000000 : ℝ)*X 1 0+(453705419/1000000000 : ℝ)*X 1 1+(253000071/625000000 : ℝ)*X 1 2+(857272141/2000000000 : ℝ)*X 2 0+(453705419/1000000000 : ℝ)*X 2 1+(253000071/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219333423573928500877285629/19128906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1988054959/100000000000000 : ℝ)*(base19) + (323188407/20000000000000 : ℝ)*(base23) + (1934629/12500000000000 : ℝ)*(lower2) + (119334373/50000000000000 : ℝ)*(upper5) + (406227548819923/12500000000000 : ℝ)*(major0) + (406227548819923/12500000000000 : ℝ)*(major1) + (406227548819923/12500000000000 : ℝ)*(major2) + (2237961090825629/50000000000000 : ℝ)*(sp0) + (2237972857305139/50000000000000 : ℝ)*(sp1) + (1118986799852089/25000000000000 : ℝ)*(sp2) + (202367855706211/10000000000000 : ℝ)*(sp3) + (26633699133/100000000000000 : ℝ)*(sp4) + (556342577/50000000000000 : ℝ)*(sp5) + (6513251923/50000000000000 : ℝ)*(sp7) + (2023691583565957/100000000000000 : ℝ)*(f.failure) + (4475948815350391/100000000000000 : ℝ)*(f.sum) + (3853389919/122425000000000000000000000 : ℝ)*base66 + (1106885829694096039/153031250000000000000000000000000 : ℝ)*base68 + (1909415658349658539/153031250000000000000000000000000 : ℝ)*base70 + (1392728212079471039/153031250000000000000000000000000 : ℝ)*base72 + (5030561490611/2448500000000000000000000000 : ℝ)*base73 + (144762663410591461/153031250000000000000000000000000 : ℝ)*base75 + (1992688825962846039/153031250000000000000000000000000 : ℝ)*base78 + (972968799841096039/153031250000000000000000000000000 : ℝ)*base80 + (1261871921453/306062500000000000000000000 : ℝ)*base81 + (86639083/10000000000000000000000 : ℝ)*base89 + (86639083/10000000000000000000000 : ℝ)*base91 + (86639083/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3755838126685831663769631501/306062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1024280083/50000000000000 : ℝ)*(base19) + (535118157/25000000000000 : ℝ)*(base23) + (238442491/100000000000000 : ℝ)*(upper3) + (3129551/4000000000000 : ℝ)*(lower4) + (266968233/100000000000000 : ℝ)*(upper5) + (3283665172199381/100000000000000 : ℝ)*(major0) + (3283665172199381/100000000000000 : ℝ)*(major1) + (3283665172199381/100000000000000 : ℝ)*(major2) + (1516421107/5000000000000 : ℝ)*(sp1) + (30764477013/100000000000000 : ℝ)*(sp2) + (4522562910214189/100000000000000 : ℝ)*(sp4) + (4522530533231883/100000000000000 : ℝ)*(sp5) + (4522530005264547/100000000000000 : ℝ)*(sp6) + (1022383512567711/50000000000000 : ℝ)*(sp7) + (1022383512567711/50000000000000 : ℝ)*(f.failure) + (4522562910214189/100000000000000 : ℝ)*(f.sum) + (695586720523/979400000000000000000000000 : ℝ)*base66 + (3078866247552685333/1224250000000000000000000000000000 : ℝ)*base68 + (6108097182883685333/1224250000000000000000000000000000 : ℝ)*base70 + (5810041116282685333/1224250000000000000000000000000000 : ℝ)*base72 + (4077425528729/979400000000000000000000000 : ℝ)*base74 + (6122737005560935333/1224250000000000000000000000000000 : ℝ)*base76 + (1419173447858185333/1224250000000000000000000000000000 : ℝ)*base78 + (5499544908625064667/1224250000000000000000000000000000 : ℝ)*base79 + (4812316750649/4897000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (60252209/5000000000000000000000 : ℝ)*base89 + (60252209/5000000000000000000000 : ℝ)*base91 + (60252209/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1477_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1947/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1477_s5_0 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19209771/100000000 : ℝ)*x 0 + (5437907079/10000000000 : ℝ)*x 1 + (5215589607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19209771/100000000 : ℝ)^4451 ≤ (469349128953/4000000000000 : ℝ)^3427 := by
    have hnat : (19209771 : ℕ)^4451*4000000000000^3427 ≤ 469349128953^3427*100000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19209771 100000000 469349128953 4000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437907079/10000000000 : ℝ)^4451 ≤ (22664588888383/50000000000000 : ℝ)^3427 := by
    have hnat : (5437907079 : ℕ)^4451*50000000000000^3427 ≤ 22664588888383^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437907079 10000000000 22664588888383 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215589607/10000000000 : ℝ)^4451 ≤ (42937093977353/100000000000000 : ℝ)^3427 := by
    have hnat : (5215589607 : ℕ)^4451*100000000000000^3427 ≤ 42937093977353^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215589607 10000000000 42937093977353 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19209771/100000000 : ℝ), (5437907079/10000000000 : ℝ), (5215589607/10000000000 : ℝ)] ![(469349128953/4000000000000 : ℝ), (22664588888383/50000000000000 : ℝ), (42937093977353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19209771/100000000 : ℝ)|^4451 ≤ (469349128953/4000000000000 : ℝ)^3427
        have hw : |(-19209771/100000000 : ℝ)|=(19209771/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437907079/10000000000 : ℝ)|^4451 ≤ (22664588888383/50000000000000 : ℝ)^3427
        have hw : |(5437907079/10000000000 : ℝ)|=(5437907079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215589607/10000000000 : ℝ)|^4451 ≤ (42937093977353/100000000000000 : ℝ)^3427
        have hw : |(5215589607/10000000000 : ℝ)|=(5215589607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_1 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338371129/2500000000 : ℝ)*x 0 + (-2034923137/10000000000 : ℝ)*x 1 + (2607794723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338371129/2500000000 : ℝ)^4451 ≤ (22208650762873/50000000000000 : ℝ)^3427 := by
    have hnat : (1338371129 : ℕ)^4451*50000000000000^3427 ≤ 22208650762873^3427*2500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338371129 2500000000 22208650762873 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034923137/10000000000 : ℝ)^4451 ≤ (12645606197621/100000000000000 : ℝ)^3427 := by
    have hnat : (2034923137 : ℕ)^4451*100000000000000^3427 ≤ 12645606197621^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034923137 10000000000 12645606197621 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607794723/5000000000 : ℝ)^4451 ≤ (42937092255887/100000000000000 : ℝ)^3427 := by
    have hnat : (2607794723 : ℕ)^4451*100000000000000^3427 ≤ 42937092255887^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607794723 5000000000 42937092255887 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338371129/2500000000 : ℝ), (-2034923137/10000000000 : ℝ), (2607794723/5000000000 : ℝ)] ![(22208650762873/50000000000000 : ℝ), (12645606197621/100000000000000 : ℝ), (42937092255887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338371129/2500000000 : ℝ)|^4451 ≤ (22208650762873/50000000000000 : ℝ)^3427
        have hw : |(1338371129/2500000000 : ℝ)|=(1338371129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034923137/10000000000 : ℝ)|^4451 ≤ (12645606197621/100000000000000 : ℝ)^3427
        have hw : |(-2034923137/10000000000 : ℝ)|=(2034923137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607794723/5000000000 : ℝ)|^4451 ≤ (42937092255887/100000000000000 : ℝ)^3427
        have hw : |(2607794723/5000000000 : ℝ)|=(2607794723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_2 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353484933/10000000000 : ℝ)*x 0 + (2607794421/5000000000 : ℝ)*x 1 + (-101746169/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353484933/10000000000 : ℝ)^4451 ≤ (22208653009677/50000000000000 : ℝ)^3427 := by
    have hnat : (5353484933 : ℕ)^4451*50000000000000^3427 ≤ 22208653009677^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353484933 10000000000 22208653009677 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607794421/5000000000 : ℝ)^4451 ≤ (21468542898857/50000000000000 : ℝ)^3427 := by
    have hnat : (2607794421 : ℕ)^4451*50000000000000^3427 ≤ 21468542898857^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607794421 5000000000 21468542898857 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101746169/500000000 : ℝ)^4451 ≤ (12645608158909/100000000000000 : ℝ)^3427 := by
    have hnat : (101746169 : ℕ)^4451*100000000000000^3427 ≤ 12645608158909^3427*500000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101746169 500000000 12645608158909 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353484933/10000000000 : ℝ), (2607794421/5000000000 : ℝ), (-101746169/500000000 : ℝ)] ![(22208653009677/50000000000000 : ℝ), (21468542898857/50000000000000 : ℝ), (12645608158909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353484933/10000000000 : ℝ)|^4451 ≤ (22208653009677/50000000000000 : ℝ)^3427
        have hw : |(5353484933/10000000000 : ℝ)|=(5353484933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607794421/5000000000 : ℝ)|^4451 ≤ (21468542898857/50000000000000 : ℝ)^3427
        have hw : |(2607794421/5000000000 : ℝ)|=(2607794421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101746169/500000000 : ℝ)|^4451 ≤ (12645608158909/100000000000000 : ℝ)^3427
        have hw : |(-101746169/500000000 : ℝ)|=(101746169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_3 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26789667/62500000 : ℝ)*x 0 + (4046653817/10000000000 : ℝ)*x 1 + (2269184997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26789667/62500000 : ℝ)^4451 ≤ (16638863375019/50000000000000 : ℝ)^3427 := by
    have hnat : (26789667 : ℕ)^4451*50000000000000^3427 ≤ 16638863375019^3427*62500000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26789667 62500000 16638863375019 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4046653817/10000000000 : ℝ)^4451 ≤ (15440627158501/50000000000000 : ℝ)^3427 := by
    have hnat : (4046653817 : ℕ)^4451*50000000000000^3427 ≤ 15440627158501^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046653817 10000000000 15440627158501 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269184997/5000000000 : ℝ)^4451 ≤ (17920509457047/50000000000000 : ℝ)^3427 := by
    have hnat : (2269184997 : ℕ)^4451*50000000000000^3427 ≤ 17920509457047^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269184997 5000000000 17920509457047 50000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26789667/62500000 : ℝ), (4046653817/10000000000 : ℝ), (2269184997/5000000000 : ℝ)] ![(16638863375019/50000000000000 : ℝ), (15440627158501/50000000000000 : ℝ), (17920509457047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26789667/62500000 : ℝ)|^4451 ≤ (16638863375019/50000000000000 : ℝ)^3427
        have hw : |(26789667/62500000 : ℝ)|=(26789667/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4046653817/10000000000 : ℝ)|^4451 ≤ (15440627158501/50000000000000 : ℝ)^3427
        have hw : |(4046653817/10000000000 : ℝ)|=(4046653817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269184997/5000000000 : ℝ)|^4451 ≤ (17920509457047/50000000000000 : ℝ)^3427
        have hw : |(2269184997/5000000000 : ℝ)|=(2269184997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_4 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-960503537/5000000000 : ℝ)*x 0 + (2608363641/5000000000 : ℝ)*x 1 + (5436761469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (960503537/5000000000 : ℝ)^4451 ≤ (11733966019003/100000000000000 : ℝ)^3427 := by
    have hnat : (960503537 : ℕ)^4451*100000000000000^3427 ≤ 11733966019003^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960503537 5000000000 11733966019003 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608363641/5000000000 : ℝ)^4451 ≤ (42949258780717/100000000000000 : ℝ)^3427 := by
    have hnat : (2608363641 : ℕ)^4451*100000000000000^3427 ≤ 42949258780717^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608363641 5000000000 42949258780717 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436761469/10000000000 : ℝ)^4451 ≤ (45316775178551/100000000000000 : ℝ)^3427 := by
    have hnat : (5436761469 : ℕ)^4451*100000000000000^3427 ≤ 45316775178551^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436761469 10000000000 45316775178551 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-960503537/5000000000 : ℝ), (2608363641/5000000000 : ℝ), (5436761469/10000000000 : ℝ)] ![(11733966019003/100000000000000 : ℝ), (42949258780717/100000000000000 : ℝ), (45316775178551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-960503537/5000000000 : ℝ)|^4451 ≤ (11733966019003/100000000000000 : ℝ)^3427
        have hw : |(-960503537/5000000000 : ℝ)|=(960503537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608363641/5000000000 : ℝ)|^4451 ≤ (42949258780717/100000000000000 : ℝ)^3427
        have hw : |(2608363641/5000000000 : ℝ)|=(2608363641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436761469/10000000000 : ℝ)|^4451 ≤ (45316775178551/100000000000000 : ℝ)^3427
        have hw : |(5436761469/10000000000 : ℝ)|=(5436761469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_5 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295452929/10000000000 : ℝ)*x 0 + (-906875733/5000000000 : ℝ)*x 1 + (5436761599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295452929/10000000000 : ℝ)^4451 ≤ (43792966285637/100000000000000 : ℝ)^3427 := by
    have hnat : (5295452929 : ℕ)^4451*100000000000000^3427 ≤ 43792966285637^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295452929 10000000000 43792966285637 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906875733/5000000000 : ℝ)^4451 ≤ (680641069633/6250000000000 : ℝ)^3427 := by
    have hnat : (906875733 : ℕ)^4451*6250000000000^3427 ≤ 680641069633^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906875733 5000000000 680641069633 6250000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436761599/10000000000 : ℝ)^4451 ≤ (5664597073239/12500000000000 : ℝ)^3427 := by
    have hnat : (5436761599 : ℕ)^4451*12500000000000^3427 ≤ 5664597073239^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436761599 10000000000 5664597073239 12500000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295452929/10000000000 : ℝ), (-906875733/5000000000 : ℝ), (5436761599/10000000000 : ℝ)] ![(43792966285637/100000000000000 : ℝ), (680641069633/6250000000000 : ℝ), (5664597073239/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295452929/10000000000 : ℝ)|^4451 ≤ (43792966285637/100000000000000 : ℝ)^3427
        have hw : |(5295452929/10000000000 : ℝ)|=(5295452929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-906875733/5000000000 : ℝ)|^4451 ≤ (680641069633/6250000000000 : ℝ)^3427
        have hw : |(-906875733/5000000000 : ℝ)|=(906875733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436761599/10000000000 : ℝ)|^4451 ≤ (5664597073239/12500000000000 : ℝ)^3427
        have hw : |(5436761599/10000000000 : ℝ)|=(5436761599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_6 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059090641/2000000000 : ℝ)*x 0 + (5436761749/10000000000 : ℝ)*x 1 + (-906875439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059090641/2000000000 : ℝ)^4451 ≤ (43792969250153/100000000000000 : ℝ)^3427 := by
    have hnat : (1059090641 : ℕ)^4451*100000000000000^3427 ≤ 43792969250153^3427*2000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059090641 2000000000 43792969250153 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436761749/10000000000 : ℝ)^4451 ≤ (4531677820979/10000000000000 : ℝ)^3427 := by
    have hnat : (5436761749 : ℕ)^4451*10000000000000^3427 ≤ 4531677820979^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436761749 10000000000 4531677820979 10000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906875439/5000000000 : ℝ)^4451 ≤ (10890252528687/100000000000000 : ℝ)^3427 := by
    have hnat : (906875439 : ℕ)^4451*100000000000000^3427 ≤ 10890252528687^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906875439 5000000000 10890252528687 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059090641/2000000000 : ℝ), (5436761749/10000000000 : ℝ), (-906875439/5000000000 : ℝ)] ![(43792969250153/100000000000000 : ℝ), (4531677820979/10000000000000 : ℝ), (10890252528687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059090641/2000000000 : ℝ)|^4451 ≤ (43792969250153/100000000000000 : ℝ)^3427
        have hw : |(1059090641/2000000000 : ℝ)|=(1059090641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436761749/10000000000 : ℝ)|^4451 ≤ (4531677820979/10000000000000 : ℝ)^3427
        have hw : |(5436761749/10000000000 : ℝ)|=(5436761749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-906875439/5000000000 : ℝ)|^4451 ≤ (10890252528687/100000000000000 : ℝ)^3427
        have hw : |(-906875439/5000000000 : ℝ)|=(906875439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1477_s5_7 (p : ℝ) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535801837/1250000000 : ℝ)*x 0 + (4535854287/10000000000 : ℝ)*x 1 + (2024593807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535801837/1250000000 : ℝ)^4451 ≤ (6655682437071/20000000000000 : ℝ)^3427 := by
    have hnat : (535801837 : ℕ)^4451*20000000000000^3427 ≤ 6655682437071^3427*1250000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535801837 1250000000 6655682437071 20000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535854287/10000000000 : ℝ)^4451 ≤ (35815217231779/100000000000000 : ℝ)^3427 := by
    have hnat : (4535854287 : ℕ)^4451*100000000000000^3427 ≤ 35815217231779^3427*10000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535854287 10000000000 35815217231779 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024593807/5000000000 : ℝ)^4451 ≤ (30906370567491/100000000000000 : ℝ)^3427 := by
    have hnat : (2024593807 : ℕ)^4451*100000000000000^3427 ≤ 30906370567491^3427*5000000000^4451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024593807 5000000000 30906370567491 100000000000000 4451 3427 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4451/1024 : ℝ)) 4451 3427 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535801837/1250000000 : ℝ), (4535854287/10000000000 : ℝ), (2024593807/5000000000 : ℝ)] ![(6655682437071/20000000000000 : ℝ), (35815217231779/100000000000000 : ℝ), (30906370567491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535801837/1250000000 : ℝ)|^4451 ≤ (6655682437071/20000000000000 : ℝ)^3427
        have hw : |(535801837/1250000000 : ℝ)|=(535801837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535854287/10000000000 : ℝ)|^4451 ≤ (35815217231779/100000000000000 : ℝ)^3427
        have hw : |(4535854287/10000000000 : ℝ)|=(4535854287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2024593807/5000000000 : ℝ)|^4451 ≤ (30906370567491/100000000000000 : ℝ)^3427
        have hw : |(2024593807/5000000000 : ℝ)|=(2024593807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1477_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2693/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (269/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (269/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (269/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (269/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (269/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (269/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (269/2500 : ℝ) ^ (4449/1024 : ℝ) ≤ (388480366791001/6250000000000000000 : ℝ) := by
    have hpowers : (269/2500 : ℝ)^4449 ≤ (388480366791001/6250000000000000000 : ℝ)^1024 := by
      have hnat : (269 : ℕ)^4449*6250000000000000000^1024 ≤ 388480366791001^1024*2500^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 2500 388480366791001 6250000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/2500 : ℝ)) (X := (388480366791001/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4449/1024 : ℝ) ≤ (15130144208944363/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4449 ≤ (15130144208944363/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4449*50000000000000000000^1024 ≤ 15130144208944363^1024*100000^4449 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 15130144208944363 50000000000000000000 4449 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (15130144208944363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125388480366791001/3125000000000000000 : ℝ) ≤ (2000057222367179/2000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (3125388480366791001/3125000000000000000 : ℝ)^1024 ≤ (2000057222367179/2000000000000000 : ℝ)^4449 := by
      have hnat : (3125388480366791001 : ℕ)^1024*2000000000000000^4449 ≤ 2000057222367179^4449*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125388480366791001 3125000000000000000 2000057222367179 2000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000057222367179/2000000000000000 : ℝ)) (X := (3125388480366791001/3125000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018237987143272371/50000000000000000000 : ℝ) ≤ (625052464253997/625000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (50018237987143272371/50000000000000000000 : ℝ)^1024 ≤ (625052464253997/625000000000000 : ℝ)^4449 := by
      have hnat : (50018237987143272371 : ℕ)^1024*625000000000000^4449 ≤ 625052464253997^4449*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018237987143272371 50000000000000000000 625052464253997 625000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625052464253997/625000000000000 : ℝ)) (X := (50018237987143272371/50000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015130144208944363/25000000000000000000 : ℝ) ≤ (10001392744292009/10000000000000000 : ℝ) ^ (4449/1024 : ℝ) := by
    have hpowers : (25015130144208944363/25000000000000000000 : ℝ)^1024 ≤ (10001392744292009/10000000000000000 : ℝ)^4449 := by
      have hnat : (25015130144208944363 : ℕ)^1024*10000000000000000^4449 ≤ 10001392744292009^4449*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015130144208944363 25000000000000000000 10001392744292009 10000000000000000 1024 4449 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001392744292009/10000000000000000 : ℝ)) (X := (25015130144208944363/25000000000000000000 : ℝ)) (by norm_num) 4449 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(388480366791001/6250000000000000000 : ℝ) ≤ ((9455889131528832163/9458000000000000000 : ℝ)+2*(553316228057/472900000000000 : ℝ)*(269/2500 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (9455889131528832163/9458000000000000000 : ℝ)+2*(553316228057/472900000000000 : ℝ)*(269/2500 : ℝ)=(2000057222367179/2000000000000000 : ℝ) by norm_num, show 1+2*(388480366791001/6250000000000000000 : ℝ)=(3125388480366791001/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15130144208944363/50000000000000000000 : ℝ)+(388480366791001/6250000000000000000 : ℝ) ≤ ((9455889131528832163/9458000000000000000 : ℝ)+(553316228057/472900000000000 : ℝ)*((15489/100000 : ℝ)+(269/2500 : ℝ)))^(4449/1024 : ℝ) := by
    rw [show (9455889131528832163/9458000000000000000 : ℝ)+(553316228057/472900000000000 : ℝ)*((15489/100000 : ℝ)+(269/2500 : ℝ))=(625052464253997/625000000000000 : ℝ) by norm_num, show 1+(15130144208944363/50000000000000000000 : ℝ)+(388480366791001/6250000000000000000 : ℝ)=(50018237987143272371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15130144208944363/50000000000000000000 : ℝ) ≤ ((9455889131528832163/9458000000000000000 : ℝ)+2*(553316228057/472900000000000 : ℝ)*(15489/100000 : ℝ))^(4449/1024 : ℝ) := by
    rw [show (9455889131528832163/9458000000000000000 : ℝ)+2*(553316228057/472900000000000 : ℝ)*(15489/100000 : ℝ)=(10001392744292009/10000000000000000 : ℝ) by norm_num, show 1+2*(15130144208944363/50000000000000000000 : ℝ)=(25015130144208944363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9455889131528832163/9458000000000000000 : ℝ)*(X 1 0+X 2 0)+(553316228057/472900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (9455889131528832163/9458000000000000000 : ℝ)) (alpha := (553316228057/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9455889131528832163/9458000000000000000 : ℝ)*(X 0 1+X 2 1)+(553316228057/472900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (9455889131528832163/9458000000000000000 : ℝ)) (alpha := (553316228057/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9455889131528832163/9458000000000000000 : ℝ)*(X 0 2+X 1 2)+(553316228057/472900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4449/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (9455889131528832163/9458000000000000000 : ℝ)) (alpha := (553316228057/472900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-19209771/100000000 : ℝ)*X 0 0+(5437907079/10000000000 : ℝ)*X 0 1+(5215589607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338371129/2500000000 : ℝ)*X 1 0+(-2034923137/10000000000 : ℝ)*X 1 1+(2607794723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353484933/10000000000 : ℝ)*X 2 0+(2607794421/5000000000 : ℝ)*X 2 1+(-101746169/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26789667/62500000 : ℝ)*X 0 0+(4046653817/10000000000 : ℝ)*X 0 1+(2269184997/5000000000 : ℝ)*X 0 2+(26789667/62500000 : ℝ)*X 1 0+(4046653817/10000000000 : ℝ)*X 1 1+(2269184997/5000000000 : ℝ)*X 1 2+(26789667/62500000 : ℝ)*X 2 0+(4046653817/10000000000 : ℝ)*X 2 1+(2269184997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-960503537/5000000000 : ℝ)*X 0 0+(2608363641/5000000000 : ℝ)*X 0 1+(5436761469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295452929/10000000000 : ℝ)*X 1 0+(-906875733/5000000000 : ℝ)*X 1 1+(5436761599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059090641/2000000000 : ℝ)*X 2 0+(5436761749/10000000000 : ℝ)*X 2 1+(-906875439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535801837/1250000000 : ℝ)*X 0 0+(4535854287/10000000000 : ℝ)*X 0 1+(2024593807/5000000000 : ℝ)*X 0 2+(535801837/1250000000 : ℝ)*X 1 0+(4535854287/10000000000 : ℝ)*X 1 1+(2024593807/5000000000 : ℝ)*X 1 2+(535801837/1250000000 : ℝ)*X 2 0+(4535854287/10000000000 : ℝ)*X 2 1+(2024593807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1477_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34210684957776098812497/23645000000000000000000000000 : ℝ) := by norm_num
    linear_combination (310420097/50000000000000 : ℝ)*(base19) + (208838409/20000000000000 : ℝ)*(base23) + (7104399/10000000000000 : ℝ)*(upper2) + (14545669/12500000000000 : ℝ)*(upper3) + (15986643/50000000000000 : ℝ)*(upper4) + (1632945798509539/50000000000000 : ℝ)*(major0) + (1632945798509539/50000000000000 : ℝ)*(major1) + (1632945798509539/50000000000000 : ℝ)*(major2) + (4498078986979641/100000000000000 : ℝ)*(sp0) + (1124520815141393/25000000000000 : ℝ)*(sp1) + (4498082837213721/100000000000000 : ℝ)*(sp2) + (1016847710884471/50000000000000 : ℝ)*(sp3) + (39155409/800000000000 : ℝ)*(sp4) + (3842635227/100000000000000 : ℝ)*(sp7) + (2033699264404169/100000000000000 : ℝ)*(f.failure) + (2249041940702883/50000000000000 : ℝ)*(f.sum) + (30981897699139/5911250000000000000000000000 : ℝ)*base65 + (2213678124930837143/472900000000000000000000000000000 : ℝ)*base68 + (2069550830569762857/472900000000000000000000000000000 : ℝ)*base69 + (4405593625706362857/472900000000000000000000000000000 : ℝ)*base71 + (63720158162909/23645000000000000000000000000 : ℝ)*base74 + (3665300092190237143/472900000000000000000000000000000 : ℝ)*base76 + (2528330752067462857/472900000000000000000000000000000 : ℝ)*base77 + (2673847748200537143/472900000000000000000000000000000 : ℝ)*base80 + (28347425804319/5911250000000000000000000000 : ℝ)*base81 + (2030489/10000000000000000000000 : ℝ)*base90 + (2030489/10000000000000000000000 : ℝ)*base92 + (2030489/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (937492844419315850208525483/236450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169983431/100000000000000 : ℝ)*(base23) + (44579901/25000000000000 : ℝ)*(lower2) + (4967849/12500000000000 : ℝ)*(upper3) + (78865517/100000000000000 : ℝ)*(lower4) + (1649887449814547/50000000000000 : ℝ)*(major0) + (1649887449814547/50000000000000 : ℝ)*(major1) + (1649887449814547/50000000000000 : ℝ)*(major2) + (6831137/781250000000 : ℝ)*(sp1) + (2977125219/25000000000000 : ℝ)*(sp2) + (1130596937/100000000000000 : ℝ)*(sp3) + (454475097377733/10000000000000 : ℝ)*(sp4) + (2272375049695897/50000000000000 : ℝ)*(sp5) + (142023090477907/3125000000000 : ℝ)*(sp6) + (2054797562721673/100000000000000 : ℝ)*(sp7) + (205479869331861/10000000000000 : ℝ)*(f.failure) + (454475097377733/10000000000000 : ℝ)*(f.sum) + (121381988145649/11822500000000000000000000000 : ℝ)*base65 + (682718776503544839/472900000000000000000000000000000 : ℝ)*base68 + (12130694569830544839/472900000000000000000000000000000 : ℝ)*base70 + (140415451317455161/472900000000000000000000000000000 : ℝ)*base71 + (20915167970489/11822500000000000000000000000 : ℝ)*base73 + (327996733357344839/472900000000000000000000000000000 : ℝ)*base76 + (1274509873177944839/472900000000000000000000000000000 : ℝ)*base78 + (14053579396963255161/472900000000000000000000000000000 : ℝ)*base79 + (7883335490801/11822500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3876059/1000000000000000000000 : ℝ)*base89 + (3876059/1000000000000000000000 : ℝ)*base91 + (3876059/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1477_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1477_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1477_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1477_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1477_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1477_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4449/1024 : ℝ) ≤ p) (hpb : p ≤ (4451/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160588719/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3229/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5079/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1477_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

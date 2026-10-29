-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1580_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:56.642849+00:00
-- url     : https://prove2.me/submissions/aee29a5c-63aa-4403-8b5d-ff1831cc14fe

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
theorem support_rectangle_w1580_s0_0 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404006557/2500000000 : ℝ)*x 0 + (366397261/625000000 : ℝ)*x 1 + (4883340407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404006557/2500000000 : ℝ)^4657 ≤ (9668099285039/100000000000000 : ℝ)^3633 := by
    have hnat : (404006557 : ℕ)^4657*100000000000000^3633 ≤ 9668099285039^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404006557 2500000000 9668099285039 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366397261/625000000 : ℝ)^4657 ≤ (50431381407711/100000000000000 : ℝ)^3633 := by
    have hnat : (366397261 : ℕ)^4657*100000000000000^3633 ≤ 50431381407711^3633*625000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366397261 625000000 50431381407711 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4883340407/10000000000 : ℝ)^4657 ≤ (997512982313/2500000000000 : ℝ)^3633 := by
    have hnat : (4883340407 : ℕ)^4657*2500000000000^3633 ≤ 997512982313^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883340407 10000000000 997512982313 2500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404006557/2500000000 : ℝ), (366397261/625000000 : ℝ), (4883340407/10000000000 : ℝ)] ![(9668099285039/100000000000000 : ℝ), (50431381407711/100000000000000 : ℝ), (997512982313/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404006557/2500000000 : ℝ)|^4657 ≤ (9668099285039/100000000000000 : ℝ)^3633
        have hw : |(-404006557/2500000000 : ℝ)|=(404006557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366397261/625000000 : ℝ)|^4657 ≤ (50431381407711/100000000000000 : ℝ)^3633
        have hw : |(366397261/625000000 : ℝ)|=(366397261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4883340407/10000000000 : ℝ)|^4657 ≤ (997512982313/2500000000000 : ℝ)^3633
        have hw : |(4883340407/10000000000 : ℝ)|=(4883340407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_1 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092669867/2000000000 : ℝ)*x 0 + (-2160175937/10000000000 : ℝ)*x 1 + (39066723/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092669867/2000000000 : ℝ)^4657 ≤ (46074323476089/100000000000000 : ℝ)^3633 := by
    have hnat : (1092669867 : ℕ)^4657*100000000000000^3633 ≤ 46074323476089^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092669867 2000000000 46074323476089 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160175937/10000000000 : ℝ)^4657 ≤ (1753144693729/12500000000000 : ℝ)^3633 := by
    have hnat : (2160175937 : ℕ)^4657*12500000000000^3633 ≤ 1753144693729^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160175937 10000000000 1753144693729 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39066723/80000000 : ℝ)^4657 ≤ (39900518957359/100000000000000 : ℝ)^3633 := by
    have hnat : (39066723 : ℕ)^4657*100000000000000^3633 ≤ 39900518957359^3633*80000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39066723 80000000 39900518957359 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092669867/2000000000 : ℝ), (-2160175937/10000000000 : ℝ), (39066723/80000000 : ℝ)] ![(46074323476089/100000000000000 : ℝ), (1753144693729/12500000000000 : ℝ), (39900518957359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092669867/2000000000 : ℝ)|^4657 ≤ (46074323476089/100000000000000 : ℝ)^3633
        have hw : |(1092669867/2000000000 : ℝ)|=(1092669867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2160175937/10000000000 : ℝ)|^4657 ≤ (1753144693729/12500000000000 : ℝ)^3633
        have hw : |(-2160175937/10000000000 : ℝ)|=(2160175937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39066723/80000000 : ℝ)|^4657 ≤ (39900518957359/100000000000000 : ℝ)^3633
        have hw : |(39066723/80000000 : ℝ)|=(39066723/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_2 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2731674701/5000000000 : ℝ)*x 0 + (4883340283/10000000000 : ℝ)*x 1 + (-1080087983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2731674701/5000000000 : ℝ)^4657 ≤ (719911315631/1562500000000 : ℝ)^3633 := by
    have hnat : (2731674701 : ℕ)^4657*1562500000000^3633 ≤ 719911315631^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731674701 5000000000 719911315631 1562500000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4883340283/10000000000 : ℝ)^4657 ≤ (19950258996887/50000000000000 : ℝ)^3633 := by
    have hnat : (4883340283 : ℕ)^4657*50000000000000^3633 ≤ 19950258996887^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883340283 10000000000 19950258996887 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080087983/5000000000 : ℝ)^4657 ≤ (14025157791187/100000000000000 : ℝ)^3633 := by
    have hnat : (1080087983 : ℕ)^4657*100000000000000^3633 ≤ 14025157791187^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080087983 5000000000 14025157791187 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2731674701/5000000000 : ℝ), (4883340283/10000000000 : ℝ), (-1080087983/5000000000 : ℝ)] ![(719911315631/1562500000000 : ℝ), (19950258996887/50000000000000 : ℝ), (14025157791187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2731674701/5000000000 : ℝ)|^4657 ≤ (719911315631/1562500000000 : ℝ)^3633
        have hw : |(2731674701/5000000000 : ℝ)|=(2731674701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4883340283/10000000000 : ℝ)|^4657 ≤ (19950258996887/50000000000000 : ℝ)^3633
        have hw : |(4883340283/10000000000 : ℝ)|=(4883340283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1080087983/5000000000 : ℝ)|^4657 ≤ (14025157791187/100000000000000 : ℝ)^3633
        have hw : |(-1080087983/5000000000 : ℝ)|=(1080087983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_3 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063639763/5000000000 : ℝ)*x 0 + (773438623/2500000000 : ℝ)*x 1 + (5420533771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063639763/5000000000 : ℝ)^4657 ≤ (16080688243809/50000000000000 : ℝ)^3633 := by
    have hnat : (2063639763 : ℕ)^4657*50000000000000^3633 ≤ 16080688243809^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063639763 5000000000 16080688243809 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773438623/2500000000 : ℝ)^4657 ≤ (22226640246589/100000000000000 : ℝ)^3633 := by
    have hnat : (773438623 : ℕ)^4657*100000000000000^3633 ≤ 22226640246589^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773438623 2500000000 22226640246589 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420533771/10000000000 : ℝ)^4657 ≤ (9122396650497/20000000000000 : ℝ)^3633 := by
    have hnat : (5420533771 : ℕ)^4657*20000000000000^3633 ≤ 9122396650497^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420533771 10000000000 9122396650497 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063639763/5000000000 : ℝ), (773438623/2500000000 : ℝ), (5420533771/10000000000 : ℝ)] ![(16080688243809/50000000000000 : ℝ), (22226640246589/100000000000000 : ℝ), (9122396650497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063639763/5000000000 : ℝ)|^4657 ≤ (16080688243809/50000000000000 : ℝ)^3633
        have hw : |(2063639763/5000000000 : ℝ)|=(2063639763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773438623/2500000000 : ℝ)|^4657 ≤ (22226640246589/100000000000000 : ℝ)^3633
        have hw : |(773438623/2500000000 : ℝ)|=(773438623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420533771/10000000000 : ℝ)|^4657 ≤ (9122396650497/20000000000000 : ℝ)^3633
        have hw : |(5420533771/10000000000 : ℝ)|=(5420533771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_4 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202375961/1250000000 : ℝ)*x 0 + (4907956071/10000000000 : ℝ)*x 1 + (5836869973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202375961/1250000000 : ℝ)^4657 ≤ (302842805321/3125000000000 : ℝ)^3633 := by
    have hnat : (202375961 : ℕ)^4657*3125000000000^3633 ≤ 302842805321^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202375961 1250000000 302842805321 3125000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4907956071/10000000000 : ℝ)^4657 ≤ (10039630161383/25000000000000 : ℝ)^3633 := by
    have hnat : (4907956071 : ℕ)^4657*25000000000000^3633 ≤ 10039630161383^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907956071 10000000000 10039630161383 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5836869973/10000000000 : ℝ)^4657 ≤ (50150509569631/100000000000000 : ℝ)^3633 := by
    have hnat : (5836869973 : ℕ)^4657*100000000000000^3633 ≤ 50150509569631^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5836869973 10000000000 50150509569631 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202375961/1250000000 : ℝ), (4907956071/10000000000 : ℝ), (5836869973/10000000000 : ℝ)] ![(302842805321/3125000000000 : ℝ), (10039630161383/25000000000000 : ℝ), (50150509569631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202375961/1250000000 : ℝ)|^4657 ≤ (302842805321/3125000000000 : ℝ)^3633
        have hw : |(-202375961/1250000000 : ℝ)|=(202375961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4907956071/10000000000 : ℝ)|^4657 ≤ (10039630161383/25000000000000 : ℝ)^3633
        have hw : |(4907956071/10000000000 : ℝ)|=(4907956071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5836869973/10000000000 : ℝ)|^4657 ≤ (50150509569631/100000000000000 : ℝ)^3633
        have hw : |(5836869973/10000000000 : ℝ)|=(5836869973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_5 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597849817/5000000000 : ℝ)*x 0 + (-603323349/5000000000 : ℝ)*x 1 + (729608733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597849817/5000000000 : ℝ)^4657 ≤ (43201145187439/100000000000000 : ℝ)^3633 := by
    have hnat : (2597849817 : ℕ)^4657*100000000000000^3633 ≤ 43201145187439^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597849817 5000000000 43201145187439 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603323349/5000000000 : ℝ)^4657 ≤ (6648346431447/100000000000000 : ℝ)^3633 := by
    have hnat : (603323349 : ℕ)^4657*100000000000000^3633 ≤ 6648346431447^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603323349 5000000000 6648346431447 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (729608733/1250000000 : ℝ)^4657 ≤ (50150508369129/100000000000000 : ℝ)^3633 := by
    have hnat : (729608733 : ℕ)^4657*100000000000000^3633 ≤ 50150508369129^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729608733 1250000000 50150508369129 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597849817/5000000000 : ℝ), (-603323349/5000000000 : ℝ), (729608733/1250000000 : ℝ)] ![(43201145187439/100000000000000 : ℝ), (6648346431447/100000000000000 : ℝ), (50150508369129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597849817/5000000000 : ℝ)|^4657 ≤ (43201145187439/100000000000000 : ℝ)^3633
        have hw : |(2597849817/5000000000 : ℝ)|=(2597849817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-603323349/5000000000 : ℝ)|^4657 ≤ (6648346431447/100000000000000 : ℝ)^3633
        have hw : |(-603323349/5000000000 : ℝ)|=(603323349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(729608733/1250000000 : ℝ)|^4657 ≤ (50150508369129/100000000000000 : ℝ)^3633
        have hw : |(729608733/1250000000 : ℝ)|=(729608733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_6 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259784913/500000000 : ℝ)*x 0 + (729608919/1250000000 : ℝ)*x 1 + (-24132929/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259784913/500000000 : ℝ)^4657 ≤ (10800282635699/25000000000000 : ℝ)^3633 := by
    have hnat : (259784913 : ℕ)^4657*25000000000000^3633 ≤ 10800282635699^3633*500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259784913 500000000 10800282635699 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729608919/1250000000 : ℝ)^4657 ≤ (25075262378813/50000000000000 : ℝ)^3633 := by
    have hnat : (729608919 : ℕ)^4657*50000000000000^3633 ≤ 25075262378813^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729608919 1250000000 25075262378813 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24132929/200000000 : ℝ)^4657 ≤ (6648344679883/100000000000000 : ℝ)^3633 := by
    have hnat : (24132929 : ℕ)^4657*100000000000000^3633 ≤ 6648344679883^3633*200000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24132929 200000000 6648344679883 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259784913/500000000 : ℝ), (729608919/1250000000 : ℝ), (-24132929/200000000 : ℝ)] ![(10800282635699/25000000000000 : ℝ), (25075262378813/50000000000000 : ℝ), (6648344679883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259784913/500000000 : ℝ)|^4657 ≤ (10800282635699/25000000000000 : ℝ)^3633
        have hw : |(259784913/500000000 : ℝ)|=(259784913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(729608919/1250000000 : ℝ)|^4657 ≤ (25075262378813/50000000000000 : ℝ)^3633
        have hw : |(729608919/1250000000 : ℝ)|=(729608919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24132929/200000000 : ℝ)|^4657 ≤ (6648344679883/100000000000000 : ℝ)^3633
        have hw : |(-24132929/200000000 : ℝ)|=(24132929/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s0_7 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4134362833/10000000000 : ℝ)*x 0 + (5362026591/10000000000 : ℝ)*x 1 + (630865083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134362833/10000000000 : ℝ)^4657 ≤ (32232147048217/100000000000000 : ℝ)^3633 := by
    have hnat : (4134362833 : ℕ)^4657*100000000000000^3633 ≤ 32232147048217^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134362833 10000000000 32232147048217 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5362026591/10000000000 : ℝ)^4657 ≤ (44981862096929/100000000000000 : ℝ)^3633 := by
    have hnat : (5362026591 : ℕ)^4657*100000000000000^3633 ≤ 44981862096929^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362026591 10000000000 44981862096929 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630865083/2000000000 : ℝ)^4657 ≤ (11392995421469/50000000000000 : ℝ)^3633 := by
    have hnat : (630865083 : ℕ)^4657*50000000000000^3633 ≤ 11392995421469^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630865083 2000000000 11392995421469 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134362833/10000000000 : ℝ), (5362026591/10000000000 : ℝ), (630865083/2000000000 : ℝ)] ![(32232147048217/100000000000000 : ℝ), (44981862096929/100000000000000 : ℝ), (11392995421469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134362833/10000000000 : ℝ)|^4657 ≤ (32232147048217/100000000000000 : ℝ)^3633
        have hw : |(4134362833/10000000000 : ℝ)|=(4134362833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5362026591/10000000000 : ℝ)|^4657 ≤ (44981862096929/100000000000000 : ℝ)^3633
        have hw : |(5362026591/10000000000 : ℝ)|=(5362026591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630865083/2000000000 : ℝ)|^4657 ≤ (11392995421469/50000000000000 : ℝ)^3633
        have hw : |(630865083/2000000000 : ℝ)|=(630865083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1580_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1831/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24633/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4655/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4655 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4655*1^1024 ≤ 0^1024*1^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4655/1024 : ℝ) ≤ (1552405369998442621/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4655 ≤ (1552405369998442621/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4655*100000000000000000000^1024 ≤ 1552405369998442621^1024*5^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1552405369998442621 100000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1552405369998442621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4655 := by
      have hnat : (1 : ℕ)^1024*1^4655 ≤ 1^4655*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101552405369998442621/100000000000000000000 : ℝ) ≤ (5016972353554497/5000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (101552405369998442621/100000000000000000000 : ℝ)^1024 ≤ (5016972353554497/5000000000000000 : ℝ)^4655 := by
      have hnat : (101552405369998442621 : ℕ)^1024*5000000000000000^4655 ≤ 5016972353554497^4655*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101552405369998442621 100000000000000000000 5016972353554497 5000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016972353554497/5000000000000000 : ℝ)) (X := (101552405369998442621/100000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51552405369998442621/50000000000000000000 : ℝ) ≤ (2516972353554497/2500000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (51552405369998442621/50000000000000000000 : ℝ)^1024 ≤ (2516972353554497/2500000000000000 : ℝ)^4655 := by
      have hnat : (51552405369998442621 : ℕ)^1024*2500000000000000^4655 ≤ 2516972353554497^4655*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51552405369998442621 50000000000000000000 2516972353554497 2500000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516972353554497/2500000000000000 : ℝ)) (X := (51552405369998442621/50000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(16972353554497/2000000000000000 : ℝ)*(0 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16972353554497/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1552405369998442621/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(16972353554497/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4655/1024 : ℝ) := by
    rw [show (1 : ℝ)+(16972353554497/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5016972353554497/5000000000000000 : ℝ) by norm_num, show 1+(1552405369998442621/100000000000000000000 : ℝ)+(0 : ℝ)=(101552405369998442621/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1552405369998442621/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(16972353554497/2000000000000000 : ℝ)*(2/5 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16972353554497/2000000000000000 : ℝ)*(2/5 : ℝ)=(2516972353554497/2500000000000000 : ℝ) by norm_num, show 1+2*(1552405369998442621/100000000000000000000 : ℝ)=(51552405369998442621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(16972353554497/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16972353554497/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(16972353554497/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16972353554497/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(16972353554497/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16972353554497/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404006557/2500000000 : ℝ)*X 0 0+(366397261/625000000 : ℝ)*X 0 1+(4883340407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1092669867/2000000000 : ℝ)*X 1 0+(-2160175937/10000000000 : ℝ)*X 1 1+(39066723/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2731674701/5000000000 : ℝ)*X 2 0+(4883340283/10000000000 : ℝ)*X 2 1+(-1080087983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2063639763/5000000000 : ℝ)*X 0 0+(773438623/2500000000 : ℝ)*X 0 1+(5420533771/10000000000 : ℝ)*X 0 2+(2063639763/5000000000 : ℝ)*X 1 0+(773438623/2500000000 : ℝ)*X 1 1+(5420533771/10000000000 : ℝ)*X 1 2+(2063639763/5000000000 : ℝ)*X 2 0+(773438623/2500000000 : ℝ)*X 2 1+(5420533771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-202375961/1250000000 : ℝ)*X 0 0+(4907956071/10000000000 : ℝ)*X 0 1+(5836869973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597849817/5000000000 : ℝ)*X 1 0+(-603323349/5000000000 : ℝ)*X 1 1+(729608733/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259784913/500000000 : ℝ)*X 2 0+(729608919/1250000000 : ℝ)*X 2 1+(-24132929/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4134362833/10000000000 : ℝ)*X 0 0+(5362026591/10000000000 : ℝ)*X 0 1+(630865083/2000000000 : ℝ)*X 0 2+(4134362833/10000000000 : ℝ)*X 1 0+(5362026591/10000000000 : ℝ)*X 1 1+(630865083/2000000000 : ℝ)*X 1 2+(4134362833/10000000000 : ℝ)*X 2 0+(5362026591/10000000000 : ℝ)*X 2 1+(630865083/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6333432148793462403/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58681391/100000000000000 : ℝ)*(base1) + (78467601/6250000000000 : ℝ)*(base19) + (317002027/25000000000000 : ℝ)*(base23) + (164446669/100000000000000 : ℝ)*(upper3) + (39759949/25000000000000 : ℝ)*(upper5) + (362806464387579/50000000000000 : ℝ)*(major0) + (362806464387579/50000000000000 : ℝ)*(major1) + (362806464387579/50000000000000 : ℝ)*(major2) + (255359617503649/25000000000000 : ℝ)*(sp0) + (1021441833376203/100000000000000 : ℝ)*(sp1) + (63840113803107/6250000000000 : ℝ)*(sp2) + (42978049989899/10000000000000 : ℝ)*(sp3) + (584690577/12500000000000 : ℝ)*(sp4) + (999498851/50000000000000 : ℝ)*(sp7) + (107445639394521/25000000000000 : ℝ)*(f.failure) + (51072154442891/5000000000000 : ℝ)*(f.sum) + (210476065892763/50000000000000000000000000000 : ℝ)*base65 + (719367653007237/100000000000000000000000000000 : ℝ)*base68 + (279745449607237/100000000000000000000000000000 : ℝ)*base70 + (179570555292763/100000000000000000000000000000 : ℝ)*base71 + (91394581157237/50000000000000000000000000000 : ℝ)*base74 + (615378531892763/100000000000000000000000000000 : ℝ)*base75 + (392649166607237/100000000000000000000000000000 : ℝ)*base78 + (107233639407237/100000000000000000000000000000 : ℝ)*base80 + (127258614992763/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (555009/312500000000000000000 : ℝ)*base90 + (555009/312500000000000000000 : ℝ)*base92 + (555009/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141476359717012865363109/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394492407/25000000000000 : ℝ)*(base19) + (1723243471/100000000000000 : ℝ)*(base23) + (102075451/20000000000000 : ℝ)*(base39) + (82894281/50000000000000 : ℝ)*(upper3) + (588043463/100000000000000 : ℝ)*(upper5) + (382370688527599/50000000000000 : ℝ)*(major0) + (382370688527599/50000000000000 : ℝ)*(major1) + (382370433338971/50000000000000 : ℝ)*(major2) + (1256926577/25000000000000 : ℝ)*(sp1) + (1814208043/50000000000000 : ℝ)*(sp2) + (538261804341539/50000000000000 : ℝ)*(sp4) + (538258501503571/50000000000000 : ℝ)*(sp5) + (1076518767400777/100000000000000 : ℝ)*(sp6) + (452958446414911/100000000000000 : ℝ)*(sp7) + (452958446414911/100000000000000 : ℝ)*(f.failure) + (1076524119060333/100000000000000 : ℝ)*(f.sum) + (22699906243471/10000000000000000000000000000 : ℝ)*base66 + (804047428502587/100000000000000000000000000000 : ℝ)*base67 + (885221060837297/100000000000000000000000000000 : ℝ)*base70 + (331514515302587/100000000000000000000000000000 : ℝ)*base71 + (15635621143471/10000000000000000000000000000 : ℝ)*base74 + (81594790237297/100000000000000000000000000000 : ℝ)*base76 + (302923789562703/100000000000000000000000000000 : ℝ)*base77 + (217773810762703/100000000000000000000000000000 : ℝ)*base79 + (264002181887297/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2202681/1250000000000000000000 : ℝ)*base89 + (2202681/1250000000000000000000 : ℝ)*base91 + (14702681/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1580_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1831/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24633/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1580_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1580_s1_0 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752120583/10000000000 : ℝ)*x 0 + (5529236129/10000000000 : ℝ)*x 1 + (2564346701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752120583/10000000000 : ℝ)^4657 ≤ (5361970212263/50000000000000 : ℝ)^3633 := by
    have hnat : (1752120583 : ℕ)^4657*50000000000000^3633 ≤ 5361970212263^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752120583 10000000000 5361970212263 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529236129/10000000000 : ℝ)^4657 ≤ (9357558325469/20000000000000 : ℝ)^3633 := by
    have hnat : (5529236129 : ℕ)^4657*20000000000000^3633 ≤ 9357558325469^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529236129 10000000000 9357558325469 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564346701/5000000000 : ℝ)^4657 ≤ (8497653587873/20000000000000 : ℝ)^3633 := by
    have hnat : (2564346701 : ℕ)^4657*20000000000000^3633 ≤ 8497653587873^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564346701 5000000000 8497653587873 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752120583/10000000000 : ℝ), (5529236129/10000000000 : ℝ), (2564346701/5000000000 : ℝ)] ![(5361970212263/50000000000000 : ℝ), (9357558325469/20000000000000 : ℝ), (8497653587873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752120583/10000000000 : ℝ)|^4657 ≤ (5361970212263/50000000000000 : ℝ)^3633
        have hw : |(-1752120583/10000000000 : ℝ)|=(1752120583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529236129/10000000000 : ℝ)|^4657 ≤ (9357558325469/20000000000000 : ℝ)^3633
        have hw : |(5529236129/10000000000 : ℝ)|=(5529236129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564346701/5000000000 : ℝ)|^4657 ≤ (8497653587873/20000000000000 : ℝ)^3633
        have hw : |(2564346701/5000000000 : ℝ)|=(2564346701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_1 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687380433/5000000000 : ℝ)*x 0 + (-490353731/2500000000 : ℝ)*x 1 + (1025738609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687380433/5000000000 : ℝ)^4657 ≤ (22559422880773/50000000000000 : ℝ)^3633 := by
    have hnat : (2687380433 : ℕ)^4657*50000000000000^3633 ≤ 22559422880773^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687380433 5000000000 22559422880773 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490353731/2500000000 : ℝ)^4657 ≤ (12392890077409/100000000000000 : ℝ)^3633 := by
    have hnat : (490353731 : ℕ)^4657*100000000000000^3633 ≤ 12392890077409^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490353731 2500000000 12392890077409 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025738609/2000000000 : ℝ)^4657 ≤ (10622066037053/25000000000000 : ℝ)^3633 := by
    have hnat : (1025738609 : ℕ)^4657*25000000000000^3633 ≤ 10622066037053^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025738609 2000000000 10622066037053 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687380433/5000000000 : ℝ), (-490353731/2500000000 : ℝ), (1025738609/2000000000 : ℝ)] ![(22559422880773/50000000000000 : ℝ), (12392890077409/100000000000000 : ℝ), (10622066037053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687380433/5000000000 : ℝ)|^4657 ≤ (22559422880773/50000000000000 : ℝ)^3633
        have hw : |(2687380433/5000000000 : ℝ)|=(2687380433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490353731/2500000000 : ℝ)|^4657 ≤ (12392890077409/100000000000000 : ℝ)^3633
        have hw : |(-490353731/2500000000 : ℝ)|=(490353731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025738609/2000000000 : ℝ)|^4657 ≤ (10622066037053/25000000000000 : ℝ)^3633
        have hw : |(1025738609/2000000000 : ℝ)|=(1025738609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_2 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374760597/10000000000 : ℝ)*x 0 + (51286933/100000000 : ℝ)*x 1 + (-1961414947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374760597/10000000000 : ℝ)^4657 ≤ (45118842866923/100000000000000 : ℝ)^3633 := by
    have hnat : (5374760597 : ℕ)^4657*100000000000000^3633 ≤ 45118842866923^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374760597 10000000000 45118842866923 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51286933/100000000 : ℝ)^4657 ≤ (21244133428089/50000000000000 : ℝ)^3633 := by
    have hnat : (51286933 : ℕ)^4657*50000000000000^3633 ≤ 21244133428089^3633*100000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51286933 100000000 21244133428089 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961414947/10000000000 : ℝ)^4657 ≤ (3098222565923/25000000000000 : ℝ)^3633 := by
    have hnat : (1961414947 : ℕ)^4657*25000000000000^3633 ≤ 3098222565923^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961414947 10000000000 3098222565923 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374760597/10000000000 : ℝ), (51286933/100000000 : ℝ), (-1961414947/10000000000 : ℝ)] ![(45118842866923/100000000000000 : ℝ), (21244133428089/50000000000000 : ℝ), (3098222565923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374760597/10000000000 : ℝ)|^4657 ≤ (45118842866923/100000000000000 : ℝ)^3633
        have hw : |(5374760597/10000000000 : ℝ)|=(5374760597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51286933/100000000 : ℝ)|^4657 ≤ (21244133428089/50000000000000 : ℝ)^3633
        have hw : |(51286933/100000000 : ℝ)|=(51286933/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961414947/10000000000 : ℝ)|^4657 ≤ (3098222565923/25000000000000 : ℝ)^3633
        have hw : |(-1961414947/10000000000 : ℝ)|=(1961414947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_3 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224822173/10000000000 : ℝ)*x 0 + (1885146377/5000000000 : ℝ)*x 1 + (4722244097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224822173/10000000000 : ℝ)^4657 ≤ (33138933616533/100000000000000 : ℝ)^3633 := by
    have hnat : (4224822173 : ℕ)^4657*100000000000000^3633 ≤ 33138933616533^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224822173 10000000000 33138933616533 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1885146377/5000000000 : ℝ)^4657 ≤ (28639923006233/100000000000000 : ℝ)^3633 := by
    have hnat : (1885146377 : ℕ)^4657*100000000000000^3633 ≤ 28639923006233^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885146377 5000000000 28639923006233 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4722244097/10000000000 : ℝ)^4657 ≤ (38221143360759/100000000000000 : ℝ)^3633 := by
    have hnat : (4722244097 : ℕ)^4657*100000000000000^3633 ≤ 38221143360759^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722244097 10000000000 38221143360759 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224822173/10000000000 : ℝ), (1885146377/5000000000 : ℝ), (4722244097/10000000000 : ℝ)] ![(33138933616533/100000000000000 : ℝ), (28639923006233/100000000000000 : ℝ), (38221143360759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224822173/10000000000 : ℝ)|^4657 ≤ (33138933616533/100000000000000 : ℝ)^3633
        have hw : |(4224822173/10000000000 : ℝ)|=(4224822173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1885146377/5000000000 : ℝ)|^4657 ≤ (28639923006233/100000000000000 : ℝ)^3633
        have hw : |(1885146377/5000000000 : ℝ)|=(1885146377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4722244097/10000000000 : ℝ)|^4657 ≤ (38221143360759/100000000000000 : ℝ)^3633
        have hw : |(4722244097/10000000000 : ℝ)|=(4722244097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_4 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219039937/1250000000 : ℝ)*x 0 + (5132769873/10000000000 : ℝ)*x 1 + (5525100391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219039937/1250000000 : ℝ)^4657 ≤ (10725501059577/100000000000000 : ℝ)^3633 := by
    have hnat : (219039937 : ℕ)^4657*100000000000000^3633 ≤ 10725501059577^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219039937 1250000000 10725501059577 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132769873/10000000000 : ℝ)^4657 ≤ (4253156277779/10000000000000 : ℝ)^3633 := by
    have hnat : (5132769873 : ℕ)^4657*10000000000000^3633 ≤ 4253156277779^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132769873 10000000000 4253156277779 10000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525100391/10000000000 : ℝ)^4657 ≤ (91294797169/195312500000 : ℝ)^3633 := by
    have hnat : (5525100391 : ℕ)^4657*195312500000^3633 ≤ 91294797169^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525100391 10000000000 91294797169 195312500000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219039937/1250000000 : ℝ), (5132769873/10000000000 : ℝ), (5525100391/10000000000 : ℝ)] ![(10725501059577/100000000000000 : ℝ), (4253156277779/10000000000000 : ℝ), (91294797169/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219039937/1250000000 : ℝ)|^4657 ≤ (10725501059577/100000000000000 : ℝ)^3633
        have hw : |(-219039937/1250000000 : ℝ)|=(219039937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132769873/10000000000 : ℝ)|^4657 ≤ (4253156277779/10000000000000 : ℝ)^3633
        have hw : |(5132769873/10000000000 : ℝ)|=(5132769873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525100391/10000000000 : ℝ)|^4657 ≤ (91294797169/195312500000 : ℝ)^3633
        have hw : |(5525100391/10000000000 : ℝ)|=(5525100391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_5 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268486227/10000000000 : ℝ)*x 0 + (-782503811/5000000000 : ℝ)*x 1 + (1381275259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268486227/10000000000 : ℝ)^4657 ≤ (10994615106517/25000000000000 : ℝ)^3633 := by
    have hnat : (5268486227 : ℕ)^4657*25000000000000^3633 ≤ 10994615106517^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268486227 10000000000 10994615106517 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782503811/5000000000 : ℝ)^4657 ≤ (9278596410519/100000000000000 : ℝ)^3633 := by
    have hnat : (782503811 : ℕ)^4657*100000000000000^3633 ≤ 9278596410519^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782503811 5000000000 9278596410519 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381275259/2500000000 : ℝ)^4657 ≤ (23371471572673/50000000000000 : ℝ)^3633 := by
    have hnat : (1381275259 : ℕ)^4657*50000000000000^3633 ≤ 23371471572673^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381275259 2500000000 23371471572673 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268486227/10000000000 : ℝ), (-782503811/5000000000 : ℝ), (1381275259/2500000000 : ℝ)] ![(10994615106517/25000000000000 : ℝ), (9278596410519/100000000000000 : ℝ), (23371471572673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268486227/10000000000 : ℝ)|^4657 ≤ (10994615106517/25000000000000 : ℝ)^3633
        have hw : |(5268486227/10000000000 : ℝ)|=(5268486227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782503811/5000000000 : ℝ)|^4657 ≤ (9278596410519/100000000000000 : ℝ)^3633
        have hw : |(-782503811/5000000000 : ℝ)|=(782503811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381275259/2500000000 : ℝ)|^4657 ≤ (23371471572673/50000000000000 : ℝ)^3633
        have hw : |(1381275259/2500000000 : ℝ)|=(1381275259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_6 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053697089/2000000000 : ℝ)*x 0 + (5525101341/10000000000 : ℝ)*x 1 + (-1565008289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053697089/2000000000 : ℝ)^4657 ≤ (43978452058451/100000000000000 : ℝ)^3633 := by
    have hnat : (1053697089 : ℕ)^4657*100000000000000^3633 ≤ 43978452058451^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053697089 2000000000 43978452058451 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525101341/10000000000 : ℝ)^4657 ≤ (46742946452973/100000000000000 : ℝ)^3633 := by
    have hnat : (5525101341 : ℕ)^4657*100000000000000^3633 ≤ 46742946452973^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525101341 10000000000 46742946452973 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1565008289/10000000000 : ℝ)^4657 ≤ (9278601479639/100000000000000 : ℝ)^3633 := by
    have hnat : (1565008289 : ℕ)^4657*100000000000000^3633 ≤ 9278601479639^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565008289 10000000000 9278601479639 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053697089/2000000000 : ℝ), (5525101341/10000000000 : ℝ), (-1565008289/10000000000 : ℝ)] ![(43978452058451/100000000000000 : ℝ), (46742946452973/100000000000000 : ℝ), (9278601479639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053697089/2000000000 : ℝ)|^4657 ≤ (43978452058451/100000000000000 : ℝ)^3633
        have hw : |(1053697089/2000000000 : ℝ)|=(1053697089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525101341/10000000000 : ℝ)|^4657 ≤ (46742946452973/100000000000000 : ℝ)^3633
        have hw : |(5525101341/10000000000 : ℝ)|=(5525101341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1565008289/10000000000 : ℝ)|^4657 ≤ (9278601479639/100000000000000 : ℝ)^3633
        have hw : |(-1565008289/10000000000 : ℝ)|=(1565008289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s1_7 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225294069/10000000000 : ℝ)*x 0 + (188502259/400000000 : ℝ)*x 1 + (3780121151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225294069/10000000000 : ℝ)^4657 ≤ (8285919620949/25000000000000 : ℝ)^3633 := by
    have hnat : (4225294069 : ℕ)^4657*25000000000000^3633 ≤ 8285919620949^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225294069 10000000000 8285919620949 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188502259/400000000 : ℝ)^4657 ≤ (9530165377521/25000000000000 : ℝ)^3633 := by
    have hnat : (188502259 : ℕ)^4657*25000000000000^3633 ≤ 9530165377521^3633*400000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188502259 400000000 9530165377521 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3780121151/10000000000 : ℝ)^4657 ≤ (28735659986447/100000000000000 : ℝ)^3633 := by
    have hnat : (3780121151 : ℕ)^4657*100000000000000^3633 ≤ 28735659986447^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780121151 10000000000 28735659986447 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225294069/10000000000 : ℝ), (188502259/400000000 : ℝ), (3780121151/10000000000 : ℝ)] ![(8285919620949/25000000000000 : ℝ), (9530165377521/25000000000000 : ℝ), (28735659986447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225294069/10000000000 : ℝ)|^4657 ≤ (8285919620949/25000000000000 : ℝ)^3633
        have hw : |(4225294069/10000000000 : ℝ)|=(4225294069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188502259/400000000 : ℝ)|^4657 ≤ (9530165377521/25000000000000 : ℝ)^3633
        have hw : |(188502259/400000000 : ℝ)|=(188502259/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3780121151/10000000000 : ℝ)|^4657 ≤ (28735659986447/100000000000000 : ℝ)^3633
        have hw : |(3780121151/10000000000 : ℝ)|=(3780121151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1580_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24633/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (459/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3533/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24633/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1831/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24633/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1831/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24633/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1831/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24633/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1831/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24633/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1831/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24633/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1831/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1831/50000 : ℝ) ^ (4655/1024 : ℝ) ≤ (14783574362451/50000000000000000000 : ℝ) := by
    have hpowers : (1831/50000 : ℝ)^4655 ≤ (14783574362451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1831 : ℕ)^4655*50000000000000000000^1024 ≤ 14783574362451^1024*50000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1831 50000 14783574362451 50000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1831/50000 : ℝ)) (X := (14783574362451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24633/100000 : ℝ) ^ (4655/1024 : ℝ) ≤ (171356063202733111/100000000000000000000 : ℝ) := by
    have hpowers : (24633/100000 : ℝ)^4655 ≤ (171356063202733111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24633 : ℕ)^4655*100000000000000000000^1024 ≤ 171356063202733111^1024*100000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24633 100000 171356063202733111 100000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24633/100000 : ℝ)) (X := (171356063202733111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000014783574362451/25000000000000000000 : ℝ) ≤ (1000000130082721/1000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (25000014783574362451/25000000000000000000 : ℝ)^1024 ≤ (1000000130082721/1000000000000000 : ℝ)^4655 := by
      have hnat : (25000014783574362451 : ℕ)^1024*1000000000000000^4655 ≤ 1000000130082721^4655*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000014783574362451 25000000000000000000 1000000130082721 1000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000130082721/1000000000000000 : ℝ)) (X := (25000014783574362451/25000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100171385630351458013/100000000000000000000 : ℝ) ≤ (10003767598222287/10000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (100171385630351458013/100000000000000000000 : ℝ)^1024 ≤ (10003767598222287/10000000000000000 : ℝ)^4655 := by
      have hnat : (100171385630351458013 : ℕ)^1024*10000000000000000^4655 ≤ 10003767598222287^4655*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100171385630351458013 100000000000000000000 10003767598222287 10000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003767598222287/10000000000000000 : ℝ)) (X := (100171385630351458013/100000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50171356063202733111/50000000000000000000 : ℝ) ≤ (2501883473904341/2500000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (50171356063202733111/50000000000000000000 : ℝ)^1024 ≤ (2501883473904341/2500000000000000 : ℝ)^4655 := by
      have hnat : (50171356063202733111 : ℕ)^1024*2500000000000000^4655 ≤ 2501883473904341^4655*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50171356063202733111 50000000000000000000 2501883473904341 2500000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501883473904341/2500000000000000 : ℝ)) (X := (50171356063202733111/50000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14783574362451/50000000000000000000 : ℝ) ≤ ((104841221458762938481/104855000000000000000 : ℝ)+2*(3766297395077/2097100000000000 : ℝ)*(1831/50000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (104841221458762938481/104855000000000000000 : ℝ)+2*(3766297395077/2097100000000000 : ℝ)*(1831/50000 : ℝ)=(1000000130082721/1000000000000000 : ℝ) by norm_num, show 1+2*(14783574362451/50000000000000000000 : ℝ)=(25000014783574362451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(171356063202733111/100000000000000000000 : ℝ)+(14783574362451/50000000000000000000 : ℝ) ≤ ((104841221458762938481/104855000000000000000 : ℝ)+(3766297395077/2097100000000000 : ℝ)*((24633/100000 : ℝ)+(1831/50000 : ℝ)))^(4655/1024 : ℝ) := by
    rw [show (104841221458762938481/104855000000000000000 : ℝ)+(3766297395077/2097100000000000 : ℝ)*((24633/100000 : ℝ)+(1831/50000 : ℝ))=(10003767598222287/10000000000000000 : ℝ) by norm_num, show 1+(171356063202733111/100000000000000000000 : ℝ)+(14783574362451/50000000000000000000 : ℝ)=(100171385630351458013/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(171356063202733111/100000000000000000000 : ℝ) ≤ ((104841221458762938481/104855000000000000000 : ℝ)+2*(3766297395077/2097100000000000 : ℝ)*(24633/100000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (104841221458762938481/104855000000000000000 : ℝ)+2*(3766297395077/2097100000000000 : ℝ)*(24633/100000 : ℝ)=(2501883473904341/2500000000000000 : ℝ) by norm_num, show 1+2*(171356063202733111/100000000000000000000 : ℝ)=(50171356063202733111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104841221458762938481/104855000000000000000 : ℝ)*(X 1 0+X 2 0)+(3766297395077/2097100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (1831/50000 : ℝ)) (hi := (24633/100000 : ℝ)) (c := (104841221458762938481/104855000000000000000 : ℝ)) (alpha := (3766297395077/2097100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104841221458762938481/104855000000000000000 : ℝ)*(X 0 1+X 2 1)+(3766297395077/2097100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (1831/50000 : ℝ)) (hi := (24633/100000 : ℝ)) (c := (104841221458762938481/104855000000000000000 : ℝ)) (alpha := (3766297395077/2097100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104841221458762938481/104855000000000000000 : ℝ)*(X 0 2+X 1 2)+(3766297395077/2097100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (1831/50000 : ℝ)) (hi := (24633/100000 : ℝ)) (c := (104841221458762938481/104855000000000000000 : ℝ)) (alpha := (3766297395077/2097100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1752120583/10000000000 : ℝ)*X 0 0+(5529236129/10000000000 : ℝ)*X 0 1+(2564346701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687380433/5000000000 : ℝ)*X 1 0+(-490353731/2500000000 : ℝ)*X 1 1+(1025738609/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374760597/10000000000 : ℝ)*X 2 0+(51286933/100000000 : ℝ)*X 2 1+(-1961414947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4224822173/10000000000 : ℝ)*X 0 0+(1885146377/5000000000 : ℝ)*X 0 1+(4722244097/10000000000 : ℝ)*X 0 2+(4224822173/10000000000 : ℝ)*X 1 0+(1885146377/5000000000 : ℝ)*X 1 1+(4722244097/10000000000 : ℝ)*X 1 2+(4224822173/10000000000 : ℝ)*X 2 0+(1885146377/5000000000 : ℝ)*X 2 1+(4722244097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219039937/1250000000 : ℝ)*X 0 0+(5132769873/10000000000 : ℝ)*X 0 1+(5525100391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268486227/10000000000 : ℝ)*X 1 0+(-782503811/5000000000 : ℝ)*X 1 1+(1381275259/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053697089/2000000000 : ℝ)*X 2 0+(5525101341/10000000000 : ℝ)*X 2 1+(-1565008289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4225294069/10000000000 : ℝ)*X 0 0+(188502259/400000000 : ℝ)*X 0 1+(3780121151/10000000000 : ℝ)*X 0 2+(4225294069/10000000000 : ℝ)*X 1 0+(188502259/400000000 : ℝ)*X 1 1+(3780121151/10000000000 : ℝ)*X 1 2+(4225294069/10000000000 : ℝ)*X 2 0+(188502259/400000000 : ℝ)*X 2 1+(3780121151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8090536270360168325465468457/2621375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83851269/6250000000000 : ℝ)*(base19) + (138330957/12500000000000 : ℝ)*(base23) + (145325661/100000000000000 : ℝ)*(upper3) + (14783181/25000000000000 : ℝ)*(upper4) + (28481151/100000000000000 : ℝ)*(upper5) + (886779913622567/50000000000000 : ℝ)*(major0) + (886779913622567/50000000000000 : ℝ)*(major1) + (886779913622567/50000000000000 : ℝ)*(major2) + (2496624556747073/100000000000000 : ℝ)*(sp0) + (2496633787314163/100000000000000 : ℝ)*(sp1) + (624158505571703/25000000000000 : ℝ)*(sp2) + (1050478740662779/100000000000000 : ℝ)*(sp3) + (5286093697/50000000000000 : ℝ)*(sp4) + (1420503493/25000000000000 : ℝ)*(sp7) + (1050484422676751/100000000000000 : ℝ)*(f.failure) + (2496635128934467/100000000000000 : ℝ)*(f.sum) + (275318864726929/52427500000000000000000000000 : ℝ)*base65 + (25453157069833500727/5242750000000000000000000000000000 : ℝ)*base67 + (12393376172686000727/5242750000000000000000000000000000 : ℝ)*base69 + (64288709481306500727/5242750000000000000000000000000000 : ℝ)*base71 + (49079710215963/26213750000000000000000000000 : ℝ)*base74 + (39574345732714750727/5242750000000000000000000000000000 : ℝ)*base75 + (30575721461450000727/5242750000000000000000000000000000 : ℝ)*base77 + (30682390101685750727/5242750000000000000000000000000000 : ℝ)*base79 + (115769745435887/104855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11846679/1250000000000000000000 : ℝ)*base90 + (11846679/1250000000000000000000 : ℝ)*base92 + (11846679/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3557286747925864491237/782500000000000000000000000 : ℝ) := by norm_num
    linear_combination (155051123/20000000000000 : ℝ)*(base19) + (654469963/100000000000000 : ℝ)*(base23) + (14352833/10000000000000 : ℝ)*(upper2) + (235287553/100000000000000 : ℝ)*(upper3) + (23393961/50000000000000 : ℝ)*(upper5) + (1810663027782261/100000000000000 : ℝ)*(major0) + (1810663027782261/100000000000000 : ℝ)*(major1) + (1810663027782261/100000000000000 : ℝ)*(major2) + (108802559/1562500000000 : ℝ)*(sp1) + (6225351443/100000000000000 : ℝ)*(sp2) + (2548865152391569/100000000000000 : ℝ)*(sp4) + (1274428706886089/50000000000000 : ℝ)*(sp5) + (2548858272570163/100000000000000 : ℝ)*(sp6) + (268115187909459/25000000000000 : ℝ)*(sp7) + (268115187909459/25000000000000 : ℝ)*(f.failure) + (2548865152391569/100000000000000 : ℝ)*(f.sum) + (2273618275809/1565000000000000000000000000 : ℝ)*base66 + (750214506911902023/156500000000000000000000000000000 : ℝ)*base67 + (876537869995097977/156500000000000000000000000000000 : ℝ)*base70 + (155970192813402023/156500000000000000000000000000000 : ℝ)*base71 + (2220077904309/1565000000000000000000000000 : ℝ)*base74 + (351466417863597977/156500000000000000000000000000000 : ℝ)*base76 + (774373257582597977/156500000000000000000000000000000 : ℝ)*base78 + (1109394566662902023/156500000000000000000000000000000 : ℝ)*base79 + (4771521267429/1565000000000000000000000000 : ℝ)*base82 + (1317411/312500000000000000000 : ℝ)*base90 + (1317411/312500000000000000000 : ℝ)*base92 + (1317411/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1580_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24633/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1580_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1580_s2_0 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442459577/2500000000 : ℝ)*x 0 + (1359744471/2500000000 : ℝ)*x 1 + (5207394137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442459577/2500000000 : ℝ)^4657 ≤ (10863145857441/100000000000000 : ℝ)^3633 := by
    have hnat : (442459577 : ℕ)^4657*100000000000000^3633 ≤ 10863145857441^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442459577 2500000000 10863145857441 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359744471/2500000000 : ℝ)^4657 ≤ (9162204943193/20000000000000 : ℝ)^3633 := by
    have hnat : (1359744471 : ℕ)^4657*20000000000000^3633 ≤ 9162204943193^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359744471 2500000000 9162204943193 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207394137/10000000000 : ℝ)^4657 ≤ (338483042257/781250000000 : ℝ)^3633 := by
    have hnat : (5207394137 : ℕ)^4657*781250000000^3633 ≤ 338483042257^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207394137 10000000000 338483042257 781250000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442459577/2500000000 : ℝ), (1359744471/2500000000 : ℝ), (5207394137/10000000000 : ℝ)] ![(10863145857441/100000000000000 : ℝ), (9162204943193/20000000000000 : ℝ), (338483042257/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442459577/2500000000 : ℝ)|^4657 ≤ (10863145857441/100000000000000 : ℝ)^3633
        have hw : |(-442459577/2500000000 : ℝ)|=(442459577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359744471/2500000000 : ℝ)|^4657 ≤ (9162204943193/20000000000000 : ℝ)^3633
        have hw : |(1359744471/2500000000 : ℝ)|=(1359744471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207394137/10000000000 : ℝ)|^4657 ≤ (338483042257/781250000000 : ℝ)^3633
        have hw : |(5207394137/10000000000 : ℝ)|=(5207394137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_1 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351390111/10000000000 : ℝ)*x 0 + (-1888648513/10000000000 : ℝ)*x 1 + (2603697477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351390111/10000000000 : ℝ)^4657 ≤ (560843935507/1250000000000 : ℝ)^3633 := by
    have hnat : (5351390111 : ℕ)^4657*1250000000000^3633 ≤ 560843935507^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351390111 10000000000 560843935507 1250000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888648513/10000000000 : ℝ)^4657 ≤ (11806647025391/100000000000000 : ℝ)^3633 := by
    have hnat : (1888648513 : ℕ)^4657*100000000000000^3633 ≤ 11806647025391^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888648513 10000000000 11806647025391 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603697477/5000000000 : ℝ)^4657 ≤ (4332583812233/10000000000000 : ℝ)^3633 := by
    have hnat : (2603697477 : ℕ)^4657*10000000000000^3633 ≤ 4332583812233^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603697477 5000000000 4332583812233 10000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351390111/10000000000 : ℝ), (-1888648513/10000000000 : ℝ), (2603697477/5000000000 : ℝ)] ![(560843935507/1250000000000 : ℝ), (11806647025391/100000000000000 : ℝ), (4332583812233/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351390111/10000000000 : ℝ)|^4657 ≤ (560843935507/1250000000000 : ℝ)^3633
        have hw : |(5351390111/10000000000 : ℝ)|=(5351390111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888648513/10000000000 : ℝ)|^4657 ≤ (11806647025391/100000000000000 : ℝ)^3633
        have hw : |(-1888648513/10000000000 : ℝ)|=(1888648513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603697477/5000000000 : ℝ)|^4657 ≤ (4332583812233/10000000000000 : ℝ)^3633
        have hw : |(2603697477/5000000000 : ℝ)|=(2603697477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_2 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351390559/10000000000 : ℝ)*x 0 + (104147883/200000000 : ℝ)*x 1 + (-944324491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351390559/10000000000 : ℝ)^4657 ≤ (44867519655427/100000000000000 : ℝ)^3633 := by
    have hnat : (5351390559 : ℕ)^4657*100000000000000^3633 ≤ 44867519655427^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351390559 10000000000 44867519655427 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104147883/200000000 : ℝ)^4657 ≤ (43325829547543/100000000000000 : ℝ)^3633 := by
    have hnat : (104147883 : ℕ)^4657*100000000000000^3633 ≤ 43325829547543^3633*200000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104147883 200000000 43325829547543 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944324491/5000000000 : ℝ)^4657 ≤ (11806650783671/100000000000000 : ℝ)^3633 := by
    have hnat : (944324491 : ℕ)^4657*100000000000000^3633 ≤ 11806650783671^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944324491 5000000000 11806650783671 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351390559/10000000000 : ℝ), (104147883/200000000 : ℝ), (-944324491/5000000000 : ℝ)] ![(44867519655427/100000000000000 : ℝ), (43325829547543/100000000000000 : ℝ), (11806650783671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351390559/10000000000 : ℝ)|^4657 ≤ (44867519655427/100000000000000 : ℝ)^3633
        have hw : |(5351390559/10000000000 : ℝ)|=(5351390559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104147883/200000000 : ℝ)|^4657 ≤ (43325829547543/100000000000000 : ℝ)^3633
        have hw : |(104147883/200000000 : ℝ)|=(104147883/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944324491/5000000000 : ℝ)|^4657 ≤ (11806650783671/100000000000000 : ℝ)^3633
        have hw : |(-944324491/5000000000 : ℝ)|=(944324491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_3 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237681893/10000000000 : ℝ)*x 0 + (793932469/2000000000 : ℝ)*x 1 + (141251713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237681893/10000000000 : ℝ)^4657 ≤ (1039634069081/3125000000000 : ℝ)^3633 := by
    have hnat : (4237681893 : ℕ)^4657*3125000000000^3633 ≤ 1039634069081^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237681893 10000000000 1039634069081 3125000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793932469/2000000000 : ℝ)^4657 ≤ (3824441057859/12500000000000 : ℝ)^3633 := by
    have hnat : (793932469 : ℕ)^4657*12500000000000^3633 ≤ 3824441057859^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793932469 2000000000 3824441057859 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141251713/312500000 : ℝ)^4657 ≤ (36136181319581/100000000000000 : ℝ)^3633 := by
    have hnat : (141251713 : ℕ)^4657*100000000000000^3633 ≤ 36136181319581^3633*312500000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141251713 312500000 36136181319581 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237681893/10000000000 : ℝ), (793932469/2000000000 : ℝ), (141251713/312500000 : ℝ)] ![(1039634069081/3125000000000 : ℝ), (3824441057859/12500000000000 : ℝ), (36136181319581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237681893/10000000000 : ℝ)|^4657 ≤ (1039634069081/3125000000000 : ℝ)^3633
        have hw : |(4237681893/10000000000 : ℝ)|=(4237681893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(793932469/2000000000 : ℝ)|^4657 ≤ (3824441057859/12500000000000 : ℝ)^3633
        have hw : |(793932469/2000000000 : ℝ)|=(793932469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141251713/312500000 : ℝ)|^4657 ≤ (36136181319581/100000000000000 : ℝ)^3633
        have hw : |(141251713/312500000 : ℝ)|=(141251713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_4 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769876197/10000000000 : ℝ)*x 0 + (1302191299/2500000000 : ℝ)*x 1 + (5437595827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769876197/10000000000 : ℝ)^4657 ≤ (339482623999/3125000000000 : ℝ)^3633 := by
    have hnat : (1769876197 : ℕ)^4657*3125000000000^3633 ≤ 339482623999^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769876197 10000000000 339482623999 3125000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302191299/2500000000 : ℝ)^4657 ≤ (2708778281981/6250000000000 : ℝ)^3633 := by
    have hnat : (1302191299 : ℕ)^4657*6250000000000^3633 ≤ 2708778281981^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302191299 2500000000 2708778281981 6250000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437595827/10000000000 : ℝ)^4657 ≤ (22898051754491/50000000000000 : ℝ)^3633 := by
    have hnat : (5437595827 : ℕ)^4657*50000000000000^3633 ≤ 22898051754491^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437595827 10000000000 22898051754491 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769876197/10000000000 : ℝ), (1302191299/2500000000 : ℝ), (5437595827/10000000000 : ℝ)] ![(339482623999/3125000000000 : ℝ), (2708778281981/6250000000000 : ℝ), (22898051754491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769876197/10000000000 : ℝ)|^4657 ≤ (339482623999/3125000000000 : ℝ)^3633
        have hw : |(-1769876197/10000000000 : ℝ)|=(1769876197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302191299/2500000000 : ℝ)|^4657 ≤ (2708778281981/6250000000000 : ℝ)^3633
        have hw : |(1302191299/2500000000 : ℝ)|=(1302191299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437595827/10000000000 : ℝ)|^4657 ≤ (22898051754491/50000000000000 : ℝ)^3633
        have hw : |(5437595827/10000000000 : ℝ)|=(5437595827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_5 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290043453/10000000000 : ℝ)*x 0 + (-331689589/2000000000 : ℝ)*x 1 + (5437596871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290043453/10000000000 : ℝ)^4657 ≤ (44209261596113/100000000000000 : ℝ)^3633 := by
    have hnat : (5290043453 : ℕ)^4657*100000000000000^3633 ≤ 44209261596113^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290043453 10000000000 44209261596113 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331689589/2000000000 : ℝ)^4657 ≤ (399784944533/4000000000000 : ℝ)^3633 := by
    have hnat : (331689589 : ℕ)^4657*4000000000000^3633 ≤ 399784944533^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331689589 2000000000 399784944533 4000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437596871/10000000000 : ℝ)^4657 ≤ (9159222955999/20000000000000 : ℝ)^3633 := by
    have hnat : (5437596871 : ℕ)^4657*20000000000000^3633 ≤ 9159222955999^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437596871 10000000000 9159222955999 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290043453/10000000000 : ℝ), (-331689589/2000000000 : ℝ), (5437596871/10000000000 : ℝ)] ![(44209261596113/100000000000000 : ℝ), (399784944533/4000000000000 : ℝ), (9159222955999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290043453/10000000000 : ℝ)|^4657 ≤ (44209261596113/100000000000000 : ℝ)^3633
        have hw : |(5290043453/10000000000 : ℝ)|=(5290043453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331689589/2000000000 : ℝ)|^4657 ≤ (399784944533/4000000000000 : ℝ)^3633
        have hw : |(-331689589/2000000000 : ℝ)|=(331689589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437596871/10000000000 : ℝ)|^4657 ≤ (9159222955999/20000000000000 : ℝ)^3633
        have hw : |(5437596871/10000000000 : ℝ)|=(5437596871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_6 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322510991/2500000000 : ℝ)*x 0 + (5437598033/10000000000 : ℝ)*x 1 + (-414611403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322510991/2500000000 : ℝ)^4657 ≤ (44209267070251/100000000000000 : ℝ)^3633 := by
    have hnat : (1322510991 : ℕ)^4657*100000000000000^3633 ≤ 44209267070251^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322510991 2500000000 44209267070251 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437598033/10000000000 : ℝ)^4657 ≤ (5724515915617/12500000000000 : ℝ)^3633 := by
    have hnat : (5437598033 : ℕ)^4657*12500000000000^3633 ≤ 5724515915617^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437598033 10000000000 5724515915617 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414611403/2500000000 : ℝ)^4657 ≤ (1998921118123/20000000000000 : ℝ)^3633 := by
    have hnat : (414611403 : ℕ)^4657*20000000000000^3633 ≤ 1998921118123^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414611403 2500000000 1998921118123 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322510991/2500000000 : ℝ), (5437598033/10000000000 : ℝ), (-414611403/2500000000 : ℝ)] ![(44209267070251/100000000000000 : ℝ), (5724515915617/12500000000000 : ℝ), (1998921118123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322510991/2500000000 : ℝ)|^4657 ≤ (44209267070251/100000000000000 : ℝ)^3633
        have hw : |(1322510991/2500000000 : ℝ)|=(1322510991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437598033/10000000000 : ℝ)|^4657 ≤ (5724515915617/12500000000000 : ℝ)^3633
        have hw : |(5437598033/10000000000 : ℝ)|=(5437598033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414611403/2500000000 : ℝ)|^4657 ≤ (1998921118123/20000000000000 : ℝ)^3633
        have hw : |(-414611403/2500000000 : ℝ)|=(414611403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_s2_7 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118887149/5000000000 : ℝ)*x 0 + (2258398911/5000000000 : ℝ)*x 1 + (496618237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118887149/5000000000 : ℝ)^4657 ≤ (259915782173/781250000000 : ℝ)^3633 := by
    have hnat : (2118887149 : ℕ)^4657*781250000000^3633 ≤ 259915782173^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118887149 5000000000 259915782173 781250000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258398911/5000000000 : ℝ)^4657 ≤ (36102807013747/100000000000000 : ℝ)^3633 := by
    have hnat : (2258398911 : ℕ)^4657*100000000000000^3633 ≤ 36102807013747^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258398911 5000000000 36102807013747 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496618237/1250000000 : ℝ)^4657 ≤ (30627972852713/100000000000000 : ℝ)^3633 := by
    have hnat : (496618237 : ℕ)^4657*100000000000000^3633 ≤ 30627972852713^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496618237 1250000000 30627972852713 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118887149/5000000000 : ℝ), (2258398911/5000000000 : ℝ), (496618237/1250000000 : ℝ)] ![(259915782173/781250000000 : ℝ), (36102807013747/100000000000000 : ℝ), (30627972852713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118887149/5000000000 : ℝ)|^4657 ≤ (259915782173/781250000000 : ℝ)^3633
        have hw : |(2118887149/5000000000 : ℝ)|=(2118887149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258398911/5000000000 : ℝ)|^4657 ≤ (36102807013747/100000000000000 : ℝ)^3633
        have hw : |(2258398911/5000000000 : ℝ)|=(2258398911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496618237/1250000000 : ℝ)|^4657 ≤ (30627972852713/100000000000000 : ℝ)^3633
        have hw : |(496618237/1250000000 : ℝ)|=(496618237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1580_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (87/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7893/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3533/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3533/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3533/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3533/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3533/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3533/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (459/5000 : ℝ) ^ (4655/1024 : ℝ) ≤ (38567204502687/2000000000000000000 : ℝ) := by
    have hpowers : (459/5000 : ℝ)^4655 ≤ (38567204502687/2000000000000000000 : ℝ)^1024 := by
      have hnat : (459 : ℕ)^4655*2000000000000000000^1024 ≤ 38567204502687^1024*5000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 5000 38567204502687 2000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/5000 : ℝ)) (X := (38567204502687/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3533/20000 : ℝ) ^ (4655/1024 : ℝ) ≤ (37796804168807327/100000000000000000000 : ℝ) := by
    have hpowers : (3533/20000 : ℝ)^4655 ≤ (37796804168807327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3533 : ℕ)^4655*100000000000000000000^1024 ≤ 37796804168807327^1024*20000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3533 20000 37796804168807327 100000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3533/20000 : ℝ)) (X := (37796804168807327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000038567204502687/1000000000000000000 : ℝ) ≤ (10000084838288697/10000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (1000038567204502687/1000000000000000000 : ℝ)^1024 ≤ (10000084838288697/10000000000000000 : ℝ)^4655 := by
      have hnat : (1000038567204502687 : ℕ)^1024*10000000000000000^4655 ≤ 10000084838288697^4655*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000038567204502687 1000000000000000000 10000084838288697 10000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084838288697/10000000000000000 : ℝ)) (X := (1000038567204502687/1000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039725164393941677/100000000000000000000 : ℝ) ≤ (2000174746583871/2000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (100039725164393941677/100000000000000000000 : ℝ)^1024 ≤ (2000174746583871/2000000000000000 : ℝ)^4655 := by
      have hnat : (100039725164393941677 : ℕ)^1024*2000000000000000^4655 ≤ 2000174746583871^4655*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039725164393941677 100000000000000000000 2000174746583871 2000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000174746583871/2000000000000000 : ℝ)) (X := (100039725164393941677/100000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037796804168807327/50000000000000000000 : ℝ) ≤ (10001662627550013/10000000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (50037796804168807327/50000000000000000000 : ℝ)^1024 ≤ (10001662627550013/10000000000000000 : ℝ)^4655 := by
      have hnat : (50037796804168807327 : ℕ)^1024*10000000000000000^4655 ≤ 10001662627550013^4655*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037796804168807327 50000000000000000000 10001662627550013 10000000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001662627550013/10000000000000000 : ℝ)) (X := (50037796804168807327/50000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(38567204502687/2000000000000000000 : ℝ) ≤ ((16967247149492142633/16970000000000000000 : ℝ)+2*(394447315329/424250000000000 : ℝ)*(459/5000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (16967247149492142633/16970000000000000000 : ℝ)+2*(394447315329/424250000000000 : ℝ)*(459/5000 : ℝ)=(10000084838288697/10000000000000000 : ℝ) by norm_num, show 1+2*(38567204502687/2000000000000000000 : ℝ)=(1000038567204502687/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37796804168807327/100000000000000000000 : ℝ)+(38567204502687/2000000000000000000 : ℝ) ≤ ((16967247149492142633/16970000000000000000 : ℝ)+(394447315329/424250000000000 : ℝ)*((3533/20000 : ℝ)+(459/5000 : ℝ)))^(4655/1024 : ℝ) := by
    rw [show (16967247149492142633/16970000000000000000 : ℝ)+(394447315329/424250000000000 : ℝ)*((3533/20000 : ℝ)+(459/5000 : ℝ))=(2000174746583871/2000000000000000 : ℝ) by norm_num, show 1+(37796804168807327/100000000000000000000 : ℝ)+(38567204502687/2000000000000000000 : ℝ)=(100039725164393941677/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37796804168807327/100000000000000000000 : ℝ) ≤ ((16967247149492142633/16970000000000000000 : ℝ)+2*(394447315329/424250000000000 : ℝ)*(3533/20000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (16967247149492142633/16970000000000000000 : ℝ)+2*(394447315329/424250000000000 : ℝ)*(3533/20000 : ℝ)=(10001662627550013/10000000000000000 : ℝ) by norm_num, show 1+2*(37796804168807327/100000000000000000000 : ℝ)=(50037796804168807327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16967247149492142633/16970000000000000000 : ℝ)*(X 1 0+X 2 0)+(394447315329/424250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (459/5000 : ℝ)) (hi := (3533/20000 : ℝ)) (c := (16967247149492142633/16970000000000000000 : ℝ)) (alpha := (394447315329/424250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16967247149492142633/16970000000000000000 : ℝ)*(X 0 1+X 2 1)+(394447315329/424250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (459/5000 : ℝ)) (hi := (3533/20000 : ℝ)) (c := (16967247149492142633/16970000000000000000 : ℝ)) (alpha := (394447315329/424250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16967247149492142633/16970000000000000000 : ℝ)*(X 0 2+X 1 2)+(394447315329/424250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (459/5000 : ℝ)) (hi := (3533/20000 : ℝ)) (c := (16967247149492142633/16970000000000000000 : ℝ)) (alpha := (394447315329/424250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442459577/2500000000 : ℝ)*X 0 0+(1359744471/2500000000 : ℝ)*X 0 1+(5207394137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351390111/10000000000 : ℝ)*X 1 0+(-1888648513/10000000000 : ℝ)*X 1 1+(2603697477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351390559/10000000000 : ℝ)*X 2 0+(104147883/200000000 : ℝ)*X 2 1+(-944324491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237681893/10000000000 : ℝ)*X 0 0+(793932469/2000000000 : ℝ)*X 0 1+(141251713/312500000 : ℝ)*X 0 2+(4237681893/10000000000 : ℝ)*X 1 0+(793932469/2000000000 : ℝ)*X 1 1+(141251713/312500000 : ℝ)*X 1 2+(4237681893/10000000000 : ℝ)*X 2 0+(793932469/2000000000 : ℝ)*X 2 1+(141251713/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1769876197/10000000000 : ℝ)*X 0 0+(1302191299/2500000000 : ℝ)*X 0 1+(5437595827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290043453/10000000000 : ℝ)*X 1 0+(-331689589/2000000000 : ℝ)*X 1 1+(5437596871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322510991/2500000000 : ℝ)*X 2 0+(5437598033/10000000000 : ℝ)*X 2 1+(-414611403/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118887149/5000000000 : ℝ)*X 0 0+(2258398911/5000000000 : ℝ)*X 0 1+(496618237/1250000000 : ℝ)*X 0 2+(2118887149/5000000000 : ℝ)*X 1 0+(2258398911/5000000000 : ℝ)*X 1 1+(496618237/1250000000 : ℝ)*X 1 2+(2118887149/5000000000 : ℝ)*X 2 0+(2258398911/5000000000 : ℝ)*X 2 1+(496618237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1981562434698188517477711441/424250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18604371/3125000000000 : ℝ)*(base23) + (170068293/100000000000000 : ℝ)*(upper2) + (5766931/25000000000000 : ℝ)*(upper4) + (15218623/100000000000000 : ℝ)*(lower5) + (3067509422895341/100000000000000 : ℝ)*(major0) + (3067509422895341/100000000000000 : ℝ)*(major1) + (3067509422895341/100000000000000 : ℝ)*(major2) + (2159054497352429/50000000000000 : ℝ)*(sp0) + (539765539999309/12500000000000 : ℝ)*(sp1) + (2159060080409429/50000000000000 : ℝ)*(sp2) + (113555609479801/6250000000000 : ℝ)*(sp3) + (7662644807/50000000000000 : ℝ)*(sp4) + (3563835743/100000000000000 : ℝ)*(sp6) + (2309213987/50000000000000 : ℝ)*(sp7) + (181689437010479/10000000000000 : ℝ)*(f.failure) + (539765539999309/12500000000000 : ℝ)*(f.sum) + (239414258738307/10606250000000000000000000000 : ℝ)*base65 + (6994901175982732853/1697000000000000000000000000000000 : ℝ)*base67 + (7153404505742732853/1697000000000000000000000000000000 : ℝ)*base69 + (50017465161486732853/1697000000000000000000000000000000 : ℝ)*base71 + (99429732797361/21212500000000000000000000000 : ℝ)*base74 + (6214563074834732853/1697000000000000000000000000000000 : ℝ)*base75 + (4828727156467267147/1697000000000000000000000000000000 : ℝ)*base78 + (5912318009091732853/1697000000000000000000000000000000 : ℝ)*base79 + (32187841922989/21212500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (310009/125000000000000000000 : ℝ)*base89 + (310009/125000000000000000000 : ℝ)*base91 + (310009/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5228361580474677006867607971/424250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3215139/1562500000000 : ℝ)*(base15) + (32195119/10000000000000 : ℝ)*(lower2) + (147580413/100000000000000 : ℝ)*(upper3) + (39366307/100000000000000 : ℝ)*(upper4) + (1552198042972957/50000000000000 : ℝ)*(major0) + (1552198042972957/50000000000000 : ℝ)*(major1) + (1552198042972957/50000000000000 : ℝ)*(major2) + (8547448549/100000000000000 : ℝ)*(sp1) + (9368408161/20000000000000 : ℝ)*(sp2) + (1009745117/100000000000000 : ℝ)*(sp3) + (1092512329447373/25000000000000 : ℝ)*(sp4) + (273127535285753/6250000000000 : ℝ)*(sp5) + (273125154734293/6250000000000 : ℝ)*(sp6) + (1838741433564703/100000000000000 : ℝ)*(sp7) + (91937122165491/5000000000000 : ℝ)*(f.failure) + (1092512329447373/25000000000000 : ℝ)*(f.sum) + (83906948167737/42425000000000000000000000000 : ℝ)*base65 + (8528800454964395781/848500000000000000000000000000000 : ℝ)*base67 + (16961044474485895781/848500000000000000000000000000000 : ℝ)*base69 + (1935994490206895781/848500000000000000000000000000000 : ℝ)*base71 + (16834709539481/21212500000000000000000000000 : ℝ)*base73 + (2763574505490895781/848500000000000000000000000000000 : ℝ)*base75 + (22439166695622895781/848500000000000000000000000000000 : ℝ)*base77 + (1312052537797395781/848500000000000000000000000000000 : ℝ)*base79 + (210240154297981/21212500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (436139/62500000000000000000 : ℝ)*base90 + (436139/62500000000000000000 : ℝ)*base92 + (436139/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1580_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3533/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7893/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1580_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1580_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7893/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1580_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1580_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1580_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7893/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1580_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1469_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:35.208509+00:00
-- url     : https://prove2.me/submissions/9dac9592-eb8f-4ba2-b25a-04382f2e371f

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
theorem support_rectangle_w1469_s0_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732406993/10000000000 : ℝ)*x 0 + (5946713299/10000000000 : ℝ)*x 1 + (4836497243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732406993/10000000000 : ℝ)^4435 ≤ (10235019242751/100000000000000 : ℝ)^3411 := by
    have hnat : (1732406993 : ℕ)^4435*100000000000000^3411 ≤ 10235019242751^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732406993 10000000000 10235019242751 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5946713299/10000000000 : ℝ)^4435 ≤ (50876096066731/100000000000000 : ℝ)^3411 := by
    have hnat : (5946713299 : ℕ)^4435*100000000000000^3411 ≤ 50876096066731^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946713299 10000000000 50876096066731 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4836497243/10000000000 : ℝ)^4435 ≤ (4861110584339/12500000000000 : ℝ)^3411 := by
    have hnat : (4836497243 : ℕ)^4435*12500000000000^3411 ≤ 4861110584339^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836497243 10000000000 4861110584339 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732406993/10000000000 : ℝ), (5946713299/10000000000 : ℝ), (4836497243/10000000000 : ℝ)] ![(10235019242751/100000000000000 : ℝ), (50876096066731/100000000000000 : ℝ), (4861110584339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732406993/10000000000 : ℝ)|^4435 ≤ (10235019242751/100000000000000 : ℝ)^3411
        have hw : |(-1732406993/10000000000 : ℝ)|=(1732406993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5946713299/10000000000 : ℝ)|^4435 ≤ (50876096066731/100000000000000 : ℝ)^3411
        have hw : |(5946713299/10000000000 : ℝ)|=(5946713299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4836497243/10000000000 : ℝ)|^4435 ≤ (4861110584339/12500000000000 : ℝ)^3411
        have hw : |(4836497243/10000000000 : ℝ)|=(4836497243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685924261/1250000000 : ℝ)*x 0 + (-2358245971/10000000000 : ℝ)*x 1 + (2418248599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685924261/1250000000 : ℝ)^4435 ≤ (5728389268693/12500000000000 : ℝ)^3411 := by
    have hnat : (685924261 : ℕ)^4435*12500000000000^3411 ≤ 5728389268693^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685924261 1250000000 5728389268693 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2358245971/10000000000 : ℝ)^4435 ≤ (3056800325083/20000000000000 : ℝ)^3411 := by
    have hnat : (2358245971 : ℕ)^4435*20000000000000^3411 ≤ 3056800325083^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358245971 10000000000 3056800325083 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2418248599/5000000000 : ℝ)^4435 ≤ (1215277631383/3125000000000 : ℝ)^3411 := by
    have hnat : (2418248599 : ℕ)^4435*3125000000000^3411 ≤ 1215277631383^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418248599 5000000000 1215277631383 3125000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685924261/1250000000 : ℝ), (-2358245971/10000000000 : ℝ), (2418248599/5000000000 : ℝ)] ![(5728389268693/12500000000000 : ℝ), (3056800325083/20000000000000 : ℝ), (1215277631383/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685924261/1250000000 : ℝ)|^4435 ≤ (5728389268693/12500000000000 : ℝ)^3411
        have hw : |(685924261/1250000000 : ℝ)|=(685924261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2358245971/10000000000 : ℝ)|^4435 ≤ (3056800325083/20000000000000 : ℝ)^3411
        have hw : |(-2358245971/10000000000 : ℝ)|=(2358245971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2418248599/5000000000 : ℝ)|^4435 ≤ (1215277631383/3125000000000 : ℝ)^3411
        have hw : |(2418248599/5000000000 : ℝ)|=(2418248599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097478827/2000000000 : ℝ)*x 0 + (2418248569/5000000000 : ℝ)*x 1 + (-1179122993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097478827/2000000000 : ℝ)^4435 ≤ (45827114659891/100000000000000 : ℝ)^3411 := by
    have hnat : (1097478827 : ℕ)^4435*100000000000000^3411 ≤ 45827114659891^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097478827 2000000000 45827114659891 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418248569/5000000000 : ℝ)^4435 ≤ (19444441788491/50000000000000 : ℝ)^3411 := by
    have hnat : (2418248569 : ℕ)^4435*50000000000000^3411 ≤ 19444441788491^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418248569 5000000000 19444441788491 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179122993/5000000000 : ℝ)^4435 ≤ (1910500218977/12500000000000 : ℝ)^3411 := by
    have hnat : (1179122993 : ℕ)^4435*12500000000000^3411 ≤ 1910500218977^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179122993 5000000000 1910500218977 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097478827/2000000000 : ℝ), (2418248569/5000000000 : ℝ), (-1179122993/5000000000 : ℝ)] ![(45827114659891/100000000000000 : ℝ), (19444441788491/50000000000000 : ℝ), (1910500218977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097478827/2000000000 : ℝ)|^4435 ≤ (45827114659891/100000000000000 : ℝ)^3411
        have hw : |(1097478827/2000000000 : ℝ)|=(1097478827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2418248569/5000000000 : ℝ)|^4435 ≤ (19444441788491/50000000000000 : ℝ)^3411
        have hw : |(2418248569/5000000000 : ℝ)|=(2418248569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1179122993/5000000000 : ℝ)|^4435 ≤ (1910500218977/12500000000000 : ℝ)^3411
        have hw : |(-1179122993/5000000000 : ℝ)|=(1179122993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039237123/2500000000 : ℝ)*x 0 + (309177871/1000000000 : ℝ)*x 1 + (2766599917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039237123/2500000000 : ℝ)^4435 ≤ (31939550645329/100000000000000 : ℝ)^3411 := by
    have hnat : (1039237123 : ℕ)^4435*100000000000000^3411 ≤ 31939550645329^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039237123 2500000000 31939550645329 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309177871/1000000000 : ℝ)^4435 ≤ (21735333305661/100000000000000 : ℝ)^3411 := by
    have hnat : (309177871 : ℕ)^4435*100000000000000^3411 ≤ 21735333305661^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309177871 1000000000 21735333305661 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2766599917/5000000000 : ℝ)^4435 ≤ (1447659876139/3125000000000 : ℝ)^3411 := by
    have hnat : (2766599917 : ℕ)^4435*3125000000000^3411 ≤ 1447659876139^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766599917 5000000000 1447659876139 3125000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039237123/2500000000 : ℝ), (309177871/1000000000 : ℝ), (2766599917/5000000000 : ℝ)] ![(31939550645329/100000000000000 : ℝ), (21735333305661/100000000000000 : ℝ), (1447659876139/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039237123/2500000000 : ℝ)|^4435 ≤ (31939550645329/100000000000000 : ℝ)^3411
        have hw : |(1039237123/2500000000 : ℝ)|=(1039237123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309177871/1000000000 : ℝ)|^4435 ≤ (21735333305661/100000000000000 : ℝ)^3411
        have hw : |(309177871/1000000000 : ℝ)|=(309177871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2766599917/5000000000 : ℝ)|^4435 ≤ (1447659876139/3125000000000 : ℝ)^3411
        have hw : |(2766599917/5000000000 : ℝ)|=(2766599917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17363123/100000000 : ℝ)*x 0 + (486503101/1000000000 : ℝ)*x 1 + (1479288081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17363123/100000000 : ℝ)^4435 ≤ (10265028322023/100000000000000 : ℝ)^3411 := by
    have hnat : (17363123 : ℕ)^4435*100000000000000^3411 ≤ 10265028322023^3411*100000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17363123 100000000 10265028322023 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486503101/1000000000 : ℝ)^4435 ≤ (39187456933281/100000000000000 : ℝ)^3411 := by
    have hnat : (486503101 : ℕ)^4435*100000000000000^3411 ≤ 39187456933281^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486503101 1000000000 39187456933281 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479288081/2500000000 : ℝ)^4435 ≤ (394902458857/781250000000 : ℝ)^3411 := by
    have hnat : (1479288081 : ℕ)^4435*781250000000^3411 ≤ 394902458857^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479288081 2500000000 394902458857 781250000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17363123/100000000 : ℝ), (486503101/1000000000 : ℝ), (1479288081/2500000000 : ℝ)] ![(10265028322023/100000000000000 : ℝ), (39187456933281/100000000000000 : ℝ), (394902458857/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17363123/100000000 : ℝ)|^4435 ≤ (10265028322023/100000000000000 : ℝ)^3411
        have hw : |(-17363123/100000000 : ℝ)|=(17363123/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486503101/1000000000 : ℝ)|^4435 ≤ (39187456933281/100000000000000 : ℝ)^3411
        have hw : |(486503101/1000000000 : ℝ)|=(486503101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1479288081/2500000000 : ℝ)|^4435 ≤ (394902458857/781250000000 : ℝ)^3411
        have hw : |(1479288081/2500000000 : ℝ)|=(1479288081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184331857/10000000000 : ℝ)*x 0 + (-319397647/2500000000 : ℝ)*x 1 + (1183430489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184331857/10000000000 : ℝ)^4435 ≤ (42563965391299/100000000000000 : ℝ)^3411 := by
    have hnat : (5184331857 : ℕ)^4435*100000000000000^3411 ≤ 42563965391299^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184331857 10000000000 42563965391299 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319397647/2500000000 : ℝ)^4435 ≤ (6888518513243/100000000000000 : ℝ)^3411 := by
    have hnat : (319397647 : ℕ)^4435*100000000000000^3411 ≤ 6888518513243^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319397647 2500000000 6888518513243 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183430489/2000000000 : ℝ)^4435 ≤ (1010950321553/2000000000000 : ℝ)^3411 := by
    have hnat : (1183430489 : ℕ)^4435*2000000000000^3411 ≤ 1010950321553^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183430489 2000000000 1010950321553 2000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184331857/10000000000 : ℝ), (-319397647/2500000000 : ℝ), (1183430489/2000000000 : ℝ)] ![(42563965391299/100000000000000 : ℝ), (6888518513243/100000000000000 : ℝ), (1010950321553/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184331857/10000000000 : ℝ)|^4435 ≤ (42563965391299/100000000000000 : ℝ)^3411
        have hw : |(5184331857/10000000000 : ℝ)|=(5184331857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-319397647/2500000000 : ℝ)|^4435 ≤ (6888518513243/100000000000000 : ℝ)^3411
        have hw : |(-319397647/2500000000 : ℝ)|=(319397647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183430489/2000000000 : ℝ)|^4435 ≤ (1010950321553/2000000000000 : ℝ)^3411
        have hw : |(1183430489/2000000000 : ℝ)|=(1183430489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_6 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036866357/2000000000 : ℝ)*x 0 + (5917152319/10000000000 : ℝ)*x 1 + (-1277590897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036866357/2000000000 : ℝ)^4435 ≤ (42563964622711/100000000000000 : ℝ)^3411 := by
    have hnat : (1036866357 : ℕ)^4435*100000000000000^3411 ≤ 42563964622711^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036866357 2000000000 42563964622711 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5917152319/10000000000 : ℝ)^4435 ≤ (631843933477/1250000000000 : ℝ)^3411 := by
    have hnat : (5917152319 : ℕ)^4435*1250000000000^3411 ≤ 631843933477^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917152319 10000000000 631843933477 1250000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277590897/10000000000 : ℝ)^4435 ≤ (6888520679473/100000000000000 : ℝ)^3411 := by
    have hnat : (1277590897 : ℕ)^4435*100000000000000^3411 ≤ 6888520679473^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277590897 10000000000 6888520679473 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036866357/2000000000 : ℝ), (5917152319/10000000000 : ℝ), (-1277590897/10000000000 : ℝ)] ![(42563964622711/100000000000000 : ℝ), (631843933477/1250000000000 : ℝ), (6888520679473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036866357/2000000000 : ℝ)|^4435 ≤ (42563964622711/100000000000000 : ℝ)^3411
        have hw : |(1036866357/2000000000 : ℝ)|=(1036866357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5917152319/10000000000 : ℝ)|^4435 ≤ (631843933477/1250000000000 : ℝ)^3411
        have hw : |(5917152319/10000000000 : ℝ)|=(5917152319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1277590897/10000000000 : ℝ)|^4435 ≤ (6888520679473/100000000000000 : ℝ)^3411
        have hw : |(-1277590897/10000000000 : ℝ)|=(1277590897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s0_7 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041384167/2500000000 : ℝ)*x 0 + (5470452459/10000000000 : ℝ)*x 1 + (3156784789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041384167/2500000000 : ℝ)^4435 ≤ (32025373230481/100000000000000 : ℝ)^3411 := by
    have hnat : (1041384167 : ℕ)^4435*100000000000000^3411 ≤ 32025373230481^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041384167 2500000000 32025373230481 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470452459/10000000000 : ℝ)^4435 ≤ (22821619724919/50000000000000 : ℝ)^3411 := by
    have hnat : (5470452459 : ℕ)^4435*50000000000000^3411 ≤ 22821619724919^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470452459 10000000000 22821619724919 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3156784789/10000000000 : ℝ)^4435 ≤ (11165693649031/50000000000000 : ℝ)^3411 := by
    have hnat : (3156784789 : ℕ)^4435*50000000000000^3411 ≤ 11165693649031^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3156784789 10000000000 11165693649031 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041384167/2500000000 : ℝ), (5470452459/10000000000 : ℝ), (3156784789/10000000000 : ℝ)] ![(32025373230481/100000000000000 : ℝ), (22821619724919/50000000000000 : ℝ), (11165693649031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041384167/2500000000 : ℝ)|^4435 ≤ (32025373230481/100000000000000 : ℝ)^3411
        have hw : |(1041384167/2500000000 : ℝ)|=(1041384167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470452459/10000000000 : ℝ)|^4435 ≤ (22821619724919/50000000000000 : ℝ)^3411
        have hw : |(5470452459/10000000000 : ℝ)|=(5470452459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3156784789/10000000000 : ℝ)|^4435 ≤ (11165693649031/50000000000000 : ℝ)^3411
        have hw : |(3156784789/10000000000 : ℝ)|=(3156784789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (141/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26053/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4433/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4433 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4433*1^1024 ≤ 0^1024*1^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4433/1024 : ℝ) ≤ (473388055184508483/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4433 ≤ (473388055184508483/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4433*25000000000000000000^1024 ≤ 473388055184508483^1024*5^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 473388055184508483 25000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (473388055184508483/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4433 := by
      have hnat : (1 : ℕ)^1024*1^4433 ≤ 1^4433*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25473388055184508483/25000000000000000000 : ℝ) ≤ (10043425122866019/10000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (25473388055184508483/25000000000000000000 : ℝ)^1024 ≤ (10043425122866019/10000000000000000 : ℝ)^4433 := by
      have hnat : (25473388055184508483 : ℕ)^1024*10000000000000000^4433 ≤ 10043425122866019^4433*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25473388055184508483 25000000000000000000 10043425122866019 10000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043425122866019/10000000000000000 : ℝ)) (X := (25473388055184508483/25000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12973388055184508483/12500000000000000000 : ℝ) ≤ (5043425122866019/5000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (12973388055184508483/12500000000000000000 : ℝ)^1024 ≤ (5043425122866019/5000000000000000 : ℝ)^4433 := by
      have hnat : (12973388055184508483 : ℕ)^1024*5000000000000000^4433 ≤ 5043425122866019^4433*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12973388055184508483 12500000000000000000 5043425122866019 5000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043425122866019/5000000000000000 : ℝ)) (X := (12973388055184508483/12500000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(43425122866019/4000000000000000 : ℝ)*(0 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43425122866019/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(473388055184508483/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(43425122866019/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (1 : ℝ)+(43425122866019/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10043425122866019/10000000000000000 : ℝ) by norm_num, show 1+(473388055184508483/25000000000000000000 : ℝ)+(0 : ℝ)=(25473388055184508483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(473388055184508483/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(43425122866019/4000000000000000 : ℝ)*(2/5 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43425122866019/4000000000000000 : ℝ)*(2/5 : ℝ)=(5043425122866019/5000000000000000 : ℝ) by norm_num, show 1+2*(473388055184508483/25000000000000000000 : ℝ)=(12973388055184508483/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(43425122866019/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43425122866019/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(43425122866019/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43425122866019/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(43425122866019/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43425122866019/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1732406993/10000000000 : ℝ)*X 0 0+(5946713299/10000000000 : ℝ)*X 0 1+(4836497243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((685924261/1250000000 : ℝ)*X 1 0+(-2358245971/10000000000 : ℝ)*X 1 1+(2418248599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1097478827/2000000000 : ℝ)*X 2 0+(2418248569/5000000000 : ℝ)*X 2 1+(-1179122993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1039237123/2500000000 : ℝ)*X 0 0+(309177871/1000000000 : ℝ)*X 0 1+(2766599917/5000000000 : ℝ)*X 0 2+(1039237123/2500000000 : ℝ)*X 1 0+(309177871/1000000000 : ℝ)*X 1 1+(2766599917/5000000000 : ℝ)*X 1 2+(1039237123/2500000000 : ℝ)*X 2 0+(309177871/1000000000 : ℝ)*X 2 1+(2766599917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17363123/100000000 : ℝ)*X 0 0+(486503101/1000000000 : ℝ)*X 0 1+(1479288081/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184331857/10000000000 : ℝ)*X 1 0+(-319397647/2500000000 : ℝ)*X 1 1+(1183430489/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036866357/2000000000 : ℝ)*X 2 0+(5917152319/10000000000 : ℝ)*X 2 1+(-1277590897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1041384167/2500000000 : ℝ)*X 0 0+(5470452459/10000000000 : ℝ)*X 0 1+(3156784789/10000000000 : ℝ)*X 0 2+(1041384167/2500000000 : ℝ)*X 1 0+(5470452459/10000000000 : ℝ)*X 1 1+(3156784789/10000000000 : ℝ)*X 1 2+(1041384167/2500000000 : ℝ)*X 2 0+(5470452459/10000000000 : ℝ)*X 2 1+(3156784789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (728310621017381630772627/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87805869/100000000000000 : ℝ)*(base1) + (1630526471/100000000000000 : ℝ)*(base19) + (81912067/5000000000000 : ℝ)*(base23) + (198548811/100000000000000 : ℝ)*(upper3) + (196961179/100000000000000 : ℝ)*(upper5) + (655169481557989/100000000000000 : ℝ)*(major0) + (655169481557989/100000000000000 : ℝ)*(major1) + (655169481557989/100000000000000 : ℝ)*(major2) + (900730814694597/100000000000000 : ℝ)*(sp0) + (900734619432493/100000000000000 : ℝ)*(sp1) + (112591826464703/12500000000000 : ℝ)*(sp2) + (40959987372501/10000000000000 : ℝ)*(sp3) + (1380767559/25000000000000 : ℝ)*(sp4) + (31360699/1250000000000 : ℝ)*(sp7) + (409602470386799/100000000000000 : ℝ)*(f.failure) + (900736249958963/100000000000000 : ℝ)*(f.sum) + (97998945724209/200000000000000000000000000000 : ℝ)*base66 + (1519805728875791/400000000000000000000000000000 : ℝ)*base67 + (1168699524075791/400000000000000000000000000000 : ℝ)*base69 + (747904680475791/400000000000000000000000000000 : ℝ)*base71 + (395747290675791/200000000000000000000000000000 : ℝ)*base73 + (393112507524209/400000000000000000000000000000 : ℝ)*base76 + (663731138075791/400000000000000000000000000000 : ℝ)*base77 + (1115712770724209/400000000000000000000000000000 : ℝ)*base80 + (245890634875791/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (42221461/5000000000000000000000 : ℝ)*base90 + (42221461/5000000000000000000000 : ℝ)*base92 + (42221461/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1556406087501399530453331/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (178669867/10000000000000 : ℝ)*(base19) + (355393953/20000000000000 : ℝ)*(base23) + (15426523/10000000000000 : ℝ)*(base32) + (133239811/50000000000000 : ℝ)*(upper3) + (16749151/10000000000000 : ℝ)*(upper5) + (691337107394039/100000000000000 : ℝ)*(major0) + (691337107394039/100000000000000 : ℝ)*(major1) + (691337107394039/100000000000000 : ℝ)*(major2) + (878176043/20000000000000 : ℝ)*(sp1) + (890051221/20000000000000 : ℝ)*(sp2) + (237615002294981/25000000000000 : ℝ)*(sp4) + (950453831601039/100000000000000 : ℝ)*(sp5) + (475226890977027/50000000000000 : ℝ)*(sp6) + (432213791941907/100000000000000 : ℝ)*(sp7) + (432213946207137/100000000000000 : ℝ)*(f.failure) + (237615002294981/25000000000000 : ℝ)*(f.sum) + (39901060741/200000000000000000000000000000 : ℝ)*base65 + (1730959015060741/400000000000000000000000000000 : ℝ)*base67 + (251942363339259/400000000000000000000000000000 : ℝ)*base70 + (618650348660741/400000000000000000000000000000 : ℝ)*base71 + (522353113060741/200000000000000000000000000000 : ℝ)*base73 + (2086543817060741/400000000000000000000000000000 : ℝ)*base75 + (1147617459860741/400000000000000000000000000000 : ℝ)*base77 + (1231904824660741/400000000000000000000000000000 : ℝ)*base79 + (531616294739259/200000000000000000000000000000 : ℝ)*base82 + (1225243/5000000000000000000000 : ℝ)*base90 + (1225243/5000000000000000000000 : ℝ)*base92 + (1225243/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1469_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1469_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1469_s1_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-474462391/2500000000 : ℝ)*x 0 + (2800420509/5000000000 : ℝ)*x 1 + (507621963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474462391/2500000000 : ℝ)^4435 ≤ (2880926739/25000000000 : ℝ)^3411 := by
    have hnat : (474462391 : ℕ)^4435*25000000000^3411 ≤ 2880926739^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474462391 2500000000 2880926739 25000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800420509/5000000000 : ℝ)^4435 ≤ (47062777653053/100000000000000 : ℝ)^3411 := by
    have hnat : (2800420509 : ℕ)^4435*100000000000000^3411 ≤ 47062777653053^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800420509 5000000000 47062777653053 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507621963/1000000000 : ℝ)^4435 ≤ (5176689420751/12500000000000 : ℝ)^3411 := by
    have hnat : (507621963 : ℕ)^4435*12500000000000^3411 ≤ 5176689420751^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507621963 1000000000 5176689420751 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474462391/2500000000 : ℝ), (2800420509/5000000000 : ℝ), (507621963/1000000000 : ℝ)] ![(2880926739/25000000000 : ℝ), (47062777653053/100000000000000 : ℝ), (5176689420751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474462391/2500000000 : ℝ)|^4435 ≤ (2880926739/25000000000 : ℝ)^3411
        have hw : |(-474462391/2500000000 : ℝ)|=(474462391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800420509/5000000000 : ℝ)|^4435 ≤ (47062777653053/100000000000000 : ℝ)^3411
        have hw : |(2800420509/5000000000 : ℝ)|=(2800420509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507621963/1000000000 : ℝ)|^4435 ≤ (5176689420751/12500000000000 : ℝ)^3411
        have hw : |(507621963/1000000000 : ℝ)|=(507621963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539465931/1000000000 : ℝ)*x 0 + (-2175676603/10000000000 : ℝ)*x 1 + (5076221059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539465931/1000000000 : ℝ)^4435 ≤ (11205680418207/25000000000000 : ℝ)^3411 := by
    have hnat : (539465931 : ℕ)^4435*25000000000000^3411 ≤ 11205680418207^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539465931 1000000000 11205680418207 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175676603/10000000000 : ℝ)^4435 ≤ (13763747792553/100000000000000 : ℝ)^3411 := by
    have hnat : (2175676603 : ℕ)^4435*100000000000000^3411 ≤ 13763747792553^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175676603 10000000000 13763747792553 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076221059/10000000000 : ℝ)^4435 ≤ (8282706104829/20000000000000 : ℝ)^3411 := by
    have hnat : (5076221059 : ℕ)^4435*20000000000000^3411 ≤ 8282706104829^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076221059 10000000000 8282706104829 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539465931/1000000000 : ℝ), (-2175676603/10000000000 : ℝ), (5076221059/10000000000 : ℝ)] ![(11205680418207/25000000000000 : ℝ), (13763747792553/100000000000000 : ℝ), (8282706104829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539465931/1000000000 : ℝ)|^4435 ≤ (11205680418207/25000000000000 : ℝ)^3411
        have hw : |(539465931/1000000000 : ℝ)|=(539465931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175676603/10000000000 : ℝ)|^4435 ≤ (13763747792553/100000000000000 : ℝ)^3411
        have hw : |(-2175676603/10000000000 : ℝ)|=(2175676603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076221059/10000000000 : ℝ)|^4435 ≤ (8282706104829/20000000000000 : ℝ)^3411
        have hw : |(5076221059/10000000000 : ℝ)|=(5076221059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697330259/5000000000 : ℝ)*x 0 + (5076219759/10000000000 : ℝ)*x 1 + (-2175676693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697330259/5000000000 : ℝ)^4435 ≤ (5602841840363/12500000000000 : ℝ)^3411 := by
    have hnat : (2697330259 : ℕ)^4435*12500000000000^3411 ≤ 5602841840363^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697330259 5000000000 5602841840363 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076219759/10000000000 : ℝ)^4435 ≤ (41413516734377/100000000000000 : ℝ)^3411 := by
    have hnat : (5076219759 : ℕ)^4435*100000000000000^3411 ≤ 41413516734377^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076219759 10000000000 41413516734377 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175676693/10000000000 : ℝ)^4435 ≤ (6881874266417/50000000000000 : ℝ)^3411 := by
    have hnat : (2175676693 : ℕ)^4435*50000000000000^3411 ≤ 6881874266417^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175676693 10000000000 6881874266417 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697330259/5000000000 : ℝ), (5076219759/10000000000 : ℝ), (-2175676693/10000000000 : ℝ)] ![(5602841840363/12500000000000 : ℝ), (41413516734377/100000000000000 : ℝ), (6881874266417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697330259/5000000000 : ℝ)|^4435 ≤ (5602841840363/12500000000000 : ℝ)^3411
        have hw : |(2697330259/5000000000 : ℝ)|=(2697330259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076219759/10000000000 : ℝ)|^4435 ≤ (41413516734377/100000000000000 : ℝ)^3411
        have hw : |(5076219759/10000000000 : ℝ)|=(5076219759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175676693/10000000000 : ℝ)|^4435 ≤ (6881874266417/50000000000000 : ℝ)^3411
        have hw : |(-2175676693/10000000000 : ℝ)|=(2175676693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132627069/5000000000 : ℝ)*x 0 + (3722546009/10000000000 : ℝ)*x 1 + (609526491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132627069/5000000000 : ℝ)^4435 ≤ (825643285609/2500000000000 : ℝ)^3411 := by
    have hnat : (2132627069 : ℕ)^4435*2500000000000^3411 ≤ 825643285609^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132627069 5000000000 825643285609 2500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3722546009/10000000000 : ℝ)^4435 ≤ (13834836442183/50000000000000 : ℝ)^3411 := by
    have hnat : (3722546009 : ℕ)^4435*50000000000000^3411 ≤ 13834836442183^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722546009 10000000000 13834836442183 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609526491/1250000000 : ℝ)^4435 ≤ (39304595673031/100000000000000 : ℝ)^3411 := by
    have hnat : (609526491 : ℕ)^4435*100000000000000^3411 ≤ 39304595673031^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609526491 1250000000 39304595673031 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132627069/5000000000 : ℝ), (3722546009/10000000000 : ℝ), (609526491/1250000000 : ℝ)] ![(825643285609/2500000000000 : ℝ), (13834836442183/50000000000000 : ℝ), (39304595673031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132627069/5000000000 : ℝ)|^4435 ≤ (825643285609/2500000000000 : ℝ)^3411
        have hw : |(2132627069/5000000000 : ℝ)|=(2132627069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3722546009/10000000000 : ℝ)|^4435 ≤ (13834836442183/50000000000000 : ℝ)^3411
        have hw : |(3722546009/10000000000 : ℝ)|=(3722546009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(609526491/1250000000 : ℝ)|^4435 ≤ (39304595673031/100000000000000 : ℝ)^3411
        have hw : |(609526491/1250000000 : ℝ)|=(609526491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898245927/10000000000 : ℝ)*x 0 + (5082455501/10000000000 : ℝ)*x 1 + (5594497951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898245927/10000000000 : ℝ)^4435 ≤ (2305367253861/20000000000000 : ℝ)^3411 := by
    have hnat : (1898245927 : ℕ)^4435*20000000000000^3411 ≤ 2305367253861^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898245927 10000000000 2305367253861 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082455501/10000000000 : ℝ)^4435 ≤ (20739837323033/50000000000000 : ℝ)^3411 := by
    have hnat : (5082455501 : ℕ)^4435*50000000000000^3411 ≤ 20739837323033^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082455501 10000000000 20739837323033 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5594497951/10000000000 : ℝ)^4435 ≤ (46993489073109/100000000000000 : ℝ)^3411 := by
    have hnat : (5594497951 : ℕ)^4435*100000000000000^3411 ≤ 46993489073109^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594497951 10000000000 46993489073109 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898245927/10000000000 : ℝ), (5082455501/10000000000 : ℝ), (5594497951/10000000000 : ℝ)] ![(2305367253861/20000000000000 : ℝ), (20739837323033/50000000000000 : ℝ), (46993489073109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898245927/10000000000 : ℝ)|^4435 ≤ (2305367253861/20000000000000 : ℝ)^3411
        have hw : |(-1898245927/10000000000 : ℝ)|=(1898245927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082455501/10000000000 : ℝ)|^4435 ≤ (20739837323033/50000000000000 : ℝ)^3411
        have hw : |(5082455501/10000000000 : ℝ)|=(5082455501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5594497951/10000000000 : ℝ)|^4435 ≤ (46993489073109/100000000000000 : ℝ)^3411
        have hw : |(5594497951/10000000000 : ℝ)|=(5594497951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314309997/2500000000 : ℝ)*x 0 + (-331479883/2000000000 : ℝ)*x 1 + (349656123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314309997/2500000000 : ℝ)^4435 ≤ (10835971307891/25000000000000 : ℝ)^3411 := by
    have hnat : (1314309997 : ℕ)^4435*25000000000000^3411 ≤ 10835971307891^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314309997 2500000000 10835971307891 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331479883/2000000000 : ℝ)^4435 ≤ (1932525100037/20000000000000 : ℝ)^3411 := by
    have hnat : (331479883 : ℕ)^4435*20000000000000^3411 ≤ 1932525100037^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331479883 2000000000 1932525100037 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349656123/625000000 : ℝ)^4435 ≤ (23496744629389/50000000000000 : ℝ)^3411 := by
    have hnat : (349656123 : ℕ)^4435*50000000000000^3411 ≤ 23496744629389^3411*625000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349656123 625000000 23496744629389 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314309997/2500000000 : ℝ), (-331479883/2000000000 : ℝ), (349656123/625000000 : ℝ)] ![(10835971307891/25000000000000 : ℝ), (1932525100037/20000000000000 : ℝ), (23496744629389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314309997/2500000000 : ℝ)|^4435 ≤ (10835971307891/25000000000000 : ℝ)^3411
        have hw : |(1314309997/2500000000 : ℝ)|=(1314309997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331479883/2000000000 : ℝ)|^4435 ≤ (1932525100037/20000000000000 : ℝ)^3411
        have hw : |(-331479883/2000000000 : ℝ)|=(331479883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349656123/625000000 : ℝ)|^4435 ≤ (23496744629389/50000000000000 : ℝ)^3411
        have hw : |(349656123/625000000 : ℝ)|=(349656123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_6 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105144801/200000000 : ℝ)*x 0 + (699312241/1250000000 : ℝ)*x 1 + (-207174923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105144801/200000000 : ℝ)^4435 ≤ (5417985737023/12500000000000 : ℝ)^3411 := by
    have hnat : (105144801 : ℕ)^4435*12500000000000^3411 ≤ 5417985737023^3411*200000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105144801 200000000 5417985737023 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699312241/1250000000 : ℝ)^4435 ≤ (46993488821911/100000000000000 : ℝ)^3411 := by
    have hnat : (699312241 : ℕ)^4435*100000000000000^3411 ≤ 46993488821911^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699312241 1250000000 46993488821911 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207174923/1250000000 : ℝ)^4435 ≤ (9662625265199/100000000000000 : ℝ)^3411 := by
    have hnat : (207174923 : ℕ)^4435*100000000000000^3411 ≤ 9662625265199^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207174923 1250000000 9662625265199 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105144801/200000000 : ℝ), (699312241/1250000000 : ℝ), (-207174923/1250000000 : ℝ)] ![(5417985737023/12500000000000 : ℝ), (46993488821911/100000000000000 : ℝ), (9662625265199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105144801/200000000 : ℝ)|^4435 ≤ (5417985737023/12500000000000 : ℝ)^3411
        have hw : |(105144801/200000000 : ℝ)|=(105144801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(699312241/1250000000 : ℝ)|^4435 ≤ (46993488821911/100000000000000 : ℝ)^3411
        have hw : |(699312241/1250000000 : ℝ)|=(699312241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207174923/1250000000 : ℝ)|^4435 ≤ (9662625265199/100000000000000 : ℝ)^3411
        have hw : |(-207174923/1250000000 : ℝ)|=(207174923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s1_7 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266126349/10000000000 : ℝ)*x 0 + (486250009/1000000000 : ℝ)*x 1 + (467061581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266126349/10000000000 : ℝ)^4435 ≤ (16517256316801/50000000000000 : ℝ)^3411 := by
    have hnat : (4266126349 : ℕ)^4435*50000000000000^3411 ≤ 16517256316801^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266126349 10000000000 16517256316801 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486250009/1000000000 : ℝ)^4435 ≤ (9790238134923/25000000000000 : ℝ)^3411 := by
    have hnat : (486250009 : ℕ)^4435*25000000000000^3411 ≤ 9790238134923^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486250009 1000000000 9790238134923 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467061581/1250000000 : ℝ)^4435 ≤ (5560906962539/20000000000000 : ℝ)^3411 := by
    have hnat : (467061581 : ℕ)^4435*20000000000000^3411 ≤ 5560906962539^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467061581 1250000000 5560906962539 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266126349/10000000000 : ℝ), (486250009/1000000000 : ℝ), (467061581/1250000000 : ℝ)] ![(16517256316801/50000000000000 : ℝ), (9790238134923/25000000000000 : ℝ), (5560906962539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266126349/10000000000 : ℝ)|^4435 ≤ (16517256316801/50000000000000 : ℝ)^3411
        have hw : |(4266126349/10000000000 : ℝ)|=(4266126349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(486250009/1000000000 : ℝ)|^4435 ≤ (9790238134923/25000000000000 : ℝ)^3411
        have hw : |(486250009/1000000000 : ℝ)|=(486250009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467061581/1250000000 : ℝ)|^4435 ≤ (5560906962539/20000000000000 : ℝ)^3411
        have hw : |(467061581/1250000000 : ℝ)|=(467061581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (7741/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18829/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (141/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (141/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (141/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (141/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (141/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (141/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (141/6250 : ℝ) ^ (4433/1024 : ℝ) ≤ (7437683687869/100000000000000000000 : ℝ) := by
    have hpowers : (141/6250 : ℝ)^4433 ≤ (7437683687869/100000000000000000000 : ℝ)^1024 := by
      have hnat : (141 : ℕ)^4433*100000000000000000000^1024 ≤ 7437683687869^1024*6250^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 6250 7437683687869 100000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/6250 : ℝ)) (X := (7437683687869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26053/100000 : ℝ) ^ (4433/1024 : ℝ) ≤ (147964943138245677/50000000000000000000 : ℝ) := by
    have hpowers : (26053/100000 : ℝ)^4433 ≤ (147964943138245677/50000000000000000000 : ℝ)^1024 := by
      have hnat : (26053 : ℕ)^4433*50000000000000000000^1024 ≤ 147964943138245677^1024*100000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26053 100000 147964943138245677 50000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26053/100000 : ℝ)) (X := (147964943138245677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007437683687869/50000000000000000000 : ℝ) ≤ (10000000343613249/10000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (50000007437683687869/50000000000000000000 : ℝ)^1024 ≤ (10000000343613249/10000000000000000 : ℝ)^4433 := by
      have hnat : (50000007437683687869 : ℕ)^1024*10000000000000000^4433 ≤ 10000000343613249^4433*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007437683687869 50000000000000000000 10000000343613249 10000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000343613249/10000000000000000 : ℝ)) (X := (50000007437683687869/50000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100295937323960179223/100000000000000000000 : ℝ) ≤ (1250853529199371/1250000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (100295937323960179223/100000000000000000000 : ℝ)^1024 ≤ (1250853529199371/1250000000000000 : ℝ)^4433 := by
      have hnat : (100295937323960179223 : ℕ)^1024*1250000000000000^4433 ≤ 1250853529199371^4433*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100295937323960179223 100000000000000000000 1250853529199371 1250000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250853529199371/1250000000000000 : ℝ)) (X := (100295937323960179223/100000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25147964943138245677/25000000000000000000 : ℝ) ≤ (10013656123576687/10000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (25147964943138245677/25000000000000000000 : ℝ)^1024 ≤ (10013656123576687/10000000000000000 : ℝ)^4433 := by
      have hnat : (25147964943138245677 : ℕ)^1024*10000000000000000^4433 ≤ 10013656123576687^4433*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25147964943138245677 25000000000000000000 10013656123576687 10000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013656123576687/10000000000000000 : ℝ)) (X := (25147964943138245677/25000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7437683687869/100000000000000000000 : ℝ) ≤ ((9517568029494678813/9518800000000000000 : ℝ)+2*(6827889981719/2379700000000000 : ℝ)*(141/6250 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (9517568029494678813/9518800000000000000 : ℝ)+2*(6827889981719/2379700000000000 : ℝ)*(141/6250 : ℝ)=(10000000343613249/10000000000000000 : ℝ) by norm_num, show 1+2*(7437683687869/100000000000000000000 : ℝ)=(50000007437683687869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(147964943138245677/50000000000000000000 : ℝ)+(7437683687869/100000000000000000000 : ℝ) ≤ ((9517568029494678813/9518800000000000000 : ℝ)+(6827889981719/2379700000000000 : ℝ)*((26053/100000 : ℝ)+(141/6250 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (9517568029494678813/9518800000000000000 : ℝ)+(6827889981719/2379700000000000 : ℝ)*((26053/100000 : ℝ)+(141/6250 : ℝ))=(1250853529199371/1250000000000000 : ℝ) by norm_num, show 1+(147964943138245677/50000000000000000000 : ℝ)+(7437683687869/100000000000000000000 : ℝ)=(100295937323960179223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(147964943138245677/50000000000000000000 : ℝ) ≤ ((9517568029494678813/9518800000000000000 : ℝ)+2*(6827889981719/2379700000000000 : ℝ)*(26053/100000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (9517568029494678813/9518800000000000000 : ℝ)+2*(6827889981719/2379700000000000 : ℝ)*(26053/100000 : ℝ)=(10013656123576687/10000000000000000 : ℝ) by norm_num, show 1+2*(147964943138245677/50000000000000000000 : ℝ)=(25147964943138245677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9517568029494678813/9518800000000000000 : ℝ)*(X 1 0+X 2 0)+(6827889981719/2379700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (141/6250 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (9517568029494678813/9518800000000000000 : ℝ)) (alpha := (6827889981719/2379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9517568029494678813/9518800000000000000 : ℝ)*(X 0 1+X 2 1)+(6827889981719/2379700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (141/6250 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (9517568029494678813/9518800000000000000 : ℝ)) (alpha := (6827889981719/2379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9517568029494678813/9518800000000000000 : ℝ)*(X 0 2+X 1 2)+(6827889981719/2379700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (141/6250 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (9517568029494678813/9518800000000000000 : ℝ)) (alpha := (6827889981719/2379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-474462391/2500000000 : ℝ)*X 0 0+(2800420509/5000000000 : ℝ)*X 0 1+(507621963/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((539465931/1000000000 : ℝ)*X 1 0+(-2175676603/10000000000 : ℝ)*X 1 1+(5076221059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2697330259/5000000000 : ℝ)*X 2 0+(5076219759/10000000000 : ℝ)*X 2 1+(-2175676693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2132627069/5000000000 : ℝ)*X 0 0+(3722546009/10000000000 : ℝ)*X 0 1+(609526491/1250000000 : ℝ)*X 0 2+(2132627069/5000000000 : ℝ)*X 1 0+(3722546009/10000000000 : ℝ)*X 1 1+(609526491/1250000000 : ℝ)*X 1 2+(2132627069/5000000000 : ℝ)*X 2 0+(3722546009/10000000000 : ℝ)*X 2 1+(609526491/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1898245927/10000000000 : ℝ)*X 0 0+(5082455501/10000000000 : ℝ)*X 0 1+(5594497951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314309997/2500000000 : ℝ)*X 1 0+(-331479883/2000000000 : ℝ)*X 1 1+(349656123/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105144801/200000000 : ℝ)*X 2 0+(699312241/1250000000 : ℝ)*X 2 1+(-207174923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266126349/10000000000 : ℝ)*X 0 0+(486250009/1000000000 : ℝ)*X 0 1+(467061581/1250000000 : ℝ)*X 0 2+(4266126349/10000000000 : ℝ)*X 1 0+(486250009/1000000000 : ℝ)*X 1 1+(467061581/1250000000 : ℝ)*X 1 2+(4266126349/10000000000 : ℝ)*X 2 0+(486250009/1000000000 : ℝ)*X 2 1+(467061581/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (444735401512237746981833847/237970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42184999/20000000000000 : ℝ)*(base19) + (567129617/100000000000000 : ℝ)*(base23) + (105183/2500000000000 : ℝ)*(upper2) + (2115493/5000000000000 : ℝ)*(upper4) + (438281/20000000000000 : ℝ)*(lower5) + (693238846389909/50000000000000 : ℝ)*(major0) + (693238846389909/50000000000000 : ℝ)*(major1) + (693238846389909/50000000000000 : ℝ)*(major2) + (381228458401967/20000000000000 : ℝ)*(sp0) + (76245973622953/4000000000000 : ℝ)*(sp1) + (1906148984369203/100000000000000 : ℝ)*(sp2) + (17336072423661/2000000000000 : ℝ)*(sp3) + (1451897797/20000000000000 : ℝ)*(sp4) + (430116407/20000000000000 : ℝ)*(sp7) + (173361154353017/20000000000000 : ℝ)*(f.failure) + (95307477574941/5000000000000 : ℝ)*(f.sum) + (43925500498329/59492500000000000000000000000 : ℝ)*base66 + (4310829820020482017/475940000000000000000000000000000 : ℝ)*base67 + (2697378584865482017/475940000000000000000000000000000 : ℝ)*base69 + (942762950785482017/475940000000000000000000000000000 : ℝ)*base71 + (85196332015983/118985000000000000000000000000 : ℝ)*base74 + (5010661210218882017/475940000000000000000000000000000 : ℝ)*base75 + (4378732582465722017/475940000000000000000000000000000 : ℝ)*base77 + (1155293571322202017/475940000000000000000000000000000 : ℝ)*base79 + (84167003129157/118985000000000000000000000000 : ℝ)*base81 + (6270563/1000000000000000000000 : ℝ)*base90 + (6270563/1000000000000000000000 : ℝ)*base92 + (6270563/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111402482004078154601907/59492500000000000000000000000 : ℝ) := by norm_num
    linear_combination (11077921/3125000000000 : ℝ)*(base19) + (395841097/100000000000000 : ℝ)*(base23) + (692521/1250000000000 : ℝ)*(upper3) + (4466723/100000000000000 : ℝ)*(lower4) + (4266609/12500000000000 : ℝ)*(upper5) + (1420528315872747/100000000000000 : ℝ)*(major0) + (1420528315872747/100000000000000 : ℝ)*(major1) + (1420528315872747/100000000000000 : ℝ)*(major2) + (502099001/25000000000000 : ℝ)*(sp1) + (2384040059/100000000000000 : ℝ)*(sp2) + (488240710298537/25000000000000 : ℝ)*(sp4) + (61030014947021/3125000000000 : ℝ)*(sp5) + (1952960061312993/100000000000000 : ℝ)*(sp6) + (888093728133119/100000000000000 : ℝ)*(sp7) + (888093728133119/100000000000000 : ℝ)*(f.failure) + (488240710298537/25000000000000 : ℝ)*(f.sum) + (325171089646441/59492500000000000000000000000 : ℝ)*base66 + (1862032581640341311/951880000000000000000000000000000 : ℝ)*base67 + (7670298681056581311/951880000000000000000000000000000 : ℝ)*base69 + (2040089868425778689/951880000000000000000000000000000 : ℝ)*base72 + (97680899138637/118985000000000000000000000000 : ℝ)*base74 + (1458364083966661311/951880000000000000000000000000000 : ℝ)*base75 + (4678357634013458689/951880000000000000000000000000000 : ℝ)*base78 + (6828342577247218689/951880000000000000000000000000000 : ℝ)*base80 + (157289250045947/29746250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17888059/5000000000000000000000 : ℝ)*base89 + (17888059/5000000000000000000000 : ℝ)*base91 + (17888059/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1469_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18829/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1469_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1469_s2_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-240970563/1250000000 : ℝ)*x 0 + (5473073717/10000000000 : ℝ)*x 1 + (5184699059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240970563/1250000000 : ℝ)^4435 ≤ (470417472717/4000000000000 : ℝ)^3411 := by
    have hnat : (240970563 : ℕ)^4435*4000000000000^3411 ≤ 470417472717^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240970563 1250000000 470417472717 4000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473073717/10000000000 : ℝ)^4435 ≤ (365373423301/800000000000 : ℝ)^3411 := by
    have hnat : (5473073717 : ℕ)^4435*800000000000^3411 ≤ 365373423301^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473073717 10000000000 365373423301 800000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184699059/10000000000 : ℝ)^4435 ≤ (4256788525393/10000000000000 : ℝ)^3411 := by
    have hnat : (5184699059 : ℕ)^4435*10000000000000^3411 ≤ 4256788525393^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184699059 10000000000 4256788525393 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240970563/1250000000 : ℝ), (5473073717/10000000000 : ℝ), (5184699059/10000000000 : ℝ)] ![(470417472717/4000000000000 : ℝ), (365373423301/800000000000 : ℝ), (4256788525393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240970563/1250000000 : ℝ)|^4435 ≤ (470417472717/4000000000000 : ℝ)^3411
        have hw : |(-240970563/1250000000 : ℝ)|=(240970563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473073717/10000000000 : ℝ)|^4435 ≤ (365373423301/800000000000 : ℝ)^3411
        have hw : |(5473073717/10000000000 : ℝ)|=(5473073717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184699059/10000000000 : ℝ)|^4435 ≤ (4256788525393/10000000000000 : ℝ)^3411
        have hw : |(5184699059/10000000000 : ℝ)|=(5184699059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362660467/10000000000 : ℝ)*x 0 + (-2076639049/10000000000 : ℝ)*x 1 + (1296175091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362660467/10000000000 : ℝ)^4435 ≤ (11119336250263/25000000000000 : ℝ)^3411 := by
    have hnat : (5362660467 : ℕ)^4435*25000000000000^3411 ≤ 11119336250263^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362660467 10000000000 11119336250263 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076639049/10000000000 : ℝ)^4435 ≤ (12954755803689/100000000000000 : ℝ)^3411 := by
    have hnat : (2076639049 : ℕ)^4435*100000000000000^3411 ≤ 12954755803689^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076639049 10000000000 12954755803689 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296175091/2500000000 : ℝ)^4435 ≤ (42567899184887/100000000000000 : ℝ)^3411 := by
    have hnat : (1296175091 : ℕ)^4435*100000000000000^3411 ≤ 42567899184887^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296175091 2500000000 42567899184887 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362660467/10000000000 : ℝ), (-2076639049/10000000000 : ℝ), (1296175091/2500000000 : ℝ)] ![(11119336250263/25000000000000 : ℝ), (12954755803689/100000000000000 : ℝ), (42567899184887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362660467/10000000000 : ℝ)|^4435 ≤ (11119336250263/25000000000000 : ℝ)^3411
        have hw : |(5362660467/10000000000 : ℝ)|=(5362660467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076639049/10000000000 : ℝ)|^4435 ≤ (12954755803689/100000000000000 : ℝ)^3411
        have hw : |(-2076639049/10000000000 : ℝ)|=(2076639049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296175091/2500000000 : ℝ)|^4435 ≤ (42567899184887/100000000000000 : ℝ)^3411
        have hw : |(1296175091/2500000000 : ℝ)|=(1296175091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536266131/1000000000 : ℝ)*x 0 + (5184699671/10000000000 : ℝ)*x 1 + (-51915971/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536266131/1000000000 : ℝ)^4435 ≤ (44477354091767/100000000000000 : ℝ)^3411 := by
    have hnat : (536266131 : ℕ)^4435*100000000000000^3411 ≤ 44477354091767^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536266131 1000000000 44477354091767 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184699671/10000000000 : ℝ)^4435 ≤ (10641972946767/25000000000000 : ℝ)^3411 := by
    have hnat : (5184699671 : ℕ)^4435*25000000000000^3411 ≤ 10641972946767^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184699671 10000000000 10641972946767 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51915971/250000000 : ℝ)^4435 ≤ (3238688527117/25000000000000 : ℝ)^3411 := by
    have hnat : (51915971 : ℕ)^4435*25000000000000^3411 ≤ 3238688527117^3411*250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51915971 250000000 3238688527117 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536266131/1000000000 : ℝ), (5184699671/10000000000 : ℝ), (-51915971/250000000 : ℝ)] ![(44477354091767/100000000000000 : ℝ), (10641972946767/25000000000000 : ℝ), (3238688527117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536266131/1000000000 : ℝ)|^4435 ≤ (44477354091767/100000000000000 : ℝ)^3411
        have hw : |(536266131/1000000000 : ℝ)|=(536266131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184699671/10000000000 : ℝ)|^4435 ≤ (10641972946767/25000000000000 : ℝ)^3411
        have hw : |(5184699671/10000000000 : ℝ)|=(5184699671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51915971/250000000 : ℝ)|^4435 ≤ (3238688527117/25000000000000 : ℝ)^3411
        have hw : |(-51915971/250000000 : ℝ)|=(51915971/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143279017/5000000000 : ℝ)*x 0 + (795958773/2000000000 : ℝ)*x 1 + (2306971591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143279017/5000000000 : ℝ)^4435 ≤ (3324036792113/10000000000000 : ℝ)^3411 := by
    have hnat : (2143279017 : ℕ)^4435*10000000000000^3411 ≤ 3324036792113^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143279017 5000000000 3324036792113 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795958773/2000000000 : ℝ)^4435 ≤ (6036241840487/20000000000000 : ℝ)^3411 := by
    have hnat : (795958773 : ℕ)^4435*20000000000000^3411 ≤ 6036241840487^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795958773 2000000000 6036241840487 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2306971591/5000000000 : ℝ)^4435 ≤ (9144605715151/25000000000000 : ℝ)^3411 := by
    have hnat : (2306971591 : ℕ)^4435*25000000000000^3411 ≤ 9144605715151^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306971591 5000000000 9144605715151 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143279017/5000000000 : ℝ), (795958773/2000000000 : ℝ), (2306971591/5000000000 : ℝ)] ![(3324036792113/10000000000000 : ℝ), (6036241840487/20000000000000 : ℝ), (9144605715151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143279017/5000000000 : ℝ)|^4435 ≤ (3324036792113/10000000000000 : ℝ)^3411
        have hw : |(2143279017/5000000000 : ℝ)|=(2143279017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795958773/2000000000 : ℝ)|^4435 ≤ (6036241840487/20000000000000 : ℝ)^3411
        have hw : |(795958773/2000000000 : ℝ)|=(795958773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2306971591/5000000000 : ℝ)|^4435 ≤ (9144605715151/25000000000000 : ℝ)^3411
        have hw : |(2306971591/5000000000 : ℝ)|=(2306971591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1927830189/10000000000 : ℝ)*x 0 + (5186593219/10000000000 : ℝ)*x 1 + (1094232373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1927830189/10000000000 : ℝ)^4435 ≤ (11760957832417/100000000000000 : ℝ)^3411 := by
    have hnat : (1927830189 : ℕ)^4435*100000000000000^3411 ≤ 11760957832417^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927830189 10000000000 11760957832417 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186593219/10000000000 : ℝ)^4435 ≤ (10647026659769/25000000000000 : ℝ)^3411 := by
    have hnat : (5186593219 : ℕ)^4435*25000000000000^3411 ≤ 10647026659769^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186593219 10000000000 10647026659769 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094232373/2000000000 : ℝ)^4435 ≤ (5706366938691/12500000000000 : ℝ)^3411 := by
    have hnat : (1094232373 : ℕ)^4435*12500000000000^3411 ≤ 5706366938691^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094232373 2000000000 5706366938691 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1927830189/10000000000 : ℝ), (5186593219/10000000000 : ℝ), (1094232373/2000000000 : ℝ)] ![(11760957832417/100000000000000 : ℝ), (10647026659769/25000000000000 : ℝ), (5706366938691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1927830189/10000000000 : ℝ)|^4435 ≤ (11760957832417/100000000000000 : ℝ)^3411
        have hw : |(-1927830189/10000000000 : ℝ)|=(1927830189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186593219/10000000000 : ℝ)|^4435 ≤ (10647026659769/25000000000000 : ℝ)^3411
        have hw : |(5186593219/10000000000 : ℝ)|=(5186593219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094232373/2000000000 : ℝ)|^4435 ≤ (5706366938691/12500000000000 : ℝ)^3411
        have hw : |(1094232373/2000000000 : ℝ)|=(1094232373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287456791/10000000000 : ℝ)*x 0 + (-55943023/312500000 : ℝ)*x 1 + (5471161793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287456791/10000000000 : ℝ)^4435 ≤ (43668078858563/100000000000000 : ℝ)^3411 := by
    have hnat : (5287456791 : ℕ)^4435*100000000000000^3411 ≤ 43668078858563^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287456791 10000000000 43668078858563 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55943023/312500000 : ℝ)^4435 ≤ (213619728059/2000000000000 : ℝ)^3411 := by
    have hnat : (55943023 : ℕ)^4435*2000000000000^3411 ≤ 213619728059^3411*312500000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55943023 312500000 213619728059 2000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471161793/10000000000 : ℝ)^4435 ≤ (22825467364207/50000000000000 : ℝ)^3411 := by
    have hnat : (5471161793 : ℕ)^4435*50000000000000^3411 ≤ 22825467364207^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471161793 10000000000 22825467364207 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287456791/10000000000 : ℝ), (-55943023/312500000 : ℝ), (5471161793/10000000000 : ℝ)] ![(43668078858563/100000000000000 : ℝ), (213619728059/2000000000000 : ℝ), (22825467364207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287456791/10000000000 : ℝ)|^4435 ≤ (43668078858563/100000000000000 : ℝ)^3411
        have hw : |(5287456791/10000000000 : ℝ)|=(5287456791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55943023/312500000 : ℝ)|^4435 ≤ (213619728059/2000000000000 : ℝ)^3411
        have hw : |(-55943023/312500000 : ℝ)|=(55943023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471161793/10000000000 : ℝ)|^4435 ≤ (22825467364207/50000000000000 : ℝ)^3411
        have hw : |(5471161793/10000000000 : ℝ)|=(5471161793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_6 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287456551/10000000000 : ℝ)*x 0 + (5471161819/10000000000 : ℝ)*x 1 + (-179017703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287456551/10000000000 : ℝ)^4435 ≤ (43668076281409/100000000000000 : ℝ)^3411 := by
    have hnat : (5287456551 : ℕ)^4435*100000000000000^3411 ≤ 43668076281409^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287456551 10000000000 43668076281409 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471161819/10000000000 : ℝ)^4435 ≤ (45650935010483/100000000000000 : ℝ)^3411 := by
    have hnat : (5471161819 : ℕ)^4435*100000000000000^3411 ≤ 45650935010483^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471161819 10000000000 45650935010483 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179017703/1000000000 : ℝ)^4435 ≤ (2136197736737/20000000000000 : ℝ)^3411 := by
    have hnat : (179017703 : ℕ)^4435*20000000000000^3411 ≤ 2136197736737^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179017703 1000000000 2136197736737 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287456551/10000000000 : ℝ), (5471161819/10000000000 : ℝ), (-179017703/1000000000 : ℝ)] ![(43668076281409/100000000000000 : ℝ), (45650935010483/100000000000000 : ℝ), (2136197736737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287456551/10000000000 : ℝ)|^4435 ≤ (43668076281409/100000000000000 : ℝ)^3411
        have hw : |(5287456551/10000000000 : ℝ)|=(5287456551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471161819/10000000000 : ℝ)|^4435 ≤ (45650935010483/100000000000000 : ℝ)^3411
        have hw : |(5471161819/10000000000 : ℝ)|=(5471161819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179017703/1000000000 : ℝ)|^4435 ≤ (2136197736737/20000000000000 : ℝ)^3411
        have hw : |(-179017703/1000000000 : ℝ)|=(179017703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s2_7 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143351859/5000000000 : ℝ)*x 0 + (1152444587/2500000000 : ℝ)*x 1 + (3983997499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143351859/5000000000 : ℝ)^4435 ≤ (1662091839511/5000000000000 : ℝ)^3411 := by
    have hnat : (2143351859 : ℕ)^4435*5000000000000^3411 ≤ 1662091839511^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143351859 5000000000 1662091839511 5000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152444587/2500000000 : ℝ)^4435 ≤ (36535498535529/100000000000000 : ℝ)^3411 := by
    have hnat : (1152444587 : ℕ)^4435*100000000000000^3411 ≤ 36535498535529^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152444587 2500000000 36535498535529 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983997499/10000000000 : ℝ)^4435 ≤ (30222664657907/100000000000000 : ℝ)^3411 := by
    have hnat : (3983997499 : ℕ)^4435*100000000000000^3411 ≤ 30222664657907^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983997499 10000000000 30222664657907 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143351859/5000000000 : ℝ), (1152444587/2500000000 : ℝ), (3983997499/10000000000 : ℝ)] ![(1662091839511/5000000000000 : ℝ), (36535498535529/100000000000000 : ℝ), (30222664657907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143351859/5000000000 : ℝ)|^4435 ≤ (1662091839511/5000000000000 : ℝ)^3411
        have hw : |(2143351859/5000000000 : ℝ)|=(2143351859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1152444587/2500000000 : ℝ)|^4435 ≤ (36535498535529/100000000000000 : ℝ)^3411
        have hw : |(1152444587/2500000000 : ℝ)|=(1152444587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983997499/10000000000 : ℝ)|^4435 ≤ (30222664657907/100000000000000 : ℝ)^3411
        have hw : |(3983997499/10000000000 : ℝ)|=(3983997499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5043/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2023/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18829/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18829/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18829/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7741/100000 : ℝ) ^ (4433/1024 : ℝ) ≤ (773498815198231/50000000000000000000 : ℝ) := by
    have hpowers : (7741/100000 : ℝ)^4433 ≤ (773498815198231/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4433*50000000000000000000^1024 ≤ 773498815198231^1024*100000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 100000 773498815198231 50000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/100000 : ℝ)) (X := (773498815198231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18829/100000 : ℝ) ^ (4433/1024 : ℝ) ≤ (14510538642906399/20000000000000000000 : ℝ) := by
    have hpowers : (18829/100000 : ℝ)^4433 ≤ (14510538642906399/20000000000000000000 : ℝ)^1024 := by
      have hnat : (18829 : ℕ)^4433*20000000000000000000^1024 ≤ 14510538642906399^1024*100000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18829 100000 14510538642906399 20000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18829/100000 : ℝ)) (X := (14510538642906399/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000773498815198231/25000000000000000000 : ℝ) ≤ (5000035734417513/5000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (25000773498815198231/25000000000000000000 : ℝ)^1024 ≤ (5000035734417513/5000000000000000 : ℝ)^4433 := by
      have hnat : (25000773498815198231 : ℕ)^1024*5000000000000000^4433 ≤ 5000035734417513^4433*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000773498815198231 25000000000000000000 5000035734417513 5000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035734417513/5000000000000000 : ℝ)) (X := (25000773498815198231/25000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074099690844928457/100000000000000000000 : ℝ) ≤ (10001711176946643/10000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (100074099690844928457/100000000000000000000 : ℝ)^1024 ≤ (10001711176946643/10000000000000000 : ℝ)^4433 := by
      have hnat : (100074099690844928457 : ℕ)^1024*10000000000000000^4433 ≤ 10001711176946643^4433*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074099690844928457 100000000000000000000 10001711176946643 10000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001711176946643/10000000000000000 : ℝ)) (X := (100074099690844928457/100000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014510538642906399/10000000000000000000 : ℝ) ≤ (500167544252913/500000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (10014510538642906399/10000000000000000000 : ℝ)^1024 ≤ (500167544252913/500000000000000 : ℝ)^4433 := by
      have hnat : (10014510538642906399 : ℕ)^1024*500000000000000^4433 ≤ 500167544252913^4433*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014510538642906399 10000000000000000000 500167544252913 500000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500167544252913/500000000000000 : ℝ)) (X := (10014510538642906399/10000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(773498815198231/50000000000000000000 : ℝ) ≤ ((18475901080909785649/18480000000000000000 : ℝ)+2*(546569370539/369600000000000 : ℝ)*(7741/100000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (18475901080909785649/18480000000000000000 : ℝ)+2*(546569370539/369600000000000 : ℝ)*(7741/100000 : ℝ)=(5000035734417513/5000000000000000 : ℝ) by norm_num, show 1+2*(773498815198231/50000000000000000000 : ℝ)=(25000773498815198231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14510538642906399/20000000000000000000 : ℝ)+(773498815198231/50000000000000000000 : ℝ) ≤ ((18475901080909785649/18480000000000000000 : ℝ)+(546569370539/369600000000000 : ℝ)*((18829/100000 : ℝ)+(7741/100000 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (18475901080909785649/18480000000000000000 : ℝ)+(546569370539/369600000000000 : ℝ)*((18829/100000 : ℝ)+(7741/100000 : ℝ))=(10001711176946643/10000000000000000 : ℝ) by norm_num, show 1+(14510538642906399/20000000000000000000 : ℝ)+(773498815198231/50000000000000000000 : ℝ)=(100074099690844928457/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14510538642906399/20000000000000000000 : ℝ) ≤ ((18475901080909785649/18480000000000000000 : ℝ)+2*(546569370539/369600000000000 : ℝ)*(18829/100000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (18475901080909785649/18480000000000000000 : ℝ)+2*(546569370539/369600000000000 : ℝ)*(18829/100000 : ℝ)=(500167544252913/500000000000000 : ℝ) by norm_num, show 1+2*(14510538642906399/20000000000000000000 : ℝ)=(10014510538642906399/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18475901080909785649/18480000000000000000 : ℝ)*(X 1 0+X 2 0)+(546569370539/369600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (7741/100000 : ℝ)) (hi := (18829/100000 : ℝ)) (c := (18475901080909785649/18480000000000000000 : ℝ)) (alpha := (546569370539/369600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18475901080909785649/18480000000000000000 : ℝ)*(X 0 1+X 2 1)+(546569370539/369600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (7741/100000 : ℝ)) (hi := (18829/100000 : ℝ)) (c := (18475901080909785649/18480000000000000000 : ℝ)) (alpha := (546569370539/369600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18475901080909785649/18480000000000000000 : ℝ)*(X 0 2+X 1 2)+(546569370539/369600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (7741/100000 : ℝ)) (hi := (18829/100000 : ℝ)) (c := (18475901080909785649/18480000000000000000 : ℝ)) (alpha := (546569370539/369600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240970563/1250000000 : ℝ)*X 0 0+(5473073717/10000000000 : ℝ)*X 0 1+(5184699059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362660467/10000000000 : ℝ)*X 1 0+(-2076639049/10000000000 : ℝ)*X 1 1+(1296175091/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536266131/1000000000 : ℝ)*X 2 0+(5184699671/10000000000 : ℝ)*X 2 1+(-51915971/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143279017/5000000000 : ℝ)*X 0 0+(795958773/2000000000 : ℝ)*X 0 1+(2306971591/5000000000 : ℝ)*X 0 2+(2143279017/5000000000 : ℝ)*X 1 0+(795958773/2000000000 : ℝ)*X 1 1+(2306971591/5000000000 : ℝ)*X 1 2+(2143279017/5000000000 : ℝ)*X 2 0+(795958773/2000000000 : ℝ)*X 2 1+(2306971591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1927830189/10000000000 : ℝ)*X 0 0+(5186593219/10000000000 : ℝ)*X 0 1+(1094232373/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287456791/10000000000 : ℝ)*X 1 0+(-55943023/312500000 : ℝ)*X 1 1+(5471161793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287456551/10000000000 : ℝ)*X 2 0+(5471161819/10000000000 : ℝ)*X 2 1+(-179017703/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143351859/5000000000 : ℝ)*X 0 0+(1152444587/2500000000 : ℝ)*X 0 1+(3983997499/10000000000 : ℝ)*X 0 2+(2143351859/5000000000 : ℝ)*X 1 0+(1152444587/2500000000 : ℝ)*X 1 1+(3983997499/10000000000 : ℝ)*X 1 2+(2143351859/5000000000 : ℝ)*X 2 0+(1152444587/2500000000 : ℝ)*X 2 1+(3983997499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1644221648818430935768053/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465457189/100000000000000 : ℝ)*(base19) + (329725467/50000000000000 : ℝ)*(base23) + (4795213/6250000000000 : ℝ)*(upper3) + (37659761/20000000000000 : ℝ)*(upper4) + (39171803/50000000000000 : ℝ)*(upper5) + (630584653649769/25000000000000 : ℝ)*(major0) + (630584653649769/25000000000000 : ℝ)*(major1) + (630584653649769/25000000000000 : ℝ)*(major2) + (866931651991481/25000000000000 : ℝ)*(sp0) + (3467747085863997/100000000000000 : ℝ)*(sp1) + (866936722967563/25000000000000 : ℝ)*(sp2) + (788460847372161/50000000000000 : ℝ)*(sp3) + (10471677631/50000000000000 : ℝ)*(sp4) + (7873517863/100000000000000 : ℝ)*(sp7) + (315385913652437/20000000000000 : ℝ)*(f.failure) + (1733873775660593/50000000000000 : ℝ)*(f.sum) + (633078373111/220000000000000000000000000 : ℝ)*base65 + (77832357752242139/22000000000000000000000000000000 : ℝ)*base68 + (227599197986242139/22000000000000000000000000000000 : ℝ)*base70 + (142054789454242139/22000000000000000000000000000000 : ℝ)*base72 + (705180153851/220000000000000000000000000 : ℝ)*base73 + (47904204750242139/22000000000000000000000000000000 : ℝ)*base76 + (18768653083757861/22000000000000000000000000000000 : ℝ)*base77 + (114042140284242139/22000000000000000000000000000000 : ℝ)*base80 + (1030785629349/220000000000000000000000000 : ℝ)*base82 + (4798057/1000000000000000000000 : ℝ)*base89 + (4798057/1000000000000000000000 : ℝ)*base91 + (4798057/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22335939729169418231363443/2750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1733652159/100000000000000 : ℝ)*(base19) + (801769563/50000000000000 : ℝ)*(base23) + (174711873/100000000000000 : ℝ)*(upper3) + (3804029/10000000000000 : ℝ)*(lower4) + (16495021/10000000000000 : ℝ)*(upper5) + (319505767182749/12500000000000 : ℝ)*(major0) + (319505767182749/12500000000000 : ℝ)*(major1) + (319505767182749/12500000000000 : ℝ)*(major2) + (20426125153/100000000000000 : ℝ)*(sp1) + (17434145849/100000000000000 : ℝ)*(sp2) + (1757044490424717/50000000000000 : ℝ)*(sp4) + (1757033410536061/50000000000000 : ℝ)*(sp5) + (3514069943164459/100000000000000 : ℝ)*(sp6) + (799001511667941/50000000000000 : ℝ)*(sp7) + (799001511667941/50000000000000 : ℝ)*(f.failure) + (1757044490424717/50000000000000 : ℝ)*(f.sum) + (2347478399173/330000000000000000000000000 : ℝ)*base65 + (100385013579411557/33000000000000000000000000000000 : ℝ)*base68 + (168524157597411557/33000000000000000000000000000000 : ℝ)*base70 + (86343993269588443/33000000000000000000000000000000 : ℝ)*base71 + (1255777878163/330000000000000000000000000 : ℝ)*base73 + (117204406521411557/33000000000000000000000000000000 : ℝ)*base76 + (190269139548411557/33000000000000000000000000000000 : ℝ)*base78 + (111952125861411557/33000000000000000000000000000000 : ℝ)*base80 + (417255289633/330000000000000000000000000 : ℝ)*base81 + (5251399/2500000000000000000000 : ℝ)*base90 + (5251399/2500000000000000000000 : ℝ)*base92 + (5251399/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1469_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18829/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1469_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1469_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1469_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1469_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1469_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5043/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2023/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1469_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

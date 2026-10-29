-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:01.139275+00:00
-- url     : https://prove2.me/submissions/eb6739cb-be49-47b0-a81c-ecad1216766a

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
theorem support_rectangle_w1591_s3_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-876551553/5000000000 : ℝ)*x 0 + (5466322699/10000000000 : ℝ)*x 1 + (5177930589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876551553/5000000000 : ℝ)^4683 ≤ (2153827957573/20000000000000 : ℝ)^3659 := by
    have hnat : (876551553 : ℕ)^4683*20000000000000^3659 ≤ 2153827957573^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876551553 5000000000 2153827957573 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466322699/10000000000 : ℝ)^4683 ≤ (46162276538573/100000000000000 : ℝ)^3659 := by
    have hnat : (5466322699 : ℕ)^4683*100000000000000^3659 ≤ 46162276538573^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466322699 10000000000 46162276538573 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177930589/10000000000 : ℝ)^4683 ≤ (10767145915651/25000000000000 : ℝ)^3659 := by
    have hnat : (5177930589 : ℕ)^4683*25000000000000^3659 ≤ 10767145915651^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177930589 10000000000 10767145915651 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-876551553/5000000000 : ℝ), (5466322699/10000000000 : ℝ), (5177930589/10000000000 : ℝ)] ![(2153827957573/20000000000000 : ℝ), (46162276538573/100000000000000 : ℝ), (10767145915651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-876551553/5000000000 : ℝ)|^4683 ≤ (2153827957573/20000000000000 : ℝ)^3659
        have hw : |(-876551553/5000000000 : ℝ)|=(876551553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466322699/10000000000 : ℝ)|^4683 ≤ (46162276538573/100000000000000 : ℝ)^3659
        have hw : |(5466322699/10000000000 : ℝ)|=(5466322699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177930589/10000000000 : ℝ)|^4683 ≤ (10767145915651/25000000000000 : ℝ)^3659
        have hw : |(5177930589/10000000000 : ℝ)|=(5177930589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356461831/10000000000 : ℝ)*x 0 + (-1901971547/10000000000 : ℝ)*x 1 + (1035586121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356461831/10000000000 : ℝ)^4683 ≤ (44978232933239/100000000000000 : ℝ)^3659 := by
    have hnat : (5356461831 : ℕ)^4683*100000000000000^3659 ≤ 44978232933239^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356461831 10000000000 44978232933239 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901971547/10000000000 : ℝ)^4683 ≤ (5976591607239/50000000000000 : ℝ)^3659 := by
    have hnat : (1901971547 : ℕ)^4683*50000000000000^3659 ≤ 5976591607239^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901971547 10000000000 5976591607239 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035586121/2000000000 : ℝ)^4683 ≤ (10767145958233/25000000000000 : ℝ)^3659 := by
    have hnat : (1035586121 : ℕ)^4683*25000000000000^3659 ≤ 10767145958233^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035586121 2000000000 10767145958233 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356461831/10000000000 : ℝ), (-1901971547/10000000000 : ℝ), (1035586121/2000000000 : ℝ)] ![(44978232933239/100000000000000 : ℝ), (5976591607239/50000000000000 : ℝ), (10767145958233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356461831/10000000000 : ℝ)|^4683 ≤ (44978232933239/100000000000000 : ℝ)^3659
        have hw : |(5356461831/10000000000 : ℝ)|=(5356461831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901971547/10000000000 : ℝ)|^4683 ≤ (5976591607239/50000000000000 : ℝ)^3659
        have hw : |(-1901971547/10000000000 : ℝ)|=(1901971547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035586121/2000000000 : ℝ)|^4683 ≤ (10767145958233/25000000000000 : ℝ)^3659
        have hw : |(1035586121/2000000000 : ℝ)|=(1035586121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071292367/2000000000 : ℝ)*x 0 + (258896529/500000000 : ℝ)*x 1 + (-76078863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071292367/2000000000 : ℝ)^4683 ≤ (44978232976227/100000000000000 : ℝ)^3659 := by
    have hnat : (1071292367 : ℕ)^4683*100000000000000^3659 ≤ 44978232976227^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071292367 2000000000 44978232976227 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258896529/500000000 : ℝ)^4683 ≤ (8613716713359/20000000000000 : ℝ)^3659 := by
    have hnat : (258896529 : ℕ)^4683*20000000000000^3659 ≤ 8613716713359^3659*500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258896529 500000000 8613716713359 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76078863/400000000 : ℝ)^4683 ≤ (5976591719847/50000000000000 : ℝ)^3659 := by
    have hnat : (76078863 : ℕ)^4683*50000000000000^3659 ≤ 5976591719847^3659*400000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76078863 400000000 5976591719847 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071292367/2000000000 : ℝ), (258896529/500000000 : ℝ), (-76078863/400000000 : ℝ)] ![(44978232976227/100000000000000 : ℝ), (8613716713359/20000000000000 : ℝ), (5976591719847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071292367/2000000000 : ℝ)|^4683 ≤ (44978232976227/100000000000000 : ℝ)^3659
        have hw : |(1071292367/2000000000 : ℝ)|=(1071292367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258896529/500000000 : ℝ)|^4683 ≤ (8613716713359/20000000000000 : ℝ)^3659
        have hw : |(258896529/500000000 : ℝ)|=(258896529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76078863/400000000 : ℝ)|^4683 ≤ (5976591719847/50000000000000 : ℝ)^3659
        have hw : |(-76078863/400000000 : ℝ)|=(76078863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114181307/5000000000 : ℝ)*x 0 + (1947033547/5000000000 : ℝ)*x 1 + (4585048079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114181307/5000000000 : ℝ)^4683 ≤ (16615888837497/50000000000000 : ℝ)^3659 := by
    have hnat : (2114181307 : ℕ)^4683*50000000000000^3659 ≤ 16615888837497^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114181307 5000000000 16615888837497 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947033547/5000000000 : ℝ)^4683 ≤ (29907120490969/100000000000000 : ℝ)^3659 := by
    have hnat : (1947033547 : ℕ)^4683*100000000000000^3659 ≤ 29907120490969^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947033547 5000000000 29907120490969 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4585048079/10000000000 : ℝ)^4683 ≤ (36861101819237/100000000000000 : ℝ)^3659 := by
    have hnat : (4585048079 : ℕ)^4683*100000000000000^3659 ≤ 36861101819237^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585048079 10000000000 36861101819237 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114181307/5000000000 : ℝ), (1947033547/5000000000 : ℝ), (4585048079/10000000000 : ℝ)] ![(16615888837497/50000000000000 : ℝ), (29907120490969/100000000000000 : ℝ), (36861101819237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114181307/5000000000 : ℝ)|^4683 ≤ (16615888837497/50000000000000 : ℝ)^3659
        have hw : |(2114181307/5000000000 : ℝ)|=(2114181307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1947033547/5000000000 : ℝ)|^4683 ≤ (29907120490969/100000000000000 : ℝ)^3659
        have hw : |(1947033547/5000000000 : ℝ)|=(1947033547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4585048079/10000000000 : ℝ)|^4683 ≤ (36861101819237/100000000000000 : ℝ)^3659
        have hw : |(4585048079/10000000000 : ℝ)|=(4585048079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8765891/50000000 : ℝ)*x 0 + (2590034633/5000000000 : ℝ)*x 1 + (683020169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8765891/50000000 : ℝ)^4683 ≤ (10769730183509/100000000000000 : ℝ)^3659 := by
    have hnat : (8765891 : ℕ)^4683*100000000000000^3659 ≤ 10769730183509^3659*50000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8765891 50000000 10769730183509 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590034633/5000000000 : ℝ)^4683 ≤ (10772838066733/25000000000000 : ℝ)^3659 := by
    have hnat : (2590034633 : ℕ)^4683*25000000000000^3659 ≤ 10772838066733^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590034633 5000000000 10772838066733 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683020169/1250000000 : ℝ)^4683 ≤ (46138917542867/100000000000000 : ℝ)^3659 := by
    have hnat : (683020169 : ℕ)^4683*100000000000000^3659 ≤ 46138917542867^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683020169 1250000000 46138917542867 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8765891/50000000 : ℝ), (2590034633/5000000000 : ℝ), (683020169/1250000000 : ℝ)] ![(10769730183509/100000000000000 : ℝ), (10772838066733/25000000000000 : ℝ), (46138917542867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8765891/50000000 : ℝ)|^4683 ≤ (10769730183509/100000000000000 : ℝ)^3659
        have hw : |(-8765891/50000000 : ℝ)|=(8765891/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590034633/5000000000 : ℝ)|^4683 ≤ (10772838066733/25000000000000 : ℝ)^3659
        have hw : |(2590034633/5000000000 : ℝ)|=(2590034633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683020169/1250000000 : ℝ)|^4683 ≤ (46138917542867/100000000000000 : ℝ)^3659
        have hw : |(683020169/1250000000 : ℝ)|=(683020169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640078131/5000000000 : ℝ)*x 0 + (-403935167/2500000000 : ℝ)*x 1 + (85377523/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640078131/5000000000 : ℝ)^4683 ≤ (4415981939621/10000000000000 : ℝ)^3659 := by
    have hnat : (2640078131 : ℕ)^4683*10000000000000^3659 ≤ 4415981939621^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640078131 5000000000 4415981939621 10000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403935167/2500000000 : ℝ)^4683 ≤ (9701261751753/100000000000000 : ℝ)^3659 := by
    have hnat : (403935167 : ℕ)^4683*100000000000000^3659 ≤ 9701261751753^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403935167 2500000000 9701261751753 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85377523/156250000 : ℝ)^4683 ≤ (11534729709927/25000000000000 : ℝ)^3659 := by
    have hnat : (85377523 : ℕ)^4683*25000000000000^3659 ≤ 11534729709927^3659*156250000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85377523 156250000 11534729709927 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640078131/5000000000 : ℝ), (-403935167/2500000000 : ℝ), (85377523/156250000 : ℝ)] ![(4415981939621/10000000000000 : ℝ), (9701261751753/100000000000000 : ℝ), (11534729709927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640078131/5000000000 : ℝ)|^4683 ≤ (4415981939621/10000000000000 : ℝ)^3659
        have hw : |(2640078131/5000000000 : ℝ)|=(2640078131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403935167/2500000000 : ℝ)|^4683 ≤ (9701261751753/100000000000000 : ℝ)^3659
        have hw : |(-403935167/2500000000 : ℝ)|=(403935167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85377523/156250000 : ℝ)|^4683 ≤ (11534729709927/25000000000000 : ℝ)^3659
        have hw : |(85377523/156250000 : ℝ)|=(85377523/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056031271/2000000000 : ℝ)*x 0 + (2732080629/5000000000 : ℝ)*x 1 + (-1615740839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056031271/2000000000 : ℝ)^4683 ≤ (44159820391673/100000000000000 : ℝ)^3659 := by
    have hnat : (1056031271 : ℕ)^4683*100000000000000^3659 ≤ 44159820391673^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056031271 2000000000 44159820391673 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732080629/5000000000 : ℝ)^4683 ≤ (46138916527007/100000000000000 : ℝ)^3659 := by
    have hnat : (2732080629 : ℕ)^4683*100000000000000^3659 ≤ 46138916527007^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732080629 5000000000 46138916527007 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1615740839/10000000000 : ℝ)^4683 ≤ (9701263065811/100000000000000 : ℝ)^3659 := by
    have hnat : (1615740839 : ℕ)^4683*100000000000000^3659 ≤ 9701263065811^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615740839 10000000000 9701263065811 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056031271/2000000000 : ℝ), (2732080629/5000000000 : ℝ), (-1615740839/10000000000 : ℝ)] ![(44159820391673/100000000000000 : ℝ), (46138916527007/100000000000000 : ℝ), (9701263065811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056031271/2000000000 : ℝ)|^4683 ≤ (44159820391673/100000000000000 : ℝ)^3659
        have hw : |(1056031271/2000000000 : ℝ)|=(1056031271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732080629/5000000000 : ℝ)|^4683 ≤ (46138916527007/100000000000000 : ℝ)^3659
        have hw : |(2732080629/5000000000 : ℝ)|=(2732080629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1615740839/10000000000 : ℝ)|^4683 ≤ (9701263065811/100000000000000 : ℝ)^3659
        have hw : |(-1615740839/10000000000 : ℝ)|=(1615740839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s3_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114271119/5000000000 : ℝ)*x 0 + (91598473/200000000 : ℝ)*x 1 + (3899245601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114271119/5000000000 : ℝ)^4683 ≤ (33233584474831/100000000000000 : ℝ)^3659 := by
    have hnat : (2114271119 : ℕ)^4683*100000000000000^3659 ≤ 33233584474831^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114271119 5000000000 33233584474831 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91598473/200000000 : ℝ)^4683 ≤ (7361676647837/20000000000000 : ℝ)^3659 := by
    have hnat : (91598473 : ℕ)^4683*20000000000000^3659 ≤ 7361676647837^3659*200000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91598473 200000000 7361676647837 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3899245601/10000000000 : ℝ)^4683 ≤ (29958032269433/100000000000000 : ℝ)^3659 := by
    have hnat : (3899245601 : ℕ)^4683*100000000000000^3659 ≤ 29958032269433^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3899245601 10000000000 29958032269433 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114271119/5000000000 : ℝ), (91598473/200000000 : ℝ), (3899245601/10000000000 : ℝ)] ![(33233584474831/100000000000000 : ℝ), (7361676647837/20000000000000 : ℝ), (29958032269433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114271119/5000000000 : ℝ)|^4683 ≤ (33233584474831/100000000000000 : ℝ)^3659
        have hw : |(2114271119/5000000000 : ℝ)|=(2114271119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91598473/200000000 : ℝ)|^4683 ≤ (7361676647837/20000000000000 : ℝ)^3659
        have hw : |(91598473/200000000 : ℝ)|=(91598473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3899245601/10000000000 : ℝ)|^4683 ≤ (29958032269433/100000000000000 : ℝ)^3659
        have hw : |(3899245601/10000000000 : ℝ)|=(3899245601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2057/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16393/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2529/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16581/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2529/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2529/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16581/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2529/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2529/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16581/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2529/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2529/25000 : ℝ) ^ (4679/1024 : ℝ) ≤ (284152215675309/10000000000000000000 : ℝ) := by
    have hpowers : (2529/25000 : ℝ)^4679 ≤ (284152215675309/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2529 : ℕ)^4679*10000000000000000000^1024 ≤ 284152215675309^1024*25000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2529 25000 284152215675309 10000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2529/25000 : ℝ)) (X := (284152215675309/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16581/100000 : ℝ) ^ (4679/1024 : ℝ) ≤ (5434620343163713/20000000000000000000 : ℝ) := by
    have hpowers : (16581/100000 : ℝ)^4679 ≤ (5434620343163713/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16581 : ℕ)^4679*20000000000000000000^1024 ≤ 5434620343163713^1024*100000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16581 100000 5434620343163713 20000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16581/100000 : ℝ)) (X := (5434620343163713/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000284152215675309/5000000000000000000 : ℝ) ≤ (625007773172967/625000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (5000284152215675309/5000000000000000000 : ℝ)^1024 ≤ (625007773172967/625000000000000 : ℝ)^4679 := by
      have hnat : (5000284152215675309 : ℕ)^1024*625000000000000^4679 ≤ 625007773172967^4679*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000284152215675309 5000000000000000000 625007773172967 625000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625007773172967/625000000000000 : ℝ)) (X := (5000284152215675309/5000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006002924774514331/20000000000000000000 : ℝ) ≤ (2000131358719551/2000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (20006002924774514331/20000000000000000000 : ℝ)^1024 ≤ (2000131358719551/2000000000000000 : ℝ)^4679 := by
      have hnat : (20006002924774514331 : ℕ)^1024*2000000000000000^4679 ≤ 2000131358719551^4679*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006002924774514331 20000000000000000000 2000131358719551 2000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131358719551/2000000000000000 : ℝ)) (X := (20006002924774514331/20000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005434620343163713/10000000000000000000 : ℝ) ≤ (5000594608214019/5000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (10005434620343163713/10000000000000000000 : ℝ)^1024 ≤ (5000594608214019/5000000000000000 : ℝ)^4679 := by
      have hnat : (10005434620343163713 : ℕ)^1024*5000000000000000^4679 ≤ 5000594608214019^4679*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005434620343163713 10000000000000000000 5000594608214019 5000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000594608214019/5000000000000000 : ℝ)) (X := (10005434620343163713/10000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(284152215675309/10000000000000000000 : ℝ) ≤ ((2693334669929559201/2693750000000000000 : ℝ)+2*(177474276761/215500000000000 : ℝ)*(2529/25000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (2693334669929559201/2693750000000000000 : ℝ)+2*(177474276761/215500000000000 : ℝ)*(2529/25000 : ℝ)=(625007773172967/625000000000000 : ℝ) by norm_num, show 1+2*(284152215675309/10000000000000000000 : ℝ)=(5000284152215675309/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5434620343163713/20000000000000000000 : ℝ)+(284152215675309/10000000000000000000 : ℝ) ≤ ((2693334669929559201/2693750000000000000 : ℝ)+(177474276761/215500000000000 : ℝ)*((16581/100000 : ℝ)+(2529/25000 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (2693334669929559201/2693750000000000000 : ℝ)+(177474276761/215500000000000 : ℝ)*((16581/100000 : ℝ)+(2529/25000 : ℝ))=(2000131358719551/2000000000000000 : ℝ) by norm_num, show 1+(5434620343163713/20000000000000000000 : ℝ)+(284152215675309/10000000000000000000 : ℝ)=(20006002924774514331/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5434620343163713/20000000000000000000 : ℝ) ≤ ((2693334669929559201/2693750000000000000 : ℝ)+2*(177474276761/215500000000000 : ℝ)*(16581/100000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (2693334669929559201/2693750000000000000 : ℝ)+2*(177474276761/215500000000000 : ℝ)*(16581/100000 : ℝ)=(5000594608214019/5000000000000000 : ℝ) by norm_num, show 1+2*(5434620343163713/20000000000000000000 : ℝ)=(10005434620343163713/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2693334669929559201/2693750000000000000 : ℝ)*(X 1 0+X 2 0)+(177474276761/215500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (2693334669929559201/2693750000000000000 : ℝ)) (alpha := (177474276761/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2693334669929559201/2693750000000000000 : ℝ)*(X 0 1+X 2 1)+(177474276761/215500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (2693334669929559201/2693750000000000000 : ℝ)) (alpha := (177474276761/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2693334669929559201/2693750000000000000 : ℝ)*(X 0 2+X 1 2)+(177474276761/215500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2529/25000 : ℝ)) (hi := (16581/100000 : ℝ)) (c := (2693334669929559201/2693750000000000000 : ℝ)) (alpha := (177474276761/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-876551553/5000000000 : ℝ)*X 0 0+(5466322699/10000000000 : ℝ)*X 0 1+(5177930589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356461831/10000000000 : ℝ)*X 1 0+(-1901971547/10000000000 : ℝ)*X 1 1+(1035586121/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071292367/2000000000 : ℝ)*X 2 0+(258896529/500000000 : ℝ)*X 2 1+(-76078863/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2114181307/5000000000 : ℝ)*X 0 0+(1947033547/5000000000 : ℝ)*X 0 1+(4585048079/10000000000 : ℝ)*X 0 2+(2114181307/5000000000 : ℝ)*X 1 0+(1947033547/5000000000 : ℝ)*X 1 1+(4585048079/10000000000 : ℝ)*X 1 2+(2114181307/5000000000 : ℝ)*X 2 0+(1947033547/5000000000 : ℝ)*X 2 1+(4585048079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8765891/50000000 : ℝ)*X 0 0+(2590034633/5000000000 : ℝ)*X 0 1+(683020169/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640078131/5000000000 : ℝ)*X 1 0+(-403935167/2500000000 : ℝ)*X 1 1+(85377523/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056031271/2000000000 : ℝ)*X 2 0+(2732080629/5000000000 : ℝ)*X 2 1+(-1615740839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2114271119/5000000000 : ℝ)*X 0 0+(91598473/200000000 : ℝ)*X 0 1+(3899245601/10000000000 : ℝ)*X 0 2+(2114271119/5000000000 : ℝ)*X 1 0+(91598473/200000000 : ℝ)*X 1 1+(3899245601/10000000000 : ℝ)*X 1 2+(2114271119/5000000000 : ℝ)*X 2 0+(91598473/200000000 : ℝ)*X 2 1+(3899245601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158362677134275555371963837/26937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125530269/12500000000000 : ℝ)*(base19) + (473394119/50000000000000 : ℝ)*(base23) + (32161979/100000000000000 : ℝ)*(lower2) + (158531291/100000000000000 : ℝ)*(upper3) + (18817919/20000000000000 : ℝ)*(upper5) + (491475339078507/20000000000000 : ℝ)*(major0) + (491475339078507/20000000000000 : ℝ)*(major1) + (491475339078507/20000000000000 : ℝ)*(major2) + (866878404390943/25000000000000 : ℝ)*(sp0) + (1733762093412717/50000000000000 : ℝ)*(sp1) + (866881061069837/25000000000000 : ℝ)*(sp2) + (723611279041493/50000000000000 : ℝ)*(sp3) + (2314700763/20000000000000 : ℝ)*(sp4) + (2722835697/50000000000000 : ℝ)*(sp7) + (72361400187719/5000000000000 : ℝ)*(f.failure) + (1733762595533793/50000000000000 : ℝ)*(f.sum) + (6213633954507/2155000000000000000000000000 : ℝ)*base65 + (17485530233280407/53875000000000000000000000000000 : ℝ)*base67 + (477477818746530407/53875000000000000000000000000000 : ℝ)*base69 + (542815611024780407/53875000000000000000000000000000 : ℝ)*base71 + (4347779776003/2155000000000000000000000000 : ℝ)*base74 + (118862761216280407/53875000000000000000000000000000 : ℝ)*base75 + (307938178261530407/53875000000000000000000000000000 : ℝ)*base77 + (443488547373030407/53875000000000000000000000000000 : ℝ)*base79 + (10988527268687/2155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2236503/500000000000000000000 : ℝ)*base90 + (2236503/500000000000000000000 : ℝ)*base92 + (2236503/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168791319177383980151990517/13468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2161351589/100000000000000 : ℝ)*(base19) + (2251867249/100000000000000 : ℝ)*(base23) + (142497977/50000000000000 : ℝ)*(upper3) + (107989/400000000000 : ℝ)*(lower4) + (293390201/100000000000000 : ℝ)*(upper5) + (249455447652263/10000000000000 : ℝ)*(major0) + (249455447652263/10000000000000 : ℝ)*(major1) + (249455447652263/10000000000000 : ℝ)*(major2) + (25769339933/100000000000000 : ℝ)*(sp1) + (24204684133/100000000000000 : ℝ)*(sp2) + (3519985343052029/100000000000000 : ℝ)*(sp4) + (879989353090127/25000000000000 : ℝ)*(sp5) + (439994860812581/12500000000000 : ℝ)*(sp6) + (734561596128777/50000000000000 : ℝ)*(sp7) + (734561596128777/50000000000000 : ℝ)*(f.failure) + (3519985343052029/100000000000000 : ℝ)*(f.sum) + (6862660440887/1077500000000000000000000000 : ℝ)*base66 + (33358262505215637/26937500000000000000000000000000 : ℝ)*base68 + (30993428754465637/26937500000000000000000000000000 : ℝ)*base70 + (199553787378153137/26937500000000000000000000000000 : ℝ)*base72 + (12240802482489/2155000000000000000000000000 : ℝ)*base74 + (179966263018403137/26937500000000000000000000000000 : ℝ)*base76 + (16300228900403137/26937500000000000000000000000000 : ℝ)*base78 + (287463514624590637/26937500000000000000000000000000 : ℝ)*base80 + (5418741398799/2155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36180551/5000000000000000000000 : ℝ)*base89 + (36180551/5000000000000000000000 : ℝ)*base91 + (36180551/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1591_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1591_s4_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109580191/625000000 : ℝ)*x 0 + (1093085297/2000000000 : ℝ)*x 1 + (2589353781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109580191/625000000 : ℝ)^4683 ≤ (538527729123/5000000000000 : ℝ)^3659 := by
    have hnat : (109580191 : ℕ)^4683*5000000000000^3659 ≤ 538527729123^3659*625000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109580191 625000000 538527729123 5000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093085297/2000000000 : ℝ)^4683 ≤ (46152590293337/100000000000000 : ℝ)^3659 := by
    have hnat : (1093085297 : ℕ)^4683*100000000000000^3659 ≤ 46152590293337^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093085297 2000000000 46152590293337 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589353781/5000000000 : ℝ)^4683 ≤ (21538427551643/50000000000000 : ℝ)^3659 := by
    have hnat : (2589353781 : ℕ)^4683*50000000000000^3659 ≤ 21538427551643^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589353781 5000000000 21538427551643 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109580191/625000000 : ℝ), (1093085297/2000000000 : ℝ), (2589353781/5000000000 : ℝ)] ![(538527729123/5000000000000 : ℝ), (46152590293337/100000000000000 : ℝ), (21538427551643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109580191/625000000 : ℝ)|^4683 ≤ (538527729123/5000000000000 : ℝ)^3659
        have hw : |(-109580191/625000000 : ℝ)|=(109580191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093085297/2000000000 : ℝ)|^4683 ≤ (46152590293337/100000000000000 : ℝ)^3659
        have hw : |(1093085297/2000000000 : ℝ)|=(1093085297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589353781/5000000000 : ℝ)|^4683 ≤ (21538427551643/50000000000000 : ℝ)^3659
        have hw : |(2589353781/5000000000 : ℝ)|=(2589353781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356223021/10000000000 : ℝ)*x 0 + (-1901260851/10000000000 : ℝ)*x 1 + (5178708627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356223021/10000000000 : ℝ)^4683 ≤ (22487833232417/50000000000000 : ℝ)^3659 := by
    have hnat : (5356223021 : ℕ)^4683*50000000000000^3659 ≤ 22487833232417^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356223021 10000000000 22487833232417 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901260851/10000000000 : ℝ)^4683 ≤ (1493433384947/12500000000000 : ℝ)^3659 := by
    have hnat : (1901260851 : ℕ)^4683*12500000000000^3659 ≤ 1493433384947^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901260851 10000000000 1493433384947 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178708627/10000000000 : ℝ)^4683 ≤ (43076866441221/100000000000000 : ℝ)^3659 := by
    have hnat : (5178708627 : ℕ)^4683*100000000000000^3659 ≤ 43076866441221^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178708627 10000000000 43076866441221 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356223021/10000000000 : ℝ), (-1901260851/10000000000 : ℝ), (5178708627/10000000000 : ℝ)] ![(22487833232417/50000000000000 : ℝ), (1493433384947/12500000000000 : ℝ), (43076866441221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356223021/10000000000 : ℝ)|^4683 ≤ (22487833232417/50000000000000 : ℝ)^3659
        have hw : |(5356223021/10000000000 : ℝ)|=(5356223021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901260851/10000000000 : ℝ)|^4683 ≤ (1493433384947/12500000000000 : ℝ)^3659
        have hw : |(-1901260851/10000000000 : ℝ)|=(1901260851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178708627/10000000000 : ℝ)|^4683 ≤ (43076866441221/100000000000000 : ℝ)^3659
        have hw : |(5178708627/10000000000 : ℝ)|=(5178708627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071244663/2000000000 : ℝ)*x 0 + (5178708451/10000000000 : ℝ)*x 1 + (-1901260691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071244663/2000000000 : ℝ)^4683 ≤ (11243917406101/25000000000000 : ℝ)^3659 := by
    have hnat : (1071244663 : ℕ)^4683*25000000000000^3659 ≤ 11243917406101^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071244663 2000000000 11243917406101 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178708451/10000000000 : ℝ)^4683 ≤ (21538432283767/50000000000000 : ℝ)^3659 := by
    have hnat : (5178708451 : ℕ)^4683*50000000000000^3659 ≤ 21538432283767^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178708451 10000000000 21538432283767 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901260691/10000000000 : ℝ)^4683 ≤ (5973732896381/50000000000000 : ℝ)^3659 := by
    have hnat : (1901260691 : ℕ)^4683*50000000000000^3659 ≤ 5973732896381^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901260691 10000000000 5973732896381 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071244663/2000000000 : ℝ), (5178708451/10000000000 : ℝ), (-1901260691/10000000000 : ℝ)] ![(11243917406101/25000000000000 : ℝ), (21538432283767/50000000000000 : ℝ), (5973732896381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071244663/2000000000 : ℝ)|^4683 ≤ (11243917406101/25000000000000 : ℝ)^3659
        have hw : |(1071244663/2000000000 : ℝ)|=(1071244663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178708451/10000000000 : ℝ)|^4683 ≤ (21538432283767/50000000000000 : ℝ)^3659
        have hw : |(5178708451/10000000000 : ℝ)|=(5178708451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901260691/10000000000 : ℝ)|^4683 ≤ (5973732896381/50000000000000 : ℝ)^3659
        have hw : |(-1901260691/10000000000 : ℝ)|=(1901260691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114239549/5000000000 : ℝ)*x 0 + (3896059701/10000000000 : ℝ)*x 1 + (572878797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114239549/5000000000 : ℝ)^4683 ≤ (33232949360473/100000000000000 : ℝ)^3659 := by
    have hnat : (2114239549 : ℕ)^4683*100000000000000^3659 ≤ 33232949360473^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114239549 5000000000 33232949360473 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3896059701/10000000000 : ℝ)^4683 ≤ (29926708291003/100000000000000 : ℝ)^3659 := by
    have hnat : (3896059701 : ℕ)^4683*100000000000000^3659 ≤ 29926708291003^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896059701 10000000000 29926708291003 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572878797/1250000000 : ℝ)^4683 ≤ (1842017116509/5000000000000 : ℝ)^3659 := by
    have hnat : (572878797 : ℕ)^4683*5000000000000^3659 ≤ 1842017116509^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572878797 1250000000 1842017116509 5000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114239549/5000000000 : ℝ), (3896059701/10000000000 : ℝ), (572878797/1250000000 : ℝ)] ![(33232949360473/100000000000000 : ℝ), (29926708291003/100000000000000 : ℝ), (1842017116509/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114239549/5000000000 : ℝ)|^4683 ≤ (33232949360473/100000000000000 : ℝ)^3659
        have hw : |(2114239549/5000000000 : ℝ)|=(2114239549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3896059701/10000000000 : ℝ)|^4683 ≤ (29926708291003/100000000000000 : ℝ)^3659
        have hw : |(3896059701/10000000000 : ℝ)|=(3896059701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572878797/1250000000 : ℝ)|^4683 ≤ (1842017116509/5000000000000 : ℝ)^3659
        have hw : |(572878797/1250000000 : ℝ)|=(572878797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438339267/2500000000 : ℝ)*x 0 + (1036164387/2000000000 : ℝ)*x 1 + (2731644841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438339267/2500000000 : ℝ)^4683 ≤ (1077113648799/10000000000000 : ℝ)^3659 := by
    have hnat : (438339267 : ℕ)^4683*10000000000000^3659 ≤ 1077113648799^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438339267 2500000000 1077113648799 10000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036164387/2000000000 : ℝ)^4683 ≤ (8619873178931/20000000000000 : ℝ)^3659 := by
    have hnat : (1036164387 : ℕ)^4683*20000000000000^3659 ≤ 8619873178931^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036164387 2000000000 8619873178931 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731644841/5000000000 : ℝ)^4683 ≤ (23064748802493/50000000000000 : ℝ)^3659 := by
    have hnat : (2731644841 : ℕ)^4683*50000000000000^3659 ≤ 23064748802493^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731644841 5000000000 23064748802493 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438339267/2500000000 : ℝ), (1036164387/2000000000 : ℝ), (2731644841/5000000000 : ℝ)] ![(1077113648799/10000000000000 : ℝ), (8619873178931/20000000000000 : ℝ), (23064748802493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438339267/2500000000 : ℝ)|^4683 ≤ (1077113648799/10000000000000 : ℝ)^3659
        have hw : |(-438339267/2500000000 : ℝ)|=(438339267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036164387/2000000000 : ℝ)|^4683 ≤ (8619873178931/20000000000000 : ℝ)^3659
        have hw : |(1036164387/2000000000 : ℝ)|=(1036164387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731644841/5000000000 : ℝ)|^4683 ≤ (23064748802493/50000000000000 : ℝ)^3659
        have hw : |(2731644841/5000000000 : ℝ)|=(2731644841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056072579/2000000000 : ℝ)*x 0 + (-404169837/2500000000 : ℝ)*x 1 + (1365822317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056072579/2000000000 : ℝ)^4683 ≤ (44162031188403/100000000000000 : ℝ)^3659 := by
    have hnat : (1056072579 : ℕ)^4683*100000000000000^3659 ≤ 44162031188403^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056072579 2000000000 44162031188403 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404169837/2500000000 : ℝ)^4683 ≤ (2427118917341/25000000000000 : ℝ)^3659 := by
    have hnat : (404169837 : ℕ)^4683*25000000000000^3659 ≤ 2427118917341^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404169837 2500000000 2427118917341 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365822317/2500000000 : ℝ)^4683 ≤ (46129493131083/100000000000000 : ℝ)^3659 := by
    have hnat : (1365822317 : ℕ)^4683*100000000000000^3659 ≤ 46129493131083^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365822317 2500000000 46129493131083 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056072579/2000000000 : ℝ), (-404169837/2500000000 : ℝ), (1365822317/2500000000 : ℝ)] ![(44162031188403/100000000000000 : ℝ), (2427118917341/25000000000000 : ℝ), (46129493131083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056072579/2000000000 : ℝ)|^4683 ≤ (44162031188403/100000000000000 : ℝ)^3659
        have hw : |(1056072579/2000000000 : ℝ)|=(1056072579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404169837/2500000000 : ℝ)|^4683 ≤ (2427118917341/25000000000000 : ℝ)^3659
        have hw : |(-404169837/2500000000 : ℝ)|=(404169837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365822317/2500000000 : ℝ)|^4683 ≤ (46129493131083/100000000000000 : ℝ)^3659
        have hw : |(1365822317/2500000000 : ℝ)|=(1365822317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280362501/10000000000 : ℝ)*x 0 + (5463289681/10000000000 : ℝ)*x 1 + (-1616679317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280362501/10000000000 : ℝ)^4683 ≤ (22081013485509/50000000000000 : ℝ)^3659 := by
    have hnat : (5280362501 : ℕ)^4683*50000000000000^3659 ≤ 22081013485509^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280362501 10000000000 22081013485509 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463289681/10000000000 : ℝ)^4683 ≤ (46129497594179/100000000000000 : ℝ)^3659 := by
    have hnat : (5463289681 : ℕ)^4683*100000000000000^3659 ≤ 46129497594179^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463289681 10000000000 46129497594179 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616679317/10000000000 : ℝ)^4683 ≤ (151694928611/1562500000000 : ℝ)^3659 := by
    have hnat : (1616679317 : ℕ)^4683*1562500000000^3659 ≤ 151694928611^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616679317 10000000000 151694928611 1562500000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280362501/10000000000 : ℝ), (5463289681/10000000000 : ℝ), (-1616679317/10000000000 : ℝ)] ![(22081013485509/50000000000000 : ℝ), (46129497594179/100000000000000 : ℝ), (151694928611/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280362501/10000000000 : ℝ)|^4683 ≤ (22081013485509/50000000000000 : ℝ)^3659
        have hw : |(5280362501/10000000000 : ℝ)|=(5280362501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463289681/10000000000 : ℝ)|^4683 ≤ (46129497594179/100000000000000 : ℝ)^3659
        have hw : |(5463289681/10000000000 : ℝ)|=(5463289681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1616679317/10000000000 : ℝ)|^4683 ≤ (151694928611/1562500000000 : ℝ)^3659
        have hw : |(-1616679317/10000000000 : ℝ)|=(1616679317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s4_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4228656137/10000000000 : ℝ)*x 0 + (1144491151/2500000000 : ℝ)*x 1 + (3901178107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228656137/10000000000 : ℝ)^4683 ≤ (16617365085959/50000000000000 : ℝ)^3659 := by
    have hnat : (4228656137 : ℕ)^4683*50000000000000^3659 ≤ 16617365085959^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228656137 10000000000 16617365085959 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144491151/2500000000 : ℝ)^4683 ≤ (4598529190637/12500000000000 : ℝ)^3659 := by
    have hnat : (1144491151 : ℕ)^4683*12500000000000^3659 ≤ 4598529190637^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144491151 2500000000 4598529190637 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3901178107/10000000000 : ℝ)^4683 ≤ (14988518143133/50000000000000 : ℝ)^3659 := by
    have hnat : (3901178107 : ℕ)^4683*50000000000000^3659 ≤ 14988518143133^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901178107 10000000000 14988518143133 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228656137/10000000000 : ℝ), (1144491151/2500000000 : ℝ), (3901178107/10000000000 : ℝ)] ![(16617365085959/50000000000000 : ℝ), (4598529190637/12500000000000 : ℝ), (14988518143133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228656137/10000000000 : ℝ)|^4683 ≤ (16617365085959/50000000000000 : ℝ)^3659
        have hw : |(4228656137/10000000000 : ℝ)|=(4228656137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144491151/2500000000 : ℝ)|^4683 ≤ (4598529190637/12500000000000 : ℝ)^3659
        have hw : |(1144491151/2500000000 : ℝ)|=(1144491151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3901178107/10000000000 : ℝ)|^4683 ≤ (14988518143133/50000000000000 : ℝ)^3659
        have hw : |(3901178107/10000000000 : ℝ)|=(3901178107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5151/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8187/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2057/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2057/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2057/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2057/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2057/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2057/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2057/20000 : ℝ) ^ (4679/1024 : ℝ) ≤ (766248433413703/25000000000000000000 : ℝ) := by
    have hpowers : (2057/20000 : ℝ)^4679 ≤ (766248433413703/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2057 : ℕ)^4679*25000000000000000000^1024 ≤ 766248433413703^1024*20000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2057 20000 766248433413703 25000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2057/20000 : ℝ)) (X := (766248433413703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16393/100000 : ℝ) ^ (4679/1024 : ℝ) ≤ (25793518094297757/100000000000000000000 : ℝ) := by
    have hpowers : (16393/100000 : ℝ)^4679 ≤ (25793518094297757/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16393 : ℕ)^4679*100000000000000000000^1024 ≤ 25793518094297757^1024*100000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16393 100000 25793518094297757 100000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16393/100000 : ℝ)) (X := (25793518094297757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500766248433413703/12500000000000000000 : ℝ) ≤ (2500033537918809/2500000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (12500766248433413703/12500000000000000000 : ℝ)^1024 ≤ (2500033537918809/2500000000000000 : ℝ)^4679 := by
      have hnat : (12500766248433413703 : ℕ)^1024*2500000000000000^4679 ≤ 2500033537918809^4679*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500766248433413703 12500000000000000000 2500033537918809 2500000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500033537918809/2500000000000000 : ℝ)) (X := (12500766248433413703/12500000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028858511827952569/100000000000000000000 : ℝ) ≤ (500031574894053/500000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (100028858511827952569/100000000000000000000 : ℝ)^1024 ≤ (500031574894053/500000000000000 : ℝ)^4679 := by
      have hnat : (100028858511827952569 : ℕ)^1024*500000000000000^4679 ≤ 500031574894053^4679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028858511827952569 100000000000000000000 500031574894053 500000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500031574894053/500000000000000 : ℝ)) (X := (100028858511827952569/100000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025793518094297757/50000000000000000000 : ℝ) ≤ (2500282211021721/2500000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (50025793518094297757/50000000000000000000 : ℝ)^1024 ≤ (2500282211021721/2500000000000000 : ℝ)^4679 := by
      have hnat : (50025793518094297757 : ℕ)^1024*2500000000000000^4679 ≤ 2500282211021721^4679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025793518094297757 50000000000000000000 2500282211021721 2500000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500282211021721/2500000000000000 : ℝ)) (X := (50025793518094297757/50000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(766248433413703/25000000000000000000 : ℝ) ≤ ((1272303937228719621/1272500000000000000 : ℝ)+2*(1295172411/1590625000000 : ℝ)*(2057/20000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (1272303937228719621/1272500000000000000 : ℝ)+2*(1295172411/1590625000000 : ℝ)*(2057/20000 : ℝ)=(2500033537918809/2500000000000000 : ℝ) by norm_num, show 1+2*(766248433413703/25000000000000000000 : ℝ)=(12500766248433413703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25793518094297757/100000000000000000000 : ℝ)+(766248433413703/25000000000000000000 : ℝ) ≤ ((1272303937228719621/1272500000000000000 : ℝ)+(1295172411/1590625000000 : ℝ)*((16393/100000 : ℝ)+(2057/20000 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (1272303937228719621/1272500000000000000 : ℝ)+(1295172411/1590625000000 : ℝ)*((16393/100000 : ℝ)+(2057/20000 : ℝ))=(500031574894053/500000000000000 : ℝ) by norm_num, show 1+(25793518094297757/100000000000000000000 : ℝ)+(766248433413703/25000000000000000000 : ℝ)=(100028858511827952569/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25793518094297757/100000000000000000000 : ℝ) ≤ ((1272303937228719621/1272500000000000000 : ℝ)+2*(1295172411/1590625000000 : ℝ)*(16393/100000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (1272303937228719621/1272500000000000000 : ℝ)+2*(1295172411/1590625000000 : ℝ)*(16393/100000 : ℝ)=(2500282211021721/2500000000000000 : ℝ) by norm_num, show 1+2*(25793518094297757/100000000000000000000 : ℝ)=(50025793518094297757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1272303937228719621/1272500000000000000 : ℝ)*(X 1 0+X 2 0)+(1295172411/1590625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (1272303937228719621/1272500000000000000 : ℝ)) (alpha := (1295172411/1590625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1272303937228719621/1272500000000000000 : ℝ)*(X 0 1+X 2 1)+(1295172411/1590625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (1272303937228719621/1272500000000000000 : ℝ)) (alpha := (1295172411/1590625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1272303937228719621/1272500000000000000 : ℝ)*(X 0 2+X 1 2)+(1295172411/1590625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (1272303937228719621/1272500000000000000 : ℝ)) (alpha := (1295172411/1590625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109580191/625000000 : ℝ)*X 0 0+(1093085297/2000000000 : ℝ)*X 0 1+(2589353781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356223021/10000000000 : ℝ)*X 1 0+(-1901260851/10000000000 : ℝ)*X 1 1+(5178708627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071244663/2000000000 : ℝ)*X 2 0+(5178708451/10000000000 : ℝ)*X 2 1+(-1901260691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2114239549/5000000000 : ℝ)*X 0 0+(3896059701/10000000000 : ℝ)*X 0 1+(572878797/1250000000 : ℝ)*X 0 2+(2114239549/5000000000 : ℝ)*X 1 0+(3896059701/10000000000 : ℝ)*X 1 1+(572878797/1250000000 : ℝ)*X 1 2+(2114239549/5000000000 : ℝ)*X 2 0+(3896059701/10000000000 : ℝ)*X 2 1+(572878797/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438339267/2500000000 : ℝ)*X 0 0+(1036164387/2000000000 : ℝ)*X 0 1+(2731644841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056072579/2000000000 : ℝ)*X 1 0+(-404169837/2500000000 : ℝ)*X 1 1+(1365822317/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280362501/10000000000 : ℝ)*X 2 0+(5463289681/10000000000 : ℝ)*X 2 1+(-1616679317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4228656137/10000000000 : ℝ)*X 0 0+(1144491151/2500000000 : ℝ)*X 0 1+(3901178107/10000000000 : ℝ)*X 0 2+(4228656137/10000000000 : ℝ)*X 1 0+(1144491151/2500000000 : ℝ)*X 1 1+(3901178107/10000000000 : ℝ)*X 1 2+(4228656137/10000000000 : ℝ)*X 2 0+(1144491151/2500000000 : ℝ)*X 2 1+(3901178107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5378649589498295541177/1272500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14321231/50000000000000 : ℝ)*(base8) + (17736157/100000000000000 : ℝ)*(base21) + (129482443/100000000000000 : ℝ)*(base29) + (60435513/50000000000000 : ℝ)*(lower2) + (10094723/100000000000000 : ℝ)*(lower4) + (1235856935841429/50000000000000 : ℝ)*(major0) + (2471714001165301/100000000000000 : ℝ)*(major1) + (2471714001165301/100000000000000 : ℝ)*(major2) + (217984056783219/6250000000000 : ℝ)*(sp0) + (1743878014341767/50000000000000 : ℝ)*(sp1) + (217984750684211/6250000000000 : ℝ)*(sp2) + (181958562880077/12500000000000 : ℝ)*(sp3) + (1122099201/10000000000000 : ℝ)*(sp4) + (3200229447/100000000000000 : ℝ)*(sp7) + (1455671703270063/100000000000000 : ℝ)*(f.failure) + (435969519770747/12500000000000 : ℝ)*(f.sum) + (35942624461383/2545000000000000000000000000 : ℝ)*base66 + (1621025004185370921/127250000000000000000000000000000 : ℝ)*base67 + (2551183066992620921/127250000000000000000000000000000 : ℝ)*base69 + (348470211244746591/63625000000000000000000000000000 : ℝ)*base72 + (2553223464967/1272500000000000000000000000 : ℝ)*base73 + (571707276753279079/127250000000000000000000000000000 : ℝ)*base76 + (323738397501003409/63625000000000000000000000000000 : ℝ)*base77 + (669660269641529079/127250000000000000000000000000000 : ℝ)*base80 + (7400282765779/2545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (20661631/10000000000000000000000 : ℝ)*base90 + (20661631/10000000000000000000000 : ℝ)*base92 + (20661631/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (482448331989602595321/50900000000000000000000000 : ℝ) := by norm_num
    linear_combination (1410132339/100000000000000 : ℝ)*(base19) + (1468065597/100000000000000 : ℝ)*(base23) + (147168283/50000000000000 : ℝ)*(lower1) + (198834853/100000000000000 : ℝ)*(upper3) + (144105239/100000000000000 : ℝ)*(lower4) + (44675429/25000000000000 : ℝ)*(upper5) + (250888969082167/10000000000000 : ℝ)*(major0) + (250888969082167/10000000000000 : ℝ)*(major1) + (250888969082167/10000000000000 : ℝ)*(major2) + (855842811/25000000000000 : ℝ)*(sp2) + (885053351415223/25000000000000 : ℝ)*(sp4) + (3540211995528553/100000000000000 : ℝ)*(sp5) + (3540208514224051/100000000000000 : ℝ)*(sp6) + (295513132007447/20000000000000 : ℝ)*(sp7) + (295513132007447/20000000000000 : ℝ)*(f.failure) + (885053351415223/25000000000000 : ℝ)*(f.sum) + (2304833501583/509000000000000000000000000 : ℝ)*base66 + (17256259927301293/12725000000000000000000000000000 : ℝ)*base68 + (35684390691173707/12725000000000000000000000000000 : ℝ)*base69 + (114756560940551293/12725000000000000000000000000000 : ℝ)*base72 + (7458282803/15906250000000000000000000 : ℝ)*base74 + (341873940547673707/12725000000000000000000000000000 : ℝ)*base75 + (14378972602348707/12725000000000000000000000000000 : ℝ)*base77 + (8580797184676293/12725000000000000000000000000000 : ℝ)*base80 + (811734123701/254500000000000000000000000 : ℝ)*base81 + (8132761/2000000000000000000000 : ℝ)*base89 + (8132761/2000000000000000000000 : ℝ)*base91 + (8132761/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1591_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1591_s5_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1753301381/10000000000 : ℝ)*x 0 + (1366334539/2500000000 : ℝ)*x 1 + (51787837/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1753301381/10000000000 : ℝ)^4683 ≤ (10770698658711/100000000000000 : ℝ)^3659 := by
    have hnat : (1753301381 : ℕ)^4683*100000000000000^3659 ≤ 10770698658711^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753301381 10000000000 10770698658711 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366334539/2500000000 : ℝ)^4683 ≤ (46151635661083/100000000000000 : ℝ)^3659 := by
    have hnat : (1366334539 : ℕ)^4683*100000000000000^3659 ≤ 46151635661083^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366334539 2500000000 46151635661083 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51787837/100000000 : ℝ)^4683 ≤ (43077665666161/100000000000000 : ℝ)^3659 := by
    have hnat : (51787837 : ℕ)^4683*100000000000000^3659 ≤ 43077665666161^3659*100000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51787837 100000000 43077665666161 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1753301381/10000000000 : ℝ), (1366334539/2500000000 : ℝ), (51787837/100000000 : ℝ)] ![(10770698658711/100000000000000 : ℝ), (46151635661083/100000000000000 : ℝ), (43077665666161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1753301381/10000000000 : ℝ)|^4683 ≤ (10770698658711/100000000000000 : ℝ)^3659
        have hw : |(-1753301381/10000000000 : ℝ)|=(1753301381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366334539/2500000000 : ℝ)|^4683 ≤ (46151635661083/100000000000000 : ℝ)^3659
        have hw : |(1366334539/2500000000 : ℝ)|=(1366334539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51787837/100000000 : ℝ)|^4683 ≤ (43077665666161/100000000000000 : ℝ)^3659
        have hw : |(51787837/100000000 : ℝ)|=(51787837/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356200397/10000000000 : ℝ)*x 0 + (-1901191647/10000000000 : ℝ)*x 1 + (2589391873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356200397/10000000000 : ℝ)^4683 ≤ (22487711664257/50000000000000 : ℝ)^3659 := by
    have hnat : (5356200397 : ℕ)^4683*50000000000000^3659 ≤ 22487711664257^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356200397 10000000000 22487711664257 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901191647/10000000000 : ℝ)^4683 ≤ (11946910503069/100000000000000 : ℝ)^3659 := by
    have hnat : (1901191647 : ℕ)^4683*100000000000000^3659 ≤ 11946910503069^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901191647 10000000000 11946910503069 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589391873/5000000000 : ℝ)^4683 ≤ (10769416538969/25000000000000 : ℝ)^3659 := by
    have hnat : (2589391873 : ℕ)^4683*25000000000000^3659 ≤ 10769416538969^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589391873 5000000000 10769416538969 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356200397/10000000000 : ℝ), (-1901191647/10000000000 : ℝ), (2589391873/5000000000 : ℝ)] ![(22487711664257/50000000000000 : ℝ), (11946910503069/100000000000000 : ℝ), (10769416538969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356200397/10000000000 : ℝ)|^4683 ≤ (22487711664257/50000000000000 : ℝ)^3659
        have hw : |(5356200397/10000000000 : ℝ)|=(5356200397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901191647/10000000000 : ℝ)|^4683 ≤ (11946910503069/100000000000000 : ℝ)^3659
        have hw : |(-1901191647/10000000000 : ℝ)|=(1901191647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589391873/5000000000 : ℝ)|^4683 ≤ (10769416538969/25000000000000 : ℝ)^3659
        have hw : |(2589391873/5000000000 : ℝ)|=(2589391873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356200403/10000000000 : ℝ)*x 0 + (5178783749/10000000000 : ℝ)*x 1 + (-380238327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356200403/10000000000 : ℝ)^4683 ≤ (8995084678599/20000000000000 : ℝ)^3659 := by
    have hnat : (5356200403 : ℕ)^4683*20000000000000^3659 ≤ 8995084678599^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356200403 10000000000 8995084678599 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178783749/10000000000 : ℝ)^4683 ≤ (21538833093907/50000000000000 : ℝ)^3659 := by
    have hnat : (5178783749 : ℕ)^4683*50000000000000^3659 ≤ 21538833093907^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178783749 10000000000 21538833093907 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380238327/2000000000 : ℝ)^4683 ≤ (11946910406559/100000000000000 : ℝ)^3659 := by
    have hnat : (380238327 : ℕ)^4683*100000000000000^3659 ≤ 11946910406559^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380238327 2000000000 11946910406559 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356200403/10000000000 : ℝ), (5178783749/10000000000 : ℝ), (-380238327/2000000000 : ℝ)] ![(8995084678599/20000000000000 : ℝ), (21538833093907/50000000000000 : ℝ), (11946910406559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356200403/10000000000 : ℝ)|^4683 ≤ (8995084678599/20000000000000 : ℝ)^3659
        have hw : |(5356200403/10000000000 : ℝ)|=(5356200403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178783749/10000000000 : ℝ)|^4683 ≤ (21538833093907/50000000000000 : ℝ)^3659
        have hw : |(5178783749/10000000000 : ℝ)|=(5178783749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380238327/2000000000 : ℝ)|^4683 ≤ (11946910406559/100000000000000 : ℝ)^3659
        have hw : |(-380238327/2000000000 : ℝ)|=(380238327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845698157/2000000000 : ℝ)*x 0 + (487031843/1250000000 : ℝ)*x 1 + (458283257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845698157/2000000000 : ℝ)^4683 ≤ (8308266729447/25000000000000 : ℝ)^3659 := by
    have hnat : (845698157 : ℕ)^4683*25000000000000^3659 ≤ 8308266729447^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845698157 2000000000 8308266729447 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487031843/1250000000 : ℝ)^4683 ≤ (14964312880343/50000000000000 : ℝ)^3659 := by
    have hnat : (487031843 : ℕ)^4683*50000000000000^3659 ≤ 14964312880343^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487031843 1250000000 14964312880343 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458283257/1000000000 : ℝ)^4683 ≤ (3683830730631/10000000000000 : ℝ)^3659 := by
    have hnat : (458283257 : ℕ)^4683*10000000000000^3659 ≤ 3683830730631^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458283257 1000000000 3683830730631 10000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845698157/2000000000 : ℝ), (487031843/1250000000 : ℝ), (458283257/1000000000 : ℝ)] ![(8308266729447/25000000000000 : ℝ), (14964312880343/50000000000000 : ℝ), (3683830730631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845698157/2000000000 : ℝ)|^4683 ≤ (8308266729447/25000000000000 : ℝ)^3659
        have hw : |(845698157/2000000000 : ℝ)|=(845698157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487031843/1250000000 : ℝ)|^4683 ≤ (14964312880343/50000000000000 : ℝ)^3659
        have hw : |(487031843/1250000000 : ℝ)|=(487031843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458283257/1000000000 : ℝ)|^4683 ≤ (3683830730631/10000000000000 : ℝ)^3659
        have hw : |(458283257/1000000000 : ℝ)|=(458283257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-350675049/2000000000 : ℝ)*x 0 + (5180895393/10000000000 : ℝ)*x 1 + (2731602041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (350675049/2000000000 : ℝ)^4683 ≤ (10771279402309/100000000000000 : ℝ)^3659 := by
    have hnat : (350675049 : ℕ)^4683*100000000000000^3659 ≤ 10771279402309^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350675049 2000000000 10771279402309 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180895393/10000000000 : ℝ)^4683 ≤ (8620029603123/20000000000000 : ℝ)^3659 := by
    have hnat : (5180895393 : ℕ)^4683*20000000000000^3659 ≤ 8620029603123^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180895393 10000000000 8620029603123 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731602041/5000000000 : ℝ)^4683 ≤ (46128572568087/100000000000000 : ℝ)^3659 := by
    have hnat : (2731602041 : ℕ)^4683*100000000000000^3659 ≤ 46128572568087^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731602041 5000000000 46128572568087 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-350675049/2000000000 : ℝ), (5180895393/10000000000 : ℝ), (2731602041/5000000000 : ℝ)] ![(10771279402309/100000000000000 : ℝ), (8620029603123/20000000000000 : ℝ), (46128572568087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-350675049/2000000000 : ℝ)|^4683 ≤ (10771279402309/100000000000000 : ℝ)^3659
        have hw : |(-350675049/2000000000 : ℝ)|=(350675049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180895393/10000000000 : ℝ)|^4683 ≤ (8620029603123/20000000000000 : ℝ)^3659
        have hw : |(5180895393/10000000000 : ℝ)|=(5180895393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731602041/5000000000 : ℝ)|^4683 ≤ (46128572568087/100000000000000 : ℝ)^3659
        have hw : |(2731602041/5000000000 : ℝ)|=(2731602041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640191299/5000000000 : ℝ)*x 0 + (-1616771513/10000000000 : ℝ)*x 1 + (5463204201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640191299/5000000000 : ℝ)^4683 ≤ (4416224208987/10000000000000 : ℝ)^3659 := by
    have hnat : (2640191299 : ℕ)^4683*10000000000000^3659 ≤ 4416224208987^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640191299 5000000000 4416224208987 10000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1616771513/10000000000 : ℝ)^4683 ≤ (9709184036487/100000000000000 : ℝ)^3659 := by
    have hnat : (1616771513 : ℕ)^4683*100000000000000^3659 ≤ 9709184036487^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616771513 10000000000 9709184036487 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463204201/10000000000 : ℝ)^4683 ≤ (23064286927029/50000000000000 : ℝ)^3659 := by
    have hnat : (5463204201 : ℕ)^4683*50000000000000^3659 ≤ 23064286927029^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463204201 10000000000 23064286927029 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640191299/5000000000 : ℝ), (-1616771513/10000000000 : ℝ), (5463204201/10000000000 : ℝ)] ![(4416224208987/10000000000000 : ℝ), (9709184036487/100000000000000 : ℝ), (23064286927029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640191299/5000000000 : ℝ)|^4683 ≤ (4416224208987/10000000000000 : ℝ)^3659
        have hw : |(2640191299/5000000000 : ℝ)|=(2640191299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1616771513/10000000000 : ℝ)|^4683 ≤ (9709184036487/100000000000000 : ℝ)^3659
        have hw : |(-1616771513/10000000000 : ℝ)|=(1616771513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463204201/10000000000 : ℝ)|^4683 ≤ (23064286927029/50000000000000 : ℝ)^3659
        have hw : |(5463204201/10000000000 : ℝ)|=(5463204201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528038271/1000000000 : ℝ)*x 0 + (682900549/1250000000 : ℝ)*x 1 + (-1616771089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528038271/1000000000 : ℝ)^4683 ≤ (22081121644361/50000000000000 : ℝ)^3659 := by
    have hnat : (528038271 : ℕ)^4683*50000000000000^3659 ≤ 22081121644361^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528038271 1000000000 22081121644361 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682900549/1250000000 : ℝ)^4683 ≤ (2883035994881/6250000000000 : ℝ)^3659 := by
    have hnat : (682900549 : ℕ)^4683*6250000000000^3659 ≤ 2883035994881^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682900549 1250000000 2883035994881 6250000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616771089/10000000000 : ℝ)^4683 ≤ (9709180777657/100000000000000 : ℝ)^3659 := by
    have hnat : (1616771089 : ℕ)^4683*100000000000000^3659 ≤ 9709180777657^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616771089 10000000000 9709180777657 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528038271/1000000000 : ℝ), (682900549/1250000000 : ℝ), (-1616771089/10000000000 : ℝ)] ![(22081121644361/50000000000000 : ℝ), (2883035994881/6250000000000 : ℝ), (9709180777657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528038271/1000000000 : ℝ)|^4683 ≤ (22081121644361/50000000000000 : ℝ)^3659
        have hw : |(528038271/1000000000 : ℝ)|=(528038271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682900549/1250000000 : ℝ)|^4683 ≤ (2883035994881/6250000000000 : ℝ)^3659
        have hw : |(682900549/1250000000 : ℝ)|=(682900549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1616771089/10000000000 : ℝ)|^4683 ≤ (9709180777657/100000000000000 : ℝ)^3659
        have hw : |(-1616771089/10000000000 : ℝ)|=(1616771089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s5_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422866709/1000000000 : ℝ)*x 0 + (2288886637/5000000000 : ℝ)*x 1 + (3901366993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422866709/1000000000 : ℝ)^4683 ≤ (16617420173677/50000000000000 : ℝ)^3659 := by
    have hnat : (422866709 : ℕ)^4683*50000000000000^3659 ≤ 16617420173677^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422866709 1000000000 16617420173677 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288886637/5000000000 : ℝ)^4683 ≤ (18393132867469/50000000000000 : ℝ)^3659 := by
    have hnat : (2288886637 : ℕ)^4683*50000000000000^3659 ≤ 18393132867469^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288886637 5000000000 18393132867469 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3901366993/10000000000 : ℝ)^4683 ≤ (14989446954197/50000000000000 : ℝ)^3659 := by
    have hnat : (3901366993 : ℕ)^4683*50000000000000^3659 ≤ 14989446954197^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901366993 10000000000 14989446954197 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422866709/1000000000 : ℝ), (2288886637/5000000000 : ℝ), (3901366993/10000000000 : ℝ)] ![(16617420173677/50000000000000 : ℝ), (18393132867469/50000000000000 : ℝ), (14989446954197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422866709/1000000000 : ℝ)|^4683 ≤ (16617420173677/50000000000000 : ℝ)^3659
        have hw : |(422866709/1000000000 : ℝ)|=(422866709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288886637/5000000000 : ℝ)|^4683 ≤ (18393132867469/50000000000000 : ℝ)^3659
        have hw : |(2288886637/5000000000 : ℝ)|=(2288886637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3901366993/10000000000 : ℝ)|^4683 ≤ (14989446954197/50000000000000 : ℝ)^3659
        have hw : |(3901366993/10000000000 : ℝ)|=(3901366993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4093/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5151/50000 : ℝ) ^ (4679/1024 : ℝ) ≤ (3088210853235097/100000000000000000000 : ℝ) := by
    have hpowers : (5151/50000 : ℝ)^4679 ≤ (3088210853235097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5151 : ℕ)^4679*100000000000000000000^1024 ≤ 3088210853235097^1024*50000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5151 50000 3088210853235097 100000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5151/50000 : ℝ)) (X := (3088210853235097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8187/50000 : ℝ) ^ (4679/1024 : ℝ) ≤ (1282859890817643/5000000000000000000 : ℝ) := by
    have hpowers : (8187/50000 : ℝ)^4679 ≤ (1282859890817643/5000000000000000000 : ℝ)^1024 := by
      have hnat : (8187 : ℕ)^4679*5000000000000000000^1024 ≤ 1282859890817643^1024*50000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8187 50000 1282859890817643 5000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8187/50000 : ℝ)) (X := (1282859890817643/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003088210853235097/50000000000000000000 : ℝ) ≤ (10000135167840561/10000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (50003088210853235097/50000000000000000000 : ℝ)^1024 ≤ (10000135167840561/10000000000000000 : ℝ)^4679 := by
      have hnat : (50003088210853235097 : ℕ)^1024*10000000000000000^4679 ≤ 10000135167840561^4679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003088210853235097 50000000000000000000 10000135167840561 10000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000135167840561/10000000000000000 : ℝ)) (X := (50003088210853235097/50000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028745408669587957/100000000000000000000 : ℝ) ≤ (5000314511586571/5000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (100028745408669587957/100000000000000000000 : ℝ)^1024 ≤ (5000314511586571/5000000000000000 : ℝ)^4679 := by
      have hnat : (100028745408669587957 : ℕ)^1024*5000000000000000^4679 ≤ 5000314511586571^4679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028745408669587957 100000000000000000000 5000314511586571 5000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000314511586571/5000000000000000 : ℝ)) (X := (100028745408669587957/100000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501282859890817643/2500000000000000000 : ℝ) ≤ (10001122878505723/10000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (2501282859890817643/2500000000000000000 : ℝ)^1024 ≤ (10001122878505723/10000000000000000 : ℝ)^4679 := by
      have hnat : (2501282859890817643 : ℕ)^1024*10000000000000000^4679 ≤ 10001122878505723^4679*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501282859890817643 2500000000000000000 10001122878505723 10000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001122878505723/10000000000000000 : ℝ)) (X := (2501282859890817643/2500000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3088210853235097/100000000000000000000 : ℝ) ≤ ((5059220445321282289/5060000000000000000 : ℝ)+2*(493855332581/607200000000000 : ℝ)*(5151/50000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (5059220445321282289/5060000000000000000 : ℝ)+2*(493855332581/607200000000000 : ℝ)*(5151/50000 : ℝ)=(10000135167840561/10000000000000000 : ℝ) by norm_num, show 1+2*(3088210853235097/100000000000000000000 : ℝ)=(50003088210853235097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1282859890817643/5000000000000000000 : ℝ)+(3088210853235097/100000000000000000000 : ℝ) ≤ ((5059220445321282289/5060000000000000000 : ℝ)+(493855332581/607200000000000 : ℝ)*((8187/50000 : ℝ)+(5151/50000 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (5059220445321282289/5060000000000000000 : ℝ)+(493855332581/607200000000000 : ℝ)*((8187/50000 : ℝ)+(5151/50000 : ℝ))=(5000314511586571/5000000000000000 : ℝ) by norm_num, show 1+(1282859890817643/5000000000000000000 : ℝ)+(3088210853235097/100000000000000000000 : ℝ)=(100028745408669587957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1282859890817643/5000000000000000000 : ℝ) ≤ ((5059220445321282289/5060000000000000000 : ℝ)+2*(493855332581/607200000000000 : ℝ)*(8187/50000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (5059220445321282289/5060000000000000000 : ℝ)+2*(493855332581/607200000000000 : ℝ)*(8187/50000 : ℝ)=(10001122878505723/10000000000000000 : ℝ) by norm_num, show 1+2*(1282859890817643/5000000000000000000 : ℝ)=(2501282859890817643/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5059220445321282289/5060000000000000000 : ℝ)*(X 1 0+X 2 0)+(493855332581/607200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (5059220445321282289/5060000000000000000 : ℝ)) (alpha := (493855332581/607200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5059220445321282289/5060000000000000000 : ℝ)*(X 0 1+X 2 1)+(493855332581/607200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (5059220445321282289/5060000000000000000 : ℝ)) (alpha := (493855332581/607200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5059220445321282289/5060000000000000000 : ℝ)*(X 0 2+X 1 2)+(493855332581/607200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (5059220445321282289/5060000000000000000 : ℝ)) (alpha := (493855332581/607200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1753301381/10000000000 : ℝ)*X 0 0+(1366334539/2500000000 : ℝ)*X 0 1+(51787837/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356200397/10000000000 : ℝ)*X 1 0+(-1901191647/10000000000 : ℝ)*X 1 1+(2589391873/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356200403/10000000000 : ℝ)*X 2 0+(5178783749/10000000000 : ℝ)*X 2 1+(-380238327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((845698157/2000000000 : ℝ)*X 0 0+(487031843/1250000000 : ℝ)*X 0 1+(458283257/1000000000 : ℝ)*X 0 2+(845698157/2000000000 : ℝ)*X 1 0+(487031843/1250000000 : ℝ)*X 1 1+(458283257/1000000000 : ℝ)*X 1 2+(845698157/2000000000 : ℝ)*X 2 0+(487031843/1250000000 : ℝ)*X 2 1+(458283257/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-350675049/2000000000 : ℝ)*X 0 0+(5180895393/10000000000 : ℝ)*X 0 1+(2731602041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640191299/5000000000 : ℝ)*X 1 0+(-1616771513/10000000000 : ℝ)*X 1 1+(5463204201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528038271/1000000000 : ℝ)*X 2 0+(682900549/1250000000 : ℝ)*X 2 1+(-1616771089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((422866709/1000000000 : ℝ)*X 0 0+(2288886637/5000000000 : ℝ)*X 0 1+(3901366993/10000000000 : ℝ)*X 0 2+(422866709/1000000000 : ℝ)*X 1 0+(2288886637/5000000000 : ℝ)*X 1 1+(3901366993/10000000000 : ℝ)*X 1 2+(422866709/1000000000 : ℝ)*X 2 0+(2288886637/5000000000 : ℝ)*X 2 1+(3901366993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (609824965598611897907087043/63250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409633789/25000000000000 : ℝ)*(base19) + (1545802071/100000000000000 : ℝ)*(base23) + (10352713/20000000000000 : ℝ)*(lower2) + (117330977/50000000000000 : ℝ)*(upper3) + (1079709/625000000000 : ℝ)*(upper5) + (1236573702101229/50000000000000 : ℝ)*(major0) + (1236573702101229/50000000000000 : ℝ)*(major1) + (1236573702101229/50000000000000 : ℝ)*(major2) + (436219814746831/12500000000000 : ℝ)*(sp0) + (3489776968163631/100000000000000 : ℝ)*(sp1) + (872444265224179/25000000000000 : ℝ)*(sp2) + (728253541245237/50000000000000 : ℝ)*(sp3) + (10044362069/50000000000000 : ℝ)*(sp4) + (8797832269/100000000000000 : ℝ)*(sp7) + (1456515880322743/100000000000000 : ℝ)*(f.failure) + (3489778606698787/100000000000000 : ℝ)*(f.sum) + (1573145125437/5060000000000000000000000000 : ℝ)*base66 + (59000673692517747/11000000000000000000000000000000 : ℝ)*base67 + (8441993126482253/11000000000000000000000000000000 : ℝ)*base70 + (15490425660482253/11000000000000000000000000000000 : ℝ)*base72 + (18267921929383/5060000000000000000000000000 : ℝ)*base73 + (170383694036482253/11000000000000000000000000000000 : ℝ)*base76 + (5121991111482253/11000000000000000000000000000000 : ℝ)*base78 + (82031458889482253/11000000000000000000000000000000 : ℝ)*base80 + (4485721782537/5060000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (34441209/10000000000000000000000 : ℝ)*base89 + (34441209/10000000000000000000000 : ℝ)*base91 + (34441209/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72596307760581886040377/10120000000000000000000000000 : ℝ) := by norm_num
    linear_combination (267230477/25000000000000 : ℝ)*(base19) + (174070533/12500000000000 : ℝ)*(base23) + (239850871/100000000000000 : ℝ)*(lower1) + (1240063/2000000000000 : ℝ)*(upper2) + (71812367/25000000000000 : ℝ)*(upper3) + (152735281/100000000000000 : ℝ)*(upper5) + (2510304706843963/100000000000000 : ℝ)*(major0) + (2510304706843963/100000000000000 : ℝ)*(major1) + (2510304706843963/100000000000000 : ℝ)*(major2) + (4564874979/50000000000000 : ℝ)*(sp2) + (1771105083091451/50000000000000 : ℝ)*(sp4) + (1771104548630497/50000000000000 : ℝ)*(sp5) + (88554991096717/2500000000000 : ℝ)*(sp6) + (739199504193371/50000000000000 : ℝ)*(sp7) + (739199504193371/50000000000000 : ℝ)*(f.failure) + (1771105083091451/50000000000000 : ℝ)*(f.sum) + (96878125834103/30360000000000000000000000000 : ℝ)*base65 + (369669448723217873/66000000000000000000000000000000 : ℝ)*base68 + (2215173758860782127/66000000000000000000000000000000 : ℝ)*base69 + (61858608991217873/66000000000000000000000000000000 : ℝ)*base72 + (42158821500457/30360000000000000000000000000 : ℝ)*base74 + (520475409919217873/66000000000000000000000000000000 : ℝ)*base76 + (101189542516782127/66000000000000000000000000000000 : ℝ)*base77 + (158072846620782127/66000000000000000000000000000000 : ℝ)*base79 + (269591515714343/30360000000000000000000000000 : ℝ)*base81 + (22062827/5000000000000000000000 : ℝ)*base90 + (22062827/5000000000000000000000 : ℝ)*base92 + (22062827/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1591_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1591_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1591_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1591_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1591_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

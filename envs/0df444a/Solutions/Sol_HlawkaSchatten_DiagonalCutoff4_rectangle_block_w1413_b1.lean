-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1413_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:27.147201+00:00
-- url     : https://prove2.me/submissions/84fea16c-8712-48dd-ab30-f0635ffbee5a

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
theorem support_rectangle_w1413_s3_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983025331/10000000000 : ℝ)*x 0 + (541893349/1000000000 : ℝ)*x 1 + (5237412637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983025331/10000000000 : ℝ)^4373 ≤ (12091419906037/100000000000000 : ℝ)^3349 := by
    have hnat : (1983025331 : ℕ)^4373*100000000000000^3349 ≤ 12091419906037^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983025331 10000000000 12091419906037 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541893349/1000000000 : ℝ)^4373 ≤ (5616484284691/12500000000000 : ℝ)^3349 := by
    have hnat : (541893349 : ℕ)^4373*12500000000000^3349 ≤ 5616484284691^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541893349 1000000000 5616484284691 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237412637/10000000000 : ℝ)^4373 ≤ (21488352901301/50000000000000 : ℝ)^3349 := by
    have hnat : (5237412637 : ℕ)^4373*50000000000000^3349 ≤ 21488352901301^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237412637 10000000000 21488352901301 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983025331/10000000000 : ℝ), (541893349/1000000000 : ℝ), (5237412637/10000000000 : ℝ)] ![(12091419906037/100000000000000 : ℝ), (5616484284691/12500000000000 : ℝ), (21488352901301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983025331/10000000000 : ℝ)|^4373 ≤ (12091419906037/100000000000000 : ℝ)^3349
        have hw : |(-1983025331/10000000000 : ℝ)|=(1983025331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541893349/1000000000 : ℝ)|^4373 ≤ (5616484284691/12500000000000 : ℝ)^3349
        have hw : |(541893349/1000000000 : ℝ)|=(541893349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237412637/10000000000 : ℝ)|^4373 ≤ (21488352901301/50000000000000 : ℝ)^3349
        have hw : |(5237412637/10000000000 : ℝ)|=(5237412637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337551673/2500000000 : ℝ)*x 0 + (-2075647603/10000000000 : ℝ)*x 1 + (104748251/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337551673/2500000000 : ℝ)^4373 ≤ (22094610782771/50000000000000 : ℝ)^3349 := by
    have hnat : (1337551673 : ℕ)^4373*50000000000000^3349 ≤ 22094610782771^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337551673 2500000000 22094610782771 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075647603/10000000000 : ℝ)^4373 ≤ (3208518387181/25000000000000 : ℝ)^3349 := by
    have hnat : (2075647603 : ℕ)^4373*25000000000000^3349 ≤ 3208518387181^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075647603 10000000000 3208518387181 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104748251/200000000 : ℝ)^4373 ≤ (21488352435211/50000000000000 : ℝ)^3349 := by
    have hnat : (104748251 : ℕ)^4373*50000000000000^3349 ≤ 21488352435211^3349*200000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104748251 200000000 21488352435211 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337551673/2500000000 : ℝ), (-2075647603/10000000000 : ℝ), (104748251/200000000 : ℝ)] ![(22094610782771/50000000000000 : ℝ), (3208518387181/25000000000000 : ℝ), (21488352435211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337551673/2500000000 : ℝ)|^4373 ≤ (22094610782771/50000000000000 : ℝ)^3349
        have hw : |(1337551673/2500000000 : ℝ)|=(1337551673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075647603/10000000000 : ℝ)|^4373 ≤ (3208518387181/25000000000000 : ℝ)^3349
        have hw : |(-2075647603/10000000000 : ℝ)|=(2075647603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104748251/200000000 : ℝ)|^4373 ≤ (21488352435211/50000000000000 : ℝ)^3349
        have hw : |(104748251/200000000 : ℝ)|=(104748251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675103317/5000000000 : ℝ)*x 0 + (5237412667/10000000000 : ℝ)*x 1 + (-83025901/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675103317/5000000000 : ℝ)^4373 ≤ (22094610470013/50000000000000 : ℝ)^3349 := by
    have hnat : (2675103317 : ℕ)^4373*50000000000000^3349 ≤ 22094610470013^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675103317 5000000000 22094610470013 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237412667/10000000000 : ℝ)^4373 ≤ (10744176531011/25000000000000 : ℝ)^3349 := by
    have hnat : (5237412667 : ℕ)^4373*25000000000000^3349 ≤ 10744176531011^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237412667 10000000000 10744176531011 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83025901/400000000 : ℝ)^4373 ≤ (3208518229743/25000000000000 : ℝ)^3349 := by
    have hnat : (83025901 : ℕ)^4373*25000000000000^3349 ≤ 3208518229743^3349*400000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83025901 400000000 3208518229743 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675103317/5000000000 : ℝ), (5237412667/10000000000 : ℝ), (-83025901/400000000 : ℝ)] ![(22094610470013/50000000000000 : ℝ), (10744176531011/25000000000000 : ℝ), (3208518229743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675103317/5000000000 : ℝ)|^4373 ≤ (22094610470013/50000000000000 : ℝ)^3349
        have hw : |(2675103317/5000000000 : ℝ)|=(2675103317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237412667/10000000000 : ℝ)|^4373 ≤ (10744176531011/25000000000000 : ℝ)^3349
        have hw : |(5237412667/10000000000 : ℝ)|=(5237412667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83025901/400000000 : ℝ)|^4373 ≤ (3208518229743/25000000000000 : ℝ)^3349
        have hw : |(-83025901/400000000 : ℝ)|=(83025901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307682069/10000000000 : ℝ)*x 0 + (514561433/1250000000 : ℝ)*x 1 + (4506880883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307682069/10000000000 : ℝ)^4373 ≤ (16648645922241/50000000000000 : ℝ)^3349 := by
    have hnat : (4307682069 : ℕ)^4373*50000000000000^3349 ≤ 16648645922241^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307682069 10000000000 16648645922241 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514561433/1250000000 : ℝ)^4373 ≤ (15690397375511/50000000000000 : ℝ)^3349 := by
    have hnat : (514561433 : ℕ)^4373*50000000000000^3349 ≤ 15690397375511^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514561433 1250000000 15690397375511 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506880883/10000000000 : ℝ)^4373 ≤ (7064382677333/20000000000000 : ℝ)^3349 := by
    have hnat : (4506880883 : ℕ)^4373*20000000000000^3349 ≤ 7064382677333^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506880883 10000000000 7064382677333 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307682069/10000000000 : ℝ), (514561433/1250000000 : ℝ), (4506880883/10000000000 : ℝ)] ![(16648645922241/50000000000000 : ℝ), (15690397375511/50000000000000 : ℝ), (7064382677333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307682069/10000000000 : ℝ)|^4373 ≤ (16648645922241/50000000000000 : ℝ)^3349
        have hw : |(4307682069/10000000000 : ℝ)|=(4307682069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514561433/1250000000 : ℝ)|^4373 ≤ (15690397375511/50000000000000 : ℝ)^3349
        have hw : |(514561433/1250000000 : ℝ)|=(514561433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506880883/10000000000 : ℝ)|^4373 ≤ (7064382677333/20000000000000 : ℝ)^3349
        have hw : |(4506880883/10000000000 : ℝ)|=(4506880883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99152079/500000000 : ℝ)*x 0 + (5238142329/10000000000 : ℝ)*x 1 + (5418199381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99152079/500000000 : ℝ)^4373 ≤ (2418309855623/20000000000000 : ℝ)^3349 := by
    have hnat : (99152079 : ℕ)^4373*20000000000000^3349 ≤ 2418309855623^3349*500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99152079 500000000 2418309855623 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238142329/10000000000 : ℝ)^4373 ≤ (21492262205813/50000000000000 : ℝ)^3349 := by
    have hnat : (5238142329 : ℕ)^4373*50000000000000^3349 ≤ 21492262205813^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238142329 10000000000 21492262205813 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418199381/10000000000 : ℝ)^4373 ≤ (11230981575151/25000000000000 : ℝ)^3349 := by
    have hnat : (5418199381 : ℕ)^4373*25000000000000^3349 ≤ 11230981575151^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418199381 10000000000 11230981575151 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99152079/500000000 : ℝ), (5238142329/10000000000 : ℝ), (5418199381/10000000000 : ℝ)] ![(2418309855623/20000000000000 : ℝ), (21492262205813/50000000000000 : ℝ), (11230981575151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99152079/500000000 : ℝ)|^4373 ≤ (2418309855623/20000000000000 : ℝ)^3349
        have hw : |(-99152079/500000000 : ℝ)|=(99152079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238142329/10000000000 : ℝ)|^4373 ≤ (21492262205813/50000000000000 : ℝ)^3349
        have hw : |(5238142329/10000000000 : ℝ)|=(5238142329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418199381/10000000000 : ℝ)|^4373 ≤ (11230981575151/25000000000000 : ℝ)^3349
        have hw : |(5418199381/10000000000 : ℝ)|=(5418199381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651545957/5000000000 : ℝ)*x 0 + (-1894860297/10000000000 : ℝ)*x 1 + (5418199599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651545957/5000000000 : ℝ)^4373 ≤ (43681785900589/100000000000000 : ℝ)^3349 := by
    have hnat : (2651545957 : ℕ)^4373*100000000000000^3349 ≤ 43681785900589^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651545957 5000000000 43681785900589 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894860297/10000000000 : ℝ)^4373 ≤ (1424285678027/12500000000000 : ℝ)^3349 := by
    have hnat : (1894860297 : ℕ)^4373*12500000000000^3349 ≤ 1424285678027^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894860297 10000000000 1424285678027 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418199599/10000000000 : ℝ)^4373 ≤ (1796957146431/4000000000000 : ℝ)^3349 := by
    have hnat : (5418199599 : ℕ)^4373*4000000000000^3349 ≤ 1796957146431^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418199599 10000000000 1796957146431 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651545957/5000000000 : ℝ), (-1894860297/10000000000 : ℝ), (5418199599/10000000000 : ℝ)] ![(43681785900589/100000000000000 : ℝ), (1424285678027/12500000000000 : ℝ), (1796957146431/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651545957/5000000000 : ℝ)|^4373 ≤ (43681785900589/100000000000000 : ℝ)^3349
        have hw : |(2651545957/5000000000 : ℝ)|=(2651545957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894860297/10000000000 : ℝ)|^4373 ≤ (1424285678027/12500000000000 : ℝ)^3349
        have hw : |(-1894860297/10000000000 : ℝ)|=(1894860297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418199599/10000000000 : ℝ)|^4373 ≤ (1796957146431/4000000000000 : ℝ)^3349
        have hw : |(5418199599/10000000000 : ℝ)|=(5418199599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303092623/10000000000 : ℝ)*x 0 + (169318719/312500000 : ℝ)*x 1 + (-1894860141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303092623/10000000000 : ℝ)^4373 ≤ (1747271741053/4000000000000 : ℝ)^3349 := by
    have hnat : (5303092623 : ℕ)^4373*4000000000000^3349 ≤ 1747271741053^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303092623 10000000000 1747271741053 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169318719/312500000 : ℝ)^4373 ≤ (44923922262329/100000000000000 : ℝ)^3349 := by
    have hnat : (169318719 : ℕ)^4373*100000000000000^3349 ≤ 44923922262329^3349*312500000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169318719 312500000 44923922262329 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894860141/10000000000 : ℝ)^4373 ≤ (11394284199321/100000000000000 : ℝ)^3349 := by
    have hnat : (1894860141 : ℕ)^4373*100000000000000^3349 ≤ 11394284199321^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894860141 10000000000 11394284199321 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303092623/10000000000 : ℝ), (169318719/312500000 : ℝ), (-1894860141/10000000000 : ℝ)] ![(1747271741053/4000000000000 : ℝ), (44923922262329/100000000000000 : ℝ), (11394284199321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303092623/10000000000 : ℝ)|^4373 ≤ (1747271741053/4000000000000 : ℝ)^3349
        have hw : |(5303092623/10000000000 : ℝ)|=(5303092623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169318719/312500000 : ℝ)|^4373 ≤ (44923922262329/100000000000000 : ℝ)^3349
        have hw : |(169318719/312500000 : ℝ)|=(169318719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894860141/10000000000 : ℝ)|^4373 ≤ (11394284199321/100000000000000 : ℝ)^3349
        have hw : |(-1894860141/10000000000 : ℝ)|=(1894860141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153858619/5000000000 : ℝ)*x 0 + (2252655637/5000000000 : ℝ)*x 1 + (2059034663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153858619/5000000000 : ℝ)^4373 ≤ (6659529362653/20000000000000 : ℝ)^3349 := by
    have hnat : (2153858619 : ℕ)^4373*20000000000000^3349 ≤ 6659529362653^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153858619 5000000000 6659529362653 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252655637/5000000000 : ℝ)^4373 ≤ (35305851342139/100000000000000 : ℝ)^3349 := by
    have hnat : (2252655637 : ℕ)^4373*100000000000000^3349 ≤ 35305851342139^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252655637 5000000000 35305851342139 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059034663/5000000000 : ℝ)^4373 ≤ (31396501833081/100000000000000 : ℝ)^3349 := by
    have hnat : (2059034663 : ℕ)^4373*100000000000000^3349 ≤ 31396501833081^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059034663 5000000000 31396501833081 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153858619/5000000000 : ℝ), (2252655637/5000000000 : ℝ), (2059034663/5000000000 : ℝ)] ![(6659529362653/20000000000000 : ℝ), (35305851342139/100000000000000 : ℝ), (31396501833081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153858619/5000000000 : ℝ)|^4373 ≤ (6659529362653/20000000000000 : ℝ)^3349
        have hw : |(2153858619/5000000000 : ℝ)|=(2153858619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252655637/5000000000 : ℝ)|^4373 ≤ (35305851342139/100000000000000 : ℝ)^3349
        have hw : |(2252655637/5000000000 : ℝ)|=(2252655637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2059034663/5000000000 : ℝ)|^4373 ≤ (31396501833081/100000000000000 : ℝ)^3349
        have hw : |(2059034663/5000000000 : ℝ)|=(2059034663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_8 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4246581/2000000000 : ℝ)*x 0 + (5717063941/10000000000 : ℝ)*x 1 + (755113791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4246581/2000000000 : ℝ)^4373 ≤ (32337617963/100000000000000 : ℝ)^3349 := by
    have hnat : (4246581 : ℕ)^4373*100000000000000^3349 ≤ 32337617963^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246581 2000000000 32337617963 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5717063941/10000000000 : ℝ)^4373 ≤ (24093260581127/50000000000000 : ℝ)^3349 := by
    have hnat : (5717063941 : ℕ)^4373*50000000000000^3349 ≤ 24093260581127^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717063941 10000000000 24093260581127 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755113791/1250000000 : ℝ)^4373 ≤ (6472642650299/12500000000000 : ℝ)^3349 := by
    have hnat : (755113791 : ℕ)^4373*12500000000000^3349 ≤ 6472642650299^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755113791 1250000000 6472642650299 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4246581/2000000000 : ℝ), (5717063941/10000000000 : ℝ), (755113791/1250000000 : ℝ)] ![(32337617963/100000000000000 : ℝ), (24093260581127/50000000000000 : ℝ), (6472642650299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4246581/2000000000 : ℝ)|^4373 ≤ (32337617963/100000000000000 : ℝ)^3349
        have hw : |(-4246581/2000000000 : ℝ)|=(4246581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5717063941/10000000000 : ℝ)|^4373 ≤ (24093260581127/50000000000000 : ℝ)^3349
        have hw : |(5717063941/10000000000 : ℝ)|=(5717063941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755113791/1250000000 : ℝ)|^4373 ≤ (6472642650299/12500000000000 : ℝ)^3349
        have hw : |(755113791/1250000000 : ℝ)|=(755113791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_9 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521266901/5000000000 : ℝ)*x 0 + (-1045623019/2500000000 : ℝ)*x 1 + (1749378081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521266901/5000000000 : ℝ)^4373 ≤ (208890417281/4000000000000 : ℝ)^3349 := by
    have hnat : (521266901 : ℕ)^4373*4000000000000^3349 ≤ 208890417281^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521266901 5000000000 208890417281 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045623019/2500000000 : ℝ)^4373 ≤ (32039374436381/100000000000000 : ℝ)^3349 := by
    have hnat : (1045623019 : ℕ)^4373*100000000000000^3349 ≤ 32039374436381^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045623019 2500000000 32039374436381 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749378081/2500000000 : ℝ)^4373 ≤ (6273836511001/10000000000000 : ℝ)^3349 := by
    have hnat : (1749378081 : ℕ)^4373*10000000000000^3349 ≤ 6273836511001^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749378081 2500000000 6273836511001 10000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521266901/5000000000 : ℝ), (-1045623019/2500000000 : ℝ), (1749378081/2500000000 : ℝ)] ![(208890417281/4000000000000 : ℝ), (32039374436381/100000000000000 : ℝ), (6273836511001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521266901/5000000000 : ℝ)|^4373 ≤ (208890417281/4000000000000 : ℝ)^3349
        have hw : |(521266901/5000000000 : ℝ)|=(521266901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045623019/2500000000 : ℝ)|^4373 ≤ (32039374436381/100000000000000 : ℝ)^3349
        have hw : |(-1045623019/2500000000 : ℝ)|=(1045623019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1749378081/2500000000 : ℝ)|^4373 ≤ (6273836511001/10000000000000 : ℝ)^3349
        have hw : |(1749378081/2500000000 : ℝ)|=(1749378081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_10 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042541281/10000000000 : ℝ)*x 0 + (1399505767/2000000000 : ℝ)*x 1 + (-2091233931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042541281/10000000000 : ℝ)^4373 ≤ (522230935093/10000000000000 : ℝ)^3349 := by
    have hnat : (1042541281 : ℕ)^4373*10000000000000^3349 ≤ 522230935093^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042541281 10000000000 522230935093 10000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1399505767/2000000000 : ℝ)^4373 ≤ (62738558408023/100000000000000 : ℝ)^3349 := by
    have hnat : (1399505767 : ℕ)^4373*100000000000000^3349 ≤ 62738558408023^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399505767 2000000000 62738558408023 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091233931/5000000000 : ℝ)^4373 ≤ (6407826446691/20000000000000 : ℝ)^3349 := by
    have hnat : (2091233931 : ℕ)^4373*20000000000000^3349 ≤ 6407826446691^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091233931 5000000000 6407826446691 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042541281/10000000000 : ℝ), (1399505767/2000000000 : ℝ), (-2091233931/5000000000 : ℝ)] ![(522230935093/10000000000000 : ℝ), (62738558408023/100000000000000 : ℝ), (6407826446691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042541281/10000000000 : ℝ)|^4373 ≤ (522230935093/10000000000000 : ℝ)^3349
        have hw : |(1042541281/10000000000 : ℝ)|=(1042541281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1399505767/2000000000 : ℝ)|^4373 ≤ (62738558408023/100000000000000 : ℝ)^3349
        have hw : |(1399505767/2000000000 : ℝ)|=(1399505767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091233931/5000000000 : ℝ)|^4373 ≤ (6407826446691/20000000000000 : ℝ)^3349
        have hw : |(-2091233931/5000000000 : ℝ)|=(2091233931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s3_11 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1473668171/10000000000 : ℝ)*x 0 + (5658912917/10000000000 : ℝ)*x 1 + (2677761011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1473668171/10000000000 : ℝ)^4373 ≤ (328236720371/4000000000000 : ℝ)^3349 := by
    have hnat : (1473668171 : ℕ)^4373*4000000000000^3349 ≤ 328236720371^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473668171 10000000000 328236720371 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5658912917/10000000000 : ℝ)^4373 ≤ (47547527200341/100000000000000 : ℝ)^3349 := by
    have hnat : (5658912917 : ℕ)^4373*100000000000000^3349 ≤ 47547527200341^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658912917 10000000000 47547527200341 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2677761011/5000000000 : ℝ)^4373 ≤ (44246554780561/100000000000000 : ℝ)^3349 := by
    have hnat : (2677761011 : ℕ)^4373*100000000000000^3349 ≤ 44246554780561^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677761011 5000000000 44246554780561 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1473668171/10000000000 : ℝ), (5658912917/10000000000 : ℝ), (2677761011/5000000000 : ℝ)] ![(328236720371/4000000000000 : ℝ), (47547527200341/100000000000000 : ℝ), (44246554780561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1473668171/10000000000 : ℝ)|^4373 ≤ (328236720371/4000000000000 : ℝ)^3349
        have hw : |(1473668171/10000000000 : ℝ)|=(1473668171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5658912917/10000000000 : ℝ)|^4373 ≤ (47547527200341/100000000000000 : ℝ)^3349
        have hw : |(5658912917/10000000000 : ℝ)|=(5658912917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2677761011/5000000000 : ℝ)|^4373 ≤ (44246554780561/100000000000000 : ℝ)^3349
        have hw : |(2677761011/5000000000 : ℝ)|=(2677761011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2991/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (317/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (257/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (317/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (257/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (317/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (257/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (317/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (257/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (317/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (257/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (317/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (257/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (257/2500 : ℝ) ^ (1093/256 : ℝ) ≤ (6048862714327793/100000000000000000000 : ℝ) := by
    have hpowers : (257/2500 : ℝ)^1093 ≤ (6048862714327793/100000000000000000000 : ℝ)^256 := by
      have hnat : (257 : ℕ)^1093*100000000000000000000^256 ≤ 6048862714327793^256*2500^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        257 2500 6048862714327793 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (257/2500 : ℝ)) (X := (6048862714327793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (317/2000 : ℝ) ^ (1093/256 : ℝ) ≤ (38414921890219613/100000000000000000000 : ℝ) := by
    have hpowers : (317/2000 : ℝ)^1093 ≤ (38414921890219613/100000000000000000000 : ℝ)^256 := by
      have hnat : (317 : ℕ)^1093*100000000000000000000^256 ≤ 38414921890219613^256*2000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 2000 38414921890219613 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/2000 : ℝ)) (X := (38414921890219613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006048862714327793/50000000000000000000 : ℝ) ≤ (10000283337078009/10000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50006048862714327793/50000000000000000000 : ℝ)^256 ≤ (10000283337078009/10000000000000000 : ℝ)^1093 := by
      have hnat : (50006048862714327793 : ℕ)^256*10000000000000000^1093 ≤ 10000283337078009^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006048862714327793 50000000000000000000 10000283337078009 10000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283337078009/10000000000000000 : ℝ)) (X := (50006048862714327793/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022231892302273703/50000000000000000000 : ℝ) ≤ (10001041243502311/10000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50022231892302273703/50000000000000000000 : ℝ)^256 ≤ (10001041243502311/10000000000000000 : ℝ)^1093 := by
      have hnat : (50022231892302273703 : ℕ)^256*10000000000000000^1093 ≤ 10001041243502311^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022231892302273703 50000000000000000000 10001041243502311 10000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001041243502311/10000000000000000 : ℝ)) (X := (50022231892302273703/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038414921890219613/50000000000000000000 : ℝ) ≤ (10001799149926613/10000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50038414921890219613/50000000000000000000 : ℝ)^256 ≤ (10001799149926613/10000000000000000 : ℝ)^1093 := by
      have hnat : (50038414921890219613 : ℕ)^256*10000000000000000^1093 ≤ 10001799149926613^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038414921890219613 50000000000000000000 10001799149926613 10000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001799149926613/10000000000000000 : ℝ)) (X := (50038414921890219613/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6048862714327793/100000000000000000000 : ℝ) ≤ ((5568599563144086101/5570000000000000000 : ℝ)+2*(378953212151/278500000000000 : ℝ)*(257/2500 : ℝ))^(1093/256 : ℝ) := by
    rw [show (5568599563144086101/5570000000000000000 : ℝ)+2*(378953212151/278500000000000 : ℝ)*(257/2500 : ℝ)=(10000283337078009/10000000000000000 : ℝ) by norm_num, show 1+2*(6048862714327793/100000000000000000000 : ℝ)=(50006048862714327793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38414921890219613/100000000000000000000 : ℝ)+(6048862714327793/100000000000000000000 : ℝ) ≤ ((5568599563144086101/5570000000000000000 : ℝ)+(378953212151/278500000000000 : ℝ)*((317/2000 : ℝ)+(257/2500 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (5568599563144086101/5570000000000000000 : ℝ)+(378953212151/278500000000000 : ℝ)*((317/2000 : ℝ)+(257/2500 : ℝ))=(10001041243502311/10000000000000000 : ℝ) by norm_num, show 1+(38414921890219613/100000000000000000000 : ℝ)+(6048862714327793/100000000000000000000 : ℝ)=(50022231892302273703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38414921890219613/100000000000000000000 : ℝ) ≤ ((5568599563144086101/5570000000000000000 : ℝ)+2*(378953212151/278500000000000 : ℝ)*(317/2000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (5568599563144086101/5570000000000000000 : ℝ)+2*(378953212151/278500000000000 : ℝ)*(317/2000 : ℝ)=(10001799149926613/10000000000000000 : ℝ) by norm_num, show 1+2*(38414921890219613/100000000000000000000 : ℝ)=(50038414921890219613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5568599563144086101/5570000000000000000 : ℝ)*(X 1 0+X 2 0)+(378953212151/278500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (317/2000 : ℝ)) (c := (5568599563144086101/5570000000000000000 : ℝ)) (alpha := (378953212151/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5568599563144086101/5570000000000000000 : ℝ)*(X 0 1+X 2 1)+(378953212151/278500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (317/2000 : ℝ)) (c := (5568599563144086101/5570000000000000000 : ℝ)) (alpha := (378953212151/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5568599563144086101/5570000000000000000 : ℝ)*(X 0 2+X 1 2)+(378953212151/278500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (317/2000 : ℝ)) (c := (5568599563144086101/5570000000000000000 : ℝ)) (alpha := (378953212151/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1983025331/10000000000 : ℝ)*X 0 0+(541893349/1000000000 : ℝ)*X 0 1+(5237412637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337551673/2500000000 : ℝ)*X 1 0+(-2075647603/10000000000 : ℝ)*X 1 1+(104748251/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675103317/5000000000 : ℝ)*X 2 0+(5237412667/10000000000 : ℝ)*X 2 1+(-83025901/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307682069/10000000000 : ℝ)*X 0 0+(514561433/1250000000 : ℝ)*X 0 1+(4506880883/10000000000 : ℝ)*X 0 2+(4307682069/10000000000 : ℝ)*X 1 0+(514561433/1250000000 : ℝ)*X 1 1+(4506880883/10000000000 : ℝ)*X 1 2+(4307682069/10000000000 : ℝ)*X 2 0+(514561433/1250000000 : ℝ)*X 2 1+(4506880883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-99152079/500000000 : ℝ)*X 0 0+(5238142329/10000000000 : ℝ)*X 0 1+(5418199381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651545957/5000000000 : ℝ)*X 1 0+(-1894860297/10000000000 : ℝ)*X 1 1+(5418199599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303092623/10000000000 : ℝ)*X 2 0+(169318719/312500000 : ℝ)*X 2 1+(-1894860141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153858619/5000000000 : ℝ)*X 0 0+(2252655637/5000000000 : ℝ)*X 0 1+(2059034663/5000000000 : ℝ)*X 0 2+(2153858619/5000000000 : ℝ)*X 1 0+(2252655637/5000000000 : ℝ)*X 1 1+(2059034663/5000000000 : ℝ)*X 1 2+(2153858619/5000000000 : ℝ)*X 2 0+(2252655637/5000000000 : ℝ)*X 2 1+(2059034663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-4246581/2000000000 : ℝ)*X 0 0+(5717063941/10000000000 : ℝ)*X 0 1+(755113791/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((521266901/5000000000 : ℝ)*X 1 0+(-1045623019/2500000000 : ℝ)*X 1 1+(1749378081/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1042541281/10000000000 : ℝ)*X 2 0+(1399505767/2000000000 : ℝ)*X 2 1+(-2091233931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1473668171/10000000000 : ℝ)*X 0 0+(5658912917/10000000000 : ℝ)*X 0 1+(2677761011/5000000000 : ℝ)*X 0 2+(1473668171/10000000000 : ℝ)*X 1 0+(5658912917/10000000000 : ℝ)*X 1 1+(2677761011/5000000000 : ℝ)*X 1 2+(1473668171/10000000000 : ℝ)*X 2 0+(5658912917/10000000000 : ℝ)*X 2 1+(2677761011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1258843521478813349793329709/139250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1316137/25000000000000 : ℝ)*(lower5) + (2017639933388397/50000000000000 : ℝ)*(major0) + (2017639933388397/50000000000000 : ℝ)*(major1) + (807055973355359/20000000000000 : ℝ)*(major2) + (5509011623520063/100000000000000 : ℝ)*(sp0) + (220360358530791/4000000000000 : ℝ)*(sp1) + (550901214304133/10000000000000 : ℝ)*(sp2) + (2561545557398433/100000000000000 : ℝ)*(sp3) + (866223393/25000000000000 : ℝ)*(sp5) + (10154799/3125000000000 : ℝ)*(sp6) + (1326704933/100000000000000 : ℝ)*(sp8) + (522061647/100000000000000 : ℝ)*(sp9) + (482230097/100000000000000 : ℝ)*(sp10) + (924591189/100000000000000 : ℝ)*(sp11) + (1280773240994811/50000000000000 : ℝ)*(f.failure) + (1101802590044999/20000000000000 : ℝ)*(f.sum) + (50503950122639/27850000000000000000000000000 : ℝ)*base65 + (1214638237665179903/278500000000000000000000000000000 : ℝ)*base68 + (1031651885171458741/111400000000000000000000000000000 : ℝ)*base70 + (1718565217059820097/278500000000000000000000000000000 : ℝ)*base71 + (71265070554539/27850000000000000000000000000 : ℝ)*base73 + (814078195927141259/111400000000000000000000000000000 : ℝ)*base75 + (1055219915026810097/278500000000000000000000000000000 : ℝ)*base77 + (894327864672310097/278500000000000000000000000000000 : ℝ)*base79 + (88243989234769/13925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (3299301/1000000000000000000000 : ℝ)*base89 + (3299301/1000000000000000000000 : ℝ)*base91 + (6700699/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (265571709756790320657725727/278500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17586837/10000000000000 : ℝ)*(lower5) + (254255101338969/6250000000000 : ℝ)*(major0) + (254255101338969/6250000000000 : ℝ)*(major1) + (813616324284701/20000000000000 : ℝ)*(major2) + (2106752747/100000000000000 : ℝ)*(sp0) + (246614/6103515625 : ℝ)*(sp1) + (5553790470589767/100000000000000 : ℝ)*(sp4) + (5553790292051983/100000000000000 : ℝ)*(sp5) + (694224181630987/12500000000000 : ℝ)*(sp6) + (2582367234187563/100000000000000 : ℝ)*(sp7) + (399525993/20000000000000 : ℝ)*(sp8) + (3029959/1250000000000 : ℝ)*(sp9) + (560962291/50000000000000 : ℝ)*(sp10) + (1401900997/100000000000000 : ℝ)*(sp11) + (32279607951107/1250000000000 : ℝ)*(f.failure) + (2776897287486239/50000000000000 : ℝ)*(f.sum) + (88981192670209/27850000000000000000000000000 : ℝ)*base65 + (769524999290423881/34812500000000000000000000000000 : ℝ)*base68 + (1268433115091743199/111400000000000000000000000000000 : ℝ)*base70 + (245293358933048881/34812500000000000000000000000000 : ℝ)*base72 + (165378982007159/27850000000000000000000000000 : ℝ)*base73 + (616001671337143199/111400000000000000000000000000000 : ℝ)*base76 + (102957014747737631/34812500000000000000000000000000 : ℝ)*base78 + (149863390825637369/34812500000000000000000000000000 : ℝ)*base79 + (2375223957001/3481250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (246237/25000000000000000000 : ℝ)*base89 + (246237/25000000000000000000 : ℝ)*base91 + (3763/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1413_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1413_s4_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984011749/10000000000 : ℝ)*x 0 + (2705292519/5000000000 : ℝ)*x 1 + (65563897/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984011749/10000000000 : ℝ)^4373 ≤ (12099274204169/100000000000000 : ℝ)^3349 := by
    have hnat : (1984011749 : ℕ)^4373*100000000000000^3349 ≤ 12099274204169^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984011749 10000000000 12099274204169 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705292519/5000000000 : ℝ)^4373 ≤ (11210376882027/25000000000000 : ℝ)^3349 := by
    have hnat : (2705292519 : ℕ)^4373*25000000000000^3349 ≤ 11210376882027^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705292519 5000000000 11210376882027 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65563897/125000000 : ℝ)^4373 ≤ (21529609125897/50000000000000 : ℝ)^3349 := by
    have hnat : (65563897 : ℕ)^4373*50000000000000^3349 ≤ 21529609125897^3349*125000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65563897 125000000 21529609125897 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984011749/10000000000 : ℝ), (2705292519/5000000000 : ℝ), (65563897/125000000 : ℝ)] ![(12099274204169/100000000000000 : ℝ), (11210376882027/25000000000000 : ℝ), (21529609125897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984011749/10000000000 : ℝ)|^4373 ≤ (12099274204169/100000000000000 : ℝ)^3349
        have hw : |(-1984011749/10000000000 : ℝ)|=(1984011749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705292519/5000000000 : ℝ)|^4373 ≤ (11210376882027/25000000000000 : ℝ)^3349
        have hw : |(2705292519/5000000000 : ℝ)|=(2705292519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65563897/125000000 : ℝ)|^4373 ≤ (21529609125897/50000000000000 : ℝ)^3349
        have hw : |(65563897/125000000 : ℝ)|=(65563897/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674028129/5000000000 : ℝ)*x 0 + (-413659173/2000000000 : ℝ)*x 1 + (2622555927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674028129/5000000000 : ℝ)^4373 ≤ (44166031095643/100000000000000 : ℝ)^3349 := by
    have hnat : (2674028129 : ℕ)^4373*100000000000000^3349 ≤ 44166031095643^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674028129 5000000000 44166031095643 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413659173/2000000000 : ℝ)^4373 ≤ (2554949926053/20000000000000 : ℝ)^3349 := by
    have hnat : (413659173 : ℕ)^4373*20000000000000^3349 ≤ 2554949926053^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413659173 2000000000 2554949926053 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622555927/5000000000 : ℝ)^4373 ≤ (43059219259429/100000000000000 : ℝ)^3349 := by
    have hnat : (2622555927 : ℕ)^4373*100000000000000^3349 ≤ 43059219259429^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622555927 5000000000 43059219259429 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674028129/5000000000 : ℝ), (-413659173/2000000000 : ℝ), (2622555927/5000000000 : ℝ)] ![(44166031095643/100000000000000 : ℝ), (2554949926053/20000000000000 : ℝ), (43059219259429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674028129/5000000000 : ℝ)|^4373 ≤ (44166031095643/100000000000000 : ℝ)^3349
        have hw : |(2674028129/5000000000 : ℝ)|=(2674028129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413659173/2000000000 : ℝ)|^4373 ≤ (2554949926053/20000000000000 : ℝ)^3349
        have hw : |(-413659173/2000000000 : ℝ)|=(413659173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622555927/5000000000 : ℝ)|^4373 ≤ (43059219259429/100000000000000 : ℝ)^3349
        have hw : |(2622555927/5000000000 : ℝ)|=(2622555927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337014061/2500000000 : ℝ)*x 0 + (5245111699/10000000000 : ℝ)*x 1 + (-2068296089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337014061/2500000000 : ℝ)^4373 ≤ (1766641237787/4000000000000 : ℝ)^3349 := by
    have hnat : (1337014061 : ℕ)^4373*4000000000000^3349 ≤ 1766641237787^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337014061 2500000000 1766641237787 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245111699/10000000000 : ℝ)^4373 ≤ (21529608798951/50000000000000 : ℝ)^3349 := by
    have hnat : (5245111699 : ℕ)^4373*50000000000000^3349 ≤ 21529608798951^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245111699 10000000000 21529608798951 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068296089/10000000000 : ℝ)^4373 ≤ (1596843929603/12500000000000 : ℝ)^3349 := by
    have hnat : (2068296089 : ℕ)^4373*12500000000000^3349 ≤ 1596843929603^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068296089 10000000000 1596843929603 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337014061/2500000000 : ℝ), (5245111699/10000000000 : ℝ), (-2068296089/10000000000 : ℝ)] ![(1766641237787/4000000000000 : ℝ), (21529608798951/50000000000000 : ℝ), (1596843929603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337014061/2500000000 : ℝ)|^4373 ≤ (1766641237787/4000000000000 : ℝ)^3349
        have hw : |(1337014061/2500000000 : ℝ)|=(1337014061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245111699/10000000000 : ℝ)|^4373 ≤ (21529608798951/50000000000000 : ℝ)^3349
        have hw : |(5245111699/10000000000 : ℝ)|=(5245111699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068296089/10000000000 : ℝ)|^4373 ≤ (1596843929603/12500000000000 : ℝ)^3349
        have hw : |(-2068296089/10000000000 : ℝ)|=(2068296089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861656981/2000000000 : ℝ)*x 0 + (1033418759/2500000000 : ℝ)*x 1 + (897910279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861656981/2000000000 : ℝ)^4373 ≤ (2081461033067/6250000000000 : ℝ)^3349 := by
    have hnat : (861656981 : ℕ)^4373*6250000000000^3349 ≤ 2081461033067^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861656981 2000000000 2081461033067 6250000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033418759/2500000000 : ℝ)^4373 ≤ (7887987605867/25000000000000 : ℝ)^3349 := by
    have hnat : (1033418759 : ℕ)^4373*25000000000000^3349 ≤ 7887987605867^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033418759 2500000000 7887987605867 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897910279/2000000000 : ℝ)^4373 ≤ (35144673035681/100000000000000 : ℝ)^3349 := by
    have hnat : (897910279 : ℕ)^4373*100000000000000^3349 ≤ 35144673035681^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897910279 2000000000 35144673035681 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861656981/2000000000 : ℝ), (1033418759/2500000000 : ℝ), (897910279/2000000000 : ℝ)] ![(2081461033067/6250000000000 : ℝ), (7887987605867/25000000000000 : ℝ), (35144673035681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861656981/2000000000 : ℝ)|^4373 ≤ (2081461033067/6250000000000 : ℝ)^3349
        have hw : |(861656981/2000000000 : ℝ)|=(861656981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033418759/2500000000 : ℝ)|^4373 ≤ (7887987605867/25000000000000 : ℝ)^3349
        have hw : |(1033418759/2500000000 : ℝ)|=(1033418759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897910279/2000000000 : ℝ)|^4373 ≤ (35144673035681/100000000000000 : ℝ)^3349
        have hw : |(897910279/2000000000 : ℝ)|=(897910279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984024113/10000000000 : ℝ)*x 0 + (655714797/1250000000 : ℝ)*x 1 + (5409975037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984024113/10000000000 : ℝ)^4373 ≤ (2419874531881/20000000000000 : ℝ)^3349 := by
    have hnat : (1984024113 : ℕ)^4373*20000000000000^3349 ≤ 2419874531881^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984024113 10000000000 2419874531881 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655714797/1250000000 : ℝ)^4373 ≤ (43065721004881/100000000000000 : ℝ)^3349 := by
    have hnat : (655714797 : ℕ)^4373*100000000000000^3349 ≤ 43065721004881^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655714797 1250000000 43065721004881 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409975037/10000000000 : ℝ)^4373 ≤ (44834906320851/100000000000000 : ℝ)^3349 := by
    have hnat : (5409975037 : ℕ)^4373*100000000000000^3349 ≤ 44834906320851^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409975037 10000000000 44834906320851 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984024113/10000000000 : ℝ), (655714797/1250000000 : ℝ), (5409975037/10000000000 : ℝ)] ![(2419874531881/20000000000000 : ℝ), (43065721004881/100000000000000 : ℝ), (44834906320851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984024113/10000000000 : ℝ)|^4373 ≤ (2419874531881/20000000000000 : ℝ)^3349
        have hw : |(-1984024113/10000000000 : ℝ)|=(1984024113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655714797/1250000000 : ℝ)|^4373 ≤ (43065721004881/100000000000000 : ℝ)^3349
        have hw : |(655714797/1250000000 : ℝ)|=(655714797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409975037/10000000000 : ℝ)|^4373 ≤ (44834906320851/100000000000000 : ℝ)^3349
        have hw : |(5409975037/10000000000 : ℝ)|=(5409975037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326276489/2500000000 : ℝ)*x 0 + (-475858099/2500000000 : ℝ)*x 1 + (540997551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326276489/2500000000 : ℝ)^4373 ≤ (43703449434203/100000000000000 : ℝ)^3349 := by
    have hnat : (1326276489 : ℕ)^4373*100000000000000^3349 ≤ 43703449434203^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326276489 2500000000 43703449434203 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475858099/2500000000 : ℝ)^4373 ≤ (1146163910797/10000000000000 : ℝ)^3349 := by
    have hnat : (475858099 : ℕ)^4373*10000000000000^3349 ≤ 1146163910797^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475858099 2500000000 1146163910797 10000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540997551/1000000000 : ℝ)^4373 ≤ (11208727859849/25000000000000 : ℝ)^3349 := by
    have hnat : (540997551 : ℕ)^4373*25000000000000^3349 ≤ 11208727859849^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540997551 1000000000 11208727859849 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326276489/2500000000 : ℝ), (-475858099/2500000000 : ℝ), (540997551/1000000000 : ℝ)] ![(43703449434203/100000000000000 : ℝ), (1146163910797/10000000000000 : ℝ), (11208727859849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326276489/2500000000 : ℝ)|^4373 ≤ (43703449434203/100000000000000 : ℝ)^3349
        have hw : |(1326276489/2500000000 : ℝ)|=(1326276489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475858099/2500000000 : ℝ)|^4373 ≤ (1146163910797/10000000000000 : ℝ)^3349
        have hw : |(-475858099/2500000000 : ℝ)|=(475858099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540997551/1000000000 : ℝ)|^4373 ≤ (11208727859849/25000000000000 : ℝ)^3349
        have hw : |(540997551/1000000000 : ℝ)|=(540997551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652552977/5000000000 : ℝ)*x 0 + (5409975207/10000000000 : ℝ)*x 1 + (-1903432817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652552977/5000000000 : ℝ)^4373 ≤ (43703449412689/100000000000000 : ℝ)^3349 := by
    have hnat : (2652552977 : ℕ)^4373*100000000000000^3349 ≤ 43703449412689^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652552977 5000000000 43703449412689 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409975207/10000000000 : ℝ)^4373 ≤ (44834908160497/100000000000000 : ℝ)^3349 := by
    have hnat : (5409975207 : ℕ)^4373*100000000000000^3349 ≤ 44834908160497^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409975207 10000000000 44834908160497 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903432817/10000000000 : ℝ)^4373 ≤ (11461642418181/100000000000000 : ℝ)^3349 := by
    have hnat : (1903432817 : ℕ)^4373*100000000000000^3349 ≤ 11461642418181^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903432817 10000000000 11461642418181 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652552977/5000000000 : ℝ), (5409975207/10000000000 : ℝ), (-1903432817/10000000000 : ℝ)] ![(43703449412689/100000000000000 : ℝ), (44834908160497/100000000000000 : ℝ), (11461642418181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652552977/5000000000 : ℝ)|^4373 ≤ (43703449412689/100000000000000 : ℝ)^3349
        have hw : |(2652552977/5000000000 : ℝ)|=(2652552977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409975207/10000000000 : ℝ)|^4373 ≤ (44834908160497/100000000000000 : ℝ)^3349
        have hw : |(5409975207/10000000000 : ℝ)|=(5409975207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903432817/10000000000 : ℝ)|^4373 ≤ (11461642418181/100000000000000 : ℝ)^3349
        have hw : |(-1903432817/10000000000 : ℝ)|=(1903432817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s4_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308310691/10000000000 : ℝ)*x 0 + (4488246533/10000000000 : ℝ)*x 1 + (4134987029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308310691/10000000000 : ℝ)^4373 ≤ (16651818402067/50000000000000 : ℝ)^3349 := by
    have hnat : (4308310691 : ℕ)^4373*50000000000000^3349 ≤ 16651818402067^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308310691 10000000000 16651818402067 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488246533/10000000000 : ℝ)^4373 ≤ (35131335789297/100000000000000 : ℝ)^3349 := by
    have hnat : (4488246533 : ℕ)^4373*100000000000000^3349 ≤ 35131335789297^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488246533 10000000000 35131335789297 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4134987029/10000000000 : ℝ)^4373 ≤ (3945628422943/12500000000000 : ℝ)^3349 := by
    have hnat : (4134987029 : ℕ)^4373*12500000000000^3349 ≤ 3945628422943^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134987029 10000000000 3945628422943 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308310691/10000000000 : ℝ), (4488246533/10000000000 : ℝ), (4134987029/10000000000 : ℝ)] ![(16651818402067/50000000000000 : ℝ), (35131335789297/100000000000000 : ℝ), (3945628422943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308310691/10000000000 : ℝ)|^4373 ≤ (16651818402067/50000000000000 : ℝ)^3349
        have hw : |(4308310691/10000000000 : ℝ)|=(4308310691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488246533/10000000000 : ℝ)|^4373 ≤ (35131335789297/100000000000000 : ℝ)^3349
        have hw : |(4488246533/10000000000 : ℝ)|=(4488246533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4134987029/10000000000 : ℝ)|^4373 ≤ (3945628422943/12500000000000 : ℝ)^3349
        have hw : |(4134987029/10000000000 : ℝ)|=(4134987029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2819/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14781/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/12500 : ℝ) ^ (1093/256 : ℝ) ≤ (4216480760200449/50000000000000000000 : ℝ) := by
    have hpowers : (1389/12500 : ℝ)^1093 ≤ (4216480760200449/50000000000000000000 : ℝ)^256 := by
      have hnat : (1389 : ℕ)^1093*50000000000000000000^256 ≤ 4216480760200449^256*12500^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 12500 4216480760200449 50000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/12500 : ℝ)) (X := (4216480760200449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2991/20000 : ℝ) ^ (1093/256 : ℝ) ≤ (29972627825422609/100000000000000000000 : ℝ) := by
    have hpowers : (2991/20000 : ℝ)^1093 ≤ (29972627825422609/100000000000000000000 : ℝ)^256 := by
      have hnat : (2991 : ℕ)^1093*100000000000000000000^256 ≤ 29972627825422609^256*20000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2991 20000 29972627825422609 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2991/20000 : ℝ)) (X := (29972627825422609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004216480760200449/25000000000000000000 : ℝ) ≤ (5000197502172859/5000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (25004216480760200449/25000000000000000000 : ℝ)^256 ≤ (5000197502172859/5000000000000000 : ℝ)^1093 := by
      have hnat : (25004216480760200449 : ℕ)^256*5000000000000000^1093 ≤ 5000197502172859^1093*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004216480760200449 25000000000000000000 5000197502172859 5000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000197502172859/5000000000000000 : ℝ)) (X := (25004216480760200449/25000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038405589345823507/100000000000000000000 : ℝ) ≤ (1000089939482277/1000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (100038405589345823507/100000000000000000000 : ℝ)^256 ≤ (1000089939482277/1000000000000000 : ℝ)^1093 := by
      have hnat : (100038405589345823507 : ℕ)^256*1000000000000000^1093 ≤ 1000089939482277^1093*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038405589345823507 100000000000000000000 1000089939482277 1000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000089939482277/1000000000000000 : ℝ)) (X := (100038405589345823507/100000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029972627825422609/50000000000000000000 : ℝ) ≤ (5000701892649911/5000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50029972627825422609/50000000000000000000 : ℝ)^256 ≤ (5000701892649911/5000000000000000 : ℝ)^1093 := by
      have hnat : (50029972627825422609 : ℕ)^256*5000000000000000^1093 ≤ 5000701892649911^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029972627825422609 50000000000000000000 5000701892649911 5000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000701892649911/5000000000000000 : ℝ)) (X := (50029972627825422609/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4216480760200449/50000000000000000000 : ℝ) ≤ ((914769248279490253/915000000000000000 : ℝ)+2*(18013945609/13725000000000 : ℝ)*(1389/12500 : ℝ))^(1093/256 : ℝ) := by
    rw [show (914769248279490253/915000000000000000 : ℝ)+2*(18013945609/13725000000000 : ℝ)*(1389/12500 : ℝ)=(5000197502172859/5000000000000000 : ℝ) by norm_num, show 1+2*(4216480760200449/50000000000000000000 : ℝ)=(25004216480760200449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29972627825422609/100000000000000000000 : ℝ)+(4216480760200449/50000000000000000000 : ℝ) ≤ ((914769248279490253/915000000000000000 : ℝ)+(18013945609/13725000000000 : ℝ)*((2991/20000 : ℝ)+(1389/12500 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (914769248279490253/915000000000000000 : ℝ)+(18013945609/13725000000000 : ℝ)*((2991/20000 : ℝ)+(1389/12500 : ℝ))=(1000089939482277/1000000000000000 : ℝ) by norm_num, show 1+(29972627825422609/100000000000000000000 : ℝ)+(4216480760200449/50000000000000000000 : ℝ)=(100038405589345823507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29972627825422609/100000000000000000000 : ℝ) ≤ ((914769248279490253/915000000000000000 : ℝ)+2*(18013945609/13725000000000 : ℝ)*(2991/20000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (914769248279490253/915000000000000000 : ℝ)+2*(18013945609/13725000000000 : ℝ)*(2991/20000 : ℝ)=(5000701892649911/5000000000000000 : ℝ) by norm_num, show 1+2*(29972627825422609/100000000000000000000 : ℝ)=(50029972627825422609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (914769248279490253/915000000000000000 : ℝ)*(X 1 0+X 2 0)+(18013945609/13725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (914769248279490253/915000000000000000 : ℝ)) (alpha := (18013945609/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (914769248279490253/915000000000000000 : ℝ)*(X 0 1+X 2 1)+(18013945609/13725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (914769248279490253/915000000000000000 : ℝ)) (alpha := (18013945609/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (914769248279490253/915000000000000000 : ℝ)*(X 0 2+X 1 2)+(18013945609/13725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (914769248279490253/915000000000000000 : ℝ)) (alpha := (18013945609/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984011749/10000000000 : ℝ)*X 0 0+(2705292519/5000000000 : ℝ)*X 0 1+(65563897/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674028129/5000000000 : ℝ)*X 1 0+(-413659173/2000000000 : ℝ)*X 1 1+(2622555927/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337014061/2500000000 : ℝ)*X 2 0+(5245111699/10000000000 : ℝ)*X 2 1+(-2068296089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861656981/2000000000 : ℝ)*X 0 0+(1033418759/2500000000 : ℝ)*X 0 1+(897910279/2000000000 : ℝ)*X 0 2+(861656981/2000000000 : ℝ)*X 1 0+(1033418759/2500000000 : ℝ)*X 1 1+(897910279/2000000000 : ℝ)*X 1 2+(861656981/2000000000 : ℝ)*X 2 0+(1033418759/2500000000 : ℝ)*X 2 1+(897910279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1984024113/10000000000 : ℝ)*X 0 0+(655714797/1250000000 : ℝ)*X 0 1+(5409975037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326276489/2500000000 : ℝ)*X 1 0+(-475858099/2500000000 : ℝ)*X 1 1+(540997551/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652552977/5000000000 : ℝ)*X 2 0+(5409975207/10000000000 : ℝ)*X 2 1+(-1903432817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308310691/10000000000 : ℝ)*X 0 0+(4488246533/10000000000 : ℝ)*X 0 1+(4134987029/10000000000 : ℝ)*X 0 2+(4308310691/10000000000 : ℝ)*X 1 0+(4488246533/10000000000 : ℝ)*X 1 1+(4134987029/10000000000 : ℝ)*X 1 2+(4308310691/10000000000 : ℝ)*X 2 0+(4488246533/10000000000 : ℝ)*X 2 1+(4134987029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20429954916189349788909793/1830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1617498773/100000000000000 : ℝ)*(base19) + (1542342697/100000000000000 : ℝ)*(base23) + (31733219/100000000000000 : ℝ)*(lower2) + (18384719/5000000000000 : ℝ)*(upper3) + (42223547/100000000000000 : ℝ)*(upper5) + (2213333390428029/50000000000000 : ℝ)*(major0) + (2213333390428029/50000000000000 : ℝ)*(major1) + (4426666780856059/100000000000000 : ℝ)*(major2) + (241732450825807/4000000000000 : ℝ)*(sp0) + (30216687234091/500000000000 : ℝ)*(sp1) + (1510834380493569/25000000000000 : ℝ)*(sp2) + (702494221963443/25000000000000 : ℝ)*(sp3) + (13896835899/50000000000000 : ℝ)*(sp4) + (107733819/625000000000 : ℝ)*(sp7) + (702498531316203/25000000000000 : ℝ)*(f.failure) + (6043339064316973/100000000000000 : ℝ)*(f.sum) + (12826214581489/2745000000000000000000000000 : ℝ)*base66 + (175882652618895989/137250000000000000000000000000000 : ℝ)*base68 + (68834363837707073/91500000000000000000000000000000 : ℝ)*base70 + (825023558971395989/137250000000000000000000000000000 : ℝ)*base72 + (1123359241967/1372500000000000000000000000 : ℝ)*base74 + (203547825908707073/91500000000000000000000000000000 : ℝ)*base76 + (202750416377366221/15250000000000000000000000000000 : ℝ)*base78 + (94181021105366221/15250000000000000000000000000000 : ℝ)*base80 + (82280994431/38125000000000000000000000 : ℝ)*base82 + (9593973/500000000000000000000 : ℝ)*base89 + (9593973/500000000000000000000 : ℝ)*base91 + (4593973/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42193199727217676350905023/4575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215670629/25000000000000 : ℝ)*(base19) + (1150192917/100000000000000 : ℝ)*(base23) + (209233219/100000000000000 : ℝ)*(upper2) + (63411759/50000000000000 : ℝ)*(upper3) + (9130001/3125000000000 : ℝ)*(upper5) + (445940479254697/10000000000000 : ℝ)*(major0) + (445940479254697/10000000000000 : ℝ)*(major1) + (445940479254697/10000000000000 : ℝ)*(major2) + (4224049933/12500000000000 : ℝ)*(sp1) + (10436609129/50000000000000 : ℝ)*(sp2) + (1217606692312623/20000000000000 : ℝ)*(sp4) + (1217599761296227/20000000000000 : ℝ)*(sp5) + (6088011438151941/100000000000000 : ℝ)*(sp6) + (1415387908056117/50000000000000 : ℝ)*(sp7) + (1415387908056117/50000000000000 : ℝ)*(f.failure) + (1217606692312623/20000000000000 : ℝ)*(f.sum) + (304206971033/549000000000000000000000000 : ℝ)*base65 + (156845877985605023/27450000000000000000000000000000 : ℝ)*base67 + (75023917332944977/27450000000000000000000000000000 : ℝ)*base70 + (71089511300805023/27450000000000000000000000000000 : ℝ)*base71 + (1831654463293/274500000000000000000000000 : ℝ)*base73 + (135597553742894977/27450000000000000000000000000000 : ℝ)*base76 + (67705207089494977/27450000000000000000000000000000 : ℝ)*base78 + (487840042667444977/27450000000000000000000000000000 : ℝ)*base80 + (504553360961/549000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16632853/1000000000000000000000 : ℝ)*base90 + (16632853/1000000000000000000000 : ℝ)*base92 + (16632853/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1413_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1413_s5_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-992081279/5000000000 : ℝ)*x 0 + (84519589/156250000 : ℝ)*x 1 + (5246343681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992081279/5000000000 : ℝ)^4373 ≤ (12100475117639/100000000000000 : ℝ)^3349 := by
    have hnat : (992081279 : ℕ)^4373*100000000000000^3349 ≤ 12100475117639^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992081279 5000000000 12100475117639 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84519589/156250000 : ℝ)^4373 ≤ (22413550263301/50000000000000 : ℝ)^3349 := by
    have hnat : (84519589 : ℕ)^4373*50000000000000^3349 ≤ 22413550263301^3349*156250000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84519589 156250000 22413550263301 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246343681/10000000000 : ℝ)^4373 ≤ (5384053042433/12500000000000 : ℝ)^3349 := by
    have hnat : (5246343681 : ℕ)^4373*12500000000000^3349 ≤ 5384053042433^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246343681 10000000000 5384053042433 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-992081279/5000000000 : ℝ), (84519589/156250000 : ℝ), (5246343681/10000000000 : ℝ)] ![(12100475117639/100000000000000 : ℝ), (22413550263301/50000000000000 : ℝ), (5384053042433/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-992081279/5000000000 : ℝ)|^4373 ≤ (12100475117639/100000000000000 : ℝ)^3349
        have hw : |(-992081279/5000000000 : ℝ)|=(992081279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84519589/156250000 : ℝ)|^4373 ≤ (22413550263301/50000000000000 : ℝ)^3349
        have hw : |(84519589/156250000 : ℝ)|=(84519589/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246343681/10000000000 : ℝ)|^4373 ≤ (5384053042433/12500000000000 : ℝ)^3349
        have hw : |(5246343681/10000000000 : ℝ)|=(5246343681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673856537/5000000000 : ℝ)*x 0 + (-516779489/2500000000 : ℝ)*x 1 + (655792897/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673856537/5000000000 : ℝ)^4373 ≤ (441623304329/1000000000000 : ℝ)^3349 := by
    have hnat : (2673856537 : ℕ)^4373*1000000000000^3349 ≤ 441623304329^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673856537 5000000000 441623304329 1000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516779489/2500000000 : ℝ)^4373 ≤ (12765250628157/100000000000000 : ℝ)^3349 := by
    have hnat : (516779489 : ℕ)^4373*100000000000000^3349 ≤ 12765250628157^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516779489 2500000000 12765250628157 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655792897/1250000000 : ℝ)^4373 ≤ (2692026182857/6250000000000 : ℝ)^3349 := by
    have hnat : (655792897 : ℕ)^4373*6250000000000^3349 ≤ 2692026182857^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655792897 1250000000 2692026182857 6250000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673856537/5000000000 : ℝ), (-516779489/2500000000 : ℝ), (655792897/1250000000 : ℝ)] ![(441623304329/1000000000000 : ℝ), (12765250628157/100000000000000 : ℝ), (2692026182857/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673856537/5000000000 : ℝ)|^4373 ≤ (441623304329/1000000000000 : ℝ)^3349
        have hw : |(2673856537/5000000000 : ℝ)|=(2673856537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516779489/2500000000 : ℝ)|^4373 ≤ (12765250628157/100000000000000 : ℝ)^3349
        have hw : |(-516779489/2500000000 : ℝ)|=(516779489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655792897/1250000000 : ℝ)|^4373 ≤ (2692026182857/6250000000000 : ℝ)^3349
        have hw : |(655792897/1250000000 : ℝ)|=(655792897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336928223/2500000000 : ℝ)*x 0 + (5246343529/10000000000 : ℝ)*x 1 + (-206711773/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336928223/2500000000 : ℝ)^4373 ≤ (8832465694071/20000000000000 : ℝ)^3349 := by
    have hnat : (1336928223 : ℕ)^4373*20000000000000^3349 ≤ 8832465694071^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336928223 2500000000 8832465694071 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246343529/10000000000 : ℝ)^4373 ≤ (21536211354989/50000000000000 : ℝ)^3349 := by
    have hnat : (5246343529 : ℕ)^4373*50000000000000^3349 ≤ 21536211354989^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246343529 10000000000 21536211354989 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206711773/1000000000 : ℝ)^4373 ≤ (6382624402893/50000000000000 : ℝ)^3349 := by
    have hnat : (206711773 : ℕ)^4373*50000000000000^3349 ≤ 6382624402893^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206711773 1000000000 6382624402893 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336928223/2500000000 : ℝ), (5246343529/10000000000 : ℝ), (-206711773/1000000000 : ℝ)] ![(8832465694071/20000000000000 : ℝ), (21536211354989/50000000000000 : ℝ), (6382624402893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336928223/2500000000 : ℝ)|^4373 ≤ (8832465694071/20000000000000 : ℝ)^3349
        have hw : |(1336928223/2500000000 : ℝ)|=(1336928223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246343529/10000000000 : ℝ)|^4373 ≤ (21536211354989/50000000000000 : ℝ)^3349
        have hw : |(5246343529/10000000000 : ℝ)|=(5246343529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206711773/1000000000 : ℝ)|^4373 ≤ (6382624402893/50000000000000 : ℝ)^3349
        have hw : |(-206711773/1000000000 : ℝ)|=(206711773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308375969/10000000000 : ℝ)*x 0 + (33091357/80000000 : ℝ)*x 1 + (4486784787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308375969/10000000000 : ℝ)^4373 ≤ (1665214785003/5000000000000 : ℝ)^3349 := by
    have hnat : (4308375969 : ℕ)^4373*5000000000000^3349 ≤ 1665214785003^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308375969 10000000000 1665214785003 5000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33091357/80000000 : ℝ)^4373 ≤ (3947413484087/12500000000000 : ℝ)^3349 := by
    have hnat : (33091357 : ℕ)^4373*12500000000000^3349 ≤ 3947413484087^3349*80000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33091357 80000000 3947413484087 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486784787/10000000000 : ℝ)^4373 ≤ (8779099102301/25000000000000 : ℝ)^3349 := by
    have hnat : (4486784787 : ℕ)^4373*25000000000000^3349 ≤ 8779099102301^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486784787 10000000000 8779099102301 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308375969/10000000000 : ℝ), (33091357/80000000 : ℝ), (4486784787/10000000000 : ℝ)] ![(1665214785003/5000000000000 : ℝ), (3947413484087/12500000000000 : ℝ), (8779099102301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308375969/10000000000 : ℝ)|^4373 ≤ (1665214785003/5000000000000 : ℝ)^3349
        have hw : |(4308375969/10000000000 : ℝ)|=(4308375969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33091357/80000000 : ℝ)|^4373 ≤ (3947413484087/12500000000000 : ℝ)^3349
        have hw : |(33091357/80000000 : ℝ)|=(33091357/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486784787/10000000000 : ℝ)|^4373 ≤ (8779099102301/25000000000000 : ℝ)^3349
        have hw : |(4486784787/10000000000 : ℝ)|=(4486784787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79366963/400000000 : ℝ)*x 0 + (1049386319/2000000000 : ℝ)*x 1 + (5408662759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79366963/400000000 : ℝ)^4373 ≤ (3025141707573/25000000000000 : ℝ)^3349 := by
    have hnat : (79366963 : ℕ)^4373*25000000000000^3349 ≤ 3025141707573^3349*400000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79366963 400000000 3025141707573 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049386319/2000000000 : ℝ)^4373 ≤ (43078727061463/100000000000000 : ℝ)^3349 := by
    have hnat : (1049386319 : ℕ)^4373*100000000000000^3349 ≤ 43078727061463^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049386319 2000000000 43078727061463 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408662759/10000000000 : ℝ)^4373 ≤ (44820706100721/100000000000000 : ℝ)^3349 := by
    have hnat : (5408662759 : ℕ)^4373*100000000000000^3349 ≤ 44820706100721^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408662759 10000000000 44820706100721 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79366963/400000000 : ℝ), (1049386319/2000000000 : ℝ), (5408662759/10000000000 : ℝ)] ![(3025141707573/25000000000000 : ℝ), (43078727061463/100000000000000 : ℝ), (44820706100721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79366963/400000000 : ℝ)|^4373 ≤ (3025141707573/25000000000000 : ℝ)^3349
        have hw : |(-79366963/400000000 : ℝ)|=(79366963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049386319/2000000000 : ℝ)|^4373 ≤ (43078727061463/100000000000000 : ℝ)^3349
        have hw : |(1049386319/2000000000 : ℝ)|=(1049386319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408662759/10000000000 : ℝ)|^4373 ≤ (44820706100721/100000000000000 : ℝ)^3349
        have hw : |(5408662759/10000000000 : ℝ)|=(5408662759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652713967/5000000000 : ℝ)*x 0 + (-119049901/625000000 : ℝ)*x 1 + (5408662759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652713967/5000000000 : ℝ)^4373 ≤ (21853456471169/50000000000000 : ℝ)^3349 := by
    have hnat : (2652713967 : ℕ)^4373*50000000000000^3349 ≤ 21853456471169^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652713967 5000000000 21853456471169 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119049901/625000000 : ℝ)^4373 ≤ (2294476187717/20000000000000 : ℝ)^3349 := by
    have hnat : (119049901 : ℕ)^4373*20000000000000^3349 ≤ 2294476187717^3349*625000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119049901 625000000 2294476187717 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408662759/10000000000 : ℝ)^4373 ≤ (44820706100721/100000000000000 : ℝ)^3349 := by
    have hnat : (5408662759 : ℕ)^4373*100000000000000^3349 ≤ 44820706100721^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408662759 10000000000 44820706100721 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652713967/5000000000 : ℝ), (-119049901/625000000 : ℝ), (5408662759/10000000000 : ℝ)] ![(21853456471169/50000000000000 : ℝ), (2294476187717/20000000000000 : ℝ), (44820706100721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652713967/5000000000 : ℝ)|^4373 ≤ (21853456471169/50000000000000 : ℝ)^3349
        have hw : |(2652713967/5000000000 : ℝ)|=(2652713967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119049901/625000000 : ℝ)|^4373 ≤ (2294476187717/20000000000000 : ℝ)^3349
        have hw : |(-119049901/625000000 : ℝ)|=(119049901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408662759/10000000000 : ℝ)|^4373 ≤ (44820706100721/100000000000000 : ℝ)^3349
        have hw : |(5408662759/10000000000 : ℝ)|=(5408662759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326356983/2500000000 : ℝ)*x 0 + (2704331381/5000000000 : ℝ)*x 1 + (-380959683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326356983/2500000000 : ℝ)^4373 ≤ (43706912920823/100000000000000 : ℝ)^3349 := by
    have hnat : (1326356983 : ℕ)^4373*100000000000000^3349 ≤ 43706912920823^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326356983 2500000000 43706912920823 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704331381/5000000000 : ℝ)^4373 ≤ (22410353066591/50000000000000 : ℝ)^3349 := by
    have hnat : (2704331381 : ℕ)^4373*50000000000000^3349 ≤ 22410353066591^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704331381 5000000000 22410353066591 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380959683/2000000000 : ℝ)^4373 ≤ (11472380930721/100000000000000 : ℝ)^3349 := by
    have hnat : (380959683 : ℕ)^4373*100000000000000^3349 ≤ 11472380930721^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380959683 2000000000 11472380930721 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326356983/2500000000 : ℝ), (2704331381/5000000000 : ℝ), (-380959683/2000000000 : ℝ)] ![(43706912920823/100000000000000 : ℝ), (22410353066591/50000000000000 : ℝ), (11472380930721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326356983/2500000000 : ℝ)|^4373 ≤ (43706912920823/100000000000000 : ℝ)^3349
        have hw : |(1326356983/2500000000 : ℝ)|=(1326356983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704331381/5000000000 : ℝ)|^4373 ≤ (22410353066591/50000000000000 : ℝ)^3349
        have hw : |(2704331381/5000000000 : ℝ)|=(2704331381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380959683/2000000000 : ℝ)|^4373 ≤ (11472380930721/100000000000000 : ℝ)^3349
        have hw : |(-380959683/2000000000 : ℝ)|=(380959683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s5_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308401049/10000000000 : ℝ)*x 0 + (4485519677/10000000000 : ℝ)*x 1 + (413769107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308401049/10000000000 : ℝ)^4373 ≤ (33304548850629/100000000000000 : ℝ)^3349 := by
    have hnat : (4308401049 : ℕ)^4373*100000000000000^3349 ≤ 33304548850629^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308401049 10000000000 33304548850629 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485519677/10000000000 : ℝ)^4373 ≤ (35103467895507/100000000000000 : ℝ)^3349 := by
    have hnat : (4485519677 : ℕ)^4373*100000000000000^3349 ≤ 35103467895507^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485519677 10000000000 35103467895507 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413769107/1000000000 : ℝ)^4373 ≤ (31591983233549/100000000000000 : ℝ)^3349 := by
    have hnat : (413769107 : ℕ)^4373*100000000000000^3349 ≤ 31591983233549^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413769107 1000000000 31591983233549 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308401049/10000000000 : ℝ), (4485519677/10000000000 : ℝ), (413769107/1000000000 : ℝ)] ![(33304548850629/100000000000000 : ℝ), (35103467895507/100000000000000 : ℝ), (31591983233549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308401049/10000000000 : ℝ)|^4373 ≤ (33304548850629/100000000000000 : ℝ)^3349
        have hw : |(4308401049/10000000000 : ℝ)|=(4308401049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485519677/10000000000 : ℝ)|^4373 ≤ (35103467895507/100000000000000 : ℝ)^3349
        have hw : |(4485519677/10000000000 : ℝ)|=(4485519677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413769107/1000000000 : ℝ)|^4373 ≤ (31591983233549/100000000000000 : ℝ)^3349
        have hw : |(413769107/1000000000 : ℝ)|=(413769107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/25000 : ℝ) ^ (1093/256 : ℝ) ≤ (8977314485016189/100000000000000000000 : ℝ) := by
    have hpowers : (2819/25000 : ℝ)^1093 ≤ (8977314485016189/100000000000000000000 : ℝ)^256 := by
      have hnat : (2819 : ℕ)^1093*100000000000000000000^256 ≤ 8977314485016189^256*25000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 25000 8977314485016189 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/25000 : ℝ)) (X := (8977314485016189/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14781/100000 : ℝ) ^ (1093/256 : ℝ) ≤ (14255895534245999/50000000000000000000 : ℝ) := by
    have hpowers : (14781/100000 : ℝ)^1093 ≤ (14255895534245999/50000000000000000000 : ℝ)^256 := by
      have hnat : (14781 : ℕ)^1093*50000000000000000000^256 ≤ 14255895534245999^256*100000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14781 100000 14255895534245999 50000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14781/100000 : ℝ)) (X := (14255895534245999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008977314485016189/50000000000000000000 : ℝ) ≤ (156256570318309/156250000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50008977314485016189/50000000000000000000 : ℝ)^256 ≤ (156256570318309/156250000000000 : ℝ)^1093 := by
      have hnat : (50008977314485016189 : ℕ)^256*156250000000000^1093 ≤ 156256570318309^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008977314485016189 50000000000000000000 156256570318309 156250000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156256570318309/156250000000000 : ℝ)) (X := (50008977314485016189/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037489105553508187/100000000000000000000 : ℝ) ≤ (10000877935381367/10000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (100037489105553508187/100000000000000000000 : ℝ)^256 ≤ (10000877935381367/10000000000000000 : ℝ)^1093 := by
      have hnat : (100037489105553508187 : ℕ)^256*10000000000000000^1093 ≤ 10000877935381367^1093*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037489105553508187 100000000000000000000 10000877935381367 10000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000877935381367/10000000000000000 : ℝ)) (X := (100037489105553508187/100000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014255895534245999/25000000000000000000 : ℝ) ≤ (5000667685195479/5000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (25014255895534245999/25000000000000000000 : ℝ)^256 ≤ (5000667685195479/5000000000000000 : ℝ)^1093 := by
      have hnat : (25014255895534245999 : ℕ)^256*5000000000000000^1093 ≤ 5000667685195479^1093*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014255895534245999 25000000000000000000 5000667685195479 5000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000667685195479/5000000000000000 : ℝ)) (X := (25014255895534245999/25000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8977314485016189/100000000000000000000 : ℝ) ≤ ((4380144722433347331/4381250000000000000 : ℝ)+2*(457435009591/350500000000000 : ℝ)*(2819/25000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (4380144722433347331/4381250000000000000 : ℝ)+2*(457435009591/350500000000000 : ℝ)*(2819/25000 : ℝ)=(156256570318309/156250000000000 : ℝ) by norm_num, show 1+2*(8977314485016189/100000000000000000000 : ℝ)=(50008977314485016189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14255895534245999/50000000000000000000 : ℝ)+(8977314485016189/100000000000000000000 : ℝ) ≤ ((4380144722433347331/4381250000000000000 : ℝ)+(457435009591/350500000000000 : ℝ)*((14781/100000 : ℝ)+(2819/25000 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (4380144722433347331/4381250000000000000 : ℝ)+(457435009591/350500000000000 : ℝ)*((14781/100000 : ℝ)+(2819/25000 : ℝ))=(10000877935381367/10000000000000000 : ℝ) by norm_num, show 1+(14255895534245999/50000000000000000000 : ℝ)+(8977314485016189/100000000000000000000 : ℝ)=(100037489105553508187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14255895534245999/50000000000000000000 : ℝ) ≤ ((4380144722433347331/4381250000000000000 : ℝ)+2*(457435009591/350500000000000 : ℝ)*(14781/100000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (4380144722433347331/4381250000000000000 : ℝ)+2*(457435009591/350500000000000 : ℝ)*(14781/100000 : ℝ)=(5000667685195479/5000000000000000 : ℝ) by norm_num, show 1+2*(14255895534245999/50000000000000000000 : ℝ)=(25014255895534245999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4380144722433347331/4381250000000000000 : ℝ)*(X 1 0+X 2 0)+(457435009591/350500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (4380144722433347331/4381250000000000000 : ℝ)) (alpha := (457435009591/350500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4380144722433347331/4381250000000000000 : ℝ)*(X 0 1+X 2 1)+(457435009591/350500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (4380144722433347331/4381250000000000000 : ℝ)) (alpha := (457435009591/350500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4380144722433347331/4381250000000000000 : ℝ)*(X 0 2+X 1 2)+(457435009591/350500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14781/100000 : ℝ)) (c := (4380144722433347331/4381250000000000000 : ℝ)) (alpha := (457435009591/350500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-992081279/5000000000 : ℝ)*X 0 0+(84519589/156250000 : ℝ)*X 0 1+(5246343681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673856537/5000000000 : ℝ)*X 1 0+(-516779489/2500000000 : ℝ)*X 1 1+(655792897/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336928223/2500000000 : ℝ)*X 2 0+(5246343529/10000000000 : ℝ)*X 2 1+(-206711773/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308375969/10000000000 : ℝ)*X 0 0+(33091357/80000000 : ℝ)*X 0 1+(4486784787/10000000000 : ℝ)*X 0 2+(4308375969/10000000000 : ℝ)*X 1 0+(33091357/80000000 : ℝ)*X 1 1+(4486784787/10000000000 : ℝ)*X 1 2+(4308375969/10000000000 : ℝ)*X 2 0+(33091357/80000000 : ℝ)*X 2 1+(4486784787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-79366963/400000000 : ℝ)*X 0 0+(1049386319/2000000000 : ℝ)*X 0 1+(5408662759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652713967/5000000000 : ℝ)*X 1 0+(-119049901/625000000 : ℝ)*X 1 1+(5408662759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326356983/2500000000 : ℝ)*X 2 0+(2704331381/5000000000 : ℝ)*X 2 1+(-380959683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308401049/10000000000 : ℝ)*X 0 0+(4485519677/10000000000 : ℝ)*X 0 1+(413769107/1000000000 : ℝ)*X 0 2+(4308401049/10000000000 : ℝ)*X 1 0+(4485519677/10000000000 : ℝ)*X 1 1+(413769107/1000000000 : ℝ)*X 1 2+(4308401049/10000000000 : ℝ)*X 2 0+(4485519677/10000000000 : ℝ)*X 2 1+(413769107/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (764332245006616152293364699/219062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (673220801/100000000000000 : ℝ)*(base19) + (176730857/50000000000000 : ℝ)*(base23) + (67049301/100000000000000 : ℝ)*(upper4) + (102761239/100000000000000 : ℝ)*(upper5) + (4496267275381521/100000000000000 : ℝ)*(major0) + (4496267275381521/100000000000000 : ℝ)*(major1) + (2248133637690761/50000000000000 : ℝ)*(major2) + (191823634612951/3125000000000 : ℝ)*(sp0) + (191823632902163/3125000000000 : ℝ)*(sp1) + (6138358410020557/100000000000000 : ℝ)*(sp2) + (1427085599883883/50000000000000 : ℝ)*(sp3) + (2455867839/100000000000000 : ℝ)*(sp4) + (918696127/50000000000000 : ℝ)*(sp5) + (4471209473/100000000000000 : ℝ)*(sp7) + (2854175670977239/100000000000000 : ℝ)*(f.failure) + (6138358763482271/100000000000000 : ℝ)*(f.sum) + (53915510522913/35050000000000000000000000000 : ℝ)*base65 + (1109060946304154549/438125000000000000000000000000000 : ℝ)*base68 + (212802999494409859/219062500000000000000000000000000 : ℝ)*base70 + (1547967474993529549/438125000000000000000000000000000 : ℝ)*base72 + (114666379830137/35050000000000000000000000000 : ℝ)*base74 + (4667269559840972359/219062500000000000000000000000000 : ℝ)*base76 + (743928602878417049/438125000000000000000000000000000 : ℝ)*base78 + (2766346269215957951/438125000000000000000000000000000 : ℝ)*base79 + (56897894475639/17525000000000000000000000000 : ℝ)*base82 + (19482249/2000000000000000000000 : ℝ)*base89 + (19482249/2000000000000000000000 : ℝ)*base91 + (517751/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (700843300792982834323494147/109531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1092394441/100000000000000 : ℝ)*(base19) + (1180922889/100000000000000 : ℝ)*(base23) + (65895217/50000000000000 : ℝ)*(upper3) + (40899777/100000000000000 : ℝ)*(lower4) + (16369019/12500000000000 : ℝ)*(upper5) + (2264519601212257/50000000000000 : ℝ)*(major0) + (2264519601212257/50000000000000 : ℝ)*(major1) + (2264519601212257/50000000000000 : ℝ)*(major2) + (22780042317/100000000000000 : ℝ)*(sp1) + (6126924349/25000000000000 : ℝ)*(sp2) + (3091549650343263/50000000000000 : ℝ)*(sp4) + (772884428531221/12500000000000 : ℝ)*(sp5) + (6183073612066241/100000000000000 : ℝ)*(sp6) + (2874978890876841/100000000000000 : ℝ)*(sp7) + (2874978890876841/100000000000000 : ℝ)*(f.failure) + (3091549650343263/50000000000000 : ℝ)*(f.sum) + (81903590412299/17525000000000000000000000000 : ℝ)*base65 + (1540835211200586067/219062500000000000000000000000000 : ℝ)*base67 + (2766510539426523567/219062500000000000000000000000000 : ℝ)*base69 + (1319431228371836067/219062500000000000000000000000000 : ℝ)*base71 + (68994744495849/17525000000000000000000000000 : ℝ)*base73 + (9512127629279648567/219062500000000000000000000000000 : ℝ)*base75 + (1694181211848711067/219062500000000000000000000000000 : ℝ)*base77 + (4321049589839336067/219062500000000000000000000000000 : ℝ)*base79 + (28400126818101/17525000000000000000000000000 : ℝ)*base82 + (19240969/2000000000000000000000 : ℝ)*base90 + (19240969/2000000000000000000000 : ℝ)*base92 + (19240969/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1413_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1413_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1413_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1413_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1413_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (317/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1413_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

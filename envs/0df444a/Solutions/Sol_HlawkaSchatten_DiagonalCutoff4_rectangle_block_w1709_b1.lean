-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1709_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:06.733935+00:00
-- url     : https://prove2.me/submissions/1ec9ae40-c097-423b-8250-bfd7edfa0562

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
theorem support_rectangle_w1709_s3_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283139219/2000000000 : ℝ)*x 0 + (5470666989/10000000000 : ℝ)*x 1 + (2569085711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283139219/2000000000 : ℝ)^5295 ≤ (8859507566649/100000000000000 : ℝ)^4271 := by
    have hnat : (283139219 : ℕ)^5295*100000000000000^4271 ≤ 8859507566649^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283139219 2000000000 8859507566649 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470666989/10000000000 : ℝ)^5295 ≤ (47340597398737/100000000000000 : ℝ)^4271 := by
    have hnat : (5470666989 : ℕ)^5295*100000000000000^4271 ≤ 47340597398737^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470666989 10000000000 47340597398737 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569085711/5000000000 : ℝ)^5295 ≤ (21899947511827/50000000000000 : ℝ)^4271 := by
    have hnat : (2569085711 : ℕ)^5295*50000000000000^4271 ≤ 21899947511827^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569085711 5000000000 21899947511827 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283139219/2000000000 : ℝ), (5470666989/10000000000 : ℝ), (2569085711/5000000000 : ℝ)] ![(8859507566649/100000000000000 : ℝ), (47340597398737/100000000000000 : ℝ), (21899947511827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283139219/2000000000 : ℝ)|^5295 ≤ (8859507566649/100000000000000 : ℝ)^4271
        have hw : |(-283139219/2000000000 : ℝ)|=(283139219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470666989/10000000000 : ℝ)|^5295 ≤ (47340597398737/100000000000000 : ℝ)^4271
        have hw : |(5470666989/10000000000 : ℝ)|=(5470666989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569085711/5000000000 : ℝ)|^5295 ≤ (21899947511827/50000000000000 : ℝ)^4271
        have hw : |(2569085711/5000000000 : ℝ)|=(2569085711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333990819/625000000 : ℝ)*x 0 + (-317623573/2000000000 : ℝ)*x 1 + (64227147/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333990819/625000000 : ℝ)^5295 ≤ (22991953192173/50000000000000 : ℝ)^4271 := by
    have hnat : (333990819 : ℕ)^5295*50000000000000^4271 ≤ 22991953192173^4271*625000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333990819 625000000 22991953192173 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317623573/2000000000 : ℝ)^5295 ≤ (10216195001563/100000000000000 : ℝ)^4271 := by
    have hnat : (317623573 : ℕ)^5295*100000000000000^4271 ≤ 10216195001563^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317623573 2000000000 10216195001563 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64227147/125000000 : ℝ)^5295 ≤ (8759979719141/20000000000000 : ℝ)^4271 := by
    have hnat : (64227147 : ℕ)^5295*20000000000000^4271 ≤ 8759979719141^4271*125000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64227147 125000000 8759979719141 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333990819/625000000 : ℝ), (-317623573/2000000000 : ℝ), (64227147/125000000 : ℝ)] ![(22991953192173/50000000000000 : ℝ), (10216195001563/100000000000000 : ℝ), (8759979719141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333990819/625000000 : ℝ)|^5295 ≤ (22991953192173/50000000000000 : ℝ)^4271
        have hw : |(333990819/625000000 : ℝ)|=(333990819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317623573/2000000000 : ℝ)|^5295 ≤ (10216195001563/100000000000000 : ℝ)^4271
        have hw : |(-317623573/2000000000 : ℝ)|=(317623573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64227147/125000000 : ℝ)|^5295 ≤ (8759979719141/20000000000000 : ℝ)^4271
        have hw : |(64227147/125000000 : ℝ)|=(64227147/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667981687/1250000000 : ℝ)*x 0 + (513817169/1000000000 : ℝ)*x 1 + (-794058717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667981687/1250000000 : ℝ)^5295 ≤ (5747988820781/12500000000000 : ℝ)^4271 := by
    have hnat : (667981687 : ℕ)^5295*12500000000000^4271 ≤ 5747988820781^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667981687 1250000000 5747988820781 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513817169/1000000000 : ℝ)^5295 ≤ (43799897855931/100000000000000 : ℝ)^4271 := by
    have hnat : (513817169 : ℕ)^5295*100000000000000^4271 ≤ 43799897855931^4271*1000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513817169 1000000000 43799897855931 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794058717/5000000000 : ℝ)^5295 ≤ (5108095782121/50000000000000 : ℝ)^4271 := by
    have hnat : (794058717 : ℕ)^5295*50000000000000^4271 ≤ 5108095782121^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794058717 5000000000 5108095782121 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667981687/1250000000 : ℝ), (513817169/1000000000 : ℝ), (-794058717/5000000000 : ℝ)] ![(5747988820781/12500000000000 : ℝ), (43799897855931/100000000000000 : ℝ), (5108095782121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667981687/1250000000 : ℝ)|^5295 ≤ (5747988820781/12500000000000 : ℝ)^4271
        have hw : |(667981687/1250000000 : ℝ)|=(667981687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513817169/1000000000 : ℝ)|^5295 ≤ (43799897855931/100000000000000 : ℝ)^4271
        have hw : |(513817169/1000000000 : ℝ)|=(513817169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-794058717/5000000000 : ℝ)|^5295 ≤ (5108095782121/50000000000000 : ℝ)^4271
        have hw : |(-794058717/5000000000 : ℝ)|=(794058717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026498367/2500000000 : ℝ)*x 0 + (728592493/2000000000 : ℝ)*x 1 + (36837949/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026498367/2500000000 : ℝ)^5295 ≤ (8292257456009/25000000000000 : ℝ)^4271 := by
    have hnat : (1026498367 : ℕ)^5295*25000000000000^4271 ≤ 8292257456009^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026498367 2500000000 8292257456009 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728592493/2000000000 : ℝ)^5295 ≤ (5719270089263/20000000000000 : ℝ)^4271 := by
    have hnat : (728592493 : ℕ)^5295*20000000000000^4271 ≤ 5719270089263^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728592493 2000000000 5719270089263 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36837949/80000000 : ℝ)^5295 ≤ (38234619709877/100000000000000 : ℝ)^4271 := by
    have hnat : (36837949 : ℕ)^5295*100000000000000^4271 ≤ 38234619709877^4271*80000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36837949 80000000 38234619709877 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026498367/2500000000 : ℝ), (728592493/2000000000 : ℝ), (36837949/80000000 : ℝ)] ![(8292257456009/25000000000000 : ℝ), (5719270089263/20000000000000 : ℝ), (38234619709877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026498367/2500000000 : ℝ)|^5295 ≤ (8292257456009/25000000000000 : ℝ)^4271
        have hw : |(1026498367/2500000000 : ℝ)|=(1026498367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(728592493/2000000000 : ℝ)|^5295 ≤ (5719270089263/20000000000000 : ℝ)^4271
        have hw : |(728592493/2000000000 : ℝ)|=(728592493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36837949/80000000 : ℝ)|^5295 ≤ (38234619709877/100000000000000 : ℝ)^4271
        have hw : |(36837949/80000000 : ℝ)|=(36837949/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283169323/2000000000 : ℝ)*x 0 + (1028370163/2000000000 : ℝ)*x 1 + (218677321/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283169323/2000000000 : ℝ)^5295 ≤ (8860675386053/100000000000000 : ℝ)^4271 := by
    have hnat : (283169323 : ℕ)^5295*100000000000000^4271 ≤ 8860675386053^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283169323 2000000000 8860675386053 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028370163/2000000000 : ℝ)^5295 ≤ (4383878290869/10000000000000 : ℝ)^4271 := by
    have hnat : (1028370163 : ℕ)^5295*10000000000000^4271 ≤ 4383878290869^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028370163 2000000000 4383878290869 10000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218677321/400000000 : ℝ)^5295 ≤ (47300541688939/100000000000000 : ℝ)^4271 := by
    have hnat : (218677321 : ℕ)^5295*100000000000000^4271 ≤ 47300541688939^4271*400000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218677321 400000000 47300541688939 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283169323/2000000000 : ℝ), (1028370163/2000000000 : ℝ), (218677321/400000000 : ℝ)] ![(8860675386053/100000000000000 : ℝ), (4383878290869/10000000000000 : ℝ), (47300541688939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283169323/2000000000 : ℝ)|^5295 ≤ (8860675386053/100000000000000 : ℝ)^4271
        have hw : |(-283169323/2000000000 : ℝ)|=(283169323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028370163/2000000000 : ℝ)|^5295 ≤ (4383878290869/10000000000000 : ℝ)^4271
        have hw : |(1028370163/2000000000 : ℝ)|=(1028370163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218677321/400000000 : ℝ)|^5295 ≤ (47300541688939/100000000000000 : ℝ)^4271
        have hw : |(218677321/400000000 : ℝ)|=(218677321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313713929/2500000000 : ℝ)*x 0 + (-157419553/1250000000 : ℝ)*x 1 + (683366641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313713929/2500000000 : ℝ)^5295 ≤ (11259093867919/25000000000000 : ℝ)^4271 := by
    have hnat : (1313713929 : ℕ)^5295*25000000000000^4271 ≤ 11259093867919^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313713929 2500000000 11259093867919 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157419553/1250000000 : ℝ)^5295 ≤ (1532616343913/20000000000000 : ℝ)^4271 := by
    have hnat : (157419553 : ℕ)^5295*20000000000000^4271 ≤ 1532616343913^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157419553 1250000000 1532616343913 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683366641/1250000000 : ℝ)^5295 ≤ (4730054279377/10000000000000 : ℝ)^4271 := by
    have hnat : (683366641 : ℕ)^5295*10000000000000^4271 ≤ 4730054279377^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683366641 1250000000 4730054279377 10000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313713929/2500000000 : ℝ), (-157419553/1250000000 : ℝ), (683366641/1250000000 : ℝ)] ![(11259093867919/25000000000000 : ℝ), (1532616343913/20000000000000 : ℝ), (4730054279377/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313713929/2500000000 : ℝ)|^5295 ≤ (11259093867919/25000000000000 : ℝ)^4271
        have hw : |(1313713929/2500000000 : ℝ)|=(1313713929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157419553/1250000000 : ℝ)|^5295 ≤ (1532616343913/20000000000000 : ℝ)^4271
        have hw : |(-157419553/1250000000 : ℝ)|=(157419553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683366641/1250000000 : ℝ)|^5295 ≤ (4730054279377/10000000000000 : ℝ)^4271
        have hw : |(683366641/1250000000 : ℝ)|=(683366641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41053561/78125000 : ℝ)*x 0 + (5466933067/10000000000 : ℝ)*x 1 + (-629678191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41053561/78125000 : ℝ)^5295 ≤ (45036376449199/100000000000000 : ℝ)^4271 := by
    have hnat : (41053561 : ℕ)^5295*100000000000000^4271 ≤ 45036376449199^4271*78125000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41053561 78125000 45036376449199 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466933067/10000000000 : ℝ)^5295 ≤ (47300542139453/100000000000000 : ℝ)^4271 := by
    have hnat : (5466933067 : ℕ)^5295*100000000000000^4271 ≤ 47300542139453^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466933067 10000000000 47300542139453 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629678191/5000000000 : ℝ)^5295 ≤ (1915770350681/25000000000000 : ℝ)^4271 := by
    have hnat : (629678191 : ℕ)^5295*25000000000000^4271 ≤ 1915770350681^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629678191 5000000000 1915770350681 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41053561/78125000 : ℝ), (5466933067/10000000000 : ℝ), (-629678191/5000000000 : ℝ)] ![(45036376449199/100000000000000 : ℝ), (47300542139453/100000000000000 : ℝ), (1915770350681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41053561/78125000 : ℝ)|^5295 ≤ (45036376449199/100000000000000 : ℝ)^4271
        have hw : |(41053561/78125000 : ℝ)|=(41053561/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466933067/10000000000 : ℝ)|^5295 ≤ (47300542139453/100000000000000 : ℝ)^4271
        have hw : |(5466933067/10000000000 : ℝ)|=(5466933067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629678191/5000000000 : ℝ)|^5295 ≤ (1915770350681/25000000000000 : ℝ)^4271
        have hw : |(-629678191/5000000000 : ℝ)|=(629678191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s3_7 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4106429597/10000000000 : ℝ)*x 0 + (2297051101/5000000000 : ℝ)*x 1 + (456720371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4106429597/10000000000 : ℝ)^5295 ≤ (8293349427781/25000000000000 : ℝ)^4271 := by
    have hnat : (4106429597 : ℕ)^5295*25000000000000^4271 ≤ 8293349427781^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106429597 10000000000 8293349427781 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297051101/5000000000 : ℝ)^5295 ≤ (19062553185817/50000000000000 : ℝ)^4271 := by
    have hnat : (2297051101 : ℕ)^5295*50000000000000^4271 ≤ 19062553185817^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297051101 5000000000 19062553185817 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456720371/1250000000 : ℝ)^5295 ≤ (7175373974951/25000000000000 : ℝ)^4271 := by
    have hnat : (456720371 : ℕ)^5295*25000000000000^4271 ≤ 7175373974951^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456720371 1250000000 7175373974951 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4106429597/10000000000 : ℝ), (2297051101/5000000000 : ℝ), (456720371/1250000000 : ℝ)] ![(8293349427781/25000000000000 : ℝ), (19062553185817/50000000000000 : ℝ), (7175373974951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4106429597/10000000000 : ℝ)|^5295 ≤ (8293349427781/25000000000000 : ℝ)^4271
        have hw : |(4106429597/10000000000 : ℝ)|=(4106429597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297051101/5000000000 : ℝ)|^5295 ≤ (19062553185817/50000000000000 : ℝ)^4271
        have hw : |(2297051101/5000000000 : ℝ)|=(2297051101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456720371/1250000000 : ℝ)|^5295 ≤ (7175373974951/25000000000000 : ℝ)^4271
        have hw : |(456720371/1250000000 : ℝ)|=(456720371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5001/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (171/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2139/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1249/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2139/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1249/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2139/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1249/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2139/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1249/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2139/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1249/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2139/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1249/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1249/12500 : ℝ) ^ (5287/1024 : ℝ) ≤ (85512483139633/12500000000000000000 : ℝ) := by
    have hpowers : (1249/12500 : ℝ)^5287 ≤ (85512483139633/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1249 : ℕ)^5287*12500000000000000000^1024 ≤ 85512483139633^1024*12500^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1249 12500 85512483139633 12500000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1249/12500 : ℝ)) (X := (85512483139633/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2139/12500 : ℝ) ^ (5287/1024 : ℝ) ≤ (1100185698966767/10000000000000000000 : ℝ) := by
    have hpowers : (2139/12500 : ℝ)^5287 ≤ (1100185698966767/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2139 : ℕ)^5287*10000000000000000000^1024 ≤ 1100185698966767^1024*12500^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2139 12500 1100185698966767 10000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2139/12500 : ℝ)) (X := (1100185698966767/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250085512483139633/6250000000000000000 : ℝ) ≤ (2500006624876091/2500000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (6250085512483139633/6250000000000000000 : ℝ)^1024 ≤ (2500006624876091/2500000000000000 : ℝ)^5287 := by
      have hnat : (6250085512483139633 : ℕ)^1024*2500000000000000^5287 ≤ 2500006624876091^5287*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250085512483139633 6250000000000000000 2500006624876091 2500000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500006624876091/2500000000000000 : ℝ)) (X := (6250085512483139633/6250000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005842978427392367/50000000000000000000 : ℝ) ≤ (10000226326008807/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50005842978427392367/50000000000000000000 : ℝ)^1024 ≤ (10000226326008807/10000000000000000 : ℝ)^5287 := by
      have hnat : (50005842978427392367 : ℕ)^1024*10000000000000000^5287 ≤ 10000226326008807^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005842978427392367 50000000000000000000 10000226326008807 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000226326008807/10000000000000000 : ℝ)) (X := (50005842978427392367/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001100185698966767/5000000000000000000 : ℝ) ≤ (40001704610053/40000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (5001100185698966767/5000000000000000000 : ℝ)^1024 ≤ (40001704610053/40000000000000 : ℝ)^5287 := by
      have hnat : (5001100185698966767 : ℕ)^1024*40000000000000^5287 ≤ 40001704610053^5287*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001100185698966767 5000000000000000000 40001704610053 40000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40001704610053/40000000000000 : ℝ)) (X := (5001100185698966767/5000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(85512483139633/12500000000000000000 : ℝ) ≤ ((4449762208975392673/4450000000000000000 : ℝ)+2*(199826504443/712000000000000 : ℝ)*(1249/12500 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (4449762208975392673/4450000000000000000 : ℝ)+2*(199826504443/712000000000000 : ℝ)*(1249/12500 : ℝ)=(2500006624876091/2500000000000000 : ℝ) by norm_num, show 1+2*(85512483139633/12500000000000000000 : ℝ)=(6250085512483139633/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1100185698966767/10000000000000000000 : ℝ)+(85512483139633/12500000000000000000 : ℝ) ≤ ((4449762208975392673/4450000000000000000 : ℝ)+(199826504443/712000000000000 : ℝ)*((2139/12500 : ℝ)+(1249/12500 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (4449762208975392673/4450000000000000000 : ℝ)+(199826504443/712000000000000 : ℝ)*((2139/12500 : ℝ)+(1249/12500 : ℝ))=(10000226326008807/10000000000000000 : ℝ) by norm_num, show 1+(1100185698966767/10000000000000000000 : ℝ)+(85512483139633/12500000000000000000 : ℝ)=(50005842978427392367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1100185698966767/10000000000000000000 : ℝ) ≤ ((4449762208975392673/4450000000000000000 : ℝ)+2*(199826504443/712000000000000 : ℝ)*(2139/12500 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (4449762208975392673/4450000000000000000 : ℝ)+2*(199826504443/712000000000000 : ℝ)*(2139/12500 : ℝ)=(40001704610053/40000000000000 : ℝ) by norm_num, show 1+2*(1100185698966767/10000000000000000000 : ℝ)=(5001100185698966767/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4449762208975392673/4450000000000000000 : ℝ)*(X 1 0+X 2 0)+(199826504443/712000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (2139/12500 : ℝ)) (c := (4449762208975392673/4450000000000000000 : ℝ)) (alpha := (199826504443/712000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4449762208975392673/4450000000000000000 : ℝ)*(X 0 1+X 2 1)+(199826504443/712000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (2139/12500 : ℝ)) (c := (4449762208975392673/4450000000000000000 : ℝ)) (alpha := (199826504443/712000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4449762208975392673/4450000000000000000 : ℝ)*(X 0 2+X 1 2)+(199826504443/712000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (2139/12500 : ℝ)) (c := (4449762208975392673/4450000000000000000 : ℝ)) (alpha := (199826504443/712000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-283139219/2000000000 : ℝ)*X 0 0+(5470666989/10000000000 : ℝ)*X 0 1+(2569085711/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((333990819/625000000 : ℝ)*X 1 0+(-317623573/2000000000 : ℝ)*X 1 1+(64227147/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667981687/1250000000 : ℝ)*X 2 0+(513817169/1000000000 : ℝ)*X 2 1+(-794058717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026498367/2500000000 : ℝ)*X 0 0+(728592493/2000000000 : ℝ)*X 0 1+(36837949/80000000 : ℝ)*X 0 2+(1026498367/2500000000 : ℝ)*X 1 0+(728592493/2000000000 : ℝ)*X 1 1+(36837949/80000000 : ℝ)*X 1 2+(1026498367/2500000000 : ℝ)*X 2 0+(728592493/2000000000 : ℝ)*X 2 1+(36837949/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-283169323/2000000000 : ℝ)*X 0 0+(1028370163/2000000000 : ℝ)*X 0 1+(218677321/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313713929/2500000000 : ℝ)*X 1 0+(-157419553/1250000000 : ℝ)*X 1 1+(683366641/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41053561/78125000 : ℝ)*X 2 0+(5466933067/10000000000 : ℝ)*X 2 1+(-629678191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4106429597/10000000000 : ℝ)*X 0 0+(2297051101/5000000000 : ℝ)*X 0 1+(456720371/1250000000 : ℝ)*X 0 2+(4106429597/10000000000 : ℝ)*X 1 0+(2297051101/5000000000 : ℝ)*X 1 1+(456720371/1250000000 : ℝ)*X 1 2+(4106429597/10000000000 : ℝ)*X 2 0+(2297051101/5000000000 : ℝ)*X 2 1+(456720371/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74254672989252858639072351/6953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1808000717/100000000000000 : ℝ)*(base19) + (995311297/50000000000000 : ℝ)*(base23) + (20611479/12500000000000 : ℝ)*(upper3) + (20307459/100000000000000 : ℝ)*(upper4) + (442181049/100000000000000 : ℝ)*(upper5) + (7904985432569/390625000000 : ℝ)*(major0) + (7904985432569/390625000000 : ℝ)*(major1) + (7904985432569/390625000000 : ℝ)*(major2) + (3007576852873169/100000000000000 : ℝ)*(sp0) + (751899964679769/25000000000000 : ℝ)*(sp1) + (7518999190243/250000000000 : ℝ)*(sp2) + (519872295993719/50000000000000 : ℝ)*(sp3) + (775432707/3125000000000 : ℝ)*(sp4) + (5926790631/100000000000000 : ℝ)*(sp7) + (103975051877807/10000000000000 : ℝ)*(f.failure) + (3007601666719793/100000000000000 : ℝ)*(f.sum) + (749464735243/556250000000000000000000000 : ℝ)*base65 + (8309056725110377/6953125000000000000000000000000 : ℝ)*base68 + (1078759133871219/869140625000000000000000000000 : ℝ)*base70 + (2639977570266627/6953125000000000000000000000000 : ℝ)*base72 + (309729569867/139062500000000000000000000 : ℝ)*base73 + (14806892138811999/3476562500000000000000000000000 : ℝ)*base75 + (31211753925266627/6953125000000000000000000000000 : ℝ)*base78 + (10057488200121219/869140625000000000000000000000 : ℝ)*base80 + (5809263014261/1112500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6407711/500000000000000000000 : ℝ)*base89 + (6407711/500000000000000000000 : ℝ)*base91 + (6407711/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26724930627297730599290637/3476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (964828807/100000000000000 : ℝ)*(base19) + (563100767/50000000000000 : ℝ)*(base23) + (148203621/50000000000000 : ℝ)*(lower1) + (172640293/100000000000000 : ℝ)*(upper3) + (41927059/100000000000000 : ℝ)*(lower4) + (17928133/12500000000000 : ℝ)*(upper5) + (258723632464917/12500000000000 : ℝ)*(major0) + (258723632464917/12500000000000 : ℝ)*(major1) + (258723632464917/12500000000000 : ℝ)*(major2) + (818647611/50000000000000 : ℝ)*(sp2) + (1538067460205603/50000000000000 : ℝ)*(sp4) + (1922583722239/62500000000 : ℝ)*(sp5) + (61522643138289/2000000000000 : ℝ)*(sp6) + (531721471394209/50000000000000 : ℝ)*(sp7) + (531721471394209/50000000000000 : ℝ)*(f.failure) + (1538067460205603/50000000000000 : ℝ)*(f.sum) + (860204767031/4450000000000000000000000000 : ℝ)*base65 + (695373594498453109/55625000000000000000000000000000 : ℝ)*base68 + (103893692543453109/55625000000000000000000000000000 : ℝ)*base70 + (1077009856485953109/55625000000000000000000000000000 : ℝ)*base72 + (9352055306031/4450000000000000000000000000 : ℝ)*base73 + (3131688658449703109/55625000000000000000000000000000 : ℝ)*base76 + (312801528215953109/55625000000000000000000000000000 : ℝ)*base78 + (553877662276546891/55625000000000000000000000000000 : ℝ)*base79 + (11102483346969/4450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (18295857/2500000000000000000000 : ℝ)*base89 + (18295857/2500000000000000000000 : ℝ)*base91 + (18295857/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1709_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5001/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (171/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1709_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1709_s4_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283140249/2000000000 : ℝ)*x 0 + (1367661701/2500000000 : ℝ)*x 1 + (1284547033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283140249/2000000000 : ℝ)^5295 ≤ (4429773761387/50000000000000 : ℝ)^4271 := by
    have hnat : (283140249 : ℕ)^5295*50000000000000^4271 ≤ 4429773761387^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283140249 2000000000 4429773761387 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367661701/2500000000 : ℝ)^5295 ≤ (47340380848627/100000000000000 : ℝ)^4271 := by
    have hnat : (1367661701 : ℕ)^5295*100000000000000^4271 ≤ 47340380848627^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367661701 2500000000 47340380848627 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284547033/2500000000 : ℝ)^5295 ≤ (10950017904571/25000000000000 : ℝ)^4271 := by
    have hnat : (1284547033 : ℕ)^5295*25000000000000^4271 ≤ 10950017904571^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284547033 2500000000 10950017904571 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283140249/2000000000 : ℝ), (1367661701/2500000000 : ℝ), (1284547033/2500000000 : ℝ)] ![(4429773761387/50000000000000 : ℝ), (47340380848627/100000000000000 : ℝ), (10950017904571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283140249/2000000000 : ℝ)|^5295 ≤ (4429773761387/50000000000000 : ℝ)^4271
        have hw : |(-283140249/2000000000 : ℝ)|=(283140249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367661701/2500000000 : ℝ)|^5295 ≤ (47340380848627/100000000000000 : ℝ)^4271
        have hw : |(1367661701/2500000000 : ℝ)|=(1367661701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284547033/2500000000 : ℝ)|^5295 ≤ (10950017904571/25000000000000 : ℝ)^4271
        have hw : |(1284547033/2500000000 : ℝ)|=(1284547033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671923571/5000000000 : ℝ)*x 0 + (-397025559/2500000000 : ℝ)*x 1 + (5138189573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671923571/5000000000 : ℝ)^5295 ≤ (9196768556209/20000000000000 : ℝ)^4271 := by
    have hnat : (2671923571 : ℕ)^5295*20000000000000^4271 ≤ 9196768556209^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671923571 5000000000 9196768556209 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397025559/2500000000 : ℝ)^5295 ≤ (204321407139/2000000000000 : ℝ)^4271 := by
    have hnat : (397025559 : ℕ)^5295*2000000000000^4271 ≤ 204321407139^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397025559 2500000000 204321407139 2000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138189573/10000000000 : ℝ)^5295 ≤ (43800086847067/100000000000000 : ℝ)^4271 := by
    have hnat : (5138189573 : ℕ)^5295*100000000000000^4271 ≤ 43800086847067^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138189573 10000000000 43800086847067 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671923571/5000000000 : ℝ), (-397025559/2500000000 : ℝ), (5138189573/10000000000 : ℝ)] ![(9196768556209/20000000000000 : ℝ), (204321407139/2000000000000 : ℝ), (43800086847067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671923571/5000000000 : ℝ)|^5295 ≤ (9196768556209/20000000000000 : ℝ)^4271
        have hw : |(2671923571/5000000000 : ℝ)|=(2671923571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397025559/2500000000 : ℝ)|^5295 ≤ (204321407139/2000000000000 : ℝ)^4271
        have hw : |(-397025559/2500000000 : ℝ)|=(397025559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138189573/10000000000 : ℝ)|^5295 ≤ (43800086847067/100000000000000 : ℝ)^4271
        have hw : |(5138189573/10000000000 : ℝ)|=(5138189573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671923923/5000000000 : ℝ)*x 0 + (1284547091/2500000000 : ℝ)*x 1 + (-99256431/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671923923/5000000000 : ℝ)^5295 ≤ (45983850291397/100000000000000 : ℝ)^4271 := by
    have hnat : (2671923923 : ℕ)^5295*100000000000000^4271 ≤ 45983850291397^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671923923 5000000000 45983850291397 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284547091/2500000000 : ℝ)^5295 ≤ (10950018517527/25000000000000 : ℝ)^4271 := by
    have hnat : (1284547091 : ℕ)^5295*25000000000000^4271 ≤ 10950018517527^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284547091 2500000000 10950018517527 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99256431/625000000 : ℝ)^5295 ≤ (2043215124117/20000000000000 : ℝ)^4271 := by
    have hnat : (99256431 : ℕ)^5295*20000000000000^4271 ≤ 2043215124117^4271*625000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99256431 625000000 2043215124117 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671923923/5000000000 : ℝ), (1284547091/2500000000 : ℝ), (-99256431/625000000 : ℝ)] ![(45983850291397/100000000000000 : ℝ), (10950018517527/25000000000000 : ℝ), (2043215124117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671923923/5000000000 : ℝ)|^5295 ≤ (45983850291397/100000000000000 : ℝ)^4271
        have hw : |(2671923923/5000000000 : ℝ)|=(2671923923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284547091/2500000000 : ℝ)|^5295 ≤ (10950018517527/25000000000000 : ℝ)^4271
        have hw : |(1284547091/2500000000 : ℝ)|=(1284547091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99256431/625000000 : ℝ)|^5295 ≤ (2043215124117/20000000000000 : ℝ)^4271
        have hw : |(-99256431/625000000 : ℝ)|=(99256431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026499151/2500000000 : ℝ)*x 0 + (3643015009/10000000000 : ℝ)*x 1 + (46046909/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026499151/2500000000 : ℝ)^5295 ≤ (8292265307769/25000000000000 : ℝ)^4271 := by
    have hnat : (1026499151 : ℕ)^5295*25000000000000^4271 ≤ 8292265307769^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026499151 2500000000 8292265307769 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3643015009/10000000000 : ℝ)^5295 ≤ (7149215448469/25000000000000 : ℝ)^4271 := by
    have hnat : (3643015009 : ℕ)^5295*25000000000000^4271 ≤ 7149215448469^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3643015009 10000000000 7149215448469 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46046909/100000000 : ℝ)^5295 ≤ (38234076955037/100000000000000 : ℝ)^4271 := by
    have hnat : (46046909 : ℕ)^5295*100000000000000^4271 ≤ 38234076955037^4271*100000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46046909 100000000 38234076955037 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026499151/2500000000 : ℝ), (3643015009/10000000000 : ℝ), (46046909/100000000 : ℝ)] ![(8292265307769/25000000000000 : ℝ), (7149215448469/25000000000000 : ℝ), (38234076955037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026499151/2500000000 : ℝ)|^5295 ≤ (8292265307769/25000000000000 : ℝ)^4271
        have hw : |(1026499151/2500000000 : ℝ)|=(1026499151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3643015009/10000000000 : ℝ)|^5295 ≤ (7149215448469/25000000000000 : ℝ)^4271
        have hw : |(3643015009/10000000000 : ℝ)|=(3643015009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46046909/100000000 : ℝ)|^5295 ≤ (38234076955037/100000000000000 : ℝ)^4271
        have hw : |(46046909/100000000 : ℝ)|=(46046909/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-70792603/500000000 : ℝ)*x 0 + (2570933347/5000000000 : ℝ)*x 1 + (34168209/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70792603/500000000 : ℝ)^5295 ≤ (1772143526401/20000000000000 : ℝ)^4271 := by
    have hnat : (70792603 : ℕ)^5295*20000000000000^4271 ≤ 1772143526401^4271*500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70792603 500000000 1772143526401 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570933347/5000000000 : ℝ)^5295 ≤ (8767790149989/20000000000000 : ℝ)^4271 := by
    have hnat : (2570933347 : ℕ)^5295*20000000000000^4271 ≤ 8767790149989^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570933347 5000000000 8767790149989 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34168209/62500000 : ℝ)^5295 ≤ (2365016580509/5000000000000 : ℝ)^4271 := by
    have hnat : (34168209 : ℕ)^5295*5000000000000^4271 ≤ 2365016580509^4271*62500000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34168209 62500000 2365016580509 5000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70792603/500000000 : ℝ), (2570933347/5000000000 : ℝ), (34168209/62500000 : ℝ)] ![(1772143526401/20000000000000 : ℝ), (8767790149989/20000000000000 : ℝ), (2365016580509/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70792603/500000000 : ℝ)|^5295 ≤ (1772143526401/20000000000000 : ℝ)^4271
        have hw : |(-70792603/500000000 : ℝ)|=(70792603/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570933347/5000000000 : ℝ)|^5295 ≤ (8767790149989/20000000000000 : ℝ)^4271
        have hw : |(2570933347/5000000000 : ℝ)|=(2570933347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34168209/62500000 : ℝ)|^5295 ≤ (2365016580509/5000000000000 : ℝ)^4271
        have hw : |(34168209/62500000 : ℝ)|=(34168209/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313715019/2500000000 : ℝ)*x 0 + (136672837/250000000 : ℝ)*x 1 + (-629689111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313715019/2500000000 : ℝ)^5295 ≤ (45036421797757/100000000000000 : ℝ)^4271 := by
    have hnat : (1313715019 : ℕ)^5295*100000000000000^4271 ≤ 45036421797757^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313715019 2500000000 45036421797757 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136672837/250000000 : ℝ)^5295 ≤ (1182508300981/2500000000000 : ℝ)^4271 := by
    have hnat : (136672837 : ℕ)^5295*2500000000000^4271 ≤ 1182508300981^4271*250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136672837 250000000 1182508300981 2500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629689111/5000000000 : ℝ)^5295 ≤ (1532649232009/20000000000000 : ℝ)^4271 := by
    have hnat : (629689111 : ℕ)^5295*20000000000000^4271 ≤ 1532649232009^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629689111 5000000000 1532649232009 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313715019/2500000000 : ℝ), (136672837/250000000 : ℝ), (-629689111/5000000000 : ℝ)] ![(45036421797757/100000000000000 : ℝ), (1182508300981/2500000000000 : ℝ), (1532649232009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313715019/2500000000 : ℝ)|^5295 ≤ (45036421797757/100000000000000 : ℝ)^4271
        have hw : |(1313715019/2500000000 : ℝ)|=(1313715019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136672837/250000000 : ℝ)|^5295 ≤ (1182508300981/2500000000000 : ℝ)^4271
        have hw : |(136672837/250000000 : ℝ)|=(136672837/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629689111/5000000000 : ℝ)|^5295 ≤ (1532649232009/20000000000000 : ℝ)^4271
        have hw : |(-629689111/5000000000 : ℝ)|=(629689111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_s4_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4106433091/10000000000 : ℝ)*x 0 + (4594050439/10000000000 : ℝ)*x 1 + (182690703/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4106433091/10000000000 : ℝ)^5295 ≤ (1326937308177/4000000000000 : ℝ)^4271 := by
    have hnat : (4106433091 : ℕ)^5295*4000000000000^4271 ≤ 1326937308177^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106433091 10000000000 1326937308177 4000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4594050439/10000000000 : ℝ)^5295 ≤ (1524982952607/4000000000000 : ℝ)^4271 := by
    have hnat : (4594050439 : ℕ)^5295*4000000000000^4271 ≤ 1524982952607^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594050439 10000000000 1524982952607 4000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182690703/500000000 : ℝ)^5295 ≤ (28701993469803/100000000000000 : ℝ)^4271 := by
    have hnat : (182690703 : ℕ)^5295*100000000000000^4271 ≤ 28701993469803^4271*500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182690703 500000000 28701993469803 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4106433091/10000000000 : ℝ), (4594050439/10000000000 : ℝ), (182690703/500000000 : ℝ)] ![(1326937308177/4000000000000 : ℝ), (1524982952607/4000000000000 : ℝ), (28701993469803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4106433091/10000000000 : ℝ)|^5295 ≤ (1326937308177/4000000000000 : ℝ)^4271
        have hw : |(4106433091/10000000000 : ℝ)|=(4106433091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4594050439/10000000000 : ℝ)|^5295 ≤ (1524982952607/4000000000000 : ℝ)^4271
        have hw : |(4594050439/10000000000 : ℝ)|=(4594050439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182690703/500000000 : ℝ)|^5295 ≤ (28701993469803/100000000000000 : ℝ)^4271
        have hw : |(182690703/500000000 : ℝ)|=(182690703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (171/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5001/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10003/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (171/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (171/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5001/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (171/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5001/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (171/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5001/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (171/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5001/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (171/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5001/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (171/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5001/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5001/50000 : ℝ) ^ (5287/1024 : ℝ) ≤ (687642131126143/100000000000000000000 : ℝ) := by
    have hpowers : (5001/50000 : ℝ)^5287 ≤ (687642131126143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5001 : ℕ)^5287*100000000000000000000^1024 ≤ 687642131126143^1024*50000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001 50000 687642131126143 100000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5001/50000 : ℝ)) (X := (687642131126143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (171/1000 : ℝ) ^ (5287/1024 : ℝ) ≤ (5481040459122951/50000000000000000000 : ℝ) := by
    have hpowers : (171/1000 : ℝ)^5287 ≤ (5481040459122951/50000000000000000000 : ℝ)^1024 := by
      have hnat : (171 : ℕ)^5287*50000000000000000000^1024 ≤ 5481040459122951^1024*1000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        171 1000 5481040459122951 50000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (171/1000 : ℝ)) (X := (5481040459122951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000687642131126143/50000000000000000000 : ℝ) ≤ (10000026636717917/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50000687642131126143/50000000000000000000 : ℝ)^1024 ≤ (10000026636717917/10000000000000000 : ℝ)^5287 := by
      have hnat : (50000687642131126143 : ℕ)^1024*10000000000000000^5287 ≤ 10000026636717917^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000687642131126143 50000000000000000000 10000026636717917 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026636717917/10000000000000000 : ℝ)) (X := (50000687642131126143/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002329944609874409/20000000000000000000 : ℝ) ≤ (2500056406072249/2500000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (20002329944609874409/20000000000000000000 : ℝ)^1024 ≤ (2500056406072249/2500000000000000 : ℝ)^5287 := by
      have hnat : (20002329944609874409 : ℕ)^1024*2500000000000000^5287 ≤ 2500056406072249^5287*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002329944609874409 20000000000000000000 2500056406072249 2500000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500056406072249/2500000000000000 : ℝ)) (X := (20002329944609874409/20000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005481040459122951/25000000000000000000 : ℝ) ≤ (400016984474403/400000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (25005481040459122951/25000000000000000000 : ℝ)^1024 ≤ (400016984474403/400000000000000 : ℝ)^5287 := by
      have hnat : (25005481040459122951 : ℕ)^1024*400000000000000^5287 ≤ 400016984474403^5287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005481040459122951 25000000000000000000 400016984474403 400000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016984474403/400000000000000 : ℝ)) (X := (25005481040459122951/25000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(687642131126143/100000000000000000000 : ℝ) ≤ ((473174723467012737/473200000000000000 : ℝ)+2*(198987571079/709800000000000 : ℝ)*(5001/50000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (473174723467012737/473200000000000000 : ℝ)+2*(198987571079/709800000000000 : ℝ)*(5001/50000 : ℝ)=(10000026636717917/10000000000000000 : ℝ) by norm_num, show 1+2*(687642131126143/100000000000000000000 : ℝ)=(50000687642131126143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5481040459122951/50000000000000000000 : ℝ)+(687642131126143/100000000000000000000 : ℝ) ≤ ((473174723467012737/473200000000000000 : ℝ)+(198987571079/709800000000000 : ℝ)*((171/1000 : ℝ)+(5001/50000 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (473174723467012737/473200000000000000 : ℝ)+(198987571079/709800000000000 : ℝ)*((171/1000 : ℝ)+(5001/50000 : ℝ))=(2500056406072249/2500000000000000 : ℝ) by norm_num, show 1+(5481040459122951/50000000000000000000 : ℝ)+(687642131126143/100000000000000000000 : ℝ)=(20002329944609874409/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5481040459122951/50000000000000000000 : ℝ) ≤ ((473174723467012737/473200000000000000 : ℝ)+2*(198987571079/709800000000000 : ℝ)*(171/1000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (473174723467012737/473200000000000000 : ℝ)+2*(198987571079/709800000000000 : ℝ)*(171/1000 : ℝ)=(400016984474403/400000000000000 : ℝ) by norm_num, show 1+2*(5481040459122951/50000000000000000000 : ℝ)=(25005481040459122951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (473174723467012737/473200000000000000 : ℝ)*(X 1 0+X 2 0)+(198987571079/709800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (5001/50000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (473174723467012737/473200000000000000 : ℝ)) (alpha := (198987571079/709800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (473174723467012737/473200000000000000 : ℝ)*(X 0 1+X 2 1)+(198987571079/709800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (5001/50000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (473174723467012737/473200000000000000 : ℝ)) (alpha := (198987571079/709800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (473174723467012737/473200000000000000 : ℝ)*(X 0 2+X 1 2)+(198987571079/709800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (5001/50000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (473174723467012737/473200000000000000 : ℝ)) (alpha := (198987571079/709800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-283140249/2000000000 : ℝ)*X 0 0+(1367661701/2500000000 : ℝ)*X 0 1+(1284547033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2671923571/5000000000 : ℝ)*X 1 0+(-397025559/2500000000 : ℝ)*X 1 1+(5138189573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671923923/5000000000 : ℝ)*X 2 0+(1284547091/2500000000 : ℝ)*X 2 1+(-99256431/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026499151/2500000000 : ℝ)*X 0 0+(3643015009/10000000000 : ℝ)*X 0 1+(46046909/100000000 : ℝ)*X 0 2+(1026499151/2500000000 : ℝ)*X 1 0+(3643015009/10000000000 : ℝ)*X 1 1+(46046909/100000000 : ℝ)*X 1 2+(1026499151/2500000000 : ℝ)*X 2 0+(3643015009/10000000000 : ℝ)*X 2 1+(46046909/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-70792603/500000000 : ℝ)*X 0 0+(2570933347/5000000000 : ℝ)*X 0 1+(34168209/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313715019/2500000000 : ℝ)*X 2 0+(136672837/250000000 : ℝ)*X 2 1+(-629689111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4106433091/10000000000 : ℝ)*X 0 0+(4594050439/10000000000 : ℝ)*X 0 1+(182690703/500000000 : ℝ)*X 0 2+(4106433091/10000000000 : ℝ)*X 1 0+(4594050439/10000000000 : ℝ)*X 1 1+(182690703/500000000 : ℝ)*X 1 2+(4106433091/10000000000 : ℝ)*X 2 0+(4594050439/10000000000 : ℝ)*X 2 1+(182690703/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43645192763511251159227469/11830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254672039/50000000000000 : ℝ)*(base19) + (882627419/100000000000000 : ℝ)*(base23) + (13023343/100000000000000 : ℝ)*(upper2) + (164888739/100000000000000 : ℝ)*(upper3) + (1011947174505707/50000000000000 : ℝ)*(major0) + (1011947174505707/50000000000000 : ℝ)*(major1) + (1011947174505707/50000000000000 : ℝ)*(major2) + (300791030651511/10000000000000 : ℝ)*(sp0) + (187995343740693/6250000000000 : ℝ)*(sp1) + (3007922282990321/100000000000000 : ℝ)*(sp2) + (1039856282302843/100000000000000 : ℝ)*(sp3) + (1962835007/12500000000000 : ℝ)*(sp4) + (2843577427/100000000000000 : ℝ)*(sp5) + (392721623/6250000000000 : ℝ)*(sp6) + (1039862565848811/100000000000000 : ℝ)*(f.failure) + (1503963004597583/50000000000000 : ℝ)*(f.sum) + (25650941489897/17745000000000000000000000000 : ℝ)*base66 + (65186478609162311/10140000000000000000000000000000 : ℝ)*base67 + (11192478345582311/10140000000000000000000000000000 : ℝ)*base69 + (20127878631342311/10140000000000000000000000000000 : ℝ)*base71 + (8876018150729/8872500000000000000000000000 : ℝ)*base73 + (3412276748622311/10140000000000000000000000000000 : ℝ)*base75 + (66392515658262311/10140000000000000000000000000000 : ℝ)*base77 + (2387658759162311/10140000000000000000000000000000 : ℝ)*base79 + (16081585047797/17745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11047397/5000000000000000000000 : ℝ)*base90 + (11047397/5000000000000000000000 : ℝ)*base92 + (11047397/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1709_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (171/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5001/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10003/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (171/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1709_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1709_box_0 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096300173/10000000000 : ℝ)*x 0 + (1354438969/2500000000 : ℝ)*x 1 + (2708878087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096300173/10000000000 : ℝ)^5295 ≤ (6452772268391/100000000000000 : ℝ)^4271 := by
    have hnat : (1096300173 : ℕ)^5295*100000000000000^4271 ≤ 6452772268391^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096300173 10000000000 6452772268391 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354438969/2500000000 : ℝ)^5295 ≤ (46773612260811/100000000000000 : ℝ)^4271 := by
    have hnat : (1354438969 : ℕ)^5295*100000000000000^4271 ≤ 46773612260811^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354438969 2500000000 46773612260811 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708878087/5000000000 : ℝ)^5295 ≤ (11693403862599/25000000000000 : ℝ)^4271 := by
    have hnat : (2708878087 : ℕ)^5295*25000000000000^4271 ≤ 11693403862599^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708878087 5000000000 11693403862599 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096300173/10000000000 : ℝ), (1354438969/2500000000 : ℝ), (2708878087/5000000000 : ℝ)] ![(6452772268391/100000000000000 : ℝ), (46773612260811/100000000000000 : ℝ), (11693403862599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096300173/10000000000 : ℝ)|^5295 ≤ (6452772268391/100000000000000 : ℝ)^4271
        have hw : |(-1096300173/10000000000 : ℝ)|=(1096300173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354438969/2500000000 : ℝ)|^5295 ≤ (46773612260811/100000000000000 : ℝ)^4271
        have hw : |(1354438969/2500000000 : ℝ)|=(1354438969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708878087/5000000000 : ℝ)|^5295 ≤ (11693403862599/25000000000000 : ℝ)^4271
        have hw : |(2708878087/5000000000 : ℝ)|=(2708878087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_1 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612725557/5000000000 : ℝ)*x 0 + (-1369463931/10000000000 : ℝ)*x 1 + (5417755941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612725557/5000000000 : ℝ)^5295 ≤ (5590519274343/12500000000000 : ℝ)^4271 := by
    have hnat : (2612725557 : ℕ)^5295*12500000000000^4271 ≤ 5590519274343^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612725557 5000000000 5590519274343 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369463931/10000000000 : ℝ)^5295 ≤ (4251116418443/50000000000000 : ℝ)^4271 := by
    have hnat : (1369463931 : ℕ)^5295*50000000000000^4271 ≤ 4251116418443^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369463931 10000000000 4251116418443 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417755941/10000000000 : ℝ)^5295 ≤ (23386806478263/50000000000000 : ℝ)^4271 := by
    have hnat : (5417755941 : ℕ)^5295*50000000000000^4271 ≤ 23386806478263^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417755941 10000000000 23386806478263 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612725557/5000000000 : ℝ), (-1369463931/10000000000 : ℝ), (5417755941/10000000000 : ℝ)] ![(5590519274343/12500000000000 : ℝ), (4251116418443/50000000000000 : ℝ), (23386806478263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612725557/5000000000 : ℝ)|^5295 ≤ (5590519274343/12500000000000 : ℝ)^4271
        have hw : |(2612725557/5000000000 : ℝ)|=(2612725557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1369463931/10000000000 : ℝ)|^5295 ≤ (4251116418443/50000000000000 : ℝ)^4271
        have hw : |(-1369463931/10000000000 : ℝ)|=(1369463931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417755941/10000000000 : ℝ)|^5295 ≤ (23386806478263/50000000000000 : ℝ)^4271
        have hw : |(5417755941/10000000000 : ℝ)|=(5417755941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_2 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306362717/2500000000 : ℝ)*x 0 + (2708878109/5000000000 : ℝ)*x 1 + (-273892777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306362717/2500000000 : ℝ)^5295 ≤ (44724151584447/100000000000000 : ℝ)^4271 := by
    have hnat : (1306362717 : ℕ)^5295*100000000000000^4271 ≤ 44724151584447^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306362717 2500000000 44724151584447 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708878109/5000000000 : ℝ)^5295 ≤ (46773615921341/100000000000000 : ℝ)^4271 := by
    have hnat : (2708878109 : ℕ)^5295*100000000000000^4271 ≤ 46773615921341^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708878109 5000000000 46773615921341 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273892777/2000000000 : ℝ)^5295 ≤ (4251116241413/50000000000000 : ℝ)^4271 := by
    have hnat : (273892777 : ℕ)^5295*50000000000000^4271 ≤ 4251116241413^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273892777 2000000000 4251116241413 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306362717/2500000000 : ℝ), (2708878109/5000000000 : ℝ), (-273892777/2000000000 : ℝ)] ![(44724151584447/100000000000000 : ℝ), (46773615921341/100000000000000 : ℝ), (4251116241413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306362717/2500000000 : ℝ)|^5295 ≤ (44724151584447/100000000000000 : ℝ)^4271
        have hw : |(1306362717/2500000000 : ℝ)|=(1306362717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708878109/5000000000 : ℝ)|^5295 ≤ (46773615921341/100000000000000 : ℝ)^4271
        have hw : |(2708878109/5000000000 : ℝ)|=(2708878109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273892777/2000000000 : ℝ)|^5295 ≤ (4251116241413/50000000000000 : ℝ)^4271
        have hw : |(-273892777/2000000000 : ℝ)|=(273892777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_3 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4487962077/10000000000 : ℝ)*x 0 + (1968345199/5000000000 : ℝ)*x 1 + (1968345227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487962077/10000000000 : ℝ)^5295 ≤ (37036139249843/100000000000000 : ℝ)^4271 := by
    have hnat : (4487962077 : ℕ)^5295*100000000000000^4271 ≤ 37036139249843^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487962077 10000000000 37036139249843 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968345199/5000000000 : ℝ)^5295 ≤ (6296386018231/20000000000000 : ℝ)^4271 := by
    have hnat : (1968345199 : ℕ)^5295*20000000000000^4271 ≤ 6296386018231^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968345199 5000000000 6296386018231 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968345227/5000000000 : ℝ)^5295 ≤ (31481930646361/100000000000000 : ℝ)^4271 := by
    have hnat : (1968345227 : ℕ)^5295*100000000000000^4271 ≤ 31481930646361^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968345227 5000000000 31481930646361 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487962077/10000000000 : ℝ), (1968345199/5000000000 : ℝ), (1968345227/5000000000 : ℝ)] ![(37036139249843/100000000000000 : ℝ), (6296386018231/20000000000000 : ℝ), (31481930646361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487962077/10000000000 : ℝ)|^5295 ≤ (37036139249843/100000000000000 : ℝ)^4271
        have hw : |(4487962077/10000000000 : ℝ)|=(4487962077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1968345199/5000000000 : ℝ)|^5295 ≤ (6296386018231/20000000000000 : ℝ)^4271
        have hw : |(1968345199/5000000000 : ℝ)|=(1968345199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1968345227/5000000000 : ℝ)|^5295 ≤ (31481930646361/100000000000000 : ℝ)^4271
        have hw : |(1968345227/5000000000 : ℝ)|=(1968345227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_4 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438937119/2500000000 : ℝ)*x 0 + (2588717351/5000000000 : ℝ)*x 1 + (2588717201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438937119/2500000000 : ℝ)^5295 ≤ (1446196281799/12500000000000 : ℝ)^4271 := by
    have hnat : (438937119 : ℕ)^5295*12500000000000^4271 ≤ 1446196281799^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438937119 2500000000 1446196281799 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588717351/5000000000 : ℝ)^5295 ≤ (44215216449171/100000000000000 : ℝ)^4271 := by
    have hnat : (2588717351 : ℕ)^5295*100000000000000^4271 ≤ 44215216449171^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588717351 5000000000 44215216449171 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588717201/5000000000 : ℝ)^5295 ≤ (44215213272921/100000000000000 : ℝ)^4271 := by
    have hnat : (2588717201 : ℕ)^5295*100000000000000^4271 ≤ 44215213272921^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588717201 5000000000 44215213272921 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438937119/2500000000 : ℝ), (2588717351/5000000000 : ℝ), (2588717201/5000000000 : ℝ)] ![(1446196281799/12500000000000 : ℝ), (44215216449171/100000000000000 : ℝ), (44215213272921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438937119/2500000000 : ℝ)|^5295 ≤ (1446196281799/12500000000000 : ℝ)^4271
        have hw : |(-438937119/2500000000 : ℝ)|=(438937119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588717351/5000000000 : ℝ)|^5295 ≤ (44215216449171/100000000000000 : ℝ)^4271
        have hw : |(2588717351/5000000000 : ℝ)|=(2588717351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588717201/5000000000 : ℝ)|^5295 ≤ (44215213272921/100000000000000 : ℝ)^4271
        have hw : |(2588717201/5000000000 : ℝ)|=(2588717201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_5 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388470901/10000000000 : ℝ)*x 0 + (-1475321103/10000000000 : ℝ)*x 1 + (517743437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388470901/10000000000 : ℝ)^5295 ≤ (46460369649889/100000000000000 : ℝ)^4271 := by
    have hnat : (5388470901 : ℕ)^5295*100000000000000^4271 ≤ 46460369649889^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388470901 10000000000 46460369649889 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1475321103/10000000000 : ℝ)^5295 ≤ (4662208699479/50000000000000 : ℝ)^4271 := by
    have hnat : (1475321103 : ℕ)^5295*50000000000000^4271 ≤ 4662208699479^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475321103 10000000000 4662208699479 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517743437/1000000000 : ℝ)^5295 ≤ (44215212934121/100000000000000 : ℝ)^4271 := by
    have hnat : (517743437 : ℕ)^5295*100000000000000^4271 ≤ 44215212934121^4271*1000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517743437 1000000000 44215212934121 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388470901/10000000000 : ℝ), (-1475321103/10000000000 : ℝ), (517743437/1000000000 : ℝ)] ![(46460369649889/100000000000000 : ℝ), (4662208699479/50000000000000 : ℝ), (44215212934121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388470901/10000000000 : ℝ)|^5295 ≤ (46460369649889/100000000000000 : ℝ)^4271
        have hw : |(5388470901/10000000000 : ℝ)|=(5388470901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1475321103/10000000000 : ℝ)|^5295 ≤ (4662208699479/50000000000000 : ℝ)^4271
        have hw : |(-1475321103/10000000000 : ℝ)|=(1475321103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517743437/1000000000 : ℝ)|^5295 ≤ (44215212934121/100000000000000 : ℝ)^4271
        have hw : |(517743437/1000000000 : ℝ)|=(517743437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_6 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694235331/5000000000 : ℝ)*x 0 + (1035486897/2000000000 : ℝ)*x 1 + (-1475321273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694235331/5000000000 : ℝ)^5295 ≤ (46460367095121/100000000000000 : ℝ)^4271 := by
    have hnat : (2694235331 : ℕ)^5295*100000000000000^4271 ≤ 46460367095121^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694235331 5000000000 46460367095121 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035486897/2000000000 : ℝ)^5295 ≤ (44215214151683/100000000000000 : ℝ)^4271 := by
    have hnat : (1035486897 : ℕ)^5295*100000000000000^4271 ≤ 44215214151683^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035486897 2000000000 44215214151683 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1475321273/10000000000 : ℝ)^5295 ≤ (9105877667/97656250000 : ℝ)^4271 := by
    have hnat : (1475321273 : ℕ)^5295*97656250000^4271 ≤ 9105877667^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475321273 10000000000 9105877667 97656250000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694235331/5000000000 : ℝ), (1035486897/2000000000 : ℝ), (-1475321273/10000000000 : ℝ)] ![(46460367095121/100000000000000 : ℝ), (44215214151683/100000000000000 : ℝ), (9105877667/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694235331/5000000000 : ℝ)|^5295 ≤ (46460367095121/100000000000000 : ℝ)^4271
        have hw : |(2694235331/5000000000 : ℝ)|=(2694235331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035486897/2000000000 : ℝ)|^5295 ≤ (44215214151683/100000000000000 : ℝ)^4271
        have hw : |(1035486897/2000000000 : ℝ)|=(1035486897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1475321273/10000000000 : ℝ)|^5295 ≤ (9105877667/97656250000 : ℝ)^4271
        have hw : |(-1475321273/10000000000 : ℝ)|=(1475321273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_7 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (463553961/1250000000 : ℝ)*x 0 + (1081406763/2500000000 : ℝ)*x 1 + (865125311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463553961/1250000000 : ℝ)^5295 ≤ (3654356122699/12500000000000 : ℝ)^4271 := by
    have hnat : (463553961 : ℕ)^5295*12500000000000^4271 ≤ 3654356122699^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463553961 1250000000 3654356122699 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081406763/2500000000 : ℝ)^5295 ≤ (8845644506699/25000000000000 : ℝ)^4271 := by
    have hnat : (1081406763 : ℕ)^5295*25000000000000^4271 ≤ 8845644506699^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081406763 2500000000 8845644506699 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865125311/2000000000 : ℝ)^5295 ≤ (7076514597353/20000000000000 : ℝ)^4271 := by
    have hnat : (865125311 : ℕ)^5295*20000000000000^4271 ≤ 7076514597353^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865125311 2000000000 7076514597353 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463553961/1250000000 : ℝ), (1081406763/2500000000 : ℝ), (865125311/2000000000 : ℝ)] ![(3654356122699/12500000000000 : ℝ), (8845644506699/25000000000000 : ℝ), (7076514597353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463553961/1250000000 : ℝ)|^5295 ≤ (3654356122699/12500000000000 : ℝ)^4271
        have hw : |(463553961/1250000000 : ℝ)|=(463553961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081406763/2500000000 : ℝ)|^5295 ≤ (8845644506699/25000000000000 : ℝ)^4271
        have hw : |(1081406763/2500000000 : ℝ)|=(1081406763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865125311/2000000000 : ℝ)|^5295 ≤ (7076514597353/20000000000000 : ℝ)^4271
        have hw : |(865125311/2000000000 : ℝ)|=(865125311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_8 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613929329/10000000000 : ℝ)*x 0 + (2500055103/5000000000 : ℝ)*x 1 + (546054073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613929329/10000000000 : ℝ)^5295 ≤ (5211223309/50000000000 : ℝ)^4271 := by
    have hnat : (1613929329 : ℕ)^5295*50000000000^4271 ≤ 5211223309^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613929329 10000000000 5211223309 50000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500055103/5000000000 : ℝ)^5295 ≤ (1693822765409/4000000000000 : ℝ)^4271 := by
    have hnat : (2500055103 : ℕ)^5295*4000000000000^4271 ≤ 1693822765409^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500055103 5000000000 1693822765409 4000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546054073/1000000000 : ℝ)^5295 ≤ (5903998029663/12500000000000 : ℝ)^4271 := by
    have hnat : (546054073 : ℕ)^5295*12500000000000^4271 ≤ 5903998029663^4271*1000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546054073 1000000000 5903998029663 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613929329/10000000000 : ℝ), (2500055103/5000000000 : ℝ), (546054073/1000000000 : ℝ)] ![(5211223309/50000000000 : ℝ), (1693822765409/4000000000000 : ℝ), (5903998029663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613929329/10000000000 : ℝ)|^5295 ≤ (5211223309/50000000000 : ℝ)^4271
        have hw : |(-1613929329/10000000000 : ℝ)|=(1613929329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500055103/5000000000 : ℝ)|^5295 ≤ (1693822765409/4000000000000 : ℝ)^4271
        have hw : |(2500055103/5000000000 : ℝ)|=(2500055103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546054073/1000000000 : ℝ)|^5295 ≤ (5903998029663/12500000000000 : ℝ)^4271
        have hw : |(546054073/1000000000 : ℝ)|=(546054073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_9 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196447063/10000000000 : ℝ)*x 0 + (-337458789/2500000000 : ℝ)*x 1 + (5460541263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196447063/10000000000 : ℝ)^5295 ≤ (22208299197317/50000000000000 : ℝ)^4271 := by
    have hnat : (5196447063 : ℕ)^5295*50000000000000^4271 ≤ 22208299197317^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196447063 10000000000 22208299197317 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337458789/2500000000 : ℝ)^5295 ≤ (4175705818641/50000000000000 : ℝ)^4271 := by
    have hnat : (337458789 : ℕ)^5295*50000000000000^4271 ≤ 4175705818641^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337458789 2500000000 4175705818641 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460541263/10000000000 : ℝ)^5295 ≤ (9446397990587/20000000000000 : ℝ)^4271 := by
    have hnat : (5460541263 : ℕ)^5295*20000000000000^4271 ≤ 9446397990587^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460541263 10000000000 9446397990587 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196447063/10000000000 : ℝ), (-337458789/2500000000 : ℝ), (5460541263/10000000000 : ℝ)] ![(22208299197317/50000000000000 : ℝ), (4175705818641/50000000000000 : ℝ), (9446397990587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196447063/10000000000 : ℝ)|^5295 ≤ (22208299197317/50000000000000 : ℝ)^4271
        have hw : |(5196447063/10000000000 : ℝ)|=(5196447063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-337458789/2500000000 : ℝ)|^5295 ≤ (4175705818641/50000000000000 : ℝ)^4271
        have hw : |(-337458789/2500000000 : ℝ)|=(337458789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460541263/10000000000 : ℝ)|^5295 ≤ (9446397990587/20000000000000 : ℝ)^4271
        have hw : |(5460541263/10000000000 : ℝ)|=(5460541263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_10 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196448067/10000000000 : ℝ)*x 0 + (5460540277/10000000000 : ℝ)*x 1 + (-1349835147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196448067/10000000000 : ℝ)^5295 ≤ (5552076129229/12500000000000 : ℝ)^4271 := by
    have hnat : (5196448067 : ℕ)^5295*12500000000000^4271 ≤ 5552076129229^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196448067 10000000000 5552076129229 12500000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460540277/10000000000 : ℝ)^5295 ≤ (9446395875911/20000000000000 : ℝ)^4271 := by
    have hnat : (5460540277 : ℕ)^5295*20000000000000^4271 ≤ 9446395875911^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460540277 10000000000 9446395875911 20000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349835147/10000000000 : ℝ)^5295 ≤ (8351411568249/100000000000000 : ℝ)^4271 := by
    have hnat : (1349835147 : ℕ)^5295*100000000000000^4271 ≤ 8351411568249^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349835147 10000000000 8351411568249 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196448067/10000000000 : ℝ), (5460540277/10000000000 : ℝ), (-1349835147/10000000000 : ℝ)] ![(5552076129229/12500000000000 : ℝ), (9446395875911/20000000000000 : ℝ), (8351411568249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196448067/10000000000 : ℝ)|^5295 ≤ (5552076129229/12500000000000 : ℝ)^4271
        have hw : |(5196448067/10000000000 : ℝ)|=(5196448067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460540277/10000000000 : ℝ)|^5295 ≤ (9446395875911/20000000000000 : ℝ)^4271
        have hw : |(5460540277/10000000000 : ℝ)|=(5460540277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349835147/10000000000 : ℝ)|^5295 ≤ (8351411568249/100000000000000 : ℝ)^4271
        have hw : |(-1349835147/10000000000 : ℝ)|=(1349835147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_11 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2310878809/5000000000 : ℝ)*x 0 + (773452761/2000000000 : ℝ)*x 1 + (3867266007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2310878809/5000000000 : ℝ)^5295 ≤ (38409840689831/100000000000000 : ℝ)^4271 := by
    have hnat : (2310878809 : ℕ)^5295*100000000000000^4271 ≤ 38409840689831^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310878809 5000000000 38409840689831 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773452761/2000000000 : ℝ)^5295 ≤ (7698767193839/25000000000000 : ℝ)^4271 := by
    have hnat : (773452761 : ℕ)^5295*25000000000000^4271 ≤ 7698767193839^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773452761 2000000000 7698767193839 25000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3867266007/10000000000 : ℝ)^5295 ≤ (30795090513933/100000000000000 : ℝ)^4271 := by
    have hnat : (3867266007 : ℕ)^5295*100000000000000^4271 ≤ 30795090513933^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867266007 10000000000 30795090513933 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2310878809/5000000000 : ℝ), (773452761/2000000000 : ℝ), (3867266007/10000000000 : ℝ)] ![(38409840689831/100000000000000 : ℝ), (7698767193839/25000000000000 : ℝ), (30795090513933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2310878809/5000000000 : ℝ)|^5295 ≤ (38409840689831/100000000000000 : ℝ)^4271
        have hw : |(2310878809/5000000000 : ℝ)|=(2310878809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773452761/2000000000 : ℝ)|^5295 ≤ (7698767193839/25000000000000 : ℝ)^4271
        have hw : |(773452761/2000000000 : ℝ)|=(773452761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3867266007/10000000000 : ℝ)|^5295 ≤ (30795090513933/100000000000000 : ℝ)^4271
        have hw : |(3867266007/10000000000 : ℝ)|=(3867266007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_12 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232694249/10000000000 : ℝ)*x 0 + (5586670947/10000000000 : ℝ)*x 1 + (644037683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232694249/10000000000 : ℝ)^5295 ≤ (7462460369497/100000000000000 : ℝ)^4271 := by
    have hnat : (1232694249 : ℕ)^5295*100000000000000^4271 ≤ 7462460369497^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232694249 10000000000 7462460369497 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5586670947/10000000000 : ℝ)^5295 ≤ (24294133166553/50000000000000 : ℝ)^4271 := by
    have hnat : (5586670947 : ℕ)^5295*50000000000000^4271 ≤ 24294133166553^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586670947 10000000000 24294133166553 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644037683/1250000000 : ℝ)^5295 ≤ (43949273276431/100000000000000 : ℝ)^4271 := by
    have hnat : (644037683 : ℕ)^5295*100000000000000^4271 ≤ 43949273276431^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644037683 1250000000 43949273276431 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232694249/10000000000 : ℝ), (5586670947/10000000000 : ℝ), (644037683/1250000000 : ℝ)] ![(7462460369497/100000000000000 : ℝ), (24294133166553/50000000000000 : ℝ), (43949273276431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232694249/10000000000 : ℝ)|^5295 ≤ (7462460369497/100000000000000 : ℝ)^4271
        have hw : |(-1232694249/10000000000 : ℝ)|=(1232694249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5586670947/10000000000 : ℝ)|^5295 ≤ (24294133166553/50000000000000 : ℝ)^4271
        have hw : |(5586670947/10000000000 : ℝ)|=(5586670947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644037683/1250000000 : ℝ)|^5295 ≤ (43949273276431/100000000000000 : ℝ)^4271
        have hw : |(644037683/1250000000 : ℝ)|=(644037683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_13 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405550363/10000000000 : ℝ)*x 0 + (-1485943511/10000000000 : ℝ)*x 1 + (2576150569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405550363/10000000000 : ℝ)^5295 ≤ (46643008243149/100000000000000 : ℝ)^4271 := by
    have hnat : (5405550363 : ℕ)^5295*100000000000000^4271 ≤ 46643008243149^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405550363 10000000000 46643008243149 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1485943511/10000000000 : ℝ)^5295 ≤ (4703860956291/50000000000000 : ℝ)^4271 := by
    have hnat : (1485943511 : ℕ)^5295*50000000000000^4271 ≤ 4703860956291^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485943511 10000000000 4703860956291 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576150569/5000000000 : ℝ)^5295 ≤ (4394926982893/10000000000000 : ℝ)^4271 := by
    have hnat : (2576150569 : ℕ)^5295*10000000000000^4271 ≤ 4394926982893^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576150569 5000000000 4394926982893 10000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405550363/10000000000 : ℝ), (-1485943511/10000000000 : ℝ), (2576150569/5000000000 : ℝ)] ![(46643008243149/100000000000000 : ℝ), (4703860956291/50000000000000 : ℝ), (4394926982893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405550363/10000000000 : ℝ)|^5295 ≤ (46643008243149/100000000000000 : ℝ)^4271
        have hw : |(5405550363/10000000000 : ℝ)|=(5405550363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1485943511/10000000000 : ℝ)|^5295 ≤ (4703860956291/50000000000000 : ℝ)^4271
        have hw : |(-1485943511/10000000000 : ℝ)|=(1485943511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576150569/5000000000 : ℝ)|^5295 ≤ (4394926982893/10000000000000 : ℝ)^4271
        have hw : |(2576150569/5000000000 : ℝ)|=(2576150569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_14 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081109961/2000000000 : ℝ)*x 0 + (2576150607/5000000000 : ℝ)*x 1 + (-1485944169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081109961/2000000000 : ℝ)^5295 ≤ (23321501136967/50000000000000 : ℝ)^4271 := by
    have hnat : (1081109961 : ℕ)^5295*50000000000000^4271 ≤ 23321501136967^4271*2000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081109961 2000000000 23321501136967 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576150607/5000000000 : ℝ)^5295 ≤ (21974635316321/50000000000000 : ℝ)^4271 := by
    have hnat : (2576150607 : ℕ)^5295*50000000000000^4271 ≤ 21974635316321^4271*5000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576150607 5000000000 21974635316321 50000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1485944169/10000000000 : ℝ)^5295 ≤ (376309083091/4000000000000 : ℝ)^4271 := by
    have hnat : (1485944169 : ℕ)^5295*4000000000000^4271 ≤ 376309083091^4271*10000000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485944169 10000000000 376309083091 4000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081109961/2000000000 : ℝ), (2576150607/5000000000 : ℝ), (-1485944169/10000000000 : ℝ)] ![(23321501136967/50000000000000 : ℝ), (21974635316321/50000000000000 : ℝ), (376309083091/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081109961/2000000000 : ℝ)|^5295 ≤ (23321501136967/50000000000000 : ℝ)^4271
        have hw : |(1081109961/2000000000 : ℝ)|=(1081109961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576150607/5000000000 : ℝ)|^5295 ≤ (21974635316321/50000000000000 : ℝ)^4271
        have hw : |(2576150607/5000000000 : ℝ)|=(2576150607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1485944169/10000000000 : ℝ)|^5295 ≤ (376309083091/4000000000000 : ℝ)^4271
        have hw : |(-1485944169/10000000000 : ℝ)|=(1485944169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1709_box_15 (p : ℝ) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (905980961/2500000000 : ℝ)*x 0 + (34110881/78125000 : ℝ)*x 1 + (545773947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905980961/2500000000 : ℝ)^5295 ≤ (28411186996583/100000000000000 : ℝ)^4271 := by
    have hnat : (905980961 : ℕ)^5295*100000000000000^4271 ≤ 28411186996583^4271*2500000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905980961 2500000000 28411186996583 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34110881/78125000 : ℝ)^5295 ≤ (35794412552493/100000000000000 : ℝ)^4271 := by
    have hnat : (34110881 : ℕ)^5295*100000000000000^4271 ≤ 35794412552493^4271*78125000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34110881 78125000 35794412552493 100000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545773947/1250000000 : ℝ)^5295 ≤ (715888008749/2000000000000 : ℝ)^4271 := by
    have hnat : (545773947 : ℕ)^5295*2000000000000^4271 ≤ 715888008749^4271*1250000000^5295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545773947 1250000000 715888008749 2000000000000 5295 4271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5295/1024 : ℝ)) 5295 4271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(905980961/2500000000 : ℝ), (34110881/78125000 : ℝ), (545773947/1250000000 : ℝ)] ![(28411186996583/100000000000000 : ℝ), (35794412552493/100000000000000 : ℝ), (715888008749/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(905980961/2500000000 : ℝ)|^5295 ≤ (28411186996583/100000000000000 : ℝ)^4271
        have hw : |(905980961/2500000000 : ℝ)|=(905980961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34110881/78125000 : ℝ)|^5295 ≤ (35794412552493/100000000000000 : ℝ)^4271
        have hw : |(34110881/78125000 : ℝ)|=(34110881/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545773947/1250000000 : ℝ)|^5295 ≤ (715888008749/2000000000000 : ℝ)^4271
        have hw : |(545773947/1250000000 : ℝ)|=(545773947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1709_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (171/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66737/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58379/100000 : ℝ) ∧ (81449/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90409/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (171/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (171/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10003/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (171/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (171/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10003/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (171/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (171/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10003/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10003/100000 : ℝ) ^ (5287/1024 : ℝ) ≤ (687997169555367/100000000000000000000 : ℝ) := by
    have hpowers : (10003/100000 : ℝ)^5287 ≤ (687997169555367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10003 : ℕ)^5287*100000000000000000000^1024 ≤ 687997169555367^1024*100000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003 100000 687997169555367 100000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10003/100000 : ℝ)) (X := (687997169555367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (171/1000 : ℝ) ^ (5287/1024 : ℝ) ≤ (5481040459122951/50000000000000000000 : ℝ) := by
    have hpowers : (171/1000 : ℝ)^5287 ≤ (5481040459122951/50000000000000000000 : ℝ)^1024 := by
      have hnat : (171 : ℕ)^5287*50000000000000000000^1024 ≤ 5481040459122951^1024*1000^5287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        171 1000 5481040459122951 50000000000000000000 5287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (171/1000 : ℝ)) (X := (5481040459122951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000687997169555367/50000000000000000000 : ℝ) ≤ (10000026650470719/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (50000687997169555367/50000000000000000000 : ℝ)^1024 ≤ (10000026650470719/10000000000000000 : ℝ)^5287 := by
      have hnat : (50000687997169555367 : ℕ)^1024*10000000000000000^5287 ≤ 10000026650470719^5287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000687997169555367 50000000000000000000 10000026650470719 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026650470719/10000000000000000 : ℝ)) (X := (50000687997169555367/50000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011650078087801269/100000000000000000000 : ℝ) ≤ (10000225631164827/10000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (100011650078087801269/100000000000000000000 : ℝ)^1024 ≤ (10000225631164827/10000000000000000 : ℝ)^5287 := by
      have hnat : (100011650078087801269 : ℕ)^1024*10000000000000000^5287 ≤ 10000225631164827^5287*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011650078087801269 100000000000000000000 10000225631164827 10000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225631164827/10000000000000000 : ℝ)) (X := (100011650078087801269/100000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005481040459122951/25000000000000000000 : ℝ) ≤ (2000084922371787/2000000000000000 : ℝ) ^ (5287/1024 : ℝ) := by
    have hpowers : (25005481040459122951/25000000000000000000 : ℝ)^1024 ≤ (2000084922371787/2000000000000000 : ℝ)^5287 := by
      have hnat : (25005481040459122951 : ℕ)^1024*2000000000000000^5287 ≤ 2000084922371787^5287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005481040459122951 25000000000000000000 2000084922371787 2000000000000000 1024 5287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000084922371787/2000000000000000 : ℝ)) (X := (25005481040459122951/25000000000000000000 : ℝ)) (by norm_num) 5287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(687997169555367/100000000000000000000 : ℝ) ≤ ((14193241666124873619/14194000000000000000 : ℝ)+2*(49745173527/177425000000000 : ℝ)*(10003/100000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (14193241666124873619/14194000000000000000 : ℝ)+2*(49745173527/177425000000000 : ℝ)*(10003/100000 : ℝ)=(10000026650470719/10000000000000000 : ℝ) by norm_num, show 1+2*(687997169555367/100000000000000000000 : ℝ)=(50000687997169555367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5481040459122951/50000000000000000000 : ℝ)+(687997169555367/100000000000000000000 : ℝ) ≤ ((14193241666124873619/14194000000000000000 : ℝ)+(49745173527/177425000000000 : ℝ)*((171/1000 : ℝ)+(10003/100000 : ℝ)))^(5287/1024 : ℝ) := by
    rw [show (14193241666124873619/14194000000000000000 : ℝ)+(49745173527/177425000000000 : ℝ)*((171/1000 : ℝ)+(10003/100000 : ℝ))=(10000225631164827/10000000000000000 : ℝ) by norm_num, show 1+(5481040459122951/50000000000000000000 : ℝ)+(687997169555367/100000000000000000000 : ℝ)=(100011650078087801269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5481040459122951/50000000000000000000 : ℝ) ≤ ((14193241666124873619/14194000000000000000 : ℝ)+2*(49745173527/177425000000000 : ℝ)*(171/1000 : ℝ))^(5287/1024 : ℝ) := by
    rw [show (14193241666124873619/14194000000000000000 : ℝ)+2*(49745173527/177425000000000 : ℝ)*(171/1000 : ℝ)=(2000084922371787/2000000000000000 : ℝ) by norm_num, show 1+2*(5481040459122951/50000000000000000000 : ℝ)=(25005481040459122951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14193241666124873619/14194000000000000000 : ℝ)*(X 1 0+X 2 0)+(49745173527/177425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (10003/100000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (14193241666124873619/14194000000000000000 : ℝ)) (alpha := (49745173527/177425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14193241666124873619/14194000000000000000 : ℝ)*(X 0 1+X 2 1)+(49745173527/177425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (10003/100000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (14193241666124873619/14194000000000000000 : ℝ)) (alpha := (49745173527/177425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14193241666124873619/14194000000000000000 : ℝ)*(X 0 2+X 1 2)+(49745173527/177425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5287/1024 : ℝ)) (lo := (10003/100000 : ℝ)) (hi := (171/1000 : ℝ)) (c := (14193241666124873619/14194000000000000000 : ℝ)) (alpha := (49745173527/177425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1096300173/10000000000 : ℝ)*X 0 0+(1354438969/2500000000 : ℝ)*X 0 1+(2708878087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612725557/5000000000 : ℝ)*X 1 0+(-1369463931/10000000000 : ℝ)*X 1 1+(5417755941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1306362717/2500000000 : ℝ)*X 2 0+(2708878109/5000000000 : ℝ)*X 2 1+(-273892777/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487962077/10000000000 : ℝ)*X 0 0+(1968345199/5000000000 : ℝ)*X 0 1+(1968345227/5000000000 : ℝ)*X 0 2+(4487962077/10000000000 : ℝ)*X 1 0+(1968345199/5000000000 : ℝ)*X 1 1+(1968345227/5000000000 : ℝ)*X 1 2+(4487962077/10000000000 : ℝ)*X 2 0+(1968345199/5000000000 : ℝ)*X 2 1+(1968345227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438937119/2500000000 : ℝ)*X 0 0+(2588717351/5000000000 : ℝ)*X 0 1+(2588717201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5388470901/10000000000 : ℝ)*X 1 0+(-1475321103/10000000000 : ℝ)*X 1 1+(517743437/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2694235331/5000000000 : ℝ)*X 2 0+(1035486897/2000000000 : ℝ)*X 2 1+(-1475321273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((463553961/1250000000 : ℝ)*X 0 0+(1081406763/2500000000 : ℝ)*X 0 1+(865125311/2000000000 : ℝ)*X 0 2+(463553961/1250000000 : ℝ)*X 1 0+(1081406763/2500000000 : ℝ)*X 1 1+(865125311/2000000000 : ℝ)*X 1 2+(463553961/1250000000 : ℝ)*X 2 0+(1081406763/2500000000 : ℝ)*X 2 1+(865125311/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1613929329/10000000000 : ℝ)*X 0 0+(2500055103/5000000000 : ℝ)*X 0 1+(546054073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196447063/10000000000 : ℝ)*X 1 0+(-337458789/2500000000 : ℝ)*X 1 1+(5460541263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196448067/10000000000 : ℝ)*X 2 0+(5460540277/10000000000 : ℝ)*X 2 1+(-1349835147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2310878809/5000000000 : ℝ)*X 0 0+(773452761/2000000000 : ℝ)*X 0 1+(3867266007/10000000000 : ℝ)*X 0 2+(2310878809/5000000000 : ℝ)*X 1 0+(773452761/2000000000 : ℝ)*X 1 1+(3867266007/10000000000 : ℝ)*X 1 2+(2310878809/5000000000 : ℝ)*X 2 0+(773452761/2000000000 : ℝ)*X 2 1+(3867266007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1232694249/10000000000 : ℝ)*X 0 0+(5586670947/10000000000 : ℝ)*X 0 1+(644037683/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5405550363/10000000000 : ℝ)*X 1 0+(-1485943511/10000000000 : ℝ)*X 1 1+(2576150569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1081109961/2000000000 : ℝ)*X 2 0+(2576150607/5000000000 : ℝ)*X 2 1+(-1485944169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((905980961/2500000000 : ℝ)*X 0 0+(34110881/78125000 : ℝ)*X 0 1+(545773947/1250000000 : ℝ)*X 0 2+(905980961/2500000000 : ℝ)*X 1 0+(34110881/78125000 : ℝ)*X 1 1+(545773947/1250000000 : ℝ)*X 1 2+(905980961/2500000000 : ℝ)*X 2 0+(34110881/78125000 : ℝ)*X 2 1+(545773947/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1709_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66737/100000 : ℝ) ≤ (-23680865843273577000028150119/35485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1134511/25000000000000 : ℝ)*(upper1) + (41443431/100000000000000 : ℝ)*(upper3) + (5353241/25000000000000 : ℝ)*(lower4) + (40860651/100000000000000 : ℝ)*(lower5) + (169264258572269/12500000000000 : ℝ)*(major0) + (169264258572269/12500000000000 : ℝ)*(major1) + (169264258572269/12500000000000 : ℝ)*(major2) + (1806602329/100000000000000 : ℝ)*(sp1) + (137032271/100000000000000 : ℝ)*(sp2) + (43210111/12500000000000 : ℝ)*(sp3) + (101736944214647/5000000000000 : ℝ)*(sp4) + (2034737077690611/100000000000000 : ℝ)*(sp5) + (203473874726067/10000000000000 : ℝ)*(sp6) + (21741683163789/3125000000000 : ℝ)*(sp7) + (695734206922137/100000000000000 : ℝ)*(f.failure) + (101736944214647/5000000000000 : ℝ)*(f.sum) + (20890502302727/4435625000000000000000000000 : ℝ)*base65 + (21201967684874713/3775000000000000000000000000000 : ℝ)*base67 + (13255656521925287/3775000000000000000000000000000 : ℝ)*base70 + (7092347175699713/3775000000000000000000000000000 : ℝ)*base71 + (15705007451921/2217812500000000000000000000 : ℝ)*base73 + (3429221437349713/3775000000000000000000000000000 : ℝ)*base75 + (16765538634325287/3775000000000000000000000000000 : ℝ)*base78 + (17036940673825287/3775000000000000000000000000000 : ℝ)*base80 + (133493944030621/35485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (36325801/5000000000000000000000 : ℝ)*base89 + (36325801/5000000000000000000000 : ℝ)*base91 + (36325801/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58379/100000 : ℝ) ≤ (414334099333441581802730475439143/709700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4138633/100000000000000 : ℝ)*(upper2) + (2635321/20000000000000 : ℝ)*(lower4) + (4507547/50000000000000 : ℝ)*(lower5) + (1458634757126977/100000000000000 : ℝ)*(major0) + (1458634757126977/100000000000000 : ℝ)*(major1) + (729317378563489/50000000000000 : ℝ)*(major2) + (2148370945326317/100000000000000 : ℝ)*(sp0) + (1074186270508639/50000000000000 : ℝ)*(sp1) + (2148370655438021/100000000000000 : ℝ)*(sp2) + (374717978781931/50000000000000 : ℝ)*(sp3) + (1067671493/50000000000000 : ℝ)*(sp6) + (238017789/100000000000000 : ℝ)*(sp7) + (15610233/6250000000000 : ℝ)*(sp9) + (184545469/10000000000000 : ℝ)*(sp12) + (749436195581651/100000000000000 : ℝ)*(f.failure) + (2148372790781007/100000000000000 : ℝ)*(f.sum) + (35432661664879/7097000000000000000000000000 : ℝ)*base65 + (7916878515211400237/1419400000000000000000000000000000 : ℝ)*base68 + (5704984746366156691/709700000000000000000000000000000 : ℝ)*base69 + (10535417243190199763/1419400000000000000000000000000000 : ℝ)*base71 + (8832304991733/1774250000000000000000000000 : ℝ)*base74 + (8963387956049356691/709700000000000000000000000000000 : ℝ)*base75 + (147243421151692771/30200000000000000000000000000000 : ℝ)*base78 + (93438307676892771/30200000000000000000000000000000 : ℝ)*base80 + (2784662019071/8871250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (27185923/5000000000000000000000 : ℝ)*base89 + (27185923/5000000000000000000000 : ℝ)*base91 + (22814077/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81449/100000 : ℝ) ≤ (28903100128214902808745400661451/35485000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1589483/20000000000000 : ℝ)*(upper0) + (37845033/50000000000000 : ℝ)*(lower1) + (10502569/5000000000000 : ℝ)*(lower3) + (17165499/50000000000000 : ℝ)*(upper4) + (73981522360719/5000000000000 : ℝ)*(major0) + (73981522360719/5000000000000 : ℝ)*(major1) + (73981522360719/5000000000000 : ℝ)*(major2) + (4885206671/100000000000000 : ℝ)*(sp0) + (63345092403/100000000000000 : ℝ)*(sp1) + (13368294117/50000000000000 : ℝ)*(sp3) + (54297046093413/2500000000000 : ℝ)*(sp8) + (542955845962697/25000000000000 : ℝ)*(sp9) + (2171886728943191/100000000000000 : ℝ)*(sp10) + (380098447843893/50000000000000 : ℝ)*(sp11) + (38011181613801/5000000000000 : ℝ)*(f.failure) + (2171886728943191/100000000000000 : ℝ)*(f.sum) + (12626100086883/7097000000000000000000000000 : ℝ)*base66 + (16032166427305363/1510000000000000000000000000000 : ℝ)*base67 + (4899585253165363/1510000000000000000000000000000 : ℝ)*base69 + (16225682630565363/1510000000000000000000000000000 : ℝ)*base71 + (3997649144731/7097000000000000000000000000 : ℝ)*base73 + (21008891732535363/1510000000000000000000000000000 : ℝ)*base75 + (8369697421955363/1510000000000000000000000000000 : ℝ)*base77 + (3969030120895363/1510000000000000000000000000000 : ℝ)*base79 + (16441309505491/7097000000000000000000000000 : ℝ)*base81 + (2357127/250000000000000000000 : ℝ)*base90 + (2357127/250000000000000000000 : ℝ)*base92 + (2357127/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-90409/100000 : ℝ) ≤ (-80201758535279442098391539811081/88712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60410099/100000000000000 : ℝ)*(upper1) + (187338547/100000000000000 : ℝ)*(upper3) + (3881587/3125000000000 : ℝ)*(lower4) + (382191078112933/25000000000000 : ℝ)*(major0) + (382191078112933/25000000000000 : ℝ)*(major1) + (382191078112933/25000000000000 : ℝ)*(major2) + (5126088491/100000000000000 : ℝ)*(sp4) + (85489759867/100000000000000 : ℝ)*(sp5) + (20750480233/25000000000000 : ℝ)*(sp6) + (32956134617/100000000000000 : ℝ)*(sp7) + (1151095347236463/50000000000000 : ℝ)*(sp12) + (46042206616031/2000000000000 : ℝ)*(sp13) + (460422563728097/20000000000000 : ℝ)*(sp14) + (157087061542121/20000000000000 : ℝ)*(sp15) + (392734131922611/50000000000000 : ℝ)*(f.failure) + (2302195820561417/100000000000000 : ℝ)*(f.sum) + (13350168387777/17742500000000000000000000000 : ℝ)*base66 + (44373279001465841/7550000000000000000000000000000 : ℝ)*base67 + (53509372727684159/7550000000000000000000000000000 : ℝ)*base70 + (22228807333715841/7550000000000000000000000000000 : ℝ)*base71 + (15736591220849/35485000000000000000000000000 : ℝ)*base74 + (47420826860115841/7550000000000000000000000000000 : ℝ)*base75 + (20024512414115841/7550000000000000000000000000000 : ℝ)*base77 + (49758745296165841/7550000000000000000000000000000 : ℝ)*base79 + (164218774354617/17742500000000000000000000000 : ℝ)*base82 + (11139997/2500000000000000000000 : ℝ)*base90 + (11139997/2500000000000000000000 : ℝ)*base92 + (11139997/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1709_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (171/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10003/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58379/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90409/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1709_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1709_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58379/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90409/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1709_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1709_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1709_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5287/1024 : ℝ) ≤ p) (hpb : p ≤ (5295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (97315473/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2139/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58379/100000 : ℝ) else (81449/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90409/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1709_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

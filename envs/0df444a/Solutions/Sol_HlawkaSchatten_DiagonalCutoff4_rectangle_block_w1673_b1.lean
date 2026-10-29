-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1673_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:16.796987+00:00
-- url     : https://prove2.me/submissions/4f760fa0-3ab3-49e5-9af1-f860ea04a880

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
theorem support_rectangle_w1673_s3_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-778829083/5000000000 : ℝ)*x 0 + (5440860331/10000000000 : ℝ)*x 1 + (5185177119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778829083/5000000000 : ℝ)^5011 ≤ (9662087682997/100000000000000 : ℝ)^3987 := by
    have hnat : (778829083 : ℕ)^5011*100000000000000^3987 ≤ 9662087682997^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778829083 5000000000 9662087682997 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440860331/10000000000 : ℝ)^5011 ≤ (23267399143539/50000000000000 : ℝ)^3987 := by
    have hnat : (5440860331 : ℕ)^5011*50000000000000^3987 ≤ 23267399143539^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440860331 10000000000 23267399143539 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185177119/10000000000 : ℝ)^5011 ≤ (5475389250441/12500000000000 : ℝ)^3987 := by
    have hnat : (5185177119 : ℕ)^5011*12500000000000^3987 ≤ 5475389250441^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185177119 10000000000 5475389250441 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-778829083/5000000000 : ℝ), (5440860331/10000000000 : ℝ), (5185177119/10000000000 : ℝ)] ![(9662087682997/100000000000000 : ℝ), (23267399143539/50000000000000 : ℝ), (5475389250441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-778829083/5000000000 : ℝ)|^5011 ≤ (9662087682997/100000000000000 : ℝ)^3987
        have hw : |(-778829083/5000000000 : ℝ)|=(778829083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440860331/10000000000 : ℝ)|^5011 ≤ (23267399143539/50000000000000 : ℝ)^3987
        have hw : |(5440860331/10000000000 : ℝ)|=(5440860331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185177119/10000000000 : ℝ)|^5011 ≤ (5475389250441/12500000000000 : ℝ)^3987
        have hw : |(5185177119/10000000000 : ℝ)|=(5185177119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344249787/10000000000 : ℝ)*x 0 + (-844582897/5000000000 : ℝ)*x 1 + (5185177119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344249787/10000000000 : ℝ)^5011 ≤ (2274933071079/5000000000000 : ℝ)^3987 := by
    have hnat : (5344249787 : ℕ)^5011*5000000000000^3987 ≤ 2274933071079^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344249787 10000000000 2274933071079 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844582897/5000000000 : ℝ)^5011 ≤ (2139644911999/20000000000000 : ℝ)^3987 := by
    have hnat : (844582897 : ℕ)^5011*20000000000000^3987 ≤ 2139644911999^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844582897 5000000000 2139644911999 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185177119/10000000000 : ℝ)^5011 ≤ (5475389250441/12500000000000 : ℝ)^3987 := by
    have hnat : (5185177119 : ℕ)^5011*12500000000000^3987 ≤ 5475389250441^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185177119 10000000000 5475389250441 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344249787/10000000000 : ℝ), (-844582897/5000000000 : ℝ), (5185177119/10000000000 : ℝ)] ![(2274933071079/5000000000000 : ℝ), (2139644911999/20000000000000 : ℝ), (5475389250441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344249787/10000000000 : ℝ)|^5011 ≤ (2274933071079/5000000000000 : ℝ)^3987
        have hw : |(5344249787/10000000000 : ℝ)|=(5344249787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844582897/5000000000 : ℝ)|^5011 ≤ (2139644911999/20000000000000 : ℝ)^3987
        have hw : |(-844582897/5000000000 : ℝ)|=(844582897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185177119/10000000000 : ℝ)|^5011 ≤ (5475389250441/12500000000000 : ℝ)^3987
        have hw : |(5185177119/10000000000 : ℝ)|=(5185177119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336062447/2500000000 : ℝ)*x 0 + (32407357/62500000 : ℝ)*x 1 + (-52786431/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336062447/2500000000 : ℝ)^5011 ≤ (1137466535807/2500000000000 : ℝ)^3987 := by
    have hnat : (1336062447 : ℕ)^5011*2500000000000^3987 ≤ 1137466535807^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336062447 2500000000 1137466535807 2500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32407357/62500000 : ℝ)^5011 ≤ (8760622802829/20000000000000 : ℝ)^3987 := by
    have hnat : (32407357 : ℕ)^5011*20000000000000^3987 ≤ 8760622802829^3987*62500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32407357 62500000 8760622802829 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52786431/312500000 : ℝ)^5011 ≤ (5349112272037/50000000000000 : ℝ)^3987 := by
    have hnat : (52786431 : ℕ)^5011*50000000000000^3987 ≤ 5349112272037^3987*312500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52786431 312500000 5349112272037 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336062447/2500000000 : ℝ), (32407357/62500000 : ℝ), (-52786431/312500000 : ℝ)] ![(1137466535807/2500000000000 : ℝ), (8760622802829/20000000000000 : ℝ), (5349112272037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336062447/2500000000 : ℝ)|^5011 ≤ (1137466535807/2500000000000 : ℝ)^3987
        have hw : |(1336062447/2500000000 : ℝ)|=(1336062447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32407357/62500000 : ℝ)|^5011 ≤ (8760622802829/20000000000000 : ℝ)^3987
        have hw : |(32407357/62500000 : ℝ)|=(32407357/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52786431/312500000 : ℝ)|^5011 ≤ (5349112272037/50000000000000 : ℝ)^3987
        have hw : |(-52786431/312500000 : ℝ)|=(52786431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520430529/1250000000 : ℝ)*x 0 + (1916421933/5000000000 : ℝ)*x 1 + (4513565149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520430529/1250000000 : ℝ)^5011 ≤ (4155516600759/12500000000000 : ℝ)^3987 := by
    have hnat : (520430529 : ℕ)^5011*12500000000000^3987 ≤ 4155516600759^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520430529 1250000000 4155516600759 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916421933/5000000000 : ℝ)^5011 ≤ (2996090288389/10000000000000 : ℝ)^3987 := by
    have hnat : (1916421933 : ℕ)^5011*10000000000000^3987 ≤ 2996090288389^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916421933 5000000000 2996090288389 10000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513565149/10000000000 : ℝ)^5011 ≤ (4599370536581/12500000000000 : ℝ)^3987 := by
    have hnat : (4513565149 : ℕ)^5011*12500000000000^3987 ≤ 4599370536581^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513565149 10000000000 4599370536581 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520430529/1250000000 : ℝ), (1916421933/5000000000 : ℝ), (4513565149/10000000000 : ℝ)] ![(4155516600759/12500000000000 : ℝ), (2996090288389/10000000000000 : ℝ), (4599370536581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520430529/1250000000 : ℝ)|^5011 ≤ (4155516600759/12500000000000 : ℝ)^3987
        have hw : |(520430529/1250000000 : ℝ)|=(520430529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1916421933/5000000000 : ℝ)|^5011 ≤ (2996090288389/10000000000000 : ℝ)^3987
        have hw : |(1916421933/5000000000 : ℝ)|=(1916421933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513565149/10000000000 : ℝ)|^5011 ≤ (4599370536581/12500000000000 : ℝ)^3987
        have hw : |(4513565149/10000000000 : ℝ)|=(4513565149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-194714927/1250000000 : ℝ)*x 0 + (5187131541/10000000000 : ℝ)*x 1 + (1087777063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194714927/1250000000 : ℝ)^5011 ≤ (2415641299019/25000000000000 : ℝ)^3987 := by
    have hnat : (194714927 : ℕ)^5011*25000000000000^3987 ≤ 2415641299019^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194714927 1250000000 2415641299019 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187131541/10000000000 : ℝ)^5011 ≤ (8764773190767/20000000000000 : ℝ)^3987 := by
    have hnat : (5187131541 : ℕ)^5011*20000000000000^3987 ≤ 8764773190767^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187131541 10000000000 8764773190767 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087777063/2000000000 : ℝ)^5011 ≤ (11628392208613/25000000000000 : ℝ)^3987 := by
    have hnat : (1087777063 : ℕ)^5011*25000000000000^3987 ≤ 11628392208613^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087777063 2000000000 11628392208613 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194714927/1250000000 : ℝ), (5187131541/10000000000 : ℝ), (1087777063/2000000000 : ℝ)] ![(2415641299019/25000000000000 : ℝ), (8764773190767/20000000000000 : ℝ), (11628392208613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194714927/1250000000 : ℝ)|^5011 ≤ (2415641299019/25000000000000 : ℝ)^3987
        have hw : |(-194714927/1250000000 : ℝ)|=(194714927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187131541/10000000000 : ℝ)|^5011 ≤ (8764773190767/20000000000000 : ℝ)^3987
        have hw : |(5187131541/10000000000 : ℝ)|=(5187131541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087777063/2000000000 : ℝ)|^5011 ≤ (11628392208613/25000000000000 : ℝ)^3987
        have hw : |(1087777063/2000000000 : ℝ)|=(1087777063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637890277/5000000000 : ℝ)*x 0 + (-1435457603/10000000000 : ℝ)*x 1 + (5438885317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637890277/5000000000 : ℝ)^5011 ≤ (22383619638749/50000000000000 : ℝ)^3987 := by
    have hnat : (2637890277 : ℕ)^5011*50000000000000^3987 ≤ 22383619638749^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637890277 5000000000 22383619638749 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435457603/10000000000 : ℝ)^5011 ≤ (8719191850531/100000000000000 : ℝ)^3987 := by
    have hnat : (1435457603 : ℕ)^5011*100000000000000^3987 ≤ 8719191850531^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435457603 10000000000 8719191850531 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438885317/10000000000 : ℝ)^5011 ≤ (46513568855949/100000000000000 : ℝ)^3987 := by
    have hnat : (5438885317 : ℕ)^5011*100000000000000^3987 ≤ 46513568855949^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438885317 10000000000 46513568855949 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637890277/5000000000 : ℝ), (-1435457603/10000000000 : ℝ), (5438885317/10000000000 : ℝ)] ![(22383619638749/50000000000000 : ℝ), (8719191850531/100000000000000 : ℝ), (46513568855949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637890277/5000000000 : ℝ)|^5011 ≤ (22383619638749/50000000000000 : ℝ)^3987
        have hw : |(2637890277/5000000000 : ℝ)|=(2637890277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1435457603/10000000000 : ℝ)|^5011 ≤ (8719191850531/100000000000000 : ℝ)^3987
        have hw : |(-1435457603/10000000000 : ℝ)|=(1435457603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438885317/10000000000 : ℝ)|^5011 ≤ (46513568855949/100000000000000 : ℝ)^3987
        have hw : |(5438885317/10000000000 : ℝ)|=(5438885317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275780553/10000000000 : ℝ)*x 0 + (2719442659/5000000000 : ℝ)*x 1 + (-1435457603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275780553/10000000000 : ℝ)^5011 ≤ (44767239266833/100000000000000 : ℝ)^3987 := by
    have hnat : (5275780553 : ℕ)^5011*100000000000000^3987 ≤ 44767239266833^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275780553 10000000000 44767239266833 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719442659/5000000000 : ℝ)^5011 ≤ (23256784433349/50000000000000 : ℝ)^3987 := by
    have hnat : (2719442659 : ℕ)^5011*50000000000000^3987 ≤ 23256784433349^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719442659 5000000000 23256784433349 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1435457603/10000000000 : ℝ)^5011 ≤ (8719191850531/100000000000000 : ℝ)^3987 := by
    have hnat : (1435457603 : ℕ)^5011*100000000000000^3987 ≤ 8719191850531^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435457603 10000000000 8719191850531 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275780553/10000000000 : ℝ), (2719442659/5000000000 : ℝ), (-1435457603/10000000000 : ℝ)] ![(44767239266833/100000000000000 : ℝ), (23256784433349/50000000000000 : ℝ), (8719191850531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275780553/10000000000 : ℝ)|^5011 ≤ (44767239266833/100000000000000 : ℝ)^3987
        have hw : |(5275780553/10000000000 : ℝ)|=(5275780553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719442659/5000000000 : ℝ)|^5011 ≤ (23256784433349/50000000000000 : ℝ)^3987
        have hw : |(2719442659/5000000000 : ℝ)|=(2719442659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1435457603/10000000000 : ℝ)|^5011 ≤ (8719191850531/100000000000000 : ℝ)^3987
        have hw : |(-1435457603/10000000000 : ℝ)|=(1435457603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s3_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16264091/39062500 : ℝ)*x 0 + (4508361771/10000000000 : ℝ)*x 1 + (959525519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16264091/39062500 : ℝ)^5011 ≤ (16622884624191/50000000000000 : ℝ)^3987 := by
    have hnat : (16264091 : ℕ)^5011*50000000000000^3987 ≤ 16622884624191^3987*39062500^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16264091 39062500 16622884624191 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508361771/10000000000 : ℝ)^5011 ≤ (7348331859793/20000000000000 : ℝ)^3987 := by
    have hnat : (4508361771 : ℕ)^5011*20000000000000^3987 ≤ 7348331859793^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508361771 10000000000 7348331859793 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959525519/2500000000 : ℝ)^5011 ≤ (1500628572093/5000000000000 : ℝ)^3987 := by
    have hnat : (959525519 : ℕ)^5011*5000000000000^3987 ≤ 1500628572093^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959525519 2500000000 1500628572093 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16264091/39062500 : ℝ), (4508361771/10000000000 : ℝ), (959525519/2500000000 : ℝ)] ![(16622884624191/50000000000000 : ℝ), (7348331859793/20000000000000 : ℝ), (1500628572093/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16264091/39062500 : ℝ)|^5011 ≤ (16622884624191/50000000000000 : ℝ)^3987
        have hw : |(16264091/39062500 : ℝ)|=(16264091/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508361771/10000000000 : ℝ)|^5011 ≤ (7348331859793/20000000000000 : ℝ)^3987
        have hw : |(4508361771/10000000000 : ℝ)|=(4508361771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959525519/2500000000 : ℝ)|^5011 ≤ (1500628572093/5000000000000 : ℝ)^3987
        have hw : |(959525519/2500000000 : ℝ)|=(959525519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (539/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (507/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8137/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8137/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8137/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8137/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8137/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8137/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (671/6250 : ℝ) ^ (5007/1024 : ℝ) ≤ (1824570119440153/100000000000000000000 : ℝ) := by
    have hpowers : (671/6250 : ℝ)^5007 ≤ (1824570119440153/100000000000000000000 : ℝ)^1024 := by
      have hnat : (671 : ℕ)^5007*100000000000000000000^1024 ≤ 1824570119440153^1024*6250^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        671 6250 1824570119440153 100000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (671/6250 : ℝ)) (X := (1824570119440153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8137/50000 : ℝ) ^ (5007/1024 : ℝ) ≤ (3486778839783737/25000000000000000000 : ℝ) := by
    have hpowers : (8137/50000 : ℝ)^5007 ≤ (3486778839783737/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8137 : ℕ)^5007*25000000000000000000^1024 ≤ 3486778839783737^1024*50000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8137 50000 3486778839783737 25000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8137/50000 : ℝ)) (X := (3486778839783737/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001824570119440153/50000000000000000000 : ℝ) ≤ (1250009328603381/1250000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (50001824570119440153/50000000000000000000 : ℝ)^1024 ≤ (1250009328603381/1250000000000000 : ℝ)^5007 := by
      have hnat : (50001824570119440153 : ℕ)^1024*1250000000000000^5007 ≤ 1250009328603381^5007*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001824570119440153 50000000000000000000 1250009328603381 1250000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009328603381/1250000000000000 : ℝ)) (X := (50001824570119440153/50000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015771685478575101/100000000000000000000 : ℝ) ≤ (10000322532312969/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (100015771685478575101/100000000000000000000 : ℝ)^1024 ≤ (10000322532312969/10000000000000000 : ℝ)^5007 := by
      have hnat : (100015771685478575101 : ℕ)^1024*10000000000000000^5007 ≤ 10000322532312969^5007*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015771685478575101 100000000000000000000 10000322532312969 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000322532312969/10000000000000000 : ℝ)) (X := (100015771685478575101/100000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503486778839783737/12500000000000000000 : ℝ) ≤ (1000057043579889/1000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (12503486778839783737/12500000000000000000 : ℝ)^1024 ≤ (1000057043579889/1000000000000000 : ℝ)^5007 := by
      have hnat : (12503486778839783737 : ℕ)^1024*1000000000000000^5007 ≤ 1000057043579889^5007*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503486778839783737 12500000000000000000 1000057043579889 1000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000057043579889/1000000000000000 : ℝ)) (X := (12503486778839783737/12500000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1824570119440153/100000000000000000000 : ℝ) ≤ ((88742131908324513/88750000000000000 : ℝ)+2*(6356499639/14200000000000 : ℝ)*(671/6250 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (88742131908324513/88750000000000000 : ℝ)+2*(6356499639/14200000000000 : ℝ)*(671/6250 : ℝ)=(1250009328603381/1250000000000000 : ℝ) by norm_num, show 1+2*(1824570119440153/100000000000000000000 : ℝ)=(50001824570119440153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3486778839783737/25000000000000000000 : ℝ)+(1824570119440153/100000000000000000000 : ℝ) ≤ ((88742131908324513/88750000000000000 : ℝ)+(6356499639/14200000000000 : ℝ)*((8137/50000 : ℝ)+(671/6250 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (88742131908324513/88750000000000000 : ℝ)+(6356499639/14200000000000 : ℝ)*((8137/50000 : ℝ)+(671/6250 : ℝ))=(10000322532312969/10000000000000000 : ℝ) by norm_num, show 1+(3486778839783737/25000000000000000000 : ℝ)+(1824570119440153/100000000000000000000 : ℝ)=(100015771685478575101/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3486778839783737/25000000000000000000 : ℝ) ≤ ((88742131908324513/88750000000000000 : ℝ)+2*(6356499639/14200000000000 : ℝ)*(8137/50000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (88742131908324513/88750000000000000 : ℝ)+2*(6356499639/14200000000000 : ℝ)*(8137/50000 : ℝ)=(1000057043579889/1000000000000000 : ℝ) by norm_num, show 1+2*(3486778839783737/25000000000000000000 : ℝ)=(12503486778839783737/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88742131908324513/88750000000000000 : ℝ)*(X 1 0+X 2 0)+(6356499639/14200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (88742131908324513/88750000000000000 : ℝ)) (alpha := (6356499639/14200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88742131908324513/88750000000000000 : ℝ)*(X 0 1+X 2 1)+(6356499639/14200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (88742131908324513/88750000000000000 : ℝ)) (alpha := (6356499639/14200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88742131908324513/88750000000000000 : ℝ)*(X 0 2+X 1 2)+(6356499639/14200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (8137/50000 : ℝ)) (c := (88742131908324513/88750000000000000 : ℝ)) (alpha := (6356499639/14200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-778829083/5000000000 : ℝ)*X 0 0+(5440860331/10000000000 : ℝ)*X 0 1+(5185177119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344249787/10000000000 : ℝ)*X 1 0+(-844582897/5000000000 : ℝ)*X 1 1+(5185177119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336062447/2500000000 : ℝ)*X 2 0+(32407357/62500000 : ℝ)*X 2 1+(-52786431/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((520430529/1250000000 : ℝ)*X 0 0+(1916421933/5000000000 : ℝ)*X 0 1+(4513565149/10000000000 : ℝ)*X 0 2+(520430529/1250000000 : ℝ)*X 1 0+(1916421933/5000000000 : ℝ)*X 1 1+(4513565149/10000000000 : ℝ)*X 1 2+(520430529/1250000000 : ℝ)*X 2 0+(1916421933/5000000000 : ℝ)*X 2 1+(4513565149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-194714927/1250000000 : ℝ)*X 0 0+(5187131541/10000000000 : ℝ)*X 0 1+(1087777063/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637890277/5000000000 : ℝ)*X 1 0+(-1435457603/10000000000 : ℝ)*X 1 1+(5438885317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275780553/10000000000 : ℝ)*X 2 0+(2719442659/5000000000 : ℝ)*X 2 1+(-1435457603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16264091/39062500 : ℝ)*X 0 0+(4508361771/10000000000 : ℝ)*X 0 1+(959525519/2500000000 : ℝ)*X 0 2+(16264091/39062500 : ℝ)*X 1 0+(4508361771/10000000000 : ℝ)*X 1 1+(959525519/2500000000 : ℝ)*X 1 2+(16264091/39062500 : ℝ)*X 2 0+(4508361771/10000000000 : ℝ)*X 2 1+(959525519/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11586783841290102272248173/1109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1619418509/100000000000000 : ℝ)*(base19) + (759212713/50000000000000 : ℝ)*(base23) + (54364339/100000000000000 : ℝ)*(lower2) + (63267903/25000000000000 : ℝ)*(upper3) + (182990761/100000000000000 : ℝ)*(upper5) + (336261133474991/12500000000000 : ℝ)*(major0) + (336261133474991/12500000000000 : ℝ)*(major1) + (336261133474991/12500000000000 : ℝ)*(major2) + (31288888670029/800000000000 : ℝ)*(sp0) + (1955565111211789/50000000000000 : ℝ)*(sp1) + (195556516170833/5000000000000 : ℝ)*(sp2) + (1469037522902127/100000000000000 : ℝ)*(sp3) + (20758088461/100000000000000 : ℝ)*(sp4) + (4211354069/50000000000000 : ℝ)*(sp7) + (183630743201283/12500000000000 : ℝ)*(f.failure) + (1955565920921043/50000000000000 : ℝ)*(f.sum) + (46622429483/177500000000000000000000000 : ℝ)*base65 + (317533525314367/1109375000000000000000000000000 : ℝ)*base68 + (3441368196211871/554687500000000000000000000000 : ℝ)*base70 + (3031180873404383/1109375000000000000000000000000 : ℝ)*base71 + (380320116511/88750000000000000000000000 : ℝ)*base74 + (3654676154274371/554687500000000000000000000000 : ℝ)*base76 + (6037154251935633/1109375000000000000000000000000 : ℝ)*base77 + (13516456737876867/1109375000000000000000000000000 : ℝ)*base80 + (1956782837309/355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9873851/1250000000000000000000 : ℝ)*base90 + (9873851/1250000000000000000000 : ℝ)*base92 + (9873851/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126962437992157981642053/17333984375000000000000000000 : ℝ) := by norm_num
    linear_combination (1049504851/100000000000000 : ℝ)*(base19) + (70717547/6250000000000 : ℝ)*(base23) + (76839581/50000000000000 : ℝ)*(upper3) + (37311361/100000000000000 : ℝ)*(lower4) + (76006211/50000000000000 : ℝ)*(upper5) + (683011696750989/25000000000000 : ℝ)*(major0) + (683011696750989/25000000000000 : ℝ)*(major1) + (683011696750989/25000000000000 : ℝ)*(major2) + (3210444769/25000000000000 : ℝ)*(sp1) + (3441736101/25000000000000 : ℝ)*(sp2) + (3972134456188931/100000000000000 : ℝ)*(sp4) + (794424112981001/20000000000000 : ℝ)*(sp5) + (1986059778881887/50000000000000 : ℝ)*(sp6) + (149195887366961/10000000000000 : ℝ)*(sp7) + (149195887366961/10000000000000 : ℝ)*(f.failure) + (3972134456188931/100000000000000 : ℝ)*(f.sum) + (842850628889/177500000000000000000000000 : ℝ)*base66 + (14890426861081643/2218750000000000000000000000000 : ℝ)*base68 + (2803800977456643/2218750000000000000000000000000 : ℝ)*base70 + (27592664468300393/2218750000000000000000000000000 : ℝ)*base72 + (721958553337/355000000000000000000000000 : ℝ)*base73 + (28632326003831643/2218750000000000000000000000000 : ℝ)*base76 + (4676402256800393/2218750000000000000000000000000 : ℝ)*base78 + (1509388457324607/2218750000000000000000000000000 : ℝ)*base79 + (57880322977/88750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3194983/1000000000000000000000 : ℝ)*base89 + (3194983/1000000000000000000000 : ℝ)*base91 + (3194983/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1673_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (507/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1673_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1673_s4_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1557684977/10000000000 : ℝ)*x 0 + (340045447/625000000 : ℝ)*x 1 + (1296323067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557684977/10000000000 : ℝ)^5011 ≤ (603893544031/6250000000000 : ℝ)^3987 := by
    have hnat : (1557684977 : ℕ)^5011*6250000000000^3987 ≤ 603893544031^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557684977 10000000000 603893544031 6250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340045447/625000000 : ℝ)^5011 ≤ (23266683341693/50000000000000 : ℝ)^3987 := by
    have hnat : (340045447 : ℕ)^5011*50000000000000^3987 ≤ 23266683341693^3987*625000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340045447 625000000 23266683341693 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296323067/2500000000 : ℝ)^5011 ≤ (21902168296943/50000000000000 : ℝ)^3987 := by
    have hnat : (1296323067 : ℕ)^5011*50000000000000^3987 ≤ 21902168296943^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296323067 2500000000 21902168296943 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1557684977/10000000000 : ℝ), (340045447/625000000 : ℝ), (1296323067/2500000000 : ℝ)] ![(603893544031/6250000000000 : ℝ), (23266683341693/50000000000000 : ℝ), (21902168296943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1557684977/10000000000 : ℝ)|^5011 ≤ (603893544031/6250000000000 : ℝ)^3987
        have hw : |(-1557684977/10000000000 : ℝ)|=(1557684977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340045447/625000000 : ℝ)|^5011 ≤ (23266683341693/50000000000000 : ℝ)^3987
        have hw : |(340045447/625000000 : ℝ)|=(340045447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296323067/2500000000 : ℝ)|^5011 ≤ (21902168296943/50000000000000 : ℝ)^3987
        have hw : |(1296323067/2500000000 : ℝ)|=(1296323067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334013333/625000000 : ℝ)*x 0 + (-844530701/5000000000 : ℝ)*x 1 + (2592646063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334013333/625000000 : ℝ)^5011 ≤ (22749135652499/50000000000000 : ℝ)^3987 := by
    have hnat : (334013333 : ℕ)^5011*50000000000000^3987 ≤ 22749135652499^3987*625000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334013333 625000000 22749135652499 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844530701/5000000000 : ℝ)^5011 ≤ (10697393597601/100000000000000 : ℝ)^3987 := by
    have hnat : (844530701 : ℕ)^5011*100000000000000^3987 ≤ 10697393597601^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844530701 5000000000 10697393597601 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592646063/5000000000 : ℝ)^5011 ≤ (21902167543101/50000000000000 : ℝ)^3987 := by
    have hnat : (2592646063 : ℕ)^5011*50000000000000^3987 ≤ 21902167543101^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592646063 5000000000 21902167543101 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334013333/625000000 : ℝ), (-844530701/5000000000 : ℝ), (2592646063/5000000000 : ℝ)] ![(22749135652499/50000000000000 : ℝ), (10697393597601/100000000000000 : ℝ), (21902167543101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334013333/625000000 : ℝ)|^5011 ≤ (22749135652499/50000000000000 : ℝ)^3987
        have hw : |(334013333/625000000 : ℝ)|=(334013333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844530701/5000000000 : ℝ)|^5011 ≤ (10697393597601/100000000000000 : ℝ)^3987
        have hw : |(-844530701/5000000000 : ℝ)|=(844530701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592646063/5000000000 : ℝ)|^5011 ≤ (21902167543101/50000000000000 : ℝ)^3987
        have hw : |(2592646063/5000000000 : ℝ)|=(2592646063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344213189/10000000000 : ℝ)*x 0 + (1296323053/2500000000 : ℝ)*x 1 + (-67562459/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344213189/10000000000 : ℝ)^5011 ≤ (45498269817679/100000000000000 : ℝ)^3987 := by
    have hnat : (5344213189 : ℕ)^5011*100000000000000^3987 ≤ 45498269817679^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344213189 10000000000 45498269817679 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296323053/2500000000 : ℝ)^5011 ≤ (21902167999653/50000000000000 : ℝ)^3987 := by
    have hnat : (1296323053 : ℕ)^5011*50000000000000^3987 ≤ 21902167999653^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296323053 2500000000 21902167999653 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67562459/400000000 : ℝ)^5011 ≤ (10697394178677/100000000000000 : ℝ)^3987 := by
    have hnat : (67562459 : ℕ)^5011*100000000000000^3987 ≤ 10697394178677^3987*400000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67562459 400000000 10697394178677 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344213189/10000000000 : ℝ), (1296323053/2500000000 : ℝ), (-67562459/400000000 : ℝ)] ![(45498269817679/100000000000000 : ℝ), (21902167999653/50000000000000 : ℝ), (10697394178677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344213189/10000000000 : ℝ)|^5011 ≤ (45498269817679/100000000000000 : ℝ)^3987
        have hw : |(5344213189/10000000000 : ℝ)|=(5344213189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296323053/2500000000 : ℝ)|^5011 ≤ (21902167999653/50000000000000 : ℝ)^3987
        have hw : |(1296323053/2500000000 : ℝ)|=(1296323053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67562459/400000000 : ℝ)|^5011 ≤ (10697394178677/100000000000000 : ℝ)^3987
        have hw : |(-67562459/400000000 : ℝ)|=(67562459/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416346149/1000000000 : ℝ)*x 0 + (766634479/2000000000 : ℝ)*x 1 + (2256616609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416346149/1000000000 : ℝ)^5011 ≤ (6648861199877/20000000000000 : ℝ)^3987 := by
    have hnat : (416346149 : ℕ)^5011*20000000000000^3987 ≤ 6648861199877^3987*1000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416346149 1000000000 6648861199877 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (766634479/2000000000 : ℝ)^5011 ≤ (29964130563567/100000000000000 : ℝ)^3987 := by
    have hnat : (766634479 : ℕ)^5011*100000000000000^3987 ≤ 29964130563567^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766634479 2000000000 29964130563567 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256616609/5000000000 : ℝ)^5011 ≤ (36791563418583/100000000000000 : ℝ)^3987 := by
    have hnat : (2256616609 : ℕ)^5011*100000000000000^3987 ≤ 36791563418583^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256616609 5000000000 36791563418583 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416346149/1000000000 : ℝ), (766634479/2000000000 : ℝ), (2256616609/5000000000 : ℝ)] ![(6648861199877/20000000000000 : ℝ), (29964130563567/100000000000000 : ℝ), (36791563418583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416346149/1000000000 : ℝ)|^5011 ≤ (6648861199877/20000000000000 : ℝ)^3987
        have hw : |(416346149/1000000000 : ℝ)|=(416346149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(766634479/2000000000 : ℝ)|^5011 ≤ (29964130563567/100000000000000 : ℝ)^3987
        have hw : |(766634479/2000000000 : ℝ)|=(766634479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256616609/5000000000 : ℝ)|^5011 ≤ (36791563418583/100000000000000 : ℝ)^3987
        have hw : |(2256616609/5000000000 : ℝ)|=(2256616609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-778873027/5000000000 : ℝ)*x 0 + (5187242829/10000000000 : ℝ)*x 1 + (5438756051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778873027/5000000000 : ℝ)^5011 ≤ (9662772870943/100000000000000 : ℝ)^3987 := by
    have hnat : (778873027 : ℕ)^5011*100000000000000^3987 ≤ 9662772870943^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778873027 5000000000 9662772870943 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187242829/10000000000 : ℝ)^5011 ≤ (21912523832211/50000000000000 : ℝ)^3987 := by
    have hnat : (5187242829 : ℕ)^5011*50000000000000^3987 ≤ 21912523832211^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187242829 10000000000 21912523832211 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438756051/10000000000 : ℝ)^5011 ≤ (11628044861093/25000000000000 : ℝ)^3987 := by
    have hnat : (5438756051 : ℕ)^5011*25000000000000^3987 ≤ 11628044861093^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438756051 10000000000 11628044861093 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-778873027/5000000000 : ℝ), (5187242829/10000000000 : ℝ), (5438756051/10000000000 : ℝ)] ![(9662772870943/100000000000000 : ℝ), (21912523832211/50000000000000 : ℝ), (11628044861093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-778873027/5000000000 : ℝ)|^5011 ≤ (9662772870943/100000000000000 : ℝ)^3987
        have hw : |(-778873027/5000000000 : ℝ)|=(778873027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187242829/10000000000 : ℝ)|^5011 ≤ (21912523832211/50000000000000 : ℝ)^3987
        have hw : |(5187242829/10000000000 : ℝ)|=(5187242829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438756051/10000000000 : ℝ)|^5011 ≤ (11628044861093/25000000000000 : ℝ)^3987
        have hw : |(5438756051/10000000000 : ℝ)|=(5438756051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275810579/10000000000 : ℝ)*x 0 + (-44862423/312500000 : ℝ)*x 1 + (1087751227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275810579/10000000000 : ℝ)^5011 ≤ (8953511897529/20000000000000 : ℝ)^3987 := by
    have hnat : (5275810579 : ℕ)^5011*20000000000000^3987 ≤ 8953511897529^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275810579 10000000000 8953511897529 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44862423/312500000 : ℝ)^5011 ≤ (2180065035409/25000000000000 : ℝ)^3987 := by
    have hnat : (44862423 : ℕ)^5011*25000000000000^3987 ≤ 2180065035409^3987*312500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44862423 312500000 2180065035409 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087751227/2000000000 : ℝ)^5011 ≤ (46512180347241/100000000000000 : ℝ)^3987 := by
    have hnat : (1087751227 : ℕ)^5011*100000000000000^3987 ≤ 46512180347241^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087751227 2000000000 46512180347241 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275810579/10000000000 : ℝ), (-44862423/312500000 : ℝ), (1087751227/2000000000 : ℝ)] ![(8953511897529/20000000000000 : ℝ), (2180065035409/25000000000000 : ℝ), (46512180347241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275810579/10000000000 : ℝ)|^5011 ≤ (8953511897529/20000000000000 : ℝ)^3987
        have hw : |(5275810579/10000000000 : ℝ)|=(5275810579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44862423/312500000 : ℝ)|^5011 ≤ (2180065035409/25000000000000 : ℝ)^3987
        have hw : |(-44862423/312500000 : ℝ)|=(44862423/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087751227/2000000000 : ℝ)|^5011 ≤ (46512180347241/100000000000000 : ℝ)^3987
        have hw : |(1087751227/2000000000 : ℝ)|=(1087751227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275810717/10000000000 : ℝ)*x 0 + (1359689009/2500000000 : ℝ)*x 1 + (-358899371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275810717/10000000000 : ℝ)^5011 ≤ (44767560959387/100000000000000 : ℝ)^3987 := by
    have hnat : (5275810717 : ℕ)^5011*100000000000000^3987 ≤ 44767560959387^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275810717 10000000000 44767560959387 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359689009/2500000000 : ℝ)^5011 ≤ (23256089641573/50000000000000 : ℝ)^3987 := by
    have hnat : (1359689009 : ℕ)^5011*50000000000000^3987 ≤ 23256089641573^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359689009 2500000000 23256089641573 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358899371/2500000000 : ℝ)^5011 ≤ (1090032468081/12500000000000 : ℝ)^3987 := by
    have hnat : (358899371 : ℕ)^5011*12500000000000^3987 ≤ 1090032468081^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358899371 2500000000 1090032468081 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275810717/10000000000 : ℝ), (1359689009/2500000000 : ℝ), (-358899371/2500000000 : ℝ)] ![(44767560959387/100000000000000 : ℝ), (23256089641573/50000000000000 : ℝ), (1090032468081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275810717/10000000000 : ℝ)|^5011 ≤ (44767560959387/100000000000000 : ℝ)^3987
        have hw : |(5275810717/10000000000 : ℝ)|=(5275810717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359689009/2500000000 : ℝ)|^5011 ≤ (23256089641573/50000000000000 : ℝ)^3987
        have hw : |(1359689009/2500000000 : ℝ)|=(1359689009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-358899371/2500000000 : ℝ)|^5011 ≤ (1090032468081/12500000000000 : ℝ)^3987
        have hw : |(-358899371/2500000000 : ℝ)|=(358899371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s4_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163624037/10000000000 : ℝ)*x 0 + (4508039827/10000000000 : ℝ)*x 1 + (1919210253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163624037/10000000000 : ℝ)^5011 ≤ (33245937255009/100000000000000 : ℝ)^3987 := by
    have hnat : (4163624037 : ℕ)^5011*100000000000000^3987 ≤ 33245937255009^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163624037 10000000000 33245937255009 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508039827/10000000000 : ℝ)^5011 ≤ (1836918086257/5000000000000 : ℝ)^3987 := by
    have hnat : (4508039827 : ℕ)^5011*5000000000000^3987 ≤ 1836918086257^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508039827 10000000000 1836918086257 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919210253/5000000000 : ℝ)^5011 ≤ (30015701003119/100000000000000 : ℝ)^3987 := by
    have hnat : (1919210253 : ℕ)^5011*100000000000000^3987 ≤ 30015701003119^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919210253 5000000000 30015701003119 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163624037/10000000000 : ℝ), (4508039827/10000000000 : ℝ), (1919210253/5000000000 : ℝ)] ![(33245937255009/100000000000000 : ℝ), (1836918086257/5000000000000 : ℝ), (30015701003119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163624037/10000000000 : ℝ)|^5011 ≤ (33245937255009/100000000000000 : ℝ)^3987
        have hw : |(4163624037/10000000000 : ℝ)|=(4163624037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508039827/10000000000 : ℝ)|^5011 ≤ (1836918086257/5000000000000 : ℝ)^3987
        have hw : |(4508039827/10000000000 : ℝ)|=(4508039827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1919210253/5000000000 : ℝ)|^5011 ≤ (30015701003119/100000000000000 : ℝ)^3987
        have hw : |(1919210253/5000000000 : ℝ)|=(1919210253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10783/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16221/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (507/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (539/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (507/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (539/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (507/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (539/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (507/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (539/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (507/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (539/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (507/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (539/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (539/5000 : ℝ) ^ (5007/1024 : ℝ) ≤ (372285251240509/20000000000000000000 : ℝ) := by
    have hpowers : (539/5000 : ℝ)^5007 ≤ (372285251240509/20000000000000000000 : ℝ)^1024 := by
      have hnat : (539 : ℕ)^5007*20000000000000000000^1024 ≤ 372285251240509^1024*5000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        539 5000 372285251240509 20000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (539/5000 : ℝ)) (X := (372285251240509/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (507/3125 : ℝ) ^ (5007/1024 : ℝ) ≤ (6869418863140563/50000000000000000000 : ℝ) := by
    have hpowers : (507/3125 : ℝ)^5007 ≤ (6869418863140563/50000000000000000000 : ℝ)^1024 := by
      have hnat : (507 : ℕ)^5007*50000000000000000000^1024 ≤ 6869418863140563^1024*3125^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        507 3125 6869418863140563 50000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (507/3125 : ℝ)) (X := (6869418863140563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000372285251240509/10000000000000000000 : ℝ) ≤ (2000015227259937/2000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (10000372285251240509/10000000000000000000 : ℝ)^1024 ≤ (2000015227259937/2000000000000000 : ℝ)^5007 := by
      have hnat : (10000372285251240509 : ℕ)^1024*2000000000000000^5007 ≤ 2000015227259937^5007*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000372285251240509 10000000000000000000 2000015227259937 2000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000015227259937/2000000000000000 : ℝ)) (X := (10000372285251240509/10000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015600263982483671/100000000000000000000 : ℝ) ≤ (10000319026946247/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (100015600263982483671/100000000000000000000 : ℝ)^1024 ≤ (10000319026946247/10000000000000000 : ℝ)^5007 := by
      have hnat : (100015600263982483671 : ℕ)^1024*10000000000000000^5007 ≤ 10000319026946247^5007*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015600263982483671 100000000000000000000 10000319026946247 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000319026946247/10000000000000000 : ℝ)) (X := (100015600263982483671/100000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006869418863140563/25000000000000000000 : ℝ) ≤ (10000561917592809/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (25006869418863140563/25000000000000000000 : ℝ)^1024 ≤ (10000561917592809/10000000000000000 : ℝ)^5007 := by
      have hnat : (25006869418863140563 : ℕ)^1024*10000000000000000^5007 ≤ 10000561917592809^5007*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006869418863140563 25000000000000000000 10000561917592809 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000561917592809/10000000000000000 : ℝ)) (X := (25006869418863140563/25000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372285251240509/20000000000000000000 : ℝ) ≤ ((2721758888183780421/2722000000000000000 : ℝ)+2*(121445323281/272200000000000 : ℝ)*(539/5000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (2721758888183780421/2722000000000000000 : ℝ)+2*(121445323281/272200000000000 : ℝ)*(539/5000 : ℝ)=(2000015227259937/2000000000000000 : ℝ) by norm_num, show 1+2*(372285251240509/20000000000000000000 : ℝ)=(10000372285251240509/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6869418863140563/50000000000000000000 : ℝ)+(372285251240509/20000000000000000000 : ℝ) ≤ ((2721758888183780421/2722000000000000000 : ℝ)+(121445323281/272200000000000 : ℝ)*((507/3125 : ℝ)+(539/5000 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (2721758888183780421/2722000000000000000 : ℝ)+(121445323281/272200000000000 : ℝ)*((507/3125 : ℝ)+(539/5000 : ℝ))=(10000319026946247/10000000000000000 : ℝ) by norm_num, show 1+(6869418863140563/50000000000000000000 : ℝ)+(372285251240509/20000000000000000000 : ℝ)=(100015600263982483671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6869418863140563/50000000000000000000 : ℝ) ≤ ((2721758888183780421/2722000000000000000 : ℝ)+2*(121445323281/272200000000000 : ℝ)*(507/3125 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (2721758888183780421/2722000000000000000 : ℝ)+2*(121445323281/272200000000000 : ℝ)*(507/3125 : ℝ)=(10000561917592809/10000000000000000 : ℝ) by norm_num, show 1+2*(6869418863140563/50000000000000000000 : ℝ)=(25006869418863140563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2721758888183780421/2722000000000000000 : ℝ)*(X 1 0+X 2 0)+(121445323281/272200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (2721758888183780421/2722000000000000000 : ℝ)) (alpha := (121445323281/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2721758888183780421/2722000000000000000 : ℝ)*(X 0 1+X 2 1)+(121445323281/272200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (2721758888183780421/2722000000000000000 : ℝ)) (alpha := (121445323281/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2721758888183780421/2722000000000000000 : ℝ)*(X 0 2+X 1 2)+(121445323281/272200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (539/5000 : ℝ)) (hi := (507/3125 : ℝ)) (c := (2721758888183780421/2722000000000000000 : ℝ)) (alpha := (121445323281/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1557684977/10000000000 : ℝ)*X 0 0+(340045447/625000000 : ℝ)*X 0 1+(1296323067/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334013333/625000000 : ℝ)*X 1 0+(-844530701/5000000000 : ℝ)*X 1 1+(2592646063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344213189/10000000000 : ℝ)*X 2 0+(1296323053/2500000000 : ℝ)*X 2 1+(-67562459/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((416346149/1000000000 : ℝ)*X 0 0+(766634479/2000000000 : ℝ)*X 0 1+(2256616609/5000000000 : ℝ)*X 0 2+(416346149/1000000000 : ℝ)*X 1 0+(766634479/2000000000 : ℝ)*X 1 1+(2256616609/5000000000 : ℝ)*X 1 2+(416346149/1000000000 : ℝ)*X 2 0+(766634479/2000000000 : ℝ)*X 2 1+(2256616609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-778873027/5000000000 : ℝ)*X 0 0+(5187242829/10000000000 : ℝ)*X 0 1+(5438756051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275810579/10000000000 : ℝ)*X 1 0+(-44862423/312500000 : ℝ)*X 1 1+(1087751227/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275810717/10000000000 : ℝ)*X 2 0+(1359689009/2500000000 : ℝ)*X 2 1+(-358899371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4163624037/10000000000 : ℝ)*X 0 0+(4508039827/10000000000 : ℝ)*X 0 1+(1919210253/5000000000 : ℝ)*X 0 2+(4163624037/10000000000 : ℝ)*X 1 0+(4508039827/10000000000 : ℝ)*X 1 1+(1919210253/5000000000 : ℝ)*X 1 2+(4163624037/10000000000 : ℝ)*X 2 0+(4508039827/10000000000 : ℝ)*X 2 1+(1919210253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1993008891679819446099/425312500000000000000000000 : ℝ) := by norm_num
    linear_combination (489219/62500000000 : ℝ)*(base19) + (625888611/100000000000000 : ℝ)*(base23) + (7353269/25000000000000 : ℝ)*(lower2) + (31064639/20000000000000 : ℝ)*(upper3) + (43406681/100000000000000 : ℝ)*(upper5) + (1346343026001803/50000000000000 : ℝ)*(major0) + (1346343026001803/50000000000000 : ℝ)*(major1) + (1346343026001803/50000000000000 : ℝ)*(major2) + (1957450626433897/50000000000000 : ℝ)*(sp0) + (1957453508831457/50000000000000 : ℝ)*(sp1) + (122340849203897/3125000000000 : ℝ)*(sp2) + (294091995696619/20000000000000 : ℝ)*(sp3) + (6547545521/100000000000000 : ℝ)*(sp4) + (4168911227/100000000000000 : ℝ)*(sp7) + (735232073697161/50000000000000 : ℝ)*(f.failure) + (1957453900206657/50000000000000 : ℝ)*(f.sum) + (16955428374171/3402500000000000000000000000 : ℝ)*base66 + (463521289862570937/136100000000000000000000000000000 : ℝ)*base68 + (147840481594970937/136100000000000000000000000000000 : ℝ)*base70 + (456115816008429063/136100000000000000000000000000000 : ℝ)*base71 + (48109725715287/6805000000000000000000000000 : ℝ)*base74 + (628569079388929063/136100000000000000000000000000000 : ℝ)*base75 + (1110803928221970937/136100000000000000000000000000000 : ℝ)*base78 + (24758739236329063/136100000000000000000000000000000 : ℝ)*base79 + (5878848645183/6805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18805583/5000000000000000000000 : ℝ)*base89 + (18805583/5000000000000000000000 : ℝ)*base91 + (18805583/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164456887684240807123308291/34025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162754593/25000000000000 : ℝ)*(base19) + (816831707/100000000000000 : ℝ)*(base23) + (28213049/12500000000000 : ℝ)*(lower1) + (13079841/12500000000000 : ℝ)*(upper3) + (10479249/50000000000000 : ℝ)*(lower4) + (19047539/20000000000000 : ℝ)*(upper5) + (683663476920157/25000000000000 : ℝ)*(major0) + (683663476920157/25000000000000 : ℝ)*(major1) + (683663476920157/25000000000000 : ℝ)*(major2) + (1703699623/100000000000000 : ℝ)*(sp2) + (1987962521654979/50000000000000 : ℝ)*(sp4) + (1987962196145793/50000000000000 : ℝ)*(sp5) + (993980630694657/25000000000000 : ℝ)*(sp6) + (46668206591797/3125000000000 : ℝ)*(sp7) + (46668206591797/3125000000000 : ℝ)*(f.failure) + (1987962521654979/50000000000000 : ℝ)*(f.sum) + (445980915927/3402500000000000000000000000 : ℝ)*base65 + (447633117518516097/68050000000000000000000000000000 : ℝ)*base67 + (1271483402632083903/68050000000000000000000000000000 : ℝ)*base70 + (2134313003334916097/68050000000000000000000000000000 : ℝ)*base71 + (2953326844963/3402500000000000000000000000 : ℝ)*base74 + (5281351717980683903/68050000000000000000000000000000 : ℝ)*base76 + (729257926023533903/68050000000000000000000000000000 : ℝ)*base78 + (1130871252792583903/68050000000000000000000000000000 : ℝ)*base80 + (8806410055101/6805000000000000000000000000 : ℝ)*base82 + (498909/312500000000000000000 : ℝ)*base90 + (498909/312500000000000000000 : ℝ)*base92 + (498909/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1673_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (507/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16221/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1673_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1673_box_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-326918649/2500000000 : ℝ)*x 0 + (5402466809/10000000000 : ℝ)*x 1 + (5402466747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326918649/2500000000 : ℝ)^5011 ≤ (3877538708659/50000000000000 : ℝ)^3987 := by
    have hnat : (326918649 : ℕ)^5011*50000000000000^3987 ≤ 3877538708659^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326918649 2500000000 3877538708659 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402466809/10000000000 : ℝ)^5011 ≤ (11530615403829/25000000000000 : ℝ)^3987 := by
    have hnat : (5402466809 : ℕ)^5011*25000000000000^3987 ≤ 11530615403829^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402466809 10000000000 11530615403829 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402466747/10000000000 : ℝ)^5011 ≤ (23061230475029/50000000000000 : ℝ)^3987 := by
    have hnat : (5402466747 : ℕ)^5011*50000000000000^3987 ≤ 23061230475029^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402466747 10000000000 23061230475029 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-326918649/2500000000 : ℝ), (5402466809/10000000000 : ℝ), (5402466747/10000000000 : ℝ)] ![(3877538708659/50000000000000 : ℝ), (11530615403829/25000000000000 : ℝ), (23061230475029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-326918649/2500000000 : ℝ)|^5011 ≤ (3877538708659/50000000000000 : ℝ)^3987
        have hw : |(-326918649/2500000000 : ℝ)|=(326918649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402466809/10000000000 : ℝ)|^5011 ≤ (11530615403829/25000000000000 : ℝ)^3987
        have hw : |(5402466809/10000000000 : ℝ)|=(5402466809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402466747/10000000000 : ℝ)|^5011 ≤ (23061230475029/50000000000000 : ℝ)^3987
        have hw : |(5402466747/10000000000 : ℝ)|=(5402466747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050122489/2000000000 : ℝ)*x 0 + (-380294509/2500000000 : ℝ)*x 1 + (1350616729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050122489/2000000000 : ℝ)^5011 ≤ (44498991648889/100000000000000 : ℝ)^3987 := by
    have hnat : (1050122489 : ℕ)^5011*100000000000000^3987 ≤ 44498991648889^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050122489 2000000000 44498991648889 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380294509/2500000000 : ℝ)^5011 ≤ (937854557253/10000000000000 : ℝ)^3987 := by
    have hnat : (380294509 : ℕ)^5011*10000000000000^3987 ≤ 937854557253^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380294509 2500000000 937854557253 10000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350616729/2500000000 : ℝ)^5011 ≤ (46122462763423/100000000000000 : ℝ)^3987 := by
    have hnat : (1350616729 : ℕ)^5011*100000000000000^3987 ≤ 46122462763423^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350616729 2500000000 46122462763423 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050122489/2000000000 : ℝ), (-380294509/2500000000 : ℝ), (1350616729/2500000000 : ℝ)] ![(44498991648889/100000000000000 : ℝ), (937854557253/10000000000000 : ℝ), (46122462763423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050122489/2000000000 : ℝ)|^5011 ≤ (44498991648889/100000000000000 : ℝ)^3987
        have hw : |(1050122489/2000000000 : ℝ)|=(1050122489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380294509/2500000000 : ℝ)|^5011 ≤ (937854557253/10000000000000 : ℝ)^3987
        have hw : |(-380294509/2500000000 : ℝ)|=(380294509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350616729/2500000000 : ℝ)|^5011 ≤ (46122462763423/100000000000000 : ℝ)^3987
        have hw : |(1350616729/2500000000 : ℝ)|=(1350616729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250612653/10000000000 : ℝ)*x 0 + (1350616697/2500000000 : ℝ)*x 1 + (-1521177927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250612653/10000000000 : ℝ)^5011 ≤ (1112474846611/2500000000000 : ℝ)^3987 := by
    have hnat : (5250612653 : ℕ)^5011*2500000000000^3987 ≤ 1112474846611^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250612653 10000000000 1112474846611 2500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350616697/2500000000 : ℝ)^5011 ≤ (23061230694993/50000000000000 : ℝ)^3987 := by
    have hnat : (1350616697 : ℕ)^5011*50000000000000^3987 ≤ 23061230694993^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350616697 2500000000 23061230694993 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521177927/10000000000 : ℝ)^5011 ≤ (1172318090989/12500000000000 : ℝ)^3987 := by
    have hnat : (1521177927 : ℕ)^5011*12500000000000^3987 ≤ 1172318090989^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521177927 10000000000 1172318090989 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250612653/10000000000 : ℝ), (1350616697/2500000000 : ℝ), (-1521177927/10000000000 : ℝ)] ![(1112474846611/2500000000000 : ℝ), (23061230694993/50000000000000 : ℝ), (1172318090989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250612653/10000000000 : ℝ)|^5011 ≤ (1112474846611/2500000000000 : ℝ)^3987
        have hw : |(5250612653/10000000000 : ℝ)|=(5250612653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350616697/2500000000 : ℝ)|^5011 ≤ (23061230694993/50000000000000 : ℝ)^3987
        have hw : |(1350616697/2500000000 : ℝ)|=(1350616697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1521177927/10000000000 : ℝ)|^5011 ≤ (1172318090989/12500000000000 : ℝ)^3987
        have hw : |(-1521177927/10000000000 : ℝ)|=(1521177927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2219422237/5000000000 : ℝ)*x 0 + (2018716077/5000000000 : ℝ)*x 1 + (201871619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219422237/5000000000 : ℝ)^5011 ≤ (36031023768501/100000000000000 : ℝ)^3987 := by
    have hnat : (2219422237 : ℕ)^5011*100000000000000^3987 ≤ 36031023768501^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219422237 5000000000 36031023768501 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018716077/5000000000 : ℝ)^5011 ≤ (1999030436259/6250000000000 : ℝ)^3987 := by
    have hnat : (2018716077 : ℕ)^5011*6250000000000^3987 ≤ 1999030436259^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018716077 5000000000 1999030436259 6250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201871619/500000000 : ℝ)^5011 ≤ (15992244615171/50000000000000 : ℝ)^3987 := by
    have hnat : (201871619 : ℕ)^5011*50000000000000^3987 ≤ 15992244615171^3987*500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201871619 500000000 15992244615171 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2219422237/5000000000 : ℝ), (2018716077/5000000000 : ℝ), (201871619/500000000 : ℝ)] ![(36031023768501/100000000000000 : ℝ), (1999030436259/6250000000000 : ℝ), (15992244615171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2219422237/5000000000 : ℝ)|^5011 ≤ (36031023768501/100000000000000 : ℝ)^3987
        have hw : |(2219422237/5000000000 : ℝ)|=(2219422237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018716077/5000000000 : ℝ)|^5011 ≤ (1999030436259/6250000000000 : ℝ)^3987
        have hw : |(2018716077/5000000000 : ℝ)|=(2018716077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201871619/500000000 : ℝ)|^5011 ≤ (15992244615171/50000000000000 : ℝ)^3987
        have hw : |(201871619/500000000 : ℝ)|=(201871619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818209667/10000000000 : ℝ)*x 0 + (5216161611/10000000000 : ℝ)*x 1 + (5216161523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818209667/10000000000 : ℝ)^5011 ≤ (2933829295503/25000000000000 : ℝ)^3987 := by
    have hnat : (1818209667 : ℕ)^5011*25000000000000^3987 ≤ 2933829295503^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818209667 10000000000 2933829295503 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216161611/10000000000 : ℝ)^5011 ≤ (44132341865871/100000000000000 : ℝ)^3987 := by
    have hnat : (5216161611 : ℕ)^5011*100000000000000^3987 ≤ 44132341865871^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216161611 10000000000 44132341865871 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216161523/10000000000 : ℝ)^5011 ≤ (22066170465053/50000000000000 : ℝ)^3987 := by
    have hnat : (5216161523 : ℕ)^5011*50000000000000^3987 ≤ 22066170465053^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216161523 10000000000 22066170465053 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818209667/10000000000 : ℝ), (5216161611/10000000000 : ℝ), (5216161523/10000000000 : ℝ)] ![(2933829295503/25000000000000 : ℝ), (44132341865871/100000000000000 : ℝ), (22066170465053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818209667/10000000000 : ℝ)|^5011 ≤ (2933829295503/25000000000000 : ℝ)^3987
        have hw : |(-1818209667/10000000000 : ℝ)|=(1818209667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216161611/10000000000 : ℝ)|^5011 ≤ (44132341865871/100000000000000 : ℝ)^3987
        have hw : |(5216161611/10000000000 : ℝ)|=(5216161611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216161523/10000000000 : ℝ)|^5011 ≤ (22066170465053/50000000000000 : ℝ)^3987
        have hw : |(5216161523/10000000000 : ℝ)|=(5216161523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689049837/5000000000 : ℝ)*x 0 + (-200209643/1250000000 : ℝ)*x 1 + (2608080949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689049837/5000000000 : ℝ)^5011 ≤ (22930577289349/50000000000000 : ℝ)^3987 := by
    have hnat : (2689049837 : ℕ)^5011*50000000000000^3987 ≤ 22930577289349^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689049837 5000000000 22930577289349 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200209643/1250000000 : ℝ)^5011 ≤ (1250812561857/12500000000000 : ℝ)^3987 := by
    have hnat : (200209643 : ℕ)^5011*12500000000000^3987 ≤ 1250812561857^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200209643 1250000000 1250812561857 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608080949/5000000000 : ℝ)^5011 ≤ (44132344917741/100000000000000 : ℝ)^3987 := by
    have hnat : (2608080949 : ℕ)^5011*100000000000000^3987 ≤ 44132344917741^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608080949 5000000000 44132344917741 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689049837/5000000000 : ℝ), (-200209643/1250000000 : ℝ), (2608080949/5000000000 : ℝ)] ![(22930577289349/50000000000000 : ℝ), (1250812561857/12500000000000 : ℝ), (44132344917741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689049837/5000000000 : ℝ)|^5011 ≤ (22930577289349/50000000000000 : ℝ)^3987
        have hw : |(2689049837/5000000000 : ℝ)|=(2689049837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200209643/1250000000 : ℝ)|^5011 ≤ (1250812561857/12500000000000 : ℝ)^3987
        have hw : |(-200209643/1250000000 : ℝ)|=(200209643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608080949/5000000000 : ℝ)|^5011 ≤ (44132344917741/100000000000000 : ℝ)^3987
        have hw : |(2608080949/5000000000 : ℝ)|=(2608080949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689049943/5000000000 : ℝ)*x 0 + (5216161411/10000000000 : ℝ)*x 1 + (-800838757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689049943/5000000000 : ℝ)^5011 ≤ (11465289212703/25000000000000 : ℝ)^3987 := by
    have hnat : (2689049943 : ℕ)^5011*25000000000000^3987 ≤ 11465289212703^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689049943 5000000000 11465289212703 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216161411/10000000000 : ℝ)^5011 ≤ (44132339739133/100000000000000 : ℝ)^3987 := by
    have hnat : (5216161411 : ℕ)^5011*100000000000000^3987 ≤ 44132339739133^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216161411 10000000000 44132339739133 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800838757/5000000000 : ℝ)^5011 ≤ (10006503400131/100000000000000 : ℝ)^3987 := by
    have hnat : (800838757 : ℕ)^5011*100000000000000^3987 ≤ 10006503400131^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800838757 5000000000 10006503400131 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689049943/5000000000 : ℝ), (5216161411/10000000000 : ℝ), (-800838757/5000000000 : ℝ)] ![(11465289212703/25000000000000 : ℝ), (44132339739133/100000000000000 : ℝ), (10006503400131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689049943/5000000000 : ℝ)|^5011 ≤ (11465289212703/25000000000000 : ℝ)^3987
        have hw : |(2689049943/5000000000 : ℝ)|=(2689049943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216161411/10000000000 : ℝ)|^5011 ≤ (44132339739133/100000000000000 : ℝ)^3987
        have hw : |(5216161411/10000000000 : ℝ)|=(5216161411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-800838757/5000000000 : ℝ)|^5011 ≤ (10006503400131/100000000000000 : ℝ)^3987
        have hw : |(-800838757/5000000000 : ℝ)|=(800838757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3881217133/10000000000 : ℝ)*x 0 + (4315930297/10000000000 : ℝ)*x 1 + (1078982451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3881217133/10000000000 : ℝ)^5011 ≤ (1521845775373/5000000000000 : ℝ)^3987 := by
    have hnat : (3881217133 : ℕ)^5011*5000000000000^3987 ≤ 1521845775373^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881217133 10000000000 1521845775373 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315930297/10000000000 : ℝ)^5011 ≤ (6956308946277/20000000000000 : ℝ)^3987 := by
    have hnat : (4315930297 : ℕ)^5011*20000000000000^3987 ≤ 6956308946277^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315930297 10000000000 6956308946277 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078982451/2500000000 : ℝ)^5011 ≤ (34781539737949/100000000000000 : ℝ)^3987 := by
    have hnat : (1078982451 : ℕ)^5011*100000000000000^3987 ≤ 34781539737949^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078982451 2500000000 34781539737949 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3881217133/10000000000 : ℝ), (4315930297/10000000000 : ℝ), (1078982451/2500000000 : ℝ)] ![(1521845775373/5000000000000 : ℝ), (6956308946277/20000000000000 : ℝ), (34781539737949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3881217133/10000000000 : ℝ)|^5011 ≤ (1521845775373/5000000000000 : ℝ)^3987
        have hw : |(3881217133/10000000000 : ℝ)|=(3881217133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315930297/10000000000 : ℝ)|^5011 ≤ (6956308946277/20000000000000 : ℝ)^3987
        have hw : |(4315930297/10000000000 : ℝ)|=(4315930297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078982451/2500000000 : ℝ)|^5011 ≤ (34781539737949/100000000000000 : ℝ)^3987
        have hw : |(1078982451/2500000000 : ℝ)|=(1078982451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_8 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1709144081/10000000000 : ℝ)*x 0 + (2540828937/5000000000 : ℝ)*x 1 + (217265461/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1709144081/10000000000 : ℝ)^5011 ≤ (5428747108773/50000000000000 : ℝ)^3987 := by
    have hnat : (1709144081 : ℕ)^5011*50000000000000^3987 ≤ 5428747108773^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709144081 10000000000 5428747108773 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540828937/5000000000 : ℝ)^5011 ≤ (1708273488773/4000000000000 : ℝ)^3987 := by
    have hnat : (2540828937 : ℕ)^5011*4000000000000^3987 ≤ 1708273488773^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540828937 5000000000 1708273488773 4000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217265461/400000000 : ℝ)^5011 ≤ (46435668542381/100000000000000 : ℝ)^3987 := by
    have hnat : (217265461 : ℕ)^5011*100000000000000^3987 ≤ 46435668542381^3987*400000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217265461 400000000 46435668542381 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1709144081/10000000000 : ℝ), (2540828937/5000000000 : ℝ), (217265461/400000000 : ℝ)] ![(5428747108773/50000000000000 : ℝ), (1708273488773/4000000000000 : ℝ), (46435668542381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1709144081/10000000000 : ℝ)|^5011 ≤ (5428747108773/50000000000000 : ℝ)^3987
        have hw : |(-1709144081/10000000000 : ℝ)|=(1709144081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540828937/5000000000 : ℝ)|^5011 ≤ (1708273488773/4000000000000 : ℝ)^3987
        have hw : |(2540828937/5000000000 : ℝ)|=(2540828937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217265461/400000000 : ℝ)|^5011 ≤ (46435668542381/100000000000000 : ℝ)^3987
        have hw : |(217265461/400000000 : ℝ)|=(217265461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_9 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653831963/1250000000 : ℝ)*x 0 + (-377040799/2500000000 : ℝ)*x 1 + (2715818331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653831963/1250000000 : ℝ)^5011 ≤ (44286522554777/100000000000000 : ℝ)^3987 := by
    have hnat : (653831963 : ℕ)^5011*100000000000000^3987 ≤ 44286522554777^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653831963 1250000000 44286522554777 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377040799/2500000000 : ℝ)^5011 ≤ (4638903707223/50000000000000 : ℝ)^3987 := by
    have hnat : (377040799 : ℕ)^5011*50000000000000^3987 ≤ 4638903707223^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377040799 2500000000 4638903707223 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715818331/5000000000 : ℝ)^5011 ≤ (46435670014421/100000000000000 : ℝ)^3987 := by
    have hnat : (2715818331 : ℕ)^5011*100000000000000^3987 ≤ 46435670014421^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715818331 5000000000 46435670014421 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653831963/1250000000 : ℝ), (-377040799/2500000000 : ℝ), (2715818331/5000000000 : ℝ)] ![(44286522554777/100000000000000 : ℝ), (4638903707223/50000000000000 : ℝ), (46435670014421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653831963/1250000000 : ℝ)|^5011 ≤ (44286522554777/100000000000000 : ℝ)^3987
        have hw : |(653831963/1250000000 : ℝ)|=(653831963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377040799/2500000000 : ℝ)|^5011 ≤ (4638903707223/50000000000000 : ℝ)^3987
        have hw : |(-377040799/2500000000 : ℝ)|=(377040799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715818331/5000000000 : ℝ)|^5011 ≤ (46435670014421/100000000000000 : ℝ)^3987
        have hw : |(2715818331/5000000000 : ℝ)|=(2715818331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_10 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230655859/10000000000 : ℝ)*x 0 + (339477287/625000000 : ℝ)*x 1 + (-1508163079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230655859/10000000000 : ℝ)^5011 ≤ (22143262102087/50000000000000 : ℝ)^3987 := by
    have hnat : (5230655859 : ℕ)^5011*50000000000000^3987 ≤ 22143262102087^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230655859 10000000000 22143262102087 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339477287/625000000 : ℝ)^5011 ≤ (11608917315571/25000000000000 : ℝ)^3987 := by
    have hnat : (339477287 : ℕ)^5011*25000000000000^3987 ≤ 11608917315571^3987*625000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339477287 625000000 11608917315571 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508163079/10000000000 : ℝ)^5011 ≤ (9277806509837/100000000000000 : ℝ)^3987 := by
    have hnat : (1508163079 : ℕ)^5011*100000000000000^3987 ≤ 9277806509837^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508163079 10000000000 9277806509837 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230655859/10000000000 : ℝ), (339477287/625000000 : ℝ), (-1508163079/10000000000 : ℝ)] ![(22143262102087/50000000000000 : ℝ), (11608917315571/25000000000000 : ℝ), (9277806509837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230655859/10000000000 : ℝ)|^5011 ≤ (22143262102087/50000000000000 : ℝ)^3987
        have hw : |(5230655859/10000000000 : ℝ)|=(5230655859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339477287/625000000 : ℝ)|^5011 ≤ (11608917315571/25000000000000 : ℝ)^3987
        have hw : |(339477287/625000000 : ℝ)|=(339477287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1508163079/10000000000 : ℝ)|^5011 ≤ (9277806509837/100000000000000 : ℝ)^3987
        have hw : |(-1508163079/10000000000 : ℝ)|=(1508163079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_11 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2261892827/5000000000 : ℝ)*x 0 + (3993747871/10000000000 : ℝ)*x 1 + (3993747697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2261892827/5000000000 : ℝ)^5011 ≤ (7379942441713/20000000000000 : ℝ)^3987 := by
    have hnat : (2261892827 : ℕ)^5011*20000000000000^3987 ≤ 7379942441713^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261892827 5000000000 7379942441713 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3993747871/10000000000 : ℝ)^5011 ≤ (15775072377303/50000000000000 : ℝ)^3987 := by
    have hnat : (3993747871 : ℕ)^5011*50000000000000^3987 ≤ 15775072377303^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993747871 10000000000 15775072377303 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3993747697/10000000000 : ℝ)^5011 ≤ (15775071513493/50000000000000 : ℝ)^3987 := by
    have hnat : (3993747697 : ℕ)^5011*50000000000000^3987 ≤ 15775071513493^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993747697 10000000000 15775071513493 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2261892827/5000000000 : ℝ), (3993747871/10000000000 : ℝ), (3993747697/10000000000 : ℝ)] ![(7379942441713/20000000000000 : ℝ), (15775072377303/50000000000000 : ℝ), (15775071513493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2261892827/5000000000 : ℝ)|^5011 ≤ (7379942441713/20000000000000 : ℝ)^3987
        have hw : |(2261892827/5000000000 : ℝ)|=(2261892827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3993747871/10000000000 : ℝ)|^5011 ≤ (15775072377303/50000000000000 : ℝ)^3987
        have hw : |(3993747871/10000000000 : ℝ)|=(3993747871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3993747697/10000000000 : ℝ)|^5011 ≤ (15775071513493/50000000000000 : ℝ)^3987
        have hw : |(3993747697/10000000000 : ℝ)|=(3993747697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_12 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1414712843/10000000000 : ℝ)*x 0 + (5531994007/10000000000 : ℝ)*x 1 + (32477523/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414712843/10000000000 : ℝ)^5011 ≤ (2140279247777/25000000000000 : ℝ)^3987 := by
    have hnat : (1414712843 : ℕ)^5011*25000000000000^3987 ≤ 2140279247777^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414712843 10000000000 2140279247777 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531994007/10000000000 : ℝ)^5011 ≤ (185611478923/390625000000 : ℝ)^3987 := by
    have hnat : (5531994007 : ℕ)^5011*390625000000^3987 ≤ 185611478923^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531994007 10000000000 185611478923 390625000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32477523/62500000 : ℝ)^5011 ≤ (43922344394281/100000000000000 : ℝ)^3987 := by
    have hnat : (32477523 : ℕ)^5011*100000000000000^3987 ≤ 43922344394281^3987*62500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32477523 62500000 43922344394281 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1414712843/10000000000 : ℝ), (5531994007/10000000000 : ℝ), (32477523/62500000 : ℝ)] ![(2140279247777/25000000000000 : ℝ), (185611478923/390625000000 : ℝ), (43922344394281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1414712843/10000000000 : ℝ)|^5011 ≤ (2140279247777/25000000000000 : ℝ)^3987
        have hw : |(-1414712843/10000000000 : ℝ)|=(1414712843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531994007/10000000000 : ℝ)|^5011 ≤ (185611478923/390625000000 : ℝ)^3987
        have hw : |(5531994007/10000000000 : ℝ)|=(5531994007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32477523/62500000 : ℝ)|^5011 ≤ (43922344394281/100000000000000 : ℝ)^3987
        have hw : |(32477523/62500000 : ℝ)|=(32477523/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_13 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695815729/5000000000 : ℝ)*x 0 + (-1609940459/10000000000 : ℝ)*x 1 + (5196403611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695815729/5000000000 : ℝ)^5011 ≤ (1840249143017/4000000000000 : ℝ)^3987 := by
    have hnat : (2695815729 : ℕ)^5011*4000000000000^3987 ≤ 1840249143017^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695815729 5000000000 1840249143017 4000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1609940459/10000000000 : ℝ)^5011 ≤ (5035713870889/50000000000000 : ℝ)^3987 := by
    have hnat : (1609940459 : ℕ)^5011*50000000000000^3987 ≤ 5035713870889^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609940459 10000000000 5035713870889 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196403611/10000000000 : ℝ)^5011 ≤ (43922343661271/100000000000000 : ℝ)^3987 := by
    have hnat : (5196403611 : ℕ)^5011*100000000000000^3987 ≤ 43922343661271^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196403611 10000000000 43922343661271 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695815729/5000000000 : ℝ), (-1609940459/10000000000 : ℝ), (5196403611/10000000000 : ℝ)] ![(1840249143017/4000000000000 : ℝ), (5035713870889/50000000000000 : ℝ), (43922343661271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695815729/5000000000 : ℝ)|^5011 ≤ (1840249143017/4000000000000 : ℝ)^3987
        have hw : |(2695815729/5000000000 : ℝ)|=(2695815729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1609940459/10000000000 : ℝ)|^5011 ≤ (5035713870889/50000000000000 : ℝ)^3987
        have hw : |(-1609940459/10000000000 : ℝ)|=(1609940459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196403611/10000000000 : ℝ)|^5011 ≤ (43922343661271/100000000000000 : ℝ)^3987
        have hw : |(5196403611/10000000000 : ℝ)|=(5196403611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_14 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078326203/2000000000 : ℝ)*x 0 + (519640377/1000000000 : ℝ)*x 1 + (-1609940849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078326203/2000000000 : ℝ)^5011 ≤ (46006223824499/100000000000000 : ℝ)^3987 := by
    have hnat : (1078326203 : ℕ)^5011*100000000000000^3987 ≤ 46006223824499^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078326203 2000000000 46006223824499 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519640377/1000000000 : ℝ)^5011 ≤ (43922345350381/100000000000000 : ℝ)^3987 := by
    have hnat : (519640377 : ℕ)^5011*100000000000000^3987 ≤ 43922345350381^3987*1000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519640377 1000000000 43922345350381 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1609940849/10000000000 : ℝ)^5011 ≤ (629464425509/6250000000000 : ℝ)^3987 := by
    have hnat : (1609940849 : ℕ)^5011*6250000000000^3987 ≤ 629464425509^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609940849 10000000000 629464425509 6250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078326203/2000000000 : ℝ), (519640377/1000000000 : ℝ), (-1609940849/10000000000 : ℝ)] ![(46006223824499/100000000000000 : ℝ), (43922345350381/100000000000000 : ℝ), (629464425509/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078326203/2000000000 : ℝ)|^5011 ≤ (46006223824499/100000000000000 : ℝ)^3987
        have hw : |(1078326203/2000000000 : ℝ)|=(1078326203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519640377/1000000000 : ℝ)|^5011 ≤ (43922345350381/100000000000000 : ℝ)^3987
        have hw : |(519640377/1000000000 : ℝ)|=(519640377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1609940849/10000000000 : ℝ)|^5011 ≤ (629464425509/6250000000000 : ℝ)^3987
        have hw : |(-1609940849/10000000000 : ℝ)|=(1609940849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_box_15 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (382044999/1000000000 : ℝ)*x 0 + (4345410847/10000000000 : ℝ)*x 1 + (4345410881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382044999/1000000000 : ℝ)^5011 ≤ (29839189437641/100000000000000 : ℝ)^3987 := by
    have hnat : (382044999 : ℕ)^5011*100000000000000^3987 ≤ 29839189437641^3987*1000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382044999 1000000000 29839189437641 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4345410847/10000000000 : ℝ)^5011 ≤ (35080405104741/100000000000000 : ℝ)^3987 := by
    have hnat : (4345410847 : ℕ)^5011*100000000000000^3987 ≤ 35080405104741^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345410847 10000000000 35080405104741 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4345410881/10000000000 : ℝ)^5011 ≤ (35080405449719/100000000000000 : ℝ)^3987 := by
    have hnat : (4345410881 : ℕ)^5011*100000000000000^3987 ≤ 35080405449719^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345410881 10000000000 35080405449719 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(382044999/1000000000 : ℝ), (4345410847/10000000000 : ℝ), (4345410881/10000000000 : ℝ)] ![(29839189437641/100000000000000 : ℝ), (35080405104741/100000000000000 : ℝ), (35080405449719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(382044999/1000000000 : ℝ)|^5011 ≤ (29839189437641/100000000000000 : ℝ)^3987
        have hw : |(382044999/1000000000 : ℝ)|=(382044999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4345410847/10000000000 : ℝ)|^5011 ≤ (35080405104741/100000000000000 : ℝ)^3987
        have hw : |(4345410847/10000000000 : ℝ)|=(4345410847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4345410881/10000000000 : ℝ)|^5011 ≤ (35080405449719/100000000000000 : ℝ)^3987
        have hw : |(4345410881/10000000000 : ℝ)|=(4345410881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65169/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58873/100000 : ℝ) ∧ (16321/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88443/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10783/100000 : ℝ) ^ (5007/1024 : ℝ) ≤ (465990143418047/25000000000000000000 : ℝ) := by
    have hpowers : (10783/100000 : ℝ)^5007 ≤ (465990143418047/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10783 : ℕ)^5007*25000000000000000000^1024 ≤ 465990143418047^1024*100000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10783 100000 465990143418047 25000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10783/100000 : ℝ)) (X := (465990143418047/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16221/100000 : ℝ) ^ (5007/1024 : ℝ) ≤ (13726420209241621/100000000000000000000 : ℝ) := by
    have hpowers : (16221/100000 : ℝ)^5007 ≤ (13726420209241621/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16221 : ℕ)^5007*100000000000000000000^1024 ≤ 13726420209241621^1024*100000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16221 100000 13726420209241621 100000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16221/100000 : ℝ)) (X := (13726420209241621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500465990143418047/12500000000000000000 : ℝ) ≤ (2500019059989283/2500000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (12500465990143418047/12500000000000000000 : ℝ)^1024 ≤ (2500019059989283/2500000000000000 : ℝ)^5007 := by
      have hnat : (12500465990143418047 : ℕ)^1024*2500000000000000^5007 ≤ 2500019059989283^5007*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500465990143418047 12500000000000000000 2500019059989283 2500000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500019059989283/2500000000000000 : ℝ)) (X := (12500465990143418047/12500000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015590380782913809/100000000000000000000 : ℝ) ≤ (5000159412423183/5000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (100015590380782913809/100000000000000000000 : ℝ)^1024 ≤ (5000159412423183/5000000000000000 : ℝ)^5007 := by
      have hnat : (100015590380782913809 : ℕ)^1024*5000000000000000^5007 ≤ 5000159412423183^5007*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015590380782913809 100000000000000000000 5000159412423183 5000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000159412423183/5000000000000000 : ℝ)) (X := (100015590380782913809/100000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013726420209241621/50000000000000000000 : ℝ) ≤ (25001403524339/25000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (50013726420209241621/50000000000000000000 : ℝ)^1024 ≤ (25001403524339/25000000000000 : ℝ)^5007 := by
      have hnat : (50013726420209241621 : ℕ)^1024*25000000000000^5007 ≤ 25001403524339^5007*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013726420209241621 50000000000000000000 25001403524339 25000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25001403524339/25000000000000 : ℝ)) (X := (50013726420209241621/50000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(465990143418047/25000000000000000000 : ℝ) ≤ ((13593795751791415843/13595000000000000000 : ℝ)+2*(121292444617/271900000000000 : ℝ)*(10783/100000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (13593795751791415843/13595000000000000000 : ℝ)+2*(121292444617/271900000000000 : ℝ)*(10783/100000 : ℝ)=(2500019059989283/2500000000000000 : ℝ) by norm_num, show 1+2*(465990143418047/25000000000000000000 : ℝ)=(12500465990143418047/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13726420209241621/100000000000000000000 : ℝ)+(465990143418047/25000000000000000000 : ℝ) ≤ ((13593795751791415843/13595000000000000000 : ℝ)+(121292444617/271900000000000 : ℝ)*((16221/100000 : ℝ)+(10783/100000 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (13593795751791415843/13595000000000000000 : ℝ)+(121292444617/271900000000000 : ℝ)*((16221/100000 : ℝ)+(10783/100000 : ℝ))=(5000159412423183/5000000000000000 : ℝ) by norm_num, show 1+(13726420209241621/100000000000000000000 : ℝ)+(465990143418047/25000000000000000000 : ℝ)=(100015590380782913809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13726420209241621/100000000000000000000 : ℝ) ≤ ((13593795751791415843/13595000000000000000 : ℝ)+2*(121292444617/271900000000000 : ℝ)*(16221/100000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (13593795751791415843/13595000000000000000 : ℝ)+2*(121292444617/271900000000000 : ℝ)*(16221/100000 : ℝ)=(25001403524339/25000000000000 : ℝ) by norm_num, show 1+2*(13726420209241621/100000000000000000000 : ℝ)=(50013726420209241621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13593795751791415843/13595000000000000000 : ℝ)*(X 1 0+X 2 0)+(121292444617/271900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (16221/100000 : ℝ)) (c := (13593795751791415843/13595000000000000000 : ℝ)) (alpha := (121292444617/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13593795751791415843/13595000000000000000 : ℝ)*(X 0 1+X 2 1)+(121292444617/271900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (16221/100000 : ℝ)) (c := (13593795751791415843/13595000000000000000 : ℝ)) (alpha := (121292444617/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13593795751791415843/13595000000000000000 : ℝ)*(X 0 2+X 1 2)+(121292444617/271900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (16221/100000 : ℝ)) (c := (13593795751791415843/13595000000000000000 : ℝ)) (alpha := (121292444617/271900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-326918649/2500000000 : ℝ)*X 0 0+(5402466809/10000000000 : ℝ)*X 0 1+(5402466747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050122489/2000000000 : ℝ)*X 1 0+(-380294509/2500000000 : ℝ)*X 1 1+(1350616729/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250612653/10000000000 : ℝ)*X 2 0+(1350616697/2500000000 : ℝ)*X 2 1+(-1521177927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2219422237/5000000000 : ℝ)*X 0 0+(2018716077/5000000000 : ℝ)*X 0 1+(201871619/500000000 : ℝ)*X 0 2+(2219422237/5000000000 : ℝ)*X 1 0+(2018716077/5000000000 : ℝ)*X 1 1+(201871619/500000000 : ℝ)*X 1 2+(2219422237/5000000000 : ℝ)*X 2 0+(2018716077/5000000000 : ℝ)*X 2 1+(201871619/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1818209667/10000000000 : ℝ)*X 0 0+(5216161611/10000000000 : ℝ)*X 0 1+(5216161523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2689049837/5000000000 : ℝ)*X 1 0+(-200209643/1250000000 : ℝ)*X 1 1+(2608080949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2689049943/5000000000 : ℝ)*X 2 0+(5216161411/10000000000 : ℝ)*X 2 1+(-800838757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3881217133/10000000000 : ℝ)*X 0 0+(4315930297/10000000000 : ℝ)*X 0 1+(1078982451/2500000000 : ℝ)*X 0 2+(3881217133/10000000000 : ℝ)*X 1 0+(4315930297/10000000000 : ℝ)*X 1 1+(1078982451/2500000000 : ℝ)*X 1 2+(3881217133/10000000000 : ℝ)*X 2 0+(4315930297/10000000000 : ℝ)*X 2 1+(1078982451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1709144081/10000000000 : ℝ)*X 0 0+(2540828937/5000000000 : ℝ)*X 0 1+(217265461/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((653831963/1250000000 : ℝ)*X 1 0+(-377040799/2500000000 : ℝ)*X 1 1+(2715818331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230655859/10000000000 : ℝ)*X 2 0+(339477287/625000000 : ℝ)*X 2 1+(-1508163079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2261892827/5000000000 : ℝ)*X 0 0+(3993747871/10000000000 : ℝ)*X 0 1+(3993747697/10000000000 : ℝ)*X 0 2+(2261892827/5000000000 : ℝ)*X 1 0+(3993747871/10000000000 : ℝ)*X 1 1+(3993747697/10000000000 : ℝ)*X 1 2+(2261892827/5000000000 : ℝ)*X 2 0+(3993747871/10000000000 : ℝ)*X 2 1+(3993747697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1414712843/10000000000 : ℝ)*X 0 0+(5531994007/10000000000 : ℝ)*X 0 1+(32477523/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695815729/5000000000 : ℝ)*X 1 0+(-1609940459/10000000000 : ℝ)*X 1 1+(5196403611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078326203/2000000000 : ℝ)*X 2 0+(519640377/1000000000 : ℝ)*X 2 1+(-1609940849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((382044999/1000000000 : ℝ)*X 0 0+(4345410847/10000000000 : ℝ)*X 0 1+(4345410881/10000000000 : ℝ)*X 0 2+(382044999/1000000000 : ℝ)*X 1 0+(4345410847/10000000000 : ℝ)*X 1 1+(4345410881/10000000000 : ℝ)*X 1 2+(382044999/1000000000 : ℝ)*X 2 0+(4345410847/10000000000 : ℝ)*X 2 1+(4345410881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65169/100000 : ℝ) ≤ (-442967806619704700077116978129519/679750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (858517/2500000000000 : ℝ)*(upper1) + (403949/1250000000000 : ℝ)*(upper2) + (57714729/100000000000000 : ℝ)*(upper3) + (466819/100000000000000 : ℝ)*(upper5) + (1802382151462311/100000000000000 : ℝ)*(major0) + (1802382151462311/100000000000000 : ℝ)*(major1) + (1802382151462311/100000000000000 : ℝ)*(major2) + (2861489369/100000000000000 : ℝ)*(sp2) + (1125084551/100000000000000 : ℝ)*(sp3) + (2642213339531677/100000000000000 : ℝ)*(sp4) + (1321087510981589/50000000000000 : ℝ)*(sp5) + (660552619510577/25000000000000 : ℝ)*(sp6) + (492135966270037/50000000000000 : ℝ)*(sp7) + (19158784249/50000000000000 : ℝ)*(sp13) + (7874184460997/800000000000 : ℝ)*(f.failure) + (2642213339531677/100000000000000 : ℝ)*(f.sum) + (9734893662007/3398750000000000000000000000 : ℝ)*base66 + (1136877877836643173/1359500000000000000000000000000000 : ℝ)*base67 + (7415824266409356827/1359500000000000000000000000000000 : ℝ)*base70 + (8688633109653143173/1359500000000000000000000000000000 : ℝ)*base71 + (55679950978177/13595000000000000000000000000 : ℝ)*base73 + (4027666311256143173/1359500000000000000000000000000000 : ℝ)*base75 + (6437094268992356827/1359500000000000000000000000000000 : ℝ)*base78 + (4173046899013143173/1359500000000000000000000000000000 : ℝ)*base79 + (1946253568901/1699375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (671309/80000000000000000000 : ℝ)*base90 + (671309/80000000000000000000 : ℝ)*base92 + (671309/80000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58873/100000 : ℝ) ≤ (100052045979634695428411952902073/169937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53930057/100000000000000 : ℝ)*(lower1) + (6170161/100000000000000 : ℝ)*(lower2) + (3327149/25000000000000 : ℝ)*(lower3) + (13479903/25000000000000 : ℝ)*(upper4) + (1999903/12500000000000 : ℝ)*(lower5) + (474011327435963/25000000000000 : ℝ)*(major0) + (474011327435963/25000000000000 : ℝ)*(major1) + (474011327435963/25000000000000 : ℝ)*(major2) + (547408650978989/20000000000000 : ℝ)*(sp0) + (2737042952456997/100000000000000 : ℝ)*(sp1) + (1368521352323023/50000000000000 : ℝ)*(sp2) + (1035422101191083/100000000000000 : ℝ)*(sp3) + (75609487/25000000000000 : ℝ)*(sp5) + (5502489/1000000000000 : ℝ)*(sp6) + (1035422101191083/100000000000000 : ℝ)*(f.failure) + (547408650978989/20000000000000 : ℝ)*(f.sum) + (57755306163047/6797500000000000000000000000 : ℝ)*base65 + (1802685025575586809/339875000000000000000000000000000 : ℝ)*base67 + (1598307526773413191/339875000000000000000000000000000 : ℝ)*base70 + (2361603116929586809/339875000000000000000000000000000 : ℝ)*base71 + (10044292887113/6797500000000000000000000000 : ℝ)*base74 + (872168178116711809/339875000000000000000000000000000 : ℝ)*base75 + (303289928892211809/339875000000000000000000000000000 : ℝ)*base77 + (1015333355839038191/339875000000000000000000000000000 : ℝ)*base80 + (30919468311687/6797500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (40524451/10000000000000000000000 : ℝ)*base90 + (40524451/10000000000000000000000 : ℝ)*base92 + (40524451/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16321/20000 : ℝ) ≤ (554725239152960484868567359118323/679750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170553/800000000000 : ℝ)*(lower3) + (9968303/20000000000000 : ℝ)*(upper4) + (414451/4000000000000 : ℝ)*(lower5) + (1983983735215929/100000000000000 : ℝ)*(major0) + (1983983735215929/100000000000000 : ℝ)*(major1) + (1983983735215929/100000000000000 : ℝ)*(major2) + (237620347/12500000000000 : ℝ)*(sp0) + (22629431567/100000000000000 : ℝ)*(sp1) + (2541190863/10000000000000 : ℝ)*(sp2) + (2571488949/20000000000000 : ℝ)*(sp3) + (914341843789/32000000000 : ℝ)*(sp8) + (1428648766685917/50000000000000 : ℝ)*(sp9) + (2857294750894771/100000000000000 : ℝ)*(sp10) + (541716017806011/50000000000000 : ℝ)*(sp11) + (541722446528383/50000000000000 : ℝ)*(f.failure) + (14286600814017/500000000000 : ℝ)*(f.sum) + (59391133466511/6797500000000000000000000000 : ℝ)*base66 + (18503328337450786853/1359500000000000000000000000000000 : ℝ)*base68 + (3962558589598286853/1359500000000000000000000000000000 : ℝ)*base70 + (18022126573409286853/1359500000000000000000000000000000 : ℝ)*base72 + (67697145953327/13595000000000000000000000000 : ℝ)*base74 + (8764961999636786853/1359500000000000000000000000000000 : ℝ)*base76 + (12788617435375286853/1359500000000000000000000000000000 : ℝ)*base78 + (15678026093211786853/1359500000000000000000000000000000 : ℝ)*base80 + (620400797899/424843750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (19382551/5000000000000000000000 : ℝ)*base90 + (19382551/5000000000000000000000 : ℝ)*base92 + (19382551/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-88443/100000 : ℝ) ≤ (-300587826540953549903761839403431/339875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152472723/100000000000000 : ℝ)*(upper3) + (62164509/50000000000000 : ℝ)*(lower4) + (35339691/100000000000000 : ℝ)*(upper5) + (1014630485195413/50000000000000 : ℝ)*(major0) + (1014630485195413/50000000000000 : ℝ)*(major1) + (1014630485195413/50000000000000 : ℝ)*(major2) + (3340750473/100000000000000 : ℝ)*(sp4) + (18183171793/20000000000000 : ℝ)*(sp5) + (85246290713/100000000000000 : ℝ)*(sp6) + (49480528249/100000000000000 : ℝ)*(sp7) + (372478529844227/12500000000000 : ℝ)*(sp12) + (744935165911331/25000000000000 : ℝ)*(sp13) + (2979746333213577/100000000000000 : ℝ)*(sp14) + (1108121113829003/100000000000000 : ℝ)*(sp15) + (277042648589313/25000000000000 : ℝ)*(f.failure) + (297983157950429/10000000000000 : ℝ)*(f.sum) + (6857791100809/6797500000000000000000000000 : ℝ)*base66 + (3807573061822428159/679750000000000000000000000000000 : ℝ)*base67 + (7806963832274678159/679750000000000000000000000000000 : ℝ)*base69 + (5864359469842428159/679750000000000000000000000000000 : ℝ)*base71 + (1500536940517/3398750000000000000000000000 : ℝ)*base74 + (6482479607093428159/679750000000000000000000000000000 : ℝ)*base75 + (2498937903955178159/679750000000000000000000000000000 : ℝ)*base77 + (2908135598736928159/679750000000000000000000000000000 : ℝ)*base79 + (22704882898169/6797500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (27366761/2500000000000000000000 : ℝ)*base90 + (27366761/2500000000000000000000 : ℝ)*base92 + (27366761/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1673_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58873/100000 : ℝ) else (16321/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88443/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1673_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1673_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58873/100000 : ℝ) else (16321/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88443/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1673_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1673_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1673_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65169/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58873/100000 : ℝ) else (16321/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88443/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1673_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

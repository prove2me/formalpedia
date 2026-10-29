-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:06.030632+00:00
-- url     : https://prove2.me/submissions/1dd01ccb-aedb-4dd9-afad-2e3078bd88ad

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
theorem support_rectangle_w1632_s3_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1650374529/10000000000 : ℝ)*x 0 + (5453069641/10000000000 : ℝ)*x 1 + (5182471337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650374529/10000000000 : ℝ)^4847 ≤ (5093074847339/50000000000000 : ℝ)^3823 := by
    have hnat : (1650374529 : ℕ)^4847*50000000000000^3823 ≤ 5093074847339^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650374529 10000000000 5093074847339 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453069641/10000000000 : ℝ)^4847 ≤ (46355332094073/100000000000000 : ℝ)^3823 := by
    have hnat : (5453069641 : ℕ)^4847*100000000000000^3823 ≤ 46355332094073^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453069641 10000000000 46355332094073 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182471337/10000000000 : ℝ)^4847 ≤ (43458518203541/100000000000000 : ℝ)^3823 := by
    have hnat : (5182471337 : ℕ)^4847*100000000000000^3823 ≤ 43458518203541^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182471337 10000000000 43458518203541 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1650374529/10000000000 : ℝ), (5453069641/10000000000 : ℝ), (5182471337/10000000000 : ℝ)] ![(5093074847339/50000000000000 : ℝ), (46355332094073/100000000000000 : ℝ), (43458518203541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1650374529/10000000000 : ℝ)|^4847 ≤ (5093074847339/50000000000000 : ℝ)^3823
        have hw : |(-1650374529/10000000000 : ℝ)|=(1650374529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453069641/10000000000 : ℝ)|^4847 ≤ (46355332094073/100000000000000 : ℝ)^3823
        have hw : |(5453069641/10000000000 : ℝ)|=(5453069641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182471337/10000000000 : ℝ)|^4847 ≤ (43458518203541/100000000000000 : ℝ)^3823
        have hw : |(5182471337/10000000000 : ℝ)|=(5182471337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350469003/10000000000 : ℝ)*x 0 + (-1789783571/10000000000 : ℝ)*x 1 + (5182471461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350469003/10000000000 : ℝ)^4847 ≤ (11313082321327/25000000000000 : ℝ)^3823 := by
    have hnat : (5350469003 : ℕ)^4847*25000000000000^3823 ≤ 11313082321327^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350469003 10000000000 11313082321327 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789783571/10000000000 : ℝ)^4847 ≤ (1128915117491/10000000000000 : ℝ)^3823 := by
    have hnat : (1789783571 : ℕ)^4847*10000000000000^3823 ≤ 1128915117491^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789783571 10000000000 1128915117491 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182471461/10000000000 : ℝ)^4847 ≤ (10864629880471/25000000000000 : ℝ)^3823 := by
    have hnat : (5182471461 : ℕ)^4847*25000000000000^3823 ≤ 10864629880471^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182471461 10000000000 10864629880471 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350469003/10000000000 : ℝ), (-1789783571/10000000000 : ℝ), (5182471461/10000000000 : ℝ)] ![(11313082321327/25000000000000 : ℝ), (1128915117491/10000000000000 : ℝ), (10864629880471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350469003/10000000000 : ℝ)|^4847 ≤ (11313082321327/25000000000000 : ℝ)^3823
        have hw : |(5350469003/10000000000 : ℝ)|=(5350469003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1789783571/10000000000 : ℝ)|^4847 ≤ (1128915117491/10000000000000 : ℝ)^3823
        have hw : |(-1789783571/10000000000 : ℝ)|=(1789783571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182471461/10000000000 : ℝ)|^4847 ≤ (10864629880471/25000000000000 : ℝ)^3823
        have hw : |(5182471461/10000000000 : ℝ)|=(5182471461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675234627/5000000000 : ℝ)*x 0 + (207298857/400000000 : ℝ)*x 1 + (-1789783283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675234627/5000000000 : ℝ)^4847 ≤ (4525233197679/10000000000000 : ℝ)^3823 := by
    have hnat : (2675234627 : ℕ)^4847*10000000000000^3823 ≤ 4525233197679^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675234627 5000000000 4525233197679 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207298857/400000000 : ℝ)^4847 ≤ (43458519139139/100000000000000 : ℝ)^3823 := by
    have hnat : (207298857 : ℕ)^4847*100000000000000^3823 ≤ 43458519139139^3823*400000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207298857 400000000 43458519139139 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789783283/10000000000 : ℝ)^4847 ≤ (5644574435881/50000000000000 : ℝ)^3823 := by
    have hnat : (1789783283 : ℕ)^4847*50000000000000^3823 ≤ 5644574435881^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789783283 10000000000 5644574435881 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675234627/5000000000 : ℝ), (207298857/400000000 : ℝ), (-1789783283/10000000000 : ℝ)] ![(4525233197679/10000000000000 : ℝ), (43458519139139/100000000000000 : ℝ), (5644574435881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675234627/5000000000 : ℝ)|^4847 ≤ (4525233197679/10000000000000 : ℝ)^3823
        have hw : |(2675234627/5000000000 : ℝ)|=(2675234627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207298857/400000000 : ℝ)|^4847 ≤ (43458519139139/100000000000000 : ℝ)^3823
        have hw : |(207298857/400000000 : ℝ)|=(207298857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789783283/10000000000 : ℝ)|^4847 ≤ (5644574435881/50000000000000 : ℝ)^3823
        have hw : |(-1789783283/10000000000 : ℝ)|=(1789783283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194728757/10000000000 : ℝ)*x 0 + (3862992483/10000000000 : ℝ)*x 1 + (142101487/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194728757/10000000000 : ℝ)^4847 ≤ (259677437121/781250000000 : ℝ)^3823 := by
    have hnat : (4194728757 : ℕ)^4847*781250000000^3823 ≤ 259677437121^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194728757 10000000000 259677437121 781250000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3862992483/10000000000 : ℝ)^4847 ≤ (1197678876681/4000000000000 : ℝ)^3823 := by
    have hnat : (3862992483 : ℕ)^4847*4000000000000^3823 ≤ 1197678876681^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862992483 10000000000 1197678876681 4000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142101487/312500000 : ℝ)^4847 ≤ (18409658057563/50000000000000 : ℝ)^3823 := by
    have hnat : (142101487 : ℕ)^4847*50000000000000^3823 ≤ 18409658057563^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142101487 312500000 18409658057563 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194728757/10000000000 : ℝ), (3862992483/10000000000 : ℝ), (142101487/312500000 : ℝ)] ![(259677437121/781250000000 : ℝ), (1197678876681/4000000000000 : ℝ), (18409658057563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194728757/10000000000 : ℝ)|^4847 ≤ (259677437121/781250000000 : ℝ)^3823
        have hw : |(4194728757/10000000000 : ℝ)|=(4194728757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3862992483/10000000000 : ℝ)|^4847 ≤ (1197678876681/4000000000000 : ℝ)^3823
        have hw : |(3862992483/10000000000 : ℝ)|=(3862992483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142101487/312500000 : ℝ)|^4847 ≤ (18409658057563/50000000000000 : ℝ)^3823
        have hw : |(142101487/312500000 : ℝ)|=(142101487/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1650441791/10000000000 : ℝ)*x 0 + (5184505897/10000000000 : ℝ)*x 1 + (340688349/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650441791/10000000000 : ℝ)^4847 ≤ (1273334504643/12500000000000 : ℝ)^3823 := by
    have hnat : (1650441791 : ℕ)^4847*12500000000000^3823 ≤ 1273334504643^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650441791 10000000000 1273334504643 12500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184505897/10000000000 : ℝ)^4847 ≤ (21740075186099/50000000000000 : ℝ)^3823 := by
    have hnat : (5184505897 : ℕ)^4847*50000000000000^3823 ≤ 21740075186099^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184505897 10000000000 21740075186099 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340688349/625000000 : ℝ)^4847 ≤ (4633317358213/10000000000000 : ℝ)^3823 := by
    have hnat : (340688349 : ℕ)^4847*10000000000000^3823 ≤ 4633317358213^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340688349 625000000 4633317358213 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1650441791/10000000000 : ℝ), (5184505897/10000000000 : ℝ), (340688349/625000000 : ℝ)] ![(1273334504643/12500000000000 : ℝ), (21740075186099/50000000000000 : ℝ), (4633317358213/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1650441791/10000000000 : ℝ)|^4847 ≤ (1273334504643/12500000000000 : ℝ)^3823
        have hw : |(-1650441791/10000000000 : ℝ)|=(1650441791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184505897/10000000000 : ℝ)|^4847 ≤ (21740075186099/50000000000000 : ℝ)^3823
        have hw : |(5184505897/10000000000 : ℝ)|=(5184505897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340688349/625000000 : ℝ)|^4847 ≤ (4633317358213/10000000000000 : ℝ)^3823
        have hw : |(340688349/625000000 : ℝ)|=(340688349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319587031/2500000000 : ℝ)*x 0 + (-152124097/1000000000 : ℝ)*x 1 + (2725506837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319587031/2500000000 : ℝ)^4847 ≤ (22240187567757/50000000000000 : ℝ)^3823 := by
    have hnat : (1319587031 : ℕ)^4847*50000000000000^3823 ≤ 22240187567757^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319587031 2500000000 22240187567757 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152124097/1000000000 : ℝ)^4847 ≤ (1148306287151/12500000000000 : ℝ)^3823 := by
    have hnat : (152124097 : ℕ)^4847*12500000000000^3823 ≤ 1148306287151^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152124097 1000000000 1148306287151 12500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725506837/5000000000 : ℝ)^4847 ≤ (11583293638007/25000000000000 : ℝ)^3823 := by
    have hnat : (2725506837 : ℕ)^4847*25000000000000^3823 ≤ 11583293638007^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725506837 5000000000 11583293638007 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319587031/2500000000 : ℝ), (-152124097/1000000000 : ℝ), (2725506837/5000000000 : ℝ)] ![(22240187567757/50000000000000 : ℝ), (1148306287151/12500000000000 : ℝ), (11583293638007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319587031/2500000000 : ℝ)|^4847 ≤ (22240187567757/50000000000000 : ℝ)^3823
        have hw : |(1319587031/2500000000 : ℝ)|=(1319587031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152124097/1000000000 : ℝ)|^4847 ≤ (1148306287151/12500000000000 : ℝ)^3823
        have hw : |(-152124097/1000000000 : ℝ)|=(152124097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725506837/5000000000 : ℝ)|^4847 ≤ (11583293638007/25000000000000 : ℝ)^3823
        have hw : |(2725506837/5000000000 : ℝ)|=(2725506837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278348183/10000000000 : ℝ)*x 0 + (272550683/500000000 : ℝ)*x 1 + (-1521240907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278348183/10000000000 : ℝ)^4847 ≤ (44480375765877/100000000000000 : ℝ)^3823 := by
    have hnat : (5278348183 : ℕ)^4847*100000000000000^3823 ≤ 44480375765877^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278348183 10000000000 44480375765877 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272550683/500000000 : ℝ)^4847 ≤ (9266634880231/20000000000000 : ℝ)^3823 := by
    have hnat : (272550683 : ℕ)^4847*20000000000000^3823 ≤ 9266634880231^3823*500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272550683 500000000 9266634880231 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521240907/10000000000 : ℝ)^4847 ≤ (4593224907431/50000000000000 : ℝ)^3823 := by
    have hnat : (1521240907 : ℕ)^4847*50000000000000^3823 ≤ 4593224907431^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521240907 10000000000 4593224907431 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278348183/10000000000 : ℝ), (272550683/500000000 : ℝ), (-1521240907/10000000000 : ℝ)] ![(44480375765877/100000000000000 : ℝ), (9266634880231/20000000000000 : ℝ), (4593224907431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278348183/10000000000 : ℝ)|^4847 ≤ (44480375765877/100000000000000 : ℝ)^3823
        have hw : |(5278348183/10000000000 : ℝ)|=(5278348183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272550683/500000000 : ℝ)|^4847 ≤ (9266634880231/20000000000000 : ℝ)^3823
        have hw : |(272550683/500000000 : ℝ)|=(272550683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1521240907/10000000000 : ℝ)|^4847 ≤ (4593224907431/50000000000000 : ℝ)^3823
        have hw : |(-1521240907/10000000000 : ℝ)|=(1521240907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s3_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194898449/10000000000 : ℝ)*x 0 + (4542103079/10000000000 : ℝ)*x 1 + (120880983/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194898449/10000000000 : ℝ)^4847 ≤ (16620208374387/50000000000000 : ℝ)^3823 := by
    have hnat : (4194898449 : ℕ)^4847*50000000000000^3823 ≤ 16620208374387^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194898449 10000000000 16620208374387 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542103079/10000000000 : ℝ)^4847 ≤ (9191627822581/25000000000000 : ℝ)^3823 := by
    have hnat : (4542103079 : ℕ)^4847*25000000000000^3823 ≤ 9191627822581^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542103079 10000000000 9191627822581 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120880983/312500000 : ℝ)^4847 ≤ (29993071936461/100000000000000 : ℝ)^3823 := by
    have hnat : (120880983 : ℕ)^4847*100000000000000^3823 ≤ 29993071936461^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120880983 312500000 29993071936461 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194898449/10000000000 : ℝ), (4542103079/10000000000 : ℝ), (120880983/312500000 : ℝ)] ![(16620208374387/50000000000000 : ℝ), (9191627822581/25000000000000 : ℝ), (29993071936461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194898449/10000000000 : ℝ)|^4847 ≤ (16620208374387/50000000000000 : ℝ)^3823
        have hw : |(4194898449/10000000000 : ℝ)|=(4194898449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542103079/10000000000 : ℝ)|^4847 ≤ (9191627822581/25000000000000 : ℝ)^3823
        have hw : |(4542103079/10000000000 : ℝ)|=(4542103079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120880983/312500000 : ℝ)|^4847 ≤ (29993071936461/100000000000000 : ℝ)^3823
        have hw : |(120880983/312500000 : ℝ)|=(120880983/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2113/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1631/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2051/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2051/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2051/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2051/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2051/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2051/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10477/100000 : ℝ) ^ (4843/1024 : ℝ) ≤ (1161952259931209/50000000000000000000 : ℝ) := by
    have hpowers : (10477/100000 : ℝ)^4843 ≤ (1161952259931209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10477 : ℕ)^4843*50000000000000000000^1024 ≤ 1161952259931209^1024*100000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10477 100000 1161952259931209 50000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10477/100000 : ℝ)) (X := (1161952259931209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2051/12500 : ℝ) ^ (4843/1024 : ℝ) ≤ (19391518396087417/100000000000000000000 : ℝ) := by
    have hpowers : (2051/12500 : ℝ)^4843 ≤ (19391518396087417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2051 : ℕ)^4843*100000000000000000000^1024 ≤ 19391518396087417^1024*12500^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2051 12500 19391518396087417 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2051/12500 : ℝ)) (X := (19391518396087417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001161952259931209/25000000000000000000 : ℝ) ≤ (2000019654219459/2000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (25001161952259931209/25000000000000000000 : ℝ)^1024 ≤ (2000019654219459/2000000000000000 : ℝ)^4843 := by
      have hnat : (25001161952259931209 : ℕ)^1024*2000000000000000^4843 ≤ 2000019654219459^4843*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001161952259931209 25000000000000000000 2000019654219459 2000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000019654219459/2000000000000000 : ℝ)) (X := (25001161952259931209/25000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004343084583189967/20000000000000000000 : ℝ) ≤ (10000459109837351/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (20004343084583189967/20000000000000000000 : ℝ)^1024 ≤ (10000459109837351/10000000000000000 : ℝ)^4843 := by
      have hnat : (20004343084583189967 : ℕ)^1024*10000000000000000^4843 ≤ 10000459109837351^4843*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004343084583189967 20000000000000000000 10000459109837351 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000459109837351/10000000000000000 : ℝ)) (X := (20004343084583189967/20000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019391518396087417/50000000000000000000 : ℝ) ≤ (10000819948577407/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50019391518396087417/50000000000000000000 : ℝ)^1024 ≤ (10000819948577407/10000000000000000 : ℝ)^4843 := by
      have hnat : (50019391518396087417 : ℕ)^1024*10000000000000000^4843 ≤ 10000819948577407^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019391518396087417 50000000000000000000 10000819948577407 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000819948577407/10000000000000000 : ℝ)) (X := (50019391518396087417/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1161952259931209/50000000000000000000 : ℝ) ≤ ((59303021830918923221/59310000000000000000 : ℝ)+2*(45104842507/74137500000000 : ℝ)*(10477/100000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (59303021830918923221/59310000000000000000 : ℝ)+2*(45104842507/74137500000000 : ℝ)*(10477/100000 : ℝ)=(2000019654219459/2000000000000000 : ℝ) by norm_num, show 1+2*(1161952259931209/50000000000000000000 : ℝ)=(25001161952259931209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19391518396087417/100000000000000000000 : ℝ)+(1161952259931209/50000000000000000000 : ℝ) ≤ ((59303021830918923221/59310000000000000000 : ℝ)+(45104842507/74137500000000 : ℝ)*((2051/12500 : ℝ)+(10477/100000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (59303021830918923221/59310000000000000000 : ℝ)+(45104842507/74137500000000 : ℝ)*((2051/12500 : ℝ)+(10477/100000 : ℝ))=(10000459109837351/10000000000000000 : ℝ) by norm_num, show 1+(19391518396087417/100000000000000000000 : ℝ)+(1161952259931209/50000000000000000000 : ℝ)=(20004343084583189967/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19391518396087417/100000000000000000000 : ℝ) ≤ ((59303021830918923221/59310000000000000000 : ℝ)+2*(45104842507/74137500000000 : ℝ)*(2051/12500 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (59303021830918923221/59310000000000000000 : ℝ)+2*(45104842507/74137500000000 : ℝ)*(2051/12500 : ℝ)=(10000819948577407/10000000000000000 : ℝ) by norm_num, show 1+2*(19391518396087417/100000000000000000000 : ℝ)=(50019391518396087417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59303021830918923221/59310000000000000000 : ℝ)*(X 1 0+X 2 0)+(45104842507/74137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (2051/12500 : ℝ)) (c := (59303021830918923221/59310000000000000000 : ℝ)) (alpha := (45104842507/74137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59303021830918923221/59310000000000000000 : ℝ)*(X 0 1+X 2 1)+(45104842507/74137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (2051/12500 : ℝ)) (c := (59303021830918923221/59310000000000000000 : ℝ)) (alpha := (45104842507/74137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59303021830918923221/59310000000000000000 : ℝ)*(X 0 2+X 1 2)+(45104842507/74137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (2051/12500 : ℝ)) (c := (59303021830918923221/59310000000000000000 : ℝ)) (alpha := (45104842507/74137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1650374529/10000000000 : ℝ)*X 0 0+(5453069641/10000000000 : ℝ)*X 0 1+(5182471337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350469003/10000000000 : ℝ)*X 1 0+(-1789783571/10000000000 : ℝ)*X 1 1+(5182471461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675234627/5000000000 : ℝ)*X 2 0+(207298857/400000000 : ℝ)*X 2 1+(-1789783283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194728757/10000000000 : ℝ)*X 0 0+(3862992483/10000000000 : ℝ)*X 0 1+(142101487/312500000 : ℝ)*X 0 2+(4194728757/10000000000 : ℝ)*X 1 0+(3862992483/10000000000 : ℝ)*X 1 1+(142101487/312500000 : ℝ)*X 1 2+(4194728757/10000000000 : ℝ)*X 2 0+(3862992483/10000000000 : ℝ)*X 2 1+(142101487/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1650441791/10000000000 : ℝ)*X 0 0+(5184505897/10000000000 : ℝ)*X 0 1+(340688349/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319587031/2500000000 : ℝ)*X 1 0+(-152124097/1000000000 : ℝ)*X 1 1+(2725506837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278348183/10000000000 : ℝ)*X 2 0+(272550683/500000000 : ℝ)*X 2 1+(-1521240907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4194898449/10000000000 : ℝ)*X 0 0+(4542103079/10000000000 : ℝ)*X 0 1+(120880983/312500000 : ℝ)*X 0 2+(4194898449/10000000000 : ℝ)*X 1 0+(4542103079/10000000000 : ℝ)*X 1 1+(120880983/312500000 : ℝ)*X 1 2+(4194898449/10000000000 : ℝ)*X 2 0+(4542103079/10000000000 : ℝ)*X 2 1+(120880983/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (406607852414313479372941901/123562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90782657/50000000000000 : ℝ)*(base19) + (21782473/10000000000000 : ℝ)*(base23) + (2934281/4000000000000 : ℝ)*(lower2) + (670737/10000000000000 : ℝ)*(upper3) + (77984277/50000000000000 : ℝ)*(upper5) + (644620468046419/25000000000000 : ℝ)*(major0) + (644620468046419/25000000000000 : ℝ)*(major1) + (644620468046419/25000000000000 : ℝ)*(major2) + (1847756971356261/50000000000000 : ℝ)*(sp0) + (3695518474992811/100000000000000 : ℝ)*(sp1) + (739103687746679/20000000000000 : ℝ)*(sp2) + (1461444376057401/100000000000000 : ℝ)*(sp3) + (4713845603/100000000000000 : ℝ)*(sp4) + (602065617/100000000000000 : ℝ)*(sp7) + (730722489061509/50000000000000 : ℝ)*(f.failure) + (5912829850493/160000000000 : ℝ)*(f.sum) + (233934392978111/29655000000000000000000000000 : ℝ)*base65 + (10553120567224145599/1482750000000000000000000000000000 : ℝ)*base67 + (6229015763755895599/1482750000000000000000000000000000 : ℝ)*base69 + (14217397488268145599/1482750000000000000000000000000000 : ℝ)*base71 + (47452428741881/29655000000000000000000000000 : ℝ)*base73 + (1273719705607854401/1482750000000000000000000000000000 : ℝ)*base76 + (19040486840991395599/1482750000000000000000000000000000 : ℝ)*base77 + (11189261267813645599/1482750000000000000000000000000000 : ℝ)*base79 + (71053111211951/29655000000000000000000000000 : ℝ)*base81 + (56762939/5000000000000000000000 : ℝ)*base90 + (56762939/5000000000000000000000 : ℝ)*base92 + (56762939/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2894863958268697212311802671/247125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860053717/50000000000000 : ℝ)*(base19) + (385428957/20000000000000 : ℝ)*(base23) + (69741281/25000000000000 : ℝ)*(upper3) + (31222127/50000000000000 : ℝ)*(lower4) + (55861217/25000000000000 : ℝ)*(upper5) + (654513722398183/25000000000000 : ℝ)*(major0) + (654513722398183/25000000000000 : ℝ)*(major1) + (654513722398183/25000000000000 : ℝ)*(major2) + (20007264577/100000000000000 : ℝ)*(sp1) + (1171594103/5000000000000 : ℝ)*(sp2) + (234514688495057/6250000000000 : ℝ)*(sp4) + (37522132885489/1000000000000 : ℝ)*(sp5) + (1876104828447033/50000000000000 : ℝ)*(sp6) + (370968593198063/25000000000000 : ℝ)*(sp7) + (370968593198063/25000000000000 : ℝ)*(f.failure) + (234514688495057/6250000000000 : ℝ)*(f.sum) + (3522803852797/7413750000000000000000000000 : ℝ)*base66 + (956303236008707443/1482750000000000000000000000000000 : ℝ)*base67 + (4210189884711707443/1482750000000000000000000000000000 : ℝ)*base69 + (10679101990504457443/1482750000000000000000000000000000 : ℝ)*base71 + (24318118334863/29655000000000000000000000000 : ℝ)*base74 + (8784878441771957443/1482750000000000000000000000000000 : ℝ)*base75 + (9162107898530207443/1482750000000000000000000000000000 : ℝ)*base77 + (16214602909689707443/1482750000000000000000000000000000 : ℝ)*base79 + (24527265453571/14827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9333073/2500000000000000000000 : ℝ)*base90 + (9333073/2500000000000000000000 : ℝ)*base92 + (9333073/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1632_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1632_s4_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-825221983/5000000000 : ℝ)*x 0 + (1363179963/2500000000 : ℝ)*x 1 + (2591387407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825221983/5000000000 : ℝ)^4847 ≤ (407467722287/4000000000000 : ℝ)^3823 := by
    have hnat : (825221983 : ℕ)^4847*4000000000000^3823 ≤ 407467722287^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825221983 5000000000 407467722287 4000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363179963/2500000000 : ℝ)^4847 ≤ (11587890548603/25000000000000 : ℝ)^3823 := by
    have hnat : (1363179963 : ℕ)^4847*25000000000000^3823 ≤ 11587890548603^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363179963 2500000000 11587890548603 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591387407/5000000000 : ℝ)^4847 ≤ (10865436183771/25000000000000 : ℝ)^3823 := by
    have hnat : (2591387407 : ℕ)^4847*25000000000000^3823 ≤ 10865436183771^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591387407 5000000000 10865436183771 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-825221983/5000000000 : ℝ), (1363179963/2500000000 : ℝ), (2591387407/5000000000 : ℝ)] ![(407467722287/4000000000000 : ℝ), (11587890548603/25000000000000 : ℝ), (10865436183771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-825221983/5000000000 : ℝ)|^4847 ≤ (407467722287/4000000000000 : ℝ)^3823
        have hw : |(-825221983/5000000000 : ℝ)|=(825221983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363179963/2500000000 : ℝ)|^4847 ≤ (11587890548603/25000000000000 : ℝ)^3823
        have hw : |(1363179963/2500000000 : ℝ)|=(1363179963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591387407/5000000000 : ℝ)|^4847 ≤ (10865436183771/25000000000000 : ℝ)^3823
        have hw : |(2591387407/5000000000 : ℝ)|=(2591387407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675187563/5000000000 : ℝ)*x 0 + (-447376571/2500000000 : ℝ)*x 1 + (5182774707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675187563/5000000000 : ℝ)^4847 ≤ (45251322641121/100000000000000 : ℝ)^3823 := by
    have hnat : (2675187563 : ℕ)^4847*100000000000000^3823 ≤ 45251322641121^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675187563 5000000000 45251322641121 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447376571/2500000000 : ℝ)^4847 ≤ (11286933744543/100000000000000 : ℝ)^3823 := by
    have hnat : (447376571 : ℕ)^4847*100000000000000^3823 ≤ 11286933744543^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447376571 2500000000 11286933744543 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182774707/10000000000 : ℝ)^4847 ≤ (5432717949683/12500000000000 : ℝ)^3823 := by
    have hnat : (5182774707 : ℕ)^4847*12500000000000^3823 ≤ 5432717949683^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182774707 10000000000 5432717949683 12500000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675187563/5000000000 : ℝ), (-447376571/2500000000 : ℝ), (5182774707/10000000000 : ℝ)] ![(45251322641121/100000000000000 : ℝ), (11286933744543/100000000000000 : ℝ), (5432717949683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675187563/5000000000 : ℝ)|^4847 ≤ (45251322641121/100000000000000 : ℝ)^3823
        have hw : |(2675187563/5000000000 : ℝ)|=(2675187563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447376571/2500000000 : ℝ)|^4847 ≤ (11286933744543/100000000000000 : ℝ)^3823
        have hw : |(-447376571/2500000000 : ℝ)|=(447376571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182774707/10000000000 : ℝ)|^4847 ≤ (5432717949683/12500000000000 : ℝ)^3823
        have hw : |(5182774707/10000000000 : ℝ)|=(5182774707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350375027/10000000000 : ℝ)*x 0 + (2591387407/5000000000 : ℝ)*x 1 + (-447376569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350375027/10000000000 : ℝ)^4847 ≤ (9050264315909/20000000000000 : ℝ)^3823 := by
    have hnat : (5350375027 : ℕ)^4847*20000000000000^3823 ≤ 9050264315909^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350375027 10000000000 9050264315909 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591387407/5000000000 : ℝ)^4847 ≤ (10865436183771/25000000000000 : ℝ)^3823 := by
    have hnat : (2591387407 : ℕ)^4847*25000000000000^3823 ≤ 10865436183771^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591387407 5000000000 10865436183771 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447376569/2500000000 : ℝ)^4847 ≤ (1128693368057/10000000000000 : ℝ)^3823 := by
    have hnat : (447376569 : ℕ)^4847*10000000000000^3823 ≤ 1128693368057^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447376569 2500000000 1128693368057 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350375027/10000000000 : ℝ), (2591387407/5000000000 : ℝ), (-447376569/2500000000 : ℝ)] ![(9050264315909/20000000000000 : ℝ), (10865436183771/25000000000000 : ℝ), (1128693368057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350375027/10000000000 : ℝ)|^4847 ≤ (9050264315909/20000000000000 : ℝ)^3823
        have hw : |(5350375027/10000000000 : ℝ)|=(5350375027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591387407/5000000000 : ℝ)|^4847 ≤ (10865436183771/25000000000000 : ℝ)^3823
        have hw : |(2591387407/5000000000 : ℝ)|=(2591387407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447376569/2500000000 : ℝ)|^4847 ≤ (1128693368057/10000000000000 : ℝ)^3823
        have hw : |(-447376569/2500000000 : ℝ)|=(447376569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048693449/2500000000 : ℝ)*x 0 + (3863813953/10000000000 : ℝ)*x 1 + (2273208553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048693449/2500000000 : ℝ)^4847 ≤ (16619582215223/50000000000000 : ℝ)^3823 := by
    have hnat : (1048693449 : ℕ)^4847*50000000000000^3823 ≤ 16619582215223^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048693449 2500000000 16619582215223 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3863813953/10000000000 : ℝ)^4847 ≤ (29950044812561/100000000000000 : ℝ)^3823 := by
    have hnat : (3863813953 : ℕ)^4847*100000000000000^3823 ≤ 29950044812561^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863813953 10000000000 29950044812561 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273208553/5000000000 : ℝ)^4847 ≤ (36810790742947/100000000000000 : ℝ)^3823 := by
    have hnat : (2273208553 : ℕ)^4847*100000000000000^3823 ≤ 36810790742947^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273208553 5000000000 36810790742947 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048693449/2500000000 : ℝ), (3863813953/10000000000 : ℝ), (2273208553/5000000000 : ℝ)] ![(16619582215223/50000000000000 : ℝ), (29950044812561/100000000000000 : ℝ), (36810790742947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048693449/2500000000 : ℝ)|^4847 ≤ (16619582215223/50000000000000 : ℝ)^3823
        have hw : |(1048693449/2500000000 : ℝ)|=(1048693449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3863813953/10000000000 : ℝ)|^4847 ≤ (29950044812561/100000000000000 : ℝ)^3823
        have hw : |(3863813953/10000000000 : ℝ)|=(3863813953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273208553/5000000000 : ℝ)|^4847 ≤ (36810790742947/100000000000000 : ℝ)^3823
        have hw : |(2273208553/5000000000 : ℝ)|=(2273208553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1650510767/10000000000 : ℝ)*x 0 + (648099949/1250000000 : ℝ)*x 1 + (2725336857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650510767/10000000000 : ℝ)^4847 ≤ (2546803949517/25000000000000 : ℝ)^3823 := by
    have hnat : (1650510767 : ℕ)^4847*25000000000000^3823 ≤ 2546803949517^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650510767 10000000000 2546803949517 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648099949/1250000000 : ℝ)^4847 ≤ (21741636615089/50000000000000 : ℝ)^3823 := by
    have hnat : (648099949 : ℕ)^4847*50000000000000^3823 ≤ 21741636615089^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648099949 1250000000 21741636615089 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725336857/5000000000 : ℝ)^4847 ≤ (46329510954979/100000000000000 : ℝ)^3823 := by
    have hnat : (2725336857 : ℕ)^4847*100000000000000^3823 ≤ 46329510954979^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725336857 5000000000 46329510954979 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1650510767/10000000000 : ℝ), (648099949/1250000000 : ℝ), (2725336857/5000000000 : ℝ)] ![(2546803949517/25000000000000 : ℝ), (21741636615089/50000000000000 : ℝ), (46329510954979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1650510767/10000000000 : ℝ)|^4847 ≤ (2546803949517/25000000000000 : ℝ)^3823
        have hw : |(-1650510767/10000000000 : ℝ)|=(1650510767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648099949/1250000000 : ℝ)|^4847 ≤ (21741636615089/50000000000000 : ℝ)^3823
        have hw : |(648099949/1250000000 : ℝ)|=(648099949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725336857/5000000000 : ℝ)|^4847 ≤ (46329510954979/100000000000000 : ℝ)^3823
        have hw : |(2725336857/5000000000 : ℝ)|=(2725336857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278428433/10000000000 : ℝ)*x 0 + (-1521607347/10000000000 : ℝ)*x 1 + (4360539/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278428433/10000000000 : ℝ)^4847 ≤ (22240616584499/50000000000000 : ℝ)^3823 := by
    have hnat : (5278428433 : ℕ)^4847*50000000000000^3823 ≤ 22240616584499^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278428433 10000000000 22240616584499 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521607347/10000000000 : ℝ)^4847 ≤ (9189255476649/100000000000000 : ℝ)^3823 := by
    have hnat : (1521607347 : ℕ)^4847*100000000000000^3823 ≤ 9189255476649^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521607347 10000000000 9189255476649 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4360539/8000000 : ℝ)^4847 ≤ (46329511342931/100000000000000 : ℝ)^3823 := by
    have hnat : (4360539 : ℕ)^4847*100000000000000^3823 ≤ 46329511342931^3823*8000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360539 8000000 46329511342931 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278428433/10000000000 : ℝ), (-1521607347/10000000000 : ℝ), (4360539/8000000 : ℝ)] ![(22240616584499/50000000000000 : ℝ), (9189255476649/100000000000000 : ℝ), (46329511342931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278428433/10000000000 : ℝ)|^4847 ≤ (22240616584499/50000000000000 : ℝ)^3823
        have hw : |(5278428433/10000000000 : ℝ)|=(5278428433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1521607347/10000000000 : ℝ)|^4847 ≤ (9189255476649/100000000000000 : ℝ)^3823
        have hw : |(-1521607347/10000000000 : ℝ)|=(1521607347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4360539/8000000 : ℝ)|^4847 ≤ (46329511342931/100000000000000 : ℝ)^3823
        have hw : |(4360539/8000000 : ℝ)|=(4360539/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055685671/2000000000 : ℝ)*x 0 + (2725336937/5000000000 : ℝ)*x 1 + (-1521607281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055685671/2000000000 : ℝ)^4847 ≤ (2780077020977/6250000000000 : ℝ)^3823 := by
    have hnat : (1055685671 : ℕ)^4847*6250000000000^3823 ≤ 2780077020977^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055685671 2000000000 2780077020977 6250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725336937/5000000000 : ℝ)^4847 ≤ (46329512679213/100000000000000 : ℝ)^3823 := by
    have hnat : (2725336937 : ℕ)^4847*100000000000000^3823 ≤ 46329512679213^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725336937 5000000000 46329512679213 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521607281/10000000000 : ℝ)^4847 ≤ (9189254971301/100000000000000 : ℝ)^3823 := by
    have hnat : (1521607281 : ℕ)^4847*100000000000000^3823 ≤ 9189254971301^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521607281 10000000000 9189254971301 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055685671/2000000000 : ℝ), (2725336937/5000000000 : ℝ), (-1521607281/10000000000 : ℝ)] ![(2780077020977/6250000000000 : ℝ), (46329512679213/100000000000000 : ℝ), (9189254971301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055685671/2000000000 : ℝ)|^4847 ≤ (2780077020977/6250000000000 : ℝ)^3823
        have hw : |(1055685671/2000000000 : ℝ)|=(1055685671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725336937/5000000000 : ℝ)|^4847 ≤ (46329512679213/100000000000000 : ℝ)^3823
        have hw : |(2725336937/5000000000 : ℝ)|=(2725336937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1521607281/10000000000 : ℝ)|^4847 ≤ (9189254971301/100000000000000 : ℝ)^3823
        have hw : |(-1521607281/10000000000 : ℝ)|=(1521607281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s4_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838988483/2000000000 : ℝ)*x 0 + (283831081/625000000 : ℝ)*x 1 + (1934493843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838988483/2000000000 : ℝ)^4847 ≤ (33240858452737/100000000000000 : ℝ)^3823 := by
    have hnat : (838988483 : ℕ)^4847*100000000000000^3823 ≤ 33240858452737^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838988483 2000000000 33240858452737 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283831081/625000000 : ℝ)^4847 ≤ (18379120964773/50000000000000 : ℝ)^3823 := by
    have hnat : (283831081 : ℕ)^4847*50000000000000^3823 ≤ 18379120964773^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283831081 625000000 18379120964773 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934493843/5000000000 : ℝ)^4847 ≤ (1200035984049/4000000000000 : ℝ)^3823 := by
    have hnat : (1934493843 : ℕ)^4847*4000000000000^3823 ≤ 1200035984049^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934493843 5000000000 1200035984049 4000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838988483/2000000000 : ℝ), (283831081/625000000 : ℝ), (1934493843/5000000000 : ℝ)] ![(33240858452737/100000000000000 : ℝ), (18379120964773/50000000000000 : ℝ), (1200035984049/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838988483/2000000000 : ℝ)|^4847 ≤ (33240858452737/100000000000000 : ℝ)^3823
        have hw : |(838988483/2000000000 : ℝ)|=(838988483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283831081/625000000 : ℝ)|^4847 ≤ (18379120964773/50000000000000 : ℝ)^3823
        have hw : |(283831081/625000000 : ℝ)|=(283831081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1934493843/5000000000 : ℝ)|^4847 ≤ (1200035984049/4000000000000 : ℝ)^3823
        have hw : |(1934493843/5000000000 : ℝ)|=(1934493843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10571/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8151/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2113/20000 : ℝ) ^ (4843/1024 : ℝ) ≤ (48353557132973/2000000000000000000 : ℝ) := by
    have hpowers : (2113/20000 : ℝ)^4843 ≤ (48353557132973/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2113 : ℕ)^4843*2000000000000000000^1024 ≤ 48353557132973^1024*20000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2113 20000 48353557132973 2000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2113/20000 : ℝ)) (X := (48353557132973/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1631/10000 : ℝ) ^ (4843/1024 : ℝ) ≤ (18849818004772037/100000000000000000000 : ℝ) := by
    have hpowers : (1631/10000 : ℝ)^4843 ≤ (18849818004772037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1631 : ℕ)^4843*100000000000000000000^1024 ≤ 18849818004772037^1024*10000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1631 10000 18849818004772037 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1631/10000 : ℝ)) (X := (18849818004772037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000048353557132973/1000000000000000000 : ℝ) ≤ (10000102236420717/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (1000048353557132973/1000000000000000000 : ℝ)^1024 ≤ (10000102236420717/10000000000000000 : ℝ)^4843 := by
      have hnat : (1000048353557132973 : ℕ)^1024*10000000000000000^4843 ≤ 10000102236420717^4843*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000048353557132973 1000000000000000000 10000102236420717 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000102236420717/10000000000000000 : ℝ)) (X := (1000048353557132973/1000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021267495861420687/100000000000000000000 : ℝ) ≤ (1250056205063591/1250000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (100021267495861420687/100000000000000000000 : ℝ)^1024 ≤ (1250056205063591/1250000000000000 : ℝ)^4843 := by
      have hnat : (100021267495861420687 : ℕ)^1024*1250000000000000^4843 ≤ 1250056205063591^4843*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021267495861420687 100000000000000000000 1250056205063591 1250000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056205063591/1250000000000000 : ℝ)) (X := (100021267495861420687/100000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018849818004772037/50000000000000000000 : ℝ) ≤ (10000797044596739/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50018849818004772037/50000000000000000000 : ℝ)^1024 ≤ (10000797044596739/10000000000000000 : ℝ)^4843 := by
      have hnat : (50018849818004772037 : ℕ)^1024*10000000000000000^4843 ≤ 10000797044596739^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018849818004772037 50000000000000000000 10000797044596739 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000797044596739/10000000000000000 : ℝ)) (X := (50018849818004772037/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48353557132973/2000000000000000000 : ℝ) ≤ ((11488649339971469347/11490000000000000000 : ℝ)+2*(347404088011/574500000000000 : ℝ)*(2113/20000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (11488649339971469347/11490000000000000000 : ℝ)+2*(347404088011/574500000000000 : ℝ)*(2113/20000 : ℝ)=(10000102236420717/10000000000000000 : ℝ) by norm_num, show 1+2*(48353557132973/2000000000000000000 : ℝ)=(1000048353557132973/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18849818004772037/100000000000000000000 : ℝ)+(48353557132973/2000000000000000000 : ℝ) ≤ ((11488649339971469347/11490000000000000000 : ℝ)+(347404088011/574500000000000 : ℝ)*((1631/10000 : ℝ)+(2113/20000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (11488649339971469347/11490000000000000000 : ℝ)+(347404088011/574500000000000 : ℝ)*((1631/10000 : ℝ)+(2113/20000 : ℝ))=(1250056205063591/1250000000000000 : ℝ) by norm_num, show 1+(18849818004772037/100000000000000000000 : ℝ)+(48353557132973/2000000000000000000 : ℝ)=(100021267495861420687/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18849818004772037/100000000000000000000 : ℝ) ≤ ((11488649339971469347/11490000000000000000 : ℝ)+2*(347404088011/574500000000000 : ℝ)*(1631/10000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (11488649339971469347/11490000000000000000 : ℝ)+2*(347404088011/574500000000000 : ℝ)*(1631/10000 : ℝ)=(10000797044596739/10000000000000000 : ℝ) by norm_num, show 1+2*(18849818004772037/100000000000000000000 : ℝ)=(50018849818004772037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11488649339971469347/11490000000000000000 : ℝ)*(X 1 0+X 2 0)+(347404088011/574500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (11488649339971469347/11490000000000000000 : ℝ)) (alpha := (347404088011/574500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11488649339971469347/11490000000000000000 : ℝ)*(X 0 1+X 2 1)+(347404088011/574500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (11488649339971469347/11490000000000000000 : ℝ)) (alpha := (347404088011/574500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11488649339971469347/11490000000000000000 : ℝ)*(X 0 2+X 1 2)+(347404088011/574500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (11488649339971469347/11490000000000000000 : ℝ)) (alpha := (347404088011/574500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-825221983/5000000000 : ℝ)*X 0 0+(1363179963/2500000000 : ℝ)*X 0 1+(2591387407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675187563/5000000000 : ℝ)*X 1 0+(-447376571/2500000000 : ℝ)*X 1 1+(5182774707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350375027/10000000000 : ℝ)*X 2 0+(2591387407/5000000000 : ℝ)*X 2 1+(-447376569/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048693449/2500000000 : ℝ)*X 0 0+(3863813953/10000000000 : ℝ)*X 0 1+(2273208553/5000000000 : ℝ)*X 0 2+(1048693449/2500000000 : ℝ)*X 1 0+(3863813953/10000000000 : ℝ)*X 1 1+(2273208553/5000000000 : ℝ)*X 1 2+(1048693449/2500000000 : ℝ)*X 2 0+(3863813953/10000000000 : ℝ)*X 2 1+(2273208553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1650510767/10000000000 : ℝ)*X 0 0+(648099949/1250000000 : ℝ)*X 0 1+(2725336857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278428433/10000000000 : ℝ)*X 1 0+(-1521607347/10000000000 : ℝ)*X 1 1+(4360539/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055685671/2000000000 : ℝ)*X 2 0+(2725336937/5000000000 : ℝ)*X 2 1+(-1521607281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838988483/2000000000 : ℝ)*X 0 0+(283831081/625000000 : ℝ)*X 0 1+(1934493843/5000000000 : ℝ)*X 0 2+(838988483/2000000000 : ℝ)*X 1 0+(283831081/625000000 : ℝ)*X 1 1+(1934493843/5000000000 : ℝ)*X 1 2+(838988483/2000000000 : ℝ)*X 2 0+(283831081/625000000 : ℝ)*X 2 1+(1934493843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (820302857024747252363280991/95750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1372527709/100000000000000 : ℝ)*(base19) + (76738389/6250000000000 : ℝ)*(base23) + (20376351/50000000000000 : ℝ)*(lower2) + (49393039/25000000000000 : ℝ)*(upper3) + (69689909/50000000000000 : ℝ)*(upper5) + (1292370881014853/50000000000000 : ℝ)*(major0) + (1292370881014853/50000000000000 : ℝ)*(major1) + (1292370881014853/50000000000000 : ℝ)*(major2) + (370447442273791/10000000000000 : ℝ)*(sp0) + (3704488875856291/100000000000000 : ℝ)*(sp1) + (3704489020569777/100000000000000 : ℝ)*(sp2) + (183123276221233/12500000000000 : ℝ)*(sp3) + (15825646091/100000000000000 : ℝ)*(sp4) + (3390167243/50000000000000 : ℝ)*(sp7) + (29299859802087/2000000000000 : ℝ)*(f.failure) + (57882660131/1562500000 : ℝ)*(f.sum) + (59804613769559/28725000000000000000000000000 : ℝ)*base66 + (1138810398097043003/191500000000000000000000000000000 : ℝ)*base68 + (101251382238043003/191500000000000000000000000000000 : ℝ)*base70 + (277764861487043003/191500000000000000000000000000000 : ℝ)*base72 + (42019014960067/14362500000000000000000000000 : ℝ)*base74 + (1084118101857456997/191500000000000000000000000000000 : ℝ)*base75 + (824447822926543003/191500000000000000000000000000000 : ℝ)*base78 + (706864249133956997/191500000000000000000000000000000 : ℝ)*base79 + (41188937793983/14362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (607577/200000000000000000000 : ℝ)*base90 + (607577/200000000000000000000 : ℝ)*base92 + (607577/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392079445675702937580376491/95750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5354541/1000000000000 : ℝ)*(base19) + (113728091/20000000000000 : ℝ)*(base23) + (140230641/100000000000000 : ℝ)*(lower1) + (28429153/100000000000000 : ℝ)*(upper2) + (23381023/20000000000000 : ℝ)*(upper3) + (28435619/50000000000000 : ℝ)*(upper5) + (1312144855149549/50000000000000 : ℝ)*(major0) + (1312144855149549/50000000000000 : ℝ)*(major1) + (1312144855149549/50000000000000 : ℝ)*(major2) + (102437857/4000000000000 : ℝ)*(sp2) + (1880585554071457/50000000000000 : ℝ)*(sp4) + (1880585286344407/50000000000000 : ℝ)*(sp5) + (1880583989278017/50000000000000 : ℝ)*(sp6) + (1487408175961127/100000000000000 : ℝ)*(sp7) + (1487408175961127/100000000000000 : ℝ)*(f.failure) + (1880585554071457/50000000000000 : ℝ)*(f.sum) + (57525065698499/9575000000000000000000000000 : ℝ)*base66 + (732641282645051501/191500000000000000000000000000000 : ℝ)*base67 + (814652873868051501/191500000000000000000000000000000 : ℝ)*base69 + (576464130384551501/191500000000000000000000000000000 : ℝ)*base71 + (962044901407/299218750000000000000000000 : ℝ)*base74 + (2213891687252051501/191500000000000000000000000000000 : ℝ)*base75 + (471479218490051501/191500000000000000000000000000000 : ℝ)*base77 + (756137455958051501/191500000000000000000000000000000 : ℝ)*base79 + (49003070776537/4787500000000000000000000000 : ℝ)*base82 + (4347417/10000000000000000000000 : ℝ)*base90 + (4347417/10000000000000000000000 : ℝ)*base92 + (4347417/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1632_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1632_s5_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1650450591/10000000000 : ℝ)*x 0 + (5452693607/10000000000 : ℝ)*x 1 + (5182796543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650450591/10000000000 : ℝ)^4847 ≤ (5093372449917/50000000000000 : ℝ)^3823 := by
    have hnat : (1650450591 : ℕ)^4847*50000000000000^3823 ≤ 5093372449917^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650450591 10000000000 5093372449917 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452693607/10000000000 : ℝ)^4847 ≤ (23175639668941/50000000000000 : ℝ)^3823 := by
    have hnat : (5452693607 : ℕ)^4847*50000000000000^3823 ≤ 23175639668941^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452693607 10000000000 23175639668941 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182796543/10000000000 : ℝ)^4847 ≤ (43461975757181/100000000000000 : ℝ)^3823 := by
    have hnat : (5182796543 : ℕ)^4847*100000000000000^3823 ≤ 43461975757181^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182796543 10000000000 43461975757181 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1650450591/10000000000 : ℝ), (5452693607/10000000000 : ℝ), (5182796543/10000000000 : ℝ)] ![(5093372449917/50000000000000 : ℝ), (23175639668941/50000000000000 : ℝ), (43461975757181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1650450591/10000000000 : ℝ)|^4847 ≤ (5093372449917/50000000000000 : ℝ)^3823
        have hw : |(-1650450591/10000000000 : ℝ)|=(1650450591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452693607/10000000000 : ℝ)|^4847 ≤ (23175639668941/50000000000000 : ℝ)^3823
        have hw : |(5452693607/10000000000 : ℝ)|=(5452693607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182796543/10000000000 : ℝ)|^4847 ≤ (43461975757181/100000000000000 : ℝ)^3823
        have hw : |(5182796543/10000000000 : ℝ)|=(5182796543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350367477/10000000000 : ℝ)*x 0 + (-447371521/2500000000 : ℝ)*x 1 + (1036559523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350367477/10000000000 : ℝ)^4847 ≤ (11312810155253/25000000000000 : ℝ)^3823 := by
    have hnat : (5350367477 : ℕ)^4847*25000000000000^3823 ≤ 11312810155253^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350367477 10000000000 11312810155253 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447371521/2500000000 : ℝ)^4847 ≤ (881779079/7812500000 : ℝ)^3823 := by
    have hnat : (447371521 : ℕ)^4847*7812500000^3823 ≤ 881779079^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447371521 2500000000 881779079 7812500000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036559523/2000000000 : ℝ)^4847 ≤ (43461987154661/100000000000000 : ℝ)^3823 := by
    have hnat : (1036559523 : ℕ)^4847*100000000000000^3823 ≤ 43461987154661^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036559523 2000000000 43461987154661 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350367477/10000000000 : ℝ), (-447371521/2500000000 : ℝ), (1036559523/2000000000 : ℝ)] ![(11312810155253/25000000000000 : ℝ), (881779079/7812500000 : ℝ), (43461987154661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350367477/10000000000 : ℝ)|^4847 ≤ (11312810155253/25000000000000 : ℝ)^3823
        have hw : |(5350367477/10000000000 : ℝ)|=(5350367477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447371521/2500000000 : ℝ)|^4847 ≤ (881779079/7812500000 : ℝ)^3823
        have hw : |(-447371521/2500000000 : ℝ)|=(447371521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036559523/2000000000 : ℝ)|^4847 ≤ (43461987154661/100000000000000 : ℝ)^3823
        have hw : |(1036559523/2000000000 : ℝ)|=(1036559523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350367721/10000000000 : ℝ)*x 0 + (323924853/625000000 : ℝ)*x 1 + (-1789485713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350367721/10000000000 : ℝ)^4847 ≤ (45251243237419/100000000000000 : ℝ)^3823 := by
    have hnat : (5350367721 : ℕ)^4847*100000000000000^3823 ≤ 45251243237419^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350367721 10000000000 45251243237419 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323924853/625000000 : ℝ)^4847 ≤ (10865496876379/25000000000000 : ℝ)^3823 := by
    have hnat : (323924853 : ℕ)^4847*25000000000000^3823 ≤ 10865496876379^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323924853 625000000 10865496876379 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789485713/10000000000 : ℝ)^4847 ≤ (2821692311107/25000000000000 : ℝ)^3823 := by
    have hnat : (1789485713 : ℕ)^4847*25000000000000^3823 ≤ 2821692311107^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789485713 10000000000 2821692311107 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350367721/10000000000 : ℝ), (323924853/625000000 : ℝ), (-1789485713/10000000000 : ℝ)] ![(45251243237419/100000000000000 : ℝ), (10865496876379/25000000000000 : ℝ), (2821692311107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350367721/10000000000 : ℝ)|^4847 ≤ (45251243237419/100000000000000 : ℝ)^3823
        have hw : |(5350367721/10000000000 : ℝ)|=(5350367721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323924853/625000000 : ℝ)|^4847 ≤ (10865496876379/25000000000000 : ℝ)^3823
        have hw : |(323924853/625000000 : ℝ)|=(323924853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789485713/10000000000 : ℝ)|^4847 ≤ (2821692311107/25000000000000 : ℝ)^3823
        have hw : |(-1789485713/10000000000 : ℝ)|=(1789485713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524347173/1250000000 : ℝ)*x 0 + (3863874271/10000000000 : ℝ)*x 1 + (568294481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524347173/1250000000 : ℝ)^4847 ≤ (16619600238459/50000000000000 : ℝ)^3823 := by
    have hnat : (524347173 : ℕ)^4847*50000000000000^3823 ≤ 16619600238459^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524347173 1250000000 16619600238459 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3863874271/10000000000 : ℝ)^4847 ≤ (29950637598417/100000000000000 : ℝ)^3823 := by
    have hnat : (3863874271 : ℕ)^4847*100000000000000^3823 ≤ 29950637598417^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863874271 10000000000 29950637598417 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568294481/1250000000 : ℝ)^4847 ≤ (36810161908069/100000000000000 : ℝ)^3823 := by
    have hnat : (568294481 : ℕ)^4847*100000000000000^3823 ≤ 36810161908069^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568294481 1250000000 36810161908069 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524347173/1250000000 : ℝ), (3863874271/10000000000 : ℝ), (568294481/1250000000 : ℝ)] ![(16619600238459/50000000000000 : ℝ), (29950637598417/100000000000000 : ℝ), (36810161908069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524347173/1250000000 : ℝ)|^4847 ≤ (16619600238459/50000000000000 : ℝ)^3823
        have hw : |(524347173/1250000000 : ℝ)|=(524347173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3863874271/10000000000 : ℝ)|^4847 ≤ (29950637598417/100000000000000 : ℝ)^3823
        have hw : |(3863874271/10000000000 : ℝ)|=(3863874271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568294481/1250000000 : ℝ)|^4847 ≤ (36810161908069/100000000000000 : ℝ)^3823
        have hw : |(568294481/1250000000 : ℝ)|=(568294481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103157329/625000000 : ℝ)*x 0 + (1036964231/2000000000 : ℝ)*x 1 + (5450647721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103157329/625000000 : ℝ)^4847 ≤ (10187266639639/100000000000000 : ℝ)^3823 := by
    have hnat : (103157329 : ℕ)^4847*100000000000000^3823 ≤ 10187266639639^3823*625000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103157329 625000000 10187266639639 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036964231/2000000000 : ℝ)^4847 ≤ (21741751255677/50000000000000 : ℝ)^3823 := by
    have hnat : (1036964231 : ℕ)^4847*50000000000000^3823 ≤ 21741751255677^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036964231 2000000000 21741751255677 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450647721/10000000000 : ℝ)^4847 ≤ (11582307710637/25000000000000 : ℝ)^3823 := by
    have hnat : (5450647721 : ℕ)^4847*25000000000000^3823 ≤ 11582307710637^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450647721 10000000000 11582307710637 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103157329/625000000 : ℝ), (1036964231/2000000000 : ℝ), (5450647721/10000000000 : ℝ)] ![(10187266639639/100000000000000 : ℝ), (21741751255677/50000000000000 : ℝ), (11582307710637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103157329/625000000 : ℝ)|^4847 ≤ (10187266639639/100000000000000 : ℝ)^3823
        have hw : |(-103157329/625000000 : ℝ)|=(103157329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036964231/2000000000 : ℝ)|^4847 ≤ (21741751255677/50000000000000 : ℝ)^3823
        have hw : |(1036964231/2000000000 : ℝ)|=(1036964231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450647721/10000000000 : ℝ)|^4847 ≤ (11582307710637/25000000000000 : ℝ)^3823
        have hw : |(5450647721/10000000000 : ℝ)|=(5450647721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659804257/1250000000 : ℝ)*x 0 + (-1521636077/10000000000 : ℝ)*x 1 + (2725323881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659804257/1250000000 : ℝ)^4847 ≤ (4448129324611/10000000000000 : ℝ)^3823 := by
    have hnat : (659804257 : ℕ)^4847*10000000000000^3823 ≤ 4448129324611^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659804257 1250000000 4448129324611 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521636077/10000000000 : ℝ)^4847 ≤ (4594737728319/50000000000000 : ℝ)^3823 := by
    have hnat : (1521636077 : ℕ)^4847*50000000000000^3823 ≤ 4594737728319^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521636077 10000000000 4594737728319 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725323881/5000000000 : ℝ)^4847 ≤ (46329231284383/100000000000000 : ℝ)^3823 := by
    have hnat : (2725323881 : ℕ)^4847*100000000000000^3823 ≤ 46329231284383^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725323881 5000000000 46329231284383 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659804257/1250000000 : ℝ), (-1521636077/10000000000 : ℝ), (2725323881/5000000000 : ℝ)] ![(4448129324611/10000000000000 : ℝ), (4594737728319/50000000000000 : ℝ), (46329231284383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659804257/1250000000 : ℝ)|^4847 ≤ (4448129324611/10000000000000 : ℝ)^3823
        have hw : |(659804257/1250000000 : ℝ)|=(659804257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1521636077/10000000000 : ℝ)|^4847 ≤ (4594737728319/50000000000000 : ℝ)^3823
        have hw : |(-1521636077/10000000000 : ℝ)|=(1521636077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725323881/5000000000 : ℝ)|^4847 ≤ (46329231284383/100000000000000 : ℝ)^3823
        have hw : |(2725323881/5000000000 : ℝ)|=(2725323881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_s5_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33559567/80000000 : ℝ)*x 0 + (4541236561/10000000000 : ℝ)*x 1 + (3869047549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33559567/80000000 : ℝ)^4847 ≤ (33240893213643/100000000000000 : ℝ)^3823 := by
    have hnat : (33559567 : ℕ)^4847*100000000000000^3823 ≤ 33240893213643^3823*80000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33559567 80000000 33240893213643 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4541236561/10000000000 : ℝ)^4847 ≤ (1470304746063/4000000000000 : ℝ)^3823 := by
    have hnat : (4541236561 : ℕ)^4847*4000000000000^3823 ≤ 1470304746063^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541236561 10000000000 1470304746063 4000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3869047549/10000000000 : ℝ)^4847 ≤ (30001488126379/100000000000000 : ℝ)^3823 := by
    have hnat : (3869047549 : ℕ)^4847*100000000000000^3823 ≤ 30001488126379^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3869047549 10000000000 30001488126379 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33559567/80000000 : ℝ), (4541236561/10000000000 : ℝ), (3869047549/10000000000 : ℝ)] ![(33240893213643/100000000000000 : ℝ), (1470304746063/4000000000000 : ℝ), (30001488126379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33559567/80000000 : ℝ)|^4847 ≤ (33240893213643/100000000000000 : ℝ)^3823
        have hw : |(33559567/80000000 : ℝ)|=(33559567/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4541236561/10000000000 : ℝ)|^4847 ≤ (1470304746063/4000000000000 : ℝ)^3823
        have hw : |(4541236561/10000000000 : ℝ)|=(4541236561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3869047549/10000000000 : ℝ)|^4847 ≤ (30001488126379/100000000000000 : ℝ)^3823
        have hw : |(3869047549/10000000000 : ℝ)|=(3869047549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2643/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8151/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10571/100000 : ℝ) ^ (4843/1024 : ℝ) ≤ (606044618534711/25000000000000000000 : ℝ) := by
    have hpowers : (10571/100000 : ℝ)^4843 ≤ (606044618534711/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10571 : ℕ)^4843*25000000000000000000^1024 ≤ 606044618534711^1024*100000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10571 100000 606044618534711 25000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10571/100000 : ℝ)) (X := (606044618534711/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8151/50000 : ℝ) ^ (4843/1024 : ℝ) ≤ (18806130175409311/100000000000000000000 : ℝ) := by
    have hpowers : (8151/50000 : ℝ)^4843 ≤ (18806130175409311/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8151 : ℕ)^4843*100000000000000000000^1024 ≤ 18806130175409311^1024*50000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8151 50000 18806130175409311 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8151/50000 : ℝ)) (X := (18806130175409311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500606044618534711/12500000000000000000 : ℝ) ≤ (5000051255653641/5000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (12500606044618534711/12500000000000000000 : ℝ)^1024 ≤ (5000051255653641/5000000000000000 : ℝ)^4843 := by
      have hnat : (12500606044618534711 : ℕ)^1024*5000000000000000^4843 ≤ 5000051255653641^4843*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500606044618534711 12500000000000000000 5000051255653641 5000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000051255653641/5000000000000000 : ℝ)) (X := (12500606044618534711/12500000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004246061729909631/20000000000000000000 : ℝ) ≤ (2000089770871411/2000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (20004246061729909631/20000000000000000000 : ℝ)^1024 ≤ (2000089770871411/2000000000000000 : ℝ)^4843 := by
      have hnat : (20004246061729909631 : ℕ)^1024*2000000000000000^4843 ≤ 2000089770871411^4843*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004246061729909631 20000000000000000000 2000089770871411 2000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000089770871411/2000000000000000 : ℝ)) (X := (20004246061729909631/20000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018806130175409311/50000000000000000000 : ℝ) ≤ (2500198799351707/2500000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50018806130175409311/50000000000000000000 : ℝ)^1024 ≤ (2500198799351707/2500000000000000 : ℝ)^4843 := by
      have hnat : (50018806130175409311 : ℕ)^1024*2500000000000000^4843 ≤ 2500198799351707^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018806130175409311 50000000000000000000 2500198799351707 2500000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500198799351707/2500000000000000 : ℝ)) (X := (50018806130175409311/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(606044618534711/25000000000000000000 : ℝ) ≤ ((651173467131178777/651250000000000000 : ℝ)+2*(346343049773/573100000000000 : ℝ)*(10571/100000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (651173467131178777/651250000000000000 : ℝ)+2*(346343049773/573100000000000 : ℝ)*(10571/100000 : ℝ)=(5000051255653641/5000000000000000 : ℝ) by norm_num, show 1+2*(606044618534711/25000000000000000000 : ℝ)=(12500606044618534711/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18806130175409311/100000000000000000000 : ℝ)+(606044618534711/25000000000000000000 : ℝ) ≤ ((651173467131178777/651250000000000000 : ℝ)+(346343049773/573100000000000 : ℝ)*((8151/50000 : ℝ)+(10571/100000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (651173467131178777/651250000000000000 : ℝ)+(346343049773/573100000000000 : ℝ)*((8151/50000 : ℝ)+(10571/100000 : ℝ))=(2000089770871411/2000000000000000 : ℝ) by norm_num, show 1+(18806130175409311/100000000000000000000 : ℝ)+(606044618534711/25000000000000000000 : ℝ)=(20004246061729909631/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18806130175409311/100000000000000000000 : ℝ) ≤ ((651173467131178777/651250000000000000 : ℝ)+2*(346343049773/573100000000000 : ℝ)*(8151/50000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (651173467131178777/651250000000000000 : ℝ)+2*(346343049773/573100000000000 : ℝ)*(8151/50000 : ℝ)=(2500198799351707/2500000000000000 : ℝ) by norm_num, show 1+2*(18806130175409311/100000000000000000000 : ℝ)=(50018806130175409311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (651173467131178777/651250000000000000 : ℝ)*(X 1 0+X 2 0)+(346343049773/573100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (651173467131178777/651250000000000000 : ℝ)) (alpha := (346343049773/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (651173467131178777/651250000000000000 : ℝ)*(X 0 1+X 2 1)+(346343049773/573100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (651173467131178777/651250000000000000 : ℝ)) (alpha := (346343049773/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (651173467131178777/651250000000000000 : ℝ)*(X 0 2+X 1 2)+(346343049773/573100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (651173467131178777/651250000000000000 : ℝ)) (alpha := (346343049773/573100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1650450591/10000000000 : ℝ)*X 0 0+(5452693607/10000000000 : ℝ)*X 0 1+(5182796543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350367477/10000000000 : ℝ)*X 1 0+(-447371521/2500000000 : ℝ)*X 1 1+(1036559523/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350367721/10000000000 : ℝ)*X 2 0+(323924853/625000000 : ℝ)*X 2 1+(-1789485713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((524347173/1250000000 : ℝ)*X 0 0+(3863874271/10000000000 : ℝ)*X 0 1+(568294481/1250000000 : ℝ)*X 0 2+(524347173/1250000000 : ℝ)*X 1 0+(3863874271/10000000000 : ℝ)*X 1 1+(568294481/1250000000 : ℝ)*X 1 2+(524347173/1250000000 : ℝ)*X 2 0+(3863874271/10000000000 : ℝ)*X 2 1+(568294481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103157329/625000000 : ℝ)*X 0 0+(1036964231/2000000000 : ℝ)*X 0 1+(5450647721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659804257/1250000000 : ℝ)*X 1 0+(-1521636077/10000000000 : ℝ)*X 1 1+(2725323881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33559567/80000000 : ℝ)*X 0 0+(4541236561/10000000000 : ℝ)*X 0 1+(3869047549/10000000000 : ℝ)*X 0 2+(33559567/80000000 : ℝ)*X 1 0+(4541236561/10000000000 : ℝ)*X 1 1+(3869047549/10000000000 : ℝ)*X 1 2+(33559567/80000000 : ℝ)*X 2 0+(4541236561/10000000000 : ℝ)*X 2 1+(3869047549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137167731295131791551408893/89546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65853537/10000000000000 : ℝ)*(base19) + (172463979/20000000000000 : ℝ)*(base23) + (243931/3125000000000 : ℝ)*(lower2) + (52752859/50000000000000 : ℝ)*(upper5) + (646304499137577/25000000000000 : ℝ)*(major0) + (646304499137577/25000000000000 : ℝ)*(major1) + (646304499137577/25000000000000 : ℝ)*(major2) + (3705142682425533/100000000000000 : ℝ)*(sp0) + (926292174078223/25000000000000 : ℝ)*(sp1) + (1852586083504811/50000000000000 : ℝ)*(sp2) + (183156512892497/12500000000000 : ℝ)*(sp3) + (1896681499/6250000000000 : ℝ)*(sp4) + (734896251/20000000000000 : ℝ)*(sp5) + (540478559/5000000000000 : ℝ)*(sp6) + (366315728177789/25000000000000 : ℝ)*(f.failure) + (926293257332379/25000000000000 : ℝ)*(f.sum) + (97484709434309/28655000000000000000000000000 : ℝ)*base65 + (129837299516992869/179093750000000000000000000000000 : ℝ)*base67 + (7936811912492869/179093750000000000000000000000000 : ℝ)*base69 + (1064617034334149119/179093750000000000000000000000000 : ℝ)*base71 + (76320917083069/28655000000000000000000000000 : ℝ)*base73 + (1056829440309913381/179093750000000000000000000000000 : ℝ)*base76 + (895019247232961619/179093750000000000000000000000000 : ℝ)*base77 + (238257667628475881/179093750000000000000000000000000 : ℝ)*base80 + (15897686005437/14327500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11754819/2500000000000000000000 : ℝ)*base90 + (11754819/2500000000000000000000 : ℝ)*base92 + (11754819/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1632_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1632_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1632_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1632_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1632_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1632_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2051/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

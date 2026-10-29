-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1654_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:17:34.813437+00:00
-- url     : https://prove2.me/submissions/5f1c6688-296a-4e91-adb9-8154608f51f9

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
theorem support_rectangle_w1654_s0_0 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1485663151/10000000000 : ℝ)*x 0 + (5780362811/10000000000 : ℝ)*x 1 + (615533099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1485663151/10000000000 : ℝ)^4935 ≤ (4508975635887/50000000000000 : ℝ)^3911 := by
    have hnat : (1485663151 : ℕ)^4935*50000000000000^3911 ≤ 4508975635887^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485663151 10000000000 4508975635887 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5780362811/10000000000 : ℝ)^4935 ≤ (50075909313679/100000000000000 : ℝ)^3911 := by
    have hnat : (5780362811 : ℕ)^4935*100000000000000^3911 ≤ 50075909313679^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5780362811 10000000000 50075909313679 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615533099/1250000000 : ℝ)^4935 ≤ (20453069698289/50000000000000 : ℝ)^3911 := by
    have hnat : (615533099 : ℕ)^4935*50000000000000^3911 ≤ 20453069698289^3911*1250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615533099 1250000000 20453069698289 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1485663151/10000000000 : ℝ), (5780362811/10000000000 : ℝ), (615533099/1250000000 : ℝ)] ![(4508975635887/50000000000000 : ℝ), (50075909313679/100000000000000 : ℝ), (20453069698289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1485663151/10000000000 : ℝ)|^4935 ≤ (4508975635887/50000000000000 : ℝ)^3911
        have hw : |(-1485663151/10000000000 : ℝ)|=(1485663151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5780362811/10000000000 : ℝ)|^4935 ≤ (50075909313679/100000000000000 : ℝ)^3911
        have hw : |(5780362811/10000000000 : ℝ)|=(5780362811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615533099/1250000000 : ℝ)|^4935 ≤ (20453069698289/50000000000000 : ℝ)^3911
        have hw : |(615533099/1250000000 : ℝ)|=(615533099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_1 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543595383/1000000000 : ℝ)*x 0 + (-1955217939/10000000000 : ℝ)*x 1 + (1231066319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543595383/1000000000 : ℝ)^4935 ≤ (46340868724231/100000000000000 : ℝ)^3911 := by
    have hnat : (543595383 : ℕ)^4935*100000000000000^3911 ≤ 46340868724231^3911*1000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543595383 1000000000 46340868724231 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955217939/10000000000 : ℝ)^4935 ≤ (2550597358637/20000000000000 : ℝ)^3911 := by
    have hnat : (1955217939 : ℕ)^4935*20000000000000^3911 ≤ 2550597358637^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955217939 10000000000 2550597358637 20000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231066319/2500000000 : ℝ)^4935 ≤ (40906144469893/100000000000000 : ℝ)^3911 := by
    have hnat : (1231066319 : ℕ)^4935*100000000000000^3911 ≤ 40906144469893^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231066319 2500000000 40906144469893 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543595383/1000000000 : ℝ), (-1955217939/10000000000 : ℝ), (1231066319/2500000000 : ℝ)] ![(46340868724231/100000000000000 : ℝ), (2550597358637/20000000000000 : ℝ), (40906144469893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543595383/1000000000 : ℝ)|^4935 ≤ (46340868724231/100000000000000 : ℝ)^3911
        have hw : |(543595383/1000000000 : ℝ)|=(543595383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955217939/10000000000 : ℝ)|^4935 ≤ (2550597358637/20000000000000 : ℝ)^3911
        have hw : |(-1955217939/10000000000 : ℝ)|=(1955217939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231066319/2500000000 : ℝ)|^4935 ≤ (40906144469893/100000000000000 : ℝ)^3911
        have hw : |(1231066319/2500000000 : ℝ)|=(1231066319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_2 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5435954723/10000000000 : ℝ)*x 0 + (492426459/1000000000 : ℝ)*x 1 + (-977608823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5435954723/10000000000 : ℝ)^4935 ≤ (11585219582539/25000000000000 : ℝ)^3911 := by
    have hnat : (5435954723 : ℕ)^4935*25000000000000^3911 ≤ 11585219582539^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435954723 10000000000 11585219582539 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492426459/1000000000 : ℝ)^4935 ≤ (40906137279203/100000000000000 : ℝ)^3911 := by
    have hnat : (492426459 : ℕ)^4935*100000000000000^3911 ≤ 40906137279203^3911*1000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492426459 1000000000 40906137279203 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977608823/5000000000 : ℝ)^4935 ≤ (2550596876341/20000000000000 : ℝ)^3911 := by
    have hnat : (977608823 : ℕ)^4935*20000000000000^3911 ≤ 2550596876341^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977608823 5000000000 2550596876341 20000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5435954723/10000000000 : ℝ), (492426459/1000000000 : ℝ), (-977608823/5000000000 : ℝ)] ![(11585219582539/25000000000000 : ℝ), (40906137279203/100000000000000 : ℝ), (2550596876341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5435954723/10000000000 : ℝ)|^4935 ≤ (11585219582539/25000000000000 : ℝ)^3911
        have hw : |(5435954723/10000000000 : ℝ)|=(5435954723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(492426459/1000000000 : ℝ)|^4935 ≤ (40906137279203/100000000000000 : ℝ)^3911
        have hw : |(492426459/1000000000 : ℝ)|=(492426459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-977608823/5000000000 : ℝ)|^4935 ≤ (2550596876341/20000000000000 : ℝ)^3911
        have hw : |(-977608823/5000000000 : ℝ)|=(977608823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_3 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (817749469/2000000000 : ℝ)*x 0 + (3083621177/10000000000 : ℝ)*x 1 + (5309728023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817749469/2000000000 : ℝ)^4935 ≤ (32351517598033/100000000000000 : ℝ)^3911 := by
    have hnat : (817749469 : ℕ)^4935*100000000000000^3911 ≤ 32351517598033^3911*2000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817749469 2000000000 32351517598033 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3083621177/10000000000 : ℝ)^4935 ≤ (2832657829887/12500000000000 : ℝ)^3911 := by
    have hnat : (3083621177 : ℕ)^4935*12500000000000^3911 ≤ 2832657829887^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3083621177 10000000000 2832657829887 12500000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309728023/10000000000 : ℝ)^4935 ≤ (8997443950893/20000000000000 : ℝ)^3911 := by
    have hnat : (5309728023 : ℕ)^4935*20000000000000^3911 ≤ 8997443950893^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309728023 10000000000 8997443950893 20000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(817749469/2000000000 : ℝ), (3083621177/10000000000 : ℝ), (5309728023/10000000000 : ℝ)] ![(32351517598033/100000000000000 : ℝ), (2832657829887/12500000000000 : ℝ), (8997443950893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(817749469/2000000000 : ℝ)|^4935 ≤ (32351517598033/100000000000000 : ℝ)^3911
        have hw : |(817749469/2000000000 : ℝ)|=(817749469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3083621177/10000000000 : ℝ)|^4935 ≤ (2832657829887/12500000000000 : ℝ)^3911
        have hw : |(3083621177/10000000000 : ℝ)|=(3083621177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309728023/10000000000 : ℝ)|^4935 ≤ (8997443950893/20000000000000 : ℝ)^3911
        have hw : |(5309728023/10000000000 : ℝ)|=(5309728023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_4 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1487914351/10000000000 : ℝ)*x 0 + (4945455131/10000000000 : ℝ)*x 1 + (1151688681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1487914351/10000000000 : ℝ)^4935 ≤ (180703944389/2000000000000 : ℝ)^3911 := by
    have hnat : (1487914351 : ℕ)^4935*2000000000000^3911 ≤ 180703944389^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487914351 10000000000 180703944389 2000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4945455131/10000000000 : ℝ)^4935 ≤ (10282095673759/25000000000000 : ℝ)^3911 := by
    have hnat : (4945455131 : ℕ)^4935*25000000000000^3911 ≤ 10282095673759^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945455131 10000000000 10282095673759 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151688681/2000000000 : ℝ)^4935 ≤ (49836420067437/100000000000000 : ℝ)^3911 := by
    have hnat : (1151688681 : ℕ)^4935*100000000000000^3911 ≤ 49836420067437^3911*2000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151688681 2000000000 49836420067437 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1487914351/10000000000 : ℝ), (4945455131/10000000000 : ℝ), (1151688681/2000000000 : ℝ)] ![(180703944389/2000000000000 : ℝ), (10282095673759/25000000000000 : ℝ), (49836420067437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1487914351/10000000000 : ℝ)|^4935 ≤ (180703944389/2000000000000 : ℝ)^3911
        have hw : |(-1487914351/10000000000 : ℝ)|=(1487914351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4945455131/10000000000 : ℝ)|^4935 ≤ (10282095673759/25000000000000 : ℝ)^3911
        have hw : |(4945455131/10000000000 : ℝ)|=(4945455131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151688681/2000000000 : ℝ)|^4935 ≤ (49836420067437/100000000000000 : ℝ)^3911
        have hw : |(1151688681/2000000000 : ℝ)|=(1151688681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_5 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202375051/10000000000 : ℝ)*x 0 + (-1121040921/10000000000 : ℝ)*x 1 + (1151688311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202375051/10000000000 : ℝ)^4935 ≤ (43842567719733/100000000000000 : ℝ)^3911 := by
    have hnat : (5202375051 : ℕ)^4935*100000000000000^3911 ≤ 43842567719733^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202375051 10000000000 43842567719733 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121040921/10000000000 : ℝ)^4935 ≤ (632103240561/10000000000000 : ℝ)^3911 := by
    have hnat : (1121040921 : ℕ)^4935*10000000000000^3911 ≤ 632103240561^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121040921 10000000000 632103240561 10000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151688311/2000000000 : ℝ)^4935 ≤ (49836399864581/100000000000000 : ℝ)^3911 := by
    have hnat : (1151688311 : ℕ)^4935*100000000000000^3911 ≤ 49836399864581^3911*2000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151688311 2000000000 49836399864581 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202375051/10000000000 : ℝ), (-1121040921/10000000000 : ℝ), (1151688311/2000000000 : ℝ)] ![(43842567719733/100000000000000 : ℝ), (632103240561/10000000000000 : ℝ), (49836399864581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202375051/10000000000 : ℝ)|^4935 ≤ (43842567719733/100000000000000 : ℝ)^3911
        have hw : |(5202375051/10000000000 : ℝ)|=(5202375051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121040921/10000000000 : ℝ)|^4935 ≤ (632103240561/10000000000000 : ℝ)^3911
        have hw : |(-1121040921/10000000000 : ℝ)|=(1121040921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151688311/2000000000 : ℝ)|^4935 ≤ (49836399864581/100000000000000 : ℝ)^3911
        have hw : |(1151688311/2000000000 : ℝ)|=(1151688311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_6 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208094971/400000000 : ℝ)*x 0 + (719805269/1250000000 : ℝ)*x 1 + (-1121041163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208094971/400000000 : ℝ)^4935 ≤ (21921279733903/50000000000000 : ℝ)^3911 := by
    have hnat : (208094971 : ℕ)^4935*50000000000000^3911 ≤ 21921279733903^3911*400000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208094971 400000000 21921279733903 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719805269/1250000000 : ℝ)^4935 ≤ (49836406384097/100000000000000 : ℝ)^3911 := by
    have hnat : (719805269 : ℕ)^4935*100000000000000^3911 ≤ 49836406384097^3911*1250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719805269 1250000000 49836406384097 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121041163/10000000000 : ℝ)^4935 ≤ (1580258531851/25000000000000 : ℝ)^3911 := by
    have hnat : (1121041163 : ℕ)^4935*25000000000000^3911 ≤ 1580258531851^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121041163 10000000000 1580258531851 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208094971/400000000 : ℝ), (719805269/1250000000 : ℝ), (-1121041163/10000000000 : ℝ)] ![(21921279733903/50000000000000 : ℝ), (49836406384097/100000000000000 : ℝ), (1580258531851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208094971/400000000 : ℝ)|^4935 ≤ (21921279733903/50000000000000 : ℝ)^3911
        have hw : |(208094971/400000000 : ℝ)|=(208094971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(719805269/1250000000 : ℝ)|^4935 ≤ (49836406384097/100000000000000 : ℝ)^3911
        have hw : |(719805269/1250000000 : ℝ)|=(719805269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121041163/10000000000 : ℝ)|^4935 ≤ (1580258531851/25000000000000 : ℝ)^3911
        have hw : |(-1121041163/10000000000 : ℝ)|=(1121041163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s0_7 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51182499/125000000 : ℝ)*x 0 + (5254627593/10000000000 : ℝ)*x 1 + (1570310247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51182499/125000000 : ℝ)^4935 ≤ (32409960538221/100000000000000 : ℝ)^3911 := by
    have hnat : (51182499 : ℕ)^4935*100000000000000^3911 ≤ 32409960538221^3911*125000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51182499 125000000 32409960538221 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254627593/10000000000 : ℝ)^4935 ≤ (22199473120769/50000000000000 : ℝ)^3911 := by
    have hnat : (5254627593 : ℕ)^4935*50000000000000^3911 ≤ 22199473120769^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254627593 10000000000 22199473120769 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570310247/5000000000 : ℝ)^4935 ≤ (11595546603379/50000000000000 : ℝ)^3911 := by
    have hnat : (1570310247 : ℕ)^4935*50000000000000^3911 ≤ 11595546603379^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570310247 5000000000 11595546603379 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51182499/125000000 : ℝ), (5254627593/10000000000 : ℝ), (1570310247/5000000000 : ℝ)] ![(32409960538221/100000000000000 : ℝ), (22199473120769/50000000000000 : ℝ), (11595546603379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51182499/125000000 : ℝ)|^4935 ≤ (32409960538221/100000000000000 : ℝ)^3911
        have hw : |(51182499/125000000 : ℝ)|=(51182499/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254627593/10000000000 : ℝ)|^4935 ≤ (22199473120769/50000000000000 : ℝ)^3911
        have hw : |(5254627593/10000000000 : ℝ)|=(5254627593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570310247/5000000000 : ℝ)|^4935 ≤ (11595546603379/50000000000000 : ℝ)^3911
        have hw : |(1570310247/5000000000 : ℝ)|=(1570310247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1654_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4921/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2909/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4931/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4931 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4931*1^1024 ≤ 0^1024*1^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4931/1024 : ℝ) ≤ (37896394268288653/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4931 ≤ (37896394268288653/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4931*3125000000000000000^1024 ≤ 37896394268288653^1024*5^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 37896394268288653 3125000000000000000 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (37896394268288653/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4931 := by
      have hnat : (1 : ℕ)^1024*1^4931 ≤ 1^4931*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3162896394268288653/3125000000000000000 : ℝ) ≤ (10025063192737307/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (3162896394268288653/3125000000000000000 : ℝ)^1024 ≤ (10025063192737307/10000000000000000 : ℝ)^4931 := by
      have hnat : (3162896394268288653 : ℕ)^1024*10000000000000000^4931 ≤ 10025063192737307^4931*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3162896394268288653 3125000000000000000 10025063192737307 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025063192737307/10000000000000000 : ℝ)) (X := (3162896394268288653/3125000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1600396394268288653/1562500000000000000 : ℝ) ≤ (5025063192737307/5000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (1600396394268288653/1562500000000000000 : ℝ)^1024 ≤ (5025063192737307/5000000000000000 : ℝ)^4931 := by
      have hnat : (1600396394268288653 : ℕ)^1024*5000000000000000^4931 ≤ 5025063192737307^4931*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1600396394268288653 1562500000000000000 5025063192737307 5000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025063192737307/5000000000000000 : ℝ)) (X := (1600396394268288653/1562500000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25063192737307/4000000000000000 : ℝ)*(0 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25063192737307/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37896394268288653/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25063192737307/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4931/1024 : ℝ) := by
    rw [show (1 : ℝ)+(25063192737307/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10025063192737307/10000000000000000 : ℝ) by norm_num, show 1+(37896394268288653/3125000000000000000 : ℝ)+(0 : ℝ)=(3162896394268288653/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37896394268288653/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25063192737307/4000000000000000 : ℝ)*(2/5 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25063192737307/4000000000000000 : ℝ)*(2/5 : ℝ)=(5025063192737307/5000000000000000 : ℝ) by norm_num, show 1+2*(37896394268288653/3125000000000000000 : ℝ)=(1600396394268288653/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25063192737307/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25063192737307/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25063192737307/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25063192737307/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25063192737307/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25063192737307/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1485663151/10000000000 : ℝ)*X 0 0+(5780362811/10000000000 : ℝ)*X 0 1+(615533099/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((543595383/1000000000 : ℝ)*X 1 0+(-1955217939/10000000000 : ℝ)*X 1 1+(1231066319/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5435954723/10000000000 : ℝ)*X 2 0+(492426459/1000000000 : ℝ)*X 2 1+(-977608823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((817749469/2000000000 : ℝ)*X 0 0+(3083621177/10000000000 : ℝ)*X 0 1+(5309728023/10000000000 : ℝ)*X 0 2+(817749469/2000000000 : ℝ)*X 1 0+(3083621177/10000000000 : ℝ)*X 1 1+(5309728023/10000000000 : ℝ)*X 1 2+(817749469/2000000000 : ℝ)*X 2 0+(3083621177/10000000000 : ℝ)*X 2 1+(5309728023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1487914351/10000000000 : ℝ)*X 0 0+(4945455131/10000000000 : ℝ)*X 0 1+(1151688681/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202375051/10000000000 : ℝ)*X 1 0+(-1121040921/10000000000 : ℝ)*X 1 1+(1151688311/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((208094971/400000000 : ℝ)*X 2 0+(719805269/1250000000 : ℝ)*X 2 1+(-1121041163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((51182499/125000000 : ℝ)*X 0 0+(5254627593/10000000000 : ℝ)*X 0 1+(1570310247/5000000000 : ℝ)*X 0 2+(51182499/125000000 : ℝ)*X 1 0+(5254627593/10000000000 : ℝ)*X 1 1+(1570310247/5000000000 : ℝ)*X 1 2+(51182499/125000000 : ℝ)*X 2 0+(5254627593/10000000000 : ℝ)*X 2 1+(1570310247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544648217190932023124493/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126651981/100000000000000 : ℝ)*(base1) + (101754147/10000000000000 : ℝ)*(base19) + (120943269/10000000000000 : ℝ)*(base23) + (27222597/50000000000000 : ℝ)*(upper3) + (25349721/12500000000000 : ℝ)*(upper5) + (808659128259133/100000000000000 : ℝ)*(major0) + (808659128259133/100000000000000 : ℝ)*(major1) + (808659128259133/100000000000000 : ℝ)*(major2) + (584047102713559/50000000000000 : ℝ)*(sp0) + (146012316262439/12500000000000 : ℝ)*(sp1) + (1168098338208291/100000000000000 : ℝ)*(sp2) + (449216697722907/100000000000000 : ℝ)*(sp3) + (1367216461/25000000000000 : ℝ)*(sp4) + (425738247/25000000000000 : ℝ)*(sp7) + (112304631831969/25000000000000 : ℝ)*(f.failure) + (1168099547640981/100000000000000 : ℝ)*(f.sum) + (199924529974831/200000000000000000000000000000 : ℝ)*base65 + (387329581425169/400000000000000000000000000000 : ℝ)*base68 + (1375686991025169/400000000000000000000000000000 : ℝ)*base70 + (491197641425169/400000000000000000000000000000 : ℝ)*base72 + (30438838425169/200000000000000000000000000000 : ℝ)*base74 + (2601749805425169/400000000000000000000000000000 : ℝ)*base76 + (196131385374831/400000000000000000000000000000 : ℝ)*base77 + (1533805847374831/400000000000000000000000000000 : ℝ)*base79 + (174299296825169/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10522067/2500000000000000000000 : ℝ)*base89 + (10522067/2500000000000000000000 : ℝ)*base91 + (10522067/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1345981063954979359120191/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (471370519/50000000000000 : ℝ)*(base19) + (747160347/100000000000000 : ℝ)*(base23) + (55195489/100000000000000 : ℝ)*(base32) + (7459573/10000000000000 : ℝ)*(upper3) + (11886481/25000000000000 : ℝ)*(upper5) + (851532432702129/100000000000000 : ℝ)*(major0) + (851532432702129/100000000000000 : ℝ)*(major1) + (851532432702129/100000000000000 : ℝ)*(major2) + (146428769/12500000000000 : ℝ)*(sp1) + (901785527/100000000000000 : ℝ)*(sp2) + (1230029548755433/100000000000000 : ℝ)*(sp4) + (1230027434584243/100000000000000 : ℝ)*(sp5) + (1230027899809559/100000000000000 : ℝ)*(sp6) + (118258759280789/25000000000000 : ℝ)*(sp7) + (94607018463729/20000000000000 : ℝ)*(f.failure) + (1230029548755433/100000000000000 : ℝ)*(f.sum) + (366271630773397/200000000000000000000000000000 : ℝ)*base66 + (899034015773397/400000000000000000000000000000 : ℝ)*base68 + (2300362705026603/400000000000000000000000000000 : ℝ)*base69 + (53073647426603/400000000000000000000000000000 : ℝ)*base71 + (709933718773397/200000000000000000000000000000 : ℝ)*base74 + (2030102524226603/400000000000000000000000000000 : ℝ)*base75 + (18439570226603/400000000000000000000000000000 : ℝ)*base77 + (1139068714226603/400000000000000000000000000000 : ℝ)*base79 + (613719575626603/200000000000000000000000000000 : ℝ)*base81 + (4383747/2000000000000000000000 : ℝ)*base89 + (4383747/2000000000000000000000 : ℝ)*base91 + (4383747/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1654_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2909/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1654_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1654_s1_0 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99368809/625000000 : ℝ)*x 0 + (1373325213/2500000000 : ℝ)*x 1 + (2571770439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99368809/625000000 : ℝ)^4935 ≤ (9823546152339/100000000000000 : ℝ)^3911 := by
    have hnat : (99368809 : ℕ)^4935*100000000000000^3911 ≤ 9823546152339^3911*625000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99368809 625000000 9823546152339 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373325213/2500000000 : ℝ)^4935 ≤ (46958595539779/100000000000000 : ℝ)^3911 := by
    have hnat : (1373325213 : ℕ)^4935*100000000000000^3911 ≤ 46958595539779^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373325213 2500000000 46958595539779 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571770439/5000000000 : ℝ)^4935 ≤ (10804464571327/25000000000000 : ℝ)^3911 := by
    have hnat : (2571770439 : ℕ)^4935*25000000000000^3911 ≤ 10804464571327^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571770439 5000000000 10804464571327 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99368809/625000000 : ℝ), (1373325213/2500000000 : ℝ), (2571770439/5000000000 : ℝ)] ![(9823546152339/100000000000000 : ℝ), (46958595539779/100000000000000 : ℝ), (10804464571327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99368809/625000000 : ℝ)|^4935 ≤ (9823546152339/100000000000000 : ℝ)^3911
        have hw : |(-99368809/625000000 : ℝ)|=(99368809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373325213/2500000000 : ℝ)|^4935 ≤ (46958595539779/100000000000000 : ℝ)^3911
        have hw : |(1373325213/2500000000 : ℝ)|=(1373325213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2571770439/5000000000 : ℝ)|^4935 ≤ (10804464571327/25000000000000 : ℝ)^3911
        have hw : |(2571770439/5000000000 : ℝ)|=(2571770439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_1 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679799413/5000000000 : ℝ)*x 0 + (-1771640077/10000000000 : ℝ)*x 1 + (1285885181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679799413/5000000000 : ℝ)^4935 ≤ (45521039979313/100000000000000 : ℝ)^3911 := by
    have hnat : (2679799413 : ℕ)^4935*100000000000000^3911 ≤ 45521039979313^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679799413 5000000000 45521039979313 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771640077/10000000000 : ℝ)^4935 ≤ (11261103350557/100000000000000 : ℝ)^3911 := by
    have hnat : (1771640077 : ℕ)^4935*100000000000000^3911 ≤ 11261103350557^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771640077 10000000000 11261103350557 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285885181/2500000000 : ℝ)^4935 ≤ (43217856652553/100000000000000 : ℝ)^3911 := by
    have hnat : (1285885181 : ℕ)^4935*100000000000000^3911 ≤ 43217856652553^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285885181 2500000000 43217856652553 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679799413/5000000000 : ℝ), (-1771640077/10000000000 : ℝ), (1285885181/2500000000 : ℝ)] ![(45521039979313/100000000000000 : ℝ), (11261103350557/100000000000000 : ℝ), (43217856652553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679799413/5000000000 : ℝ)|^4935 ≤ (45521039979313/100000000000000 : ℝ)^3911
        have hw : |(2679799413/5000000000 : ℝ)|=(2679799413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1771640077/10000000000 : ℝ)|^4935 ≤ (11261103350557/100000000000000 : ℝ)^3911
        have hw : |(-1771640077/10000000000 : ℝ)|=(1771640077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285885181/2500000000 : ℝ)|^4935 ≤ (43217856652553/100000000000000 : ℝ)^3911
        have hw : |(1285885181/2500000000 : ℝ)|=(1285885181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_2 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133989957/250000000 : ℝ)*x 0 + (5143541313/10000000000 : ℝ)*x 1 + (-442910007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133989957/250000000 : ℝ)^4935 ≤ (45521034127751/100000000000000 : ℝ)^3911 := by
    have hnat : (133989957 : ℕ)^4935*100000000000000^3911 ≤ 45521034127751^3911*250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133989957 250000000 45521034127751 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143541313/10000000000 : ℝ)^4935 ≤ (1350558215541/3125000000000 : ℝ)^3911 := by
    have hnat : (5143541313 : ℕ)^4935*3125000000000^3911 ≤ 1350558215541^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143541313 10000000000 1350558215541 3125000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442910007/2500000000 : ℝ)^4935 ≤ (225222059151/2000000000000 : ℝ)^3911 := by
    have hnat : (442910007 : ℕ)^4935*2000000000000^3911 ≤ 225222059151^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442910007 2500000000 225222059151 2000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133989957/250000000 : ℝ), (5143541313/10000000000 : ℝ), (-442910007/2500000000 : ℝ)] ![(45521034127751/100000000000000 : ℝ), (1350558215541/3125000000000 : ℝ), (225222059151/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133989957/250000000 : ℝ)|^4935 ≤ (45521034127751/100000000000000 : ℝ)^3911
        have hw : |(133989957/250000000 : ℝ)|=(133989957/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143541313/10000000000 : ℝ)|^4935 ≤ (1350558215541/3125000000000 : ℝ)^3911
        have hw : |(5143541313/10000000000 : ℝ)|=(5143541313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442910007/2500000000 : ℝ)|^4935 ≤ (225222059151/2000000000000 : ℝ)^3911
        have hw : |(-442910007/2500000000 : ℝ)|=(442910007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_3 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170571633/10000000000 : ℝ)*x 0 + (1866834693/5000000000 : ℝ)*x 1 + (4643147833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170571633/10000000000 : ℝ)^4935 ≤ (33170579473663/100000000000000 : ℝ)^3911 := by
    have hnat : (4170571633 : ℕ)^4935*100000000000000^3911 ≤ 33170579473663^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170571633 10000000000 33170579473663 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866834693/5000000000 : ℝ)^4935 ≤ (14423812529457/50000000000000 : ℝ)^3911 := by
    have hnat : (1866834693 : ℕ)^4935*50000000000000^3911 ≤ 14423812529457^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866834693 5000000000 14423812529457 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4643147833/10000000000 : ℝ)^4935 ≤ (2373862215653/6250000000000 : ℝ)^3911 := by
    have hnat : (4643147833 : ℕ)^4935*6250000000000^3911 ≤ 2373862215653^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643147833 10000000000 2373862215653 6250000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170571633/10000000000 : ℝ), (1866834693/5000000000 : ℝ), (4643147833/10000000000 : ℝ)] ![(33170579473663/100000000000000 : ℝ), (14423812529457/50000000000000 : ℝ), (2373862215653/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170571633/10000000000 : ℝ)|^4935 ≤ (33170579473663/100000000000000 : ℝ)^3911
        have hw : |(4170571633/10000000000 : ℝ)|=(4170571633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866834693/5000000000 : ℝ)|^4935 ≤ (14423812529457/50000000000000 : ℝ)^3911
        have hw : |(1866834693/5000000000 : ℝ)|=(1866834693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4643147833/10000000000 : ℝ)|^4935 ≤ (2373862215653/6250000000000 : ℝ)^3911
        have hw : |(4643147833/10000000000 : ℝ)|=(4643147833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_4 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590051777/10000000000 : ℝ)*x 0 + (5147067939/10000000000 : ℝ)*x 1 + (2744862193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590051777/10000000000 : ℝ)^4935 ≤ (9824722130689/100000000000000 : ℝ)^3911 := by
    have hnat : (1590051777 : ℕ)^4935*100000000000000^3911 ≤ 9824722130689^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590051777 10000000000 9824722130689 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5147067939/10000000000 : ℝ)^4935 ≤ (43255256626173/100000000000000 : ℝ)^3911 := by
    have hnat : (5147067939 : ℕ)^4935*100000000000000^3911 ≤ 43255256626173^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147067939 10000000000 43255256626173 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744862193/5000000000 : ℝ)^4935 ≤ (4692002123273/10000000000000 : ℝ)^3911 := by
    have hnat : (2744862193 : ℕ)^4935*10000000000000^3911 ≤ 4692002123273^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744862193 5000000000 4692002123273 10000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590051777/10000000000 : ℝ), (5147067939/10000000000 : ℝ), (2744862193/5000000000 : ℝ)] ![(9824722130689/100000000000000 : ℝ), (43255256626173/100000000000000 : ℝ), (4692002123273/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590051777/10000000000 : ℝ)|^4935 ≤ (9824722130689/100000000000000 : ℝ)^3911
        have hw : |(-1590051777/10000000000 : ℝ)|=(1590051777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5147067939/10000000000 : ℝ)|^4935 ≤ (43255256626173/100000000000000 : ℝ)^3911
        have hw : |(5147067939/10000000000 : ℝ)|=(5147067939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744862193/5000000000 : ℝ)|^4935 ≤ (4692002123273/10000000000000 : ℝ)^3911
        have hw : |(2744862193/5000000000 : ℝ)|=(2744862193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_5 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266043393/10000000000 : ℝ)*x 0 + (-712728287/5000000000 : ℝ)*x 1 + (686215553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266043393/10000000000 : ℝ)^4935 ≤ (278254335527/625000000000 : ℝ)^3911 := by
    have hnat : (5266043393 : ℕ)^4935*625000000000^3911 ≤ 278254335527^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266043393 10000000000 278254335527 625000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712728287/5000000000 : ℝ)^4935 ≤ (4279642332459/50000000000000 : ℝ)^3911 := by
    have hnat : (712728287 : ℕ)^4935*50000000000000^3911 ≤ 4279642332459^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712728287 5000000000 4279642332459 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686215553/1250000000 : ℝ)^4935 ≤ (11730005410637/25000000000000 : ℝ)^3911 := by
    have hnat : (686215553 : ℕ)^4935*25000000000000^3911 ≤ 11730005410637^3911*1250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686215553 1250000000 11730005410637 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266043393/10000000000 : ℝ), (-712728287/5000000000 : ℝ), (686215553/1250000000 : ℝ)] ![(278254335527/625000000000 : ℝ), (4279642332459/50000000000000 : ℝ), (11730005410637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266043393/10000000000 : ℝ)|^4935 ≤ (278254335527/625000000000 : ℝ)^3911
        have hw : |(5266043393/10000000000 : ℝ)|=(5266043393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-712728287/5000000000 : ℝ)|^4935 ≤ (4279642332459/50000000000000 : ℝ)^3911
        have hw : |(-712728287/5000000000 : ℝ)|=(712728287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686215553/1250000000 : ℝ)|^4935 ≤ (11730005410637/25000000000000 : ℝ)^3911
        have hw : |(686215553/1250000000 : ℝ)|=(686215553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_6 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633021587/5000000000 : ℝ)*x 0 + (5489724723/10000000000 : ℝ)*x 1 + (-178182057/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633021587/5000000000 : ℝ)^4935 ≤ (44520691348061/100000000000000 : ℝ)^3911 := by
    have hnat : (2633021587 : ℕ)^4935*100000000000000^3911 ≤ 44520691348061^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633021587 5000000000 44520691348061 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489724723/10000000000 : ℝ)^4935 ≤ (9384004973433/20000000000000 : ℝ)^3911 := by
    have hnat : (5489724723 : ℕ)^4935*20000000000000^3911 ≤ 9384004973433^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489724723 10000000000 9384004973433 20000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178182057/1250000000 : ℝ)^4935 ≤ (4279641885431/50000000000000 : ℝ)^3911 := by
    have hnat : (178182057 : ℕ)^4935*50000000000000^3911 ≤ 4279641885431^3911*1250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178182057 1250000000 4279641885431 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633021587/5000000000 : ℝ), (5489724723/10000000000 : ℝ), (-178182057/1250000000 : ℝ)] ![(44520691348061/100000000000000 : ℝ), (9384004973433/20000000000000 : ℝ), (4279641885431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633021587/5000000000 : ℝ)|^4935 ≤ (44520691348061/100000000000000 : ℝ)^3911
        have hw : |(2633021587/5000000000 : ℝ)|=(2633021587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489724723/10000000000 : ℝ)|^4935 ≤ (9384004973433/20000000000000 : ℝ)^3911
        have hw : |(5489724723/10000000000 : ℝ)|=(5489724723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178182057/1250000000 : ℝ)|^4935 ≤ (4279641885431/50000000000000 : ℝ)^3911
        have hw : |(-178182057/1250000000 : ℝ)|=(178182057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s1_7 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170964123/10000000000 : ℝ)*x 0 + (115849421/250000000 : ℝ)*x 1 + (748593899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170964123/10000000000 : ℝ)^4935 ≤ (1658725925851/5000000000000 : ℝ)^3911 := by
    have hnat : (4170964123 : ℕ)^4935*5000000000000^3911 ≤ 1658725925851^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170964123 10000000000 1658725925851 5000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115849421/250000000 : ℝ)^4935 ≤ (9471789321111/25000000000000 : ℝ)^3911 := by
    have hnat : (115849421 : ℕ)^4935*25000000000000^3911 ≤ 9471789321111^3911*250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115849421 250000000 9471789321111 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748593899/2000000000 : ℝ)^4935 ≤ (28938324183207/100000000000000 : ℝ)^3911 := by
    have hnat : (748593899 : ℕ)^4935*100000000000000^3911 ≤ 28938324183207^3911*2000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748593899 2000000000 28938324183207 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170964123/10000000000 : ℝ), (115849421/250000000 : ℝ), (748593899/2000000000 : ℝ)] ![(1658725925851/5000000000000 : ℝ), (9471789321111/25000000000000 : ℝ), (28938324183207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170964123/10000000000 : ℝ)|^4935 ≤ (1658725925851/5000000000000 : ℝ)^3911
        have hw : |(4170964123/10000000000 : ℝ)|=(4170964123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(115849421/250000000 : ℝ)|^4935 ≤ (9471789321111/25000000000000 : ℝ)^3911
        have hw : |(115849421/250000000 : ℝ)|=(115849421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748593899/2000000000 : ℝ)|^4935 ≤ (28938324183207/100000000000000 : ℝ)^3911
        have hw : |(748593899/2000000000 : ℝ)|=(748593899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1654_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2909/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9811/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4311/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2909/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2909/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2909/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2909/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2909/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2909/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4921/100000 : ℝ) ^ (4931/1024 : ℝ) ≤ (25156194775363/50000000000000000000 : ℝ) := by
    have hpowers : (4921/100000 : ℝ)^4931 ≤ (25156194775363/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4921 : ℕ)^4931*50000000000000000000^1024 ≤ 25156194775363^1024*100000^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4921 100000 25156194775363 50000000000000000000 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4921/100000 : ℝ)) (X := (25156194775363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2909/12500 : ℝ) ^ (4931/1024 : ℝ) ≤ (89337180418106541/100000000000000000000 : ℝ) := by
    have hpowers : (2909/12500 : ℝ)^4931 ≤ (89337180418106541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2909 : ℕ)^4931*100000000000000000000^1024 ≤ 89337180418106541^1024*12500^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2909 12500 89337180418106541 100000000000000000000 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2909/12500 : ℝ)) (X := (89337180418106541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025156194775363/25000000000000000000 : ℝ) ≤ (10000002089631571/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (25000025156194775363/25000000000000000000 : ℝ)^1024 ≤ (10000002089631571/10000000000000000 : ℝ)^4931 := by
      have hnat : (25000025156194775363 : ℕ)^1024*10000000000000000^4931 ≤ 10000002089631571^4931*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025156194775363 25000000000000000000 10000002089631571 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002089631571/10000000000000000 : ℝ)) (X := (25000025156194775363/25000000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100089387492807657267/100000000000000000000 : ℝ) ≤ (10001855615412499/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (100089387492807657267/100000000000000000000 : ℝ)^1024 ≤ (10001855615412499/10000000000000000 : ℝ)^4931 := by
      have hnat : (100089387492807657267 : ℕ)^1024*10000000000000000^4931 ≤ 10001855615412499^4931*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100089387492807657267 100000000000000000000 10001855615412499 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001855615412499/10000000000000000 : ℝ)) (X := (100089387492807657267/100000000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50089337180418106541/50000000000000000000 : ℝ) ≤ (10003709141193427/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (50089337180418106541/50000000000000000000 : ℝ)^1024 ≤ (10003709141193427/10000000000000000 : ℝ)^4931 := by
      have hnat : (50089337180418106541 : ℕ)^1024*10000000000000000^4931 ≤ 10003709141193427^4931*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50089337180418106541 50000000000000000000 10003709141193427 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003709141193427/10000000000000000 : ℝ)) (X := (50089337180418106541/50000000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25156194775363/50000000000000000000 : ℝ) ≤ ((4077595465468734801/4078000000000000000 : ℝ)+2*(3217926703/3185937500000 : ℝ)*(4921/100000 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (4077595465468734801/4078000000000000000 : ℝ)+2*(3217926703/3185937500000 : ℝ)*(4921/100000 : ℝ)=(10000002089631571/10000000000000000 : ℝ) by norm_num, show 1+2*(25156194775363/50000000000000000000 : ℝ)=(25000025156194775363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(89337180418106541/100000000000000000000 : ℝ)+(25156194775363/50000000000000000000 : ℝ) ≤ ((4077595465468734801/4078000000000000000 : ℝ)+(3217926703/3185937500000 : ℝ)*((2909/12500 : ℝ)+(4921/100000 : ℝ)))^(4931/1024 : ℝ) := by
    rw [show (4077595465468734801/4078000000000000000 : ℝ)+(3217926703/3185937500000 : ℝ)*((2909/12500 : ℝ)+(4921/100000 : ℝ))=(10001855615412499/10000000000000000 : ℝ) by norm_num, show 1+(89337180418106541/100000000000000000000 : ℝ)+(25156194775363/50000000000000000000 : ℝ)=(100089387492807657267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(89337180418106541/100000000000000000000 : ℝ) ≤ ((4077595465468734801/4078000000000000000 : ℝ)+2*(3217926703/3185937500000 : ℝ)*(2909/12500 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (4077595465468734801/4078000000000000000 : ℝ)+2*(3217926703/3185937500000 : ℝ)*(2909/12500 : ℝ)=(10003709141193427/10000000000000000 : ℝ) by norm_num, show 1+2*(89337180418106541/100000000000000000000 : ℝ)=(50089337180418106541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4077595465468734801/4078000000000000000 : ℝ)*(X 1 0+X 2 0)+(3217926703/3185937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (4921/100000 : ℝ)) (hi := (2909/12500 : ℝ)) (c := (4077595465468734801/4078000000000000000 : ℝ)) (alpha := (3217926703/3185937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4077595465468734801/4078000000000000000 : ℝ)*(X 0 1+X 2 1)+(3217926703/3185937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (4921/100000 : ℝ)) (hi := (2909/12500 : ℝ)) (c := (4077595465468734801/4078000000000000000 : ℝ)) (alpha := (3217926703/3185937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4077595465468734801/4078000000000000000 : ℝ)*(X 0 2+X 1 2)+(3217926703/3185937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (4921/100000 : ℝ)) (hi := (2909/12500 : ℝ)) (c := (4077595465468734801/4078000000000000000 : ℝ)) (alpha := (3217926703/3185937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99368809/625000000 : ℝ)*X 0 0+(1373325213/2500000000 : ℝ)*X 0 1+(2571770439/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679799413/5000000000 : ℝ)*X 1 0+(-1771640077/10000000000 : ℝ)*X 1 1+(1285885181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133989957/250000000 : ℝ)*X 2 0+(5143541313/10000000000 : ℝ)*X 2 1+(-442910007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4170571633/10000000000 : ℝ)*X 0 0+(1866834693/5000000000 : ℝ)*X 0 1+(4643147833/10000000000 : ℝ)*X 0 2+(4170571633/10000000000 : ℝ)*X 1 0+(1866834693/5000000000 : ℝ)*X 1 1+(4643147833/10000000000 : ℝ)*X 1 2+(4170571633/10000000000 : ℝ)*X 2 0+(1866834693/5000000000 : ℝ)*X 2 1+(4643147833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1590051777/10000000000 : ℝ)*X 0 0+(5147067939/10000000000 : ℝ)*X 0 1+(2744862193/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266043393/10000000000 : ℝ)*X 1 0+(-712728287/5000000000 : ℝ)*X 1 1+(686215553/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633021587/5000000000 : ℝ)*X 2 0+(5489724723/10000000000 : ℝ)*X 2 1+(-178182057/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170964123/10000000000 : ℝ)*X 0 0+(115849421/250000000 : ℝ)*X 0 1+(748593899/2000000000 : ℝ)*X 0 2+(4170964123/10000000000 : ℝ)*X 1 0+(115849421/250000000 : ℝ)*X 1 1+(748593899/2000000000 : ℝ)*X 1 2+(4170964123/10000000000 : ℝ)*X 2 0+(115849421/250000000 : ℝ)*X 2 1+(748593899/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (372391771462726884376068711/50975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912527341/50000000000000 : ℝ)*(base19) + (1428649113/100000000000000 : ℝ)*(base23) + (54818409/20000000000000 : ℝ)*(upper3) + (5634863/10000000000000 : ℝ)*(upper4) + (186490141/100000000000000 : ℝ)*(upper5) + (1979341409205451/100000000000000 : ℝ)*(major0) + (1979341409205451/100000000000000 : ℝ)*(major1) + (494835352301363/25000000000000 : ℝ)*(major2) + (285912149315183/10000000000000 : ℝ)*(sp0) + (1429568040788521/50000000000000 : ℝ)*(sp1) + (714784119495653/25000000000000 : ℝ)*(sp2) + (549768865310849/50000000000000 : ℝ)*(sp3) + (8206739947/50000000000000 : ℝ)*(sp4) + (6937644789/100000000000000 : ℝ)*(sp7) + (1099544668266487/100000000000000 : ℝ)*(f.failure) + (714784476657931/25000000000000 : ℝ)*(f.sum) + (6589000388903/10195000000000000000000000000 : ℝ)*base65 + (493657352381080251/407800000000000000000000000000000 : ℝ)*base67 + (1178537258619443763/101950000000000000000000000000000 : ℝ)*base69 + (840185908460880251/407800000000000000000000000000000 : ℝ)*base71 + (2972780499429/5097500000000000000000000000 : ℝ)*base73 + (791896309880643763/101950000000000000000000000000000 : ℝ)*base75 + (3492059071329359749/407800000000000000000000000000000 : ℝ)*base78 + (3582251586852759749/407800000000000000000000000000000 : ℝ)*base80 + (55750304409057/10195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13830859/10000000000000000000000 : ℝ)*base90 + (13830859/10000000000000000000000 : ℝ)*base92 + (113830859/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185172678132834536422095009/50975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (805726291/100000000000000 : ℝ)*(base19) + (803679083/100000000000000 : ℝ)*(base23) + (4637789/10000000000000 : ℝ)*(upper2) + (105476551/100000000000000 : ℝ)*(upper3) + (22426109/25000000000000 : ℝ)*(upper5) + (1010174743499397/50000000000000 : ℝ)*(major0) + (1010174743499397/50000000000000 : ℝ)*(major1) + (1010174743499397/50000000000000 : ℝ)*(major2) + (1554192359/20000000000000 : ℝ)*(sp1) + (9529996037/100000000000000 : ℝ)*(sp2) + (11399897548397/390625000000 : ℝ)*(sp4) + (2918365195701547/100000000000000 : ℝ)*(sp5) + (2918363438714511/100000000000000 : ℝ)*(sp6) + (140290635065087/12500000000000 : ℝ)*(sp7) + (140290635065087/12500000000000 : ℝ)*(f.failure) + (11399897548397/390625000000 : ℝ)*(f.sum) + (4711937034321/1274375000000000000000000000 : ℝ)*base65 + (645401209409694997/203900000000000000000000000000000 : ℝ)*base67 + (18154775612094997/203900000000000000000000000000000 : ℝ)*base69 + (128640686781794997/203900000000000000000000000000000 : ℝ)*base71 + (42215052908483/10195000000000000000000000000 : ℝ)*base73 + (660252650056305003/203900000000000000000000000000000 : ℝ)*base76 + (2300943852913094997/203900000000000000000000000000000 : ℝ)*base77 + (3269976810224294997/203900000000000000000000000000000 : ℝ)*base79 + (7629182446403/2548750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (6931059/1250000000000000000000 : ℝ)*base90 + (6931059/1250000000000000000000 : ℝ)*base92 + (6931059/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1654_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2909/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4311/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1654_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1654_s2_0 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399707553/2500000000 : ℝ)*x 0 + (2724836113/5000000000 : ℝ)*x 1 + (2590637047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399707553/2500000000 : ℝ)^4935 ≤ (395728558593/4000000000000 : ℝ)^3911 := by
    have hnat : (399707553 : ℕ)^4935*4000000000000^3911 ≤ 395728558593^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399707553 2500000000 395728558593 4000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724836113/5000000000 : ℝ)^4935 ≤ (2905530316999/6250000000000 : ℝ)^3911 := by
    have hnat : (2724836113 : ℕ)^4935*6250000000000^3911 ≤ 2905530316999^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724836113 5000000000 2905530316999 6250000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590637047/5000000000 : ℝ)^4935 ≤ (43618300953567/100000000000000 : ℝ)^3911 := by
    have hnat : (2590637047 : ℕ)^4935*100000000000000^3911 ≤ 43618300953567^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590637047 5000000000 43618300953567 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399707553/2500000000 : ℝ), (2724836113/5000000000 : ℝ), (2590637047/5000000000 : ℝ)] ![(395728558593/4000000000000 : ℝ), (2905530316999/6250000000000 : ℝ), (43618300953567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399707553/2500000000 : ℝ)|^4935 ≤ (395728558593/4000000000000 : ℝ)^3911
        have hw : |(-399707553/2500000000 : ℝ)|=(399707553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724836113/5000000000 : ℝ)|^4935 ≤ (2905530316999/6250000000000 : ℝ)^3911
        have hw : |(2724836113/5000000000 : ℝ)|=(2724836113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590637047/5000000000 : ℝ)|^4935 ≤ (43618300953567/100000000000000 : ℝ)^3911
        have hw : |(2590637047/5000000000 : ℝ)|=(2590637047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_1 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668504413/1250000000 : ℝ)*x 0 + (-1737069959/10000000000 : ℝ)*x 1 + (5181274913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668504413/1250000000 : ℝ)^4935 ≤ (11349286755787/25000000000000 : ℝ)^3911 := by
    have hnat : (668504413 : ℕ)^4935*25000000000000^3911 ≤ 11349286755787^3911*1250000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668504413 1250000000 11349286755787 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737069959/10000000000 : ℝ)^4935 ≤ (5492271653051/50000000000000 : ℝ)^3911 := by
    have hnat : (1737069959 : ℕ)^4935*50000000000000^3911 ≤ 5492271653051^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737069959 10000000000 5492271653051 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181274913/10000000000 : ℝ)^4935 ≤ (43618309653491/100000000000000 : ℝ)^3911 := by
    have hnat : (5181274913 : ℕ)^4935*100000000000000^3911 ≤ 43618309653491^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181274913 10000000000 43618309653491 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668504413/1250000000 : ℝ), (-1737069959/10000000000 : ℝ), (5181274913/10000000000 : ℝ)] ![(11349286755787/25000000000000 : ℝ), (5492271653051/50000000000000 : ℝ), (43618309653491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668504413/1250000000 : ℝ)|^4935 ≤ (11349286755787/25000000000000 : ℝ)^3911
        have hw : |(668504413/1250000000 : ℝ)|=(668504413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737069959/10000000000 : ℝ)|^4935 ≤ (5492271653051/50000000000000 : ℝ)^3911
        have hw : |(-1737069959/10000000000 : ℝ)|=(1737069959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181274913/10000000000 : ℝ)|^4935 ≤ (43618309653491/100000000000000 : ℝ)^3911
        have hw : |(5181274913/10000000000 : ℝ)|=(5181274913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_2 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348036171/10000000000 : ℝ)*x 0 + (1295318517/2500000000 : ℝ)*x 1 + (-10856687/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348036171/10000000000 : ℝ)^4935 ≤ (22698578154831/50000000000000 : ℝ)^3911 := by
    have hnat : (5348036171 : ℕ)^4935*50000000000000^3911 ≤ 22698578154831^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348036171 10000000000 22698578154831 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295318517/2500000000 : ℝ)^4935 ≤ (43618300677379/100000000000000 : ℝ)^3911 := by
    have hnat : (1295318517 : ℕ)^4935*100000000000000^3911 ≤ 43618300677379^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295318517 2500000000 43618300677379 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10856687/62500000 : ℝ)^4935 ≤ (1098454299491/10000000000000 : ℝ)^3911 := by
    have hnat : (10856687 : ℕ)^4935*10000000000000^3911 ≤ 1098454299491^3911*62500000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10856687 62500000 1098454299491 10000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348036171/10000000000 : ℝ), (1295318517/2500000000 : ℝ), (-10856687/62500000 : ℝ)] ![(22698578154831/50000000000000 : ℝ), (43618300677379/100000000000000 : ℝ), (1098454299491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348036171/10000000000 : ℝ)|^4935 ≤ (22698578154831/50000000000000 : ℝ)^3911
        have hw : |(5348036171/10000000000 : ℝ)|=(5348036171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295318517/2500000000 : ℝ)|^4935 ≤ (43618300677379/100000000000000 : ℝ)^3911
        have hw : |(1295318517/2500000000 : ℝ)|=(1295318517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10856687/62500000 : ℝ)|^4935 ≤ (1098454299491/10000000000000 : ℝ)^3911
        have hw : |(-10856687/62500000 : ℝ)|=(10856687/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_3 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044308577/2500000000 : ℝ)*x 0 + (3838786513/10000000000 : ℝ)*x 1 + (4536698461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044308577/2500000000 : ℝ)^4935 ≤ (33237459467839/100000000000000 : ℝ)^3911 := by
    have hnat : (1044308577 : ℕ)^4935*100000000000000^3911 ≤ 33237459467839^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044308577 2500000000 33237459467839 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3838786513/10000000000 : ℝ)^4935 ≤ (14938097526009/50000000000000 : ℝ)^3911 := by
    have hnat : (3838786513 : ℕ)^4935*50000000000000^3911 ≤ 14938097526009^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838786513 10000000000 14938097526009 50000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536698461/10000000000 : ℝ)^4935 ≤ (36886345459039/100000000000000 : ℝ)^3911 := by
    have hnat : (4536698461 : ℕ)^4935*100000000000000^3911 ≤ 36886345459039^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536698461 10000000000 36886345459039 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044308577/2500000000 : ℝ), (3838786513/10000000000 : ℝ), (4536698461/10000000000 : ℝ)] ![(33237459467839/100000000000000 : ℝ), (14938097526009/50000000000000 : ℝ), (36886345459039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044308577/2500000000 : ℝ)|^4935 ≤ (33237459467839/100000000000000 : ℝ)^3911
        have hw : |(1044308577/2500000000 : ℝ)|=(1044308577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3838786513/10000000000 : ℝ)|^4935 ≤ (14938097526009/50000000000000 : ℝ)^3911
        have hw : |(3838786513/10000000000 : ℝ)|=(3838786513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536698461/10000000000 : ℝ)|^4935 ≤ (36886345459039/100000000000000 : ℝ)^3911
        have hw : |(4536698461/10000000000 : ℝ)|=(4536698461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_4 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-799449121/5000000000 : ℝ)*x 0 + (5183356959/10000000000 : ℝ)*x 1 + (5447567159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (799449121/5000000000 : ℝ)^4935 ≤ (989374513941/10000000000000 : ℝ)^3911 := by
    have hnat : (799449121 : ℕ)^4935*10000000000000^3911 ≤ 989374513941^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799449121 5000000000 989374513941 10000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183356959/10000000000 : ℝ)^4935 ≤ (174561710379/400000000000 : ℝ)^3911 := by
    have hnat : (5183356959 : ℕ)^4935*400000000000^3911 ≤ 174561710379^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183356959 10000000000 174561710379 400000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447567159/10000000000 : ℝ)^4935 ≤ (9293165448419/20000000000000 : ℝ)^3911 := by
    have hnat : (5447567159 : ℕ)^4935*20000000000000^3911 ≤ 9293165448419^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447567159 10000000000 9293165448419 20000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-799449121/5000000000 : ℝ), (5183356959/10000000000 : ℝ), (5447567159/10000000000 : ℝ)] ![(989374513941/10000000000000 : ℝ), (174561710379/400000000000 : ℝ), (9293165448419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-799449121/5000000000 : ℝ)|^4935 ≤ (989374513941/10000000000000 : ℝ)^3911
        have hw : |(-799449121/5000000000 : ℝ)|=(799449121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183356959/10000000000 : ℝ)|^4935 ≤ (174561710379/400000000000 : ℝ)^3911
        have hw : |(5183356959/10000000000 : ℝ)|=(5183356959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447567159/10000000000 : ℝ)|^4935 ≤ (9293165448419/20000000000000 : ℝ)^3911
        have hw : |(5447567159/10000000000 : ℝ)|=(5447567159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_5 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42210363/80000000 : ℝ)*x 0 + (-1470776801/10000000000 : ℝ)*x 1 + (5447567331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42210363/80000000 : ℝ)^4935 ≤ (174336281769/390625000000 : ℝ)^3911 := by
    have hnat : (42210363 : ℕ)^4935*390625000000^3911 ≤ 174336281769^3911*80000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42210363 80000000 174336281769 390625000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470776801/10000000000 : ℝ)^4935 ≤ (8904082764241/100000000000000 : ℝ)^3911 := by
    have hnat : (1470776801 : ℕ)^4935*100000000000000^3911 ≤ 8904082764241^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470776801 10000000000 8904082764241 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447567331/10000000000 : ℝ)^4935 ≤ (46465829093319/100000000000000 : ℝ)^3911 := by
    have hnat : (5447567331 : ℕ)^4935*100000000000000^3911 ≤ 46465829093319^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447567331 10000000000 46465829093319 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42210363/80000000 : ℝ), (-1470776801/10000000000 : ℝ), (5447567331/10000000000 : ℝ)] ![(174336281769/390625000000 : ℝ), (8904082764241/100000000000000 : ℝ), (46465829093319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42210363/80000000 : ℝ)|^4935 ≤ (174336281769/390625000000 : ℝ)^3911
        have hw : |(42210363/80000000 : ℝ)|=(42210363/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1470776801/10000000000 : ℝ)|^4935 ≤ (8904082764241/100000000000000 : ℝ)^3911
        have hw : |(-1470776801/10000000000 : ℝ)|=(1470776801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447567331/10000000000 : ℝ)|^4935 ≤ (46465829093319/100000000000000 : ℝ)^3911
        have hw : |(5447567331/10000000000 : ℝ)|=(5447567331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_6 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319073913/2500000000 : ℝ)*x 0 + (5447566939/10000000000 : ℝ)*x 1 + (-735388483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319073913/2500000000 : ℝ)^4935 ≤ (11157522772341/25000000000000 : ℝ)^3911 := by
    have hnat : (1319073913 : ℕ)^4935*25000000000000^3911 ≤ 11157522772341^3911*2500000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319073913 2500000000 11157522772341 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447566939/10000000000 : ℝ)^4935 ≤ (46465824874251/100000000000000 : ℝ)^3911 := by
    have hnat : (5447566939 : ℕ)^4935*100000000000000^3911 ≤ 46465824874251^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447566939 10000000000 46465824874251 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735388483/5000000000 : ℝ)^4935 ≤ (8904084024691/100000000000000 : ℝ)^3911 := by
    have hnat : (735388483 : ℕ)^4935*100000000000000^3911 ≤ 8904084024691^3911*5000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735388483 5000000000 8904084024691 100000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319073913/2500000000 : ℝ), (5447566939/10000000000 : ℝ), (-735388483/5000000000 : ℝ)] ![(11157522772341/25000000000000 : ℝ), (46465824874251/100000000000000 : ℝ), (8904084024691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319073913/2500000000 : ℝ)|^4935 ≤ (11157522772341/25000000000000 : ℝ)^3911
        have hw : |(1319073913/2500000000 : ℝ)|=(1319073913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447566939/10000000000 : ℝ)|^4935 ≤ (46465824874251/100000000000000 : ℝ)^3911
        have hw : |(5447566939/10000000000 : ℝ)|=(5447566939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735388483/5000000000 : ℝ)|^4935 ≤ (8904084024691/100000000000000 : ℝ)^3911
        have hw : |(-735388483/5000000000 : ℝ)|=(735388483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1654_s2_7 (p : ℝ) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177412401/10000000000 : ℝ)*x 0 + (4531283889/10000000000 : ℝ)*x 1 + (3844259171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177412401/10000000000 : ℝ)^4935 ≤ (3323924755053/10000000000000 : ℝ)^3911 := by
    have hnat : (4177412401 : ℕ)^4935*10000000000000^3911 ≤ 3323924755053^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177412401 10000000000 3323924755053 10000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531283889/10000000000 : ℝ)^4935 ≤ (9207700871359/25000000000000 : ℝ)^3911 := by
    have hnat : (4531283889 : ℕ)^4935*25000000000000^3911 ≤ 9207700871359^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531283889 10000000000 9207700871359 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3844259171/10000000000 : ℝ)^4935 ≤ (7482487238439/25000000000000 : ℝ)^3911 := by
    have hnat : (3844259171 : ℕ)^4935*25000000000000^3911 ≤ 7482487238439^3911*10000000000^4935 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844259171 10000000000 7482487238439 25000000000000 4935 3911 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4935/1024 : ℝ)) 4935 3911 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177412401/10000000000 : ℝ), (4531283889/10000000000 : ℝ), (3844259171/10000000000 : ℝ)] ![(3323924755053/10000000000000 : ℝ), (9207700871359/25000000000000 : ℝ), (7482487238439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177412401/10000000000 : ℝ)|^4935 ≤ (3323924755053/10000000000000 : ℝ)^3911
        have hw : |(4177412401/10000000000 : ℝ)|=(4177412401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531283889/10000000000 : ℝ)|^4935 ≤ (9207700871359/25000000000000 : ℝ)^3911
        have hw : |(4531283889/10000000000 : ℝ)|=(4531283889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3844259171/10000000000 : ℝ)|^4935 ≤ (7482487238439/25000000000000 : ℝ)^3911
        have hw : |(3844259171/10000000000 : ℝ)|=(3844259171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1654_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4311/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5313/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16333/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4311/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4311/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4311/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4311/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4311/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4311/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9811/100000 : ℝ) ^ (4931/1024 : ℝ) ≤ (1395295438238967/100000000000000000000 : ℝ) := by
    have hpowers : (9811/100000 : ℝ)^4931 ≤ (1395295438238967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9811 : ℕ)^4931*100000000000000000000^1024 ≤ 1395295438238967^1024*100000^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9811 100000 1395295438238967 100000000000000000000 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9811/100000 : ℝ)) (X := (1395295438238967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4311/25000 : ℝ) ^ (4931/1024 : ℝ) ≤ (21090361856492009/100000000000000000000 : ℝ) := by
    have hpowers : (4311/25000 : ℝ)^4931 ≤ (21090361856492009/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4311 : ℕ)^4931*100000000000000000000^1024 ≤ 21090361856492009^1024*25000^4931 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4311 25000 21090361856492009 100000000000000000000 4931 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4311/25000 : ℝ)) (X := (21090361856492009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001395295438238967/50000000000000000000 : ℝ) ≤ (10000057950384639/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (50001395295438238967/50000000000000000000 : ℝ)^1024 ≤ (10000057950384639/10000000000000000 : ℝ)^4931 := by
      have hnat : (50001395295438238967 : ℕ)^1024*10000000000000000^4931 ≤ 10000057950384639^4931*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001395295438238967 50000000000000000000 10000057950384639 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057950384639/10000000000000000 : ℝ)) (X := (50001395295438238967/50000000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125702676790460343/3125000000000000000 : ℝ) ≤ (10000466908583097/10000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (3125702676790460343/3125000000000000000 : ℝ)^1024 ≤ (10000466908583097/10000000000000000 : ℝ)^4931 := by
      have hnat : (3125702676790460343 : ℕ)^1024*10000000000000000^4931 ≤ 10000466908583097^4931*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125702676790460343 3125000000000000000 10000466908583097 10000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000466908583097/10000000000000000 : ℝ)) (X := (3125702676790460343/3125000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021090361856492009/50000000000000000000 : ℝ) ≤ (2000175173356311/2000000000000000 : ℝ) ^ (4931/1024 : ℝ) := by
    have hpowers : (50021090361856492009/50000000000000000000 : ℝ)^1024 ≤ (2000175173356311/2000000000000000 : ℝ)^4931 := by
      have hnat : (50021090361856492009 : ℕ)^1024*2000000000000000^4931 ≤ 2000175173356311^4931*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021090361856492009 50000000000000000000 2000175173356311 2000000000000000 1024 4931 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000175173356311/2000000000000000 : ℝ)) (X := (50021090361856492009/50000000000000000000 : ℝ)) (by norm_num) 4931 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1395295438238967/100000000000000000000 : ℝ) ≤ ((74322406167438878811/74330000000000000000 : ℝ)+2*(204479099229/371650000000000 : ℝ)*(9811/100000 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (74322406167438878811/74330000000000000000 : ℝ)+2*(204479099229/371650000000000 : ℝ)*(9811/100000 : ℝ)=(10000057950384639/10000000000000000 : ℝ) by norm_num, show 1+2*(1395295438238967/100000000000000000000 : ℝ)=(50001395295438238967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21090361856492009/100000000000000000000 : ℝ)+(1395295438238967/100000000000000000000 : ℝ) ≤ ((74322406167438878811/74330000000000000000 : ℝ)+(204479099229/371650000000000 : ℝ)*((4311/25000 : ℝ)+(9811/100000 : ℝ)))^(4931/1024 : ℝ) := by
    rw [show (74322406167438878811/74330000000000000000 : ℝ)+(204479099229/371650000000000 : ℝ)*((4311/25000 : ℝ)+(9811/100000 : ℝ))=(10000466908583097/10000000000000000 : ℝ) by norm_num, show 1+(21090361856492009/100000000000000000000 : ℝ)+(1395295438238967/100000000000000000000 : ℝ)=(3125702676790460343/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21090361856492009/100000000000000000000 : ℝ) ≤ ((74322406167438878811/74330000000000000000 : ℝ)+2*(204479099229/371650000000000 : ℝ)*(4311/25000 : ℝ))^(4931/1024 : ℝ) := by
    rw [show (74322406167438878811/74330000000000000000 : ℝ)+2*(204479099229/371650000000000 : ℝ)*(4311/25000 : ℝ)=(2000175173356311/2000000000000000 : ℝ) by norm_num, show 1+2*(21090361856492009/100000000000000000000 : ℝ)=(50021090361856492009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74322406167438878811/74330000000000000000 : ℝ)*(X 1 0+X 2 0)+(204479099229/371650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (4311/25000 : ℝ)) (c := (74322406167438878811/74330000000000000000 : ℝ)) (alpha := (204479099229/371650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74322406167438878811/74330000000000000000 : ℝ)*(X 0 1+X 2 1)+(204479099229/371650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (4311/25000 : ℝ)) (c := (74322406167438878811/74330000000000000000 : ℝ)) (alpha := (204479099229/371650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74322406167438878811/74330000000000000000 : ℝ)*(X 0 2+X 1 2)+(204479099229/371650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4931/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (4311/25000 : ℝ)) (c := (74322406167438878811/74330000000000000000 : ℝ)) (alpha := (204479099229/371650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399707553/2500000000 : ℝ)*X 0 0+(2724836113/5000000000 : ℝ)*X 0 1+(2590637047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668504413/1250000000 : ℝ)*X 1 0+(-1737069959/10000000000 : ℝ)*X 1 1+(5181274913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348036171/10000000000 : ℝ)*X 2 0+(1295318517/2500000000 : ℝ)*X 2 1+(-10856687/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1044308577/2500000000 : ℝ)*X 0 0+(3838786513/10000000000 : ℝ)*X 0 1+(4536698461/10000000000 : ℝ)*X 0 2+(1044308577/2500000000 : ℝ)*X 1 0+(3838786513/10000000000 : ℝ)*X 1 1+(4536698461/10000000000 : ℝ)*X 1 2+(1044308577/2500000000 : ℝ)*X 2 0+(3838786513/10000000000 : ℝ)*X 2 1+(4536698461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-799449121/5000000000 : ℝ)*X 0 0+(5183356959/10000000000 : ℝ)*X 0 1+(5447567159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42210363/80000000 : ℝ)*X 1 0+(-1470776801/10000000000 : ℝ)*X 1 1+(5447567331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319073913/2500000000 : ℝ)*X 2 0+(5447566939/10000000000 : ℝ)*X 2 1+(-735388483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4177412401/10000000000 : ℝ)*X 0 0+(4531283889/10000000000 : ℝ)*X 0 1+(3844259171/10000000000 : ℝ)*X 0 2+(4177412401/10000000000 : ℝ)*X 1 0+(4531283889/10000000000 : ℝ)*X 1 1+(3844259171/10000000000 : ℝ)*X 1 2+(4177412401/10000000000 : ℝ)*X 2 0+(4531283889/10000000000 : ℝ)*X 2 1+(3844259171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1654_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7118576574796786092327667779/929125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797824323/100000000000000 : ℝ)*(base19) + (601971839/50000000000000 : ℝ)*(base23) + (99545253/50000000000000 : ℝ)*(upper3) + (105836261/100000000000000 : ℝ)*(upper4) + (179987637/100000000000000 : ℝ)*(upper5) + (1289673990967437/50000000000000 : ℝ)*(major0) + (1289673990967437/50000000000000 : ℝ)*(major1) + (1289673990967437/50000000000000 : ℝ)*(major2) + (3725822750362889/100000000000000 : ℝ)*(sp0) + (1862920186150393/50000000000000 : ℝ)*(sp1) + (465729995772679/12500000000000 : ℝ)*(sp2) + (89553077230591/6250000000000 : ℝ)*(sp3) + (18419762221/100000000000000 : ℝ)*(sp4) + (2651334389/50000000000000 : ℝ)*(sp7) + (286570907671647/20000000000000 : ℝ)*(f.failure) + (372584117012511/10000000000000 : ℝ)*(f.sum) + (16450541077969/4645625000000000000000000000 : ℝ)*base65 + (13505681680125377407/3716500000000000000000000000000000 : ℝ)*base67 + (4985751195918622593/3716500000000000000000000000000000 : ℝ)*base70 + (22138256582099877407/3716500000000000000000000000000000 : ℝ)*base71 + (6262303025119/4645625000000000000000000000 : ℝ)*base73 + (13564103391416877407/3716500000000000000000000000000000 : ℝ)*base75 + (30130114387687877407/3716500000000000000000000000000000 : ℝ)*base77 + (7356217609395877407/3716500000000000000000000000000000 : ℝ)*base79 + (103279158205991/18582500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (15927021/2000000000000000000000 : ℝ)*base89 + (15927021/2000000000000000000000 : ℝ)*base91 + (15927021/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11828503487603322354963788313/929125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1867305427/100000000000000 : ℝ)*(base19) + (283700721/12500000000000 : ℝ)*(base23) + (37811393/12500000000000 : ℝ)*(upper3) + (928403/1000000000000 : ℝ)*(lower4) + (24840297/12500000000000 : ℝ)*(upper5) + (655051855242361/25000000000000 : ℝ)*(major0) + (655051855242361/25000000000000 : ℝ)*(major1) + (655051855242361/25000000000000 : ℝ)*(major2) + (23008041717/100000000000000 : ℝ)*(sp1) + (6260205429/25000000000000 : ℝ)*(sp2) + (3784862037337583/100000000000000 : ℝ)*(sp4) + (1892418580995219/50000000000000 : ℝ)*(sp5) + (37848347269101/1000000000000 : ℝ)*(sp6) + (181944047530167/12500000000000 : ℝ)*(sp7) + (181944047530167/12500000000000 : ℝ)*(f.failure) + (3784862037337583/100000000000000 : ℝ)*(f.sum) + (42229249695051/18582500000000000000000000000 : ℝ)*base65 + (3254047873261937229/1858250000000000000000000000000000 : ℝ)*base68 + (2331990452115937229/1858250000000000000000000000000000 : ℝ)*base70 + (1216073792324187229/1858250000000000000000000000000000 : ℝ)*base72 + (137600465812043/37165000000000000000000000000 : ℝ)*base74 + (13304272937492562771/1858250000000000000000000000000000 : ℝ)*base75 + (9616800996322687229/1858250000000000000000000000000000 : ℝ)*base78 + (7464422693837312771/1858250000000000000000000000000000 : ℝ)*base79 + (9757454327239/4645625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (5764619/1250000000000000000000 : ℝ)*base90 + (5764619/1250000000000000000000 : ℝ)*base92 + (5764619/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1654_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4311/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1654_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1654_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1654_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1654_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1654_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4931/1024 : ℝ) ≤ p) (hpb : p ≤ (4935/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180014643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16333/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1654_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

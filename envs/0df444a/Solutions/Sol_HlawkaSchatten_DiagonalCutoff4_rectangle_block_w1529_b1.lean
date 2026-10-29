-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:50.409828+00:00
-- url     : https://prove2.me/submissions/4a07f600-100f-42b9-9ea6-eb26e9ac03f4

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
theorem support_rectangle_w1529_s3_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1842785633/10000000000 : ℝ)*x 0 + (5433725821/10000000000 : ℝ)*x 1 + (1043204733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1842785633/10000000000 : ℝ)^4555 ≤ (1410491416453/12500000000000 : ℝ)^3531 := by
    have hnat : (1842785633 : ℕ)^4555*12500000000000^3531 ≤ 1410491416453^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842785633 10000000000 1410491416453 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433725821/10000000000 : ℝ)^4555 ≤ (45527657919157/100000000000000 : ℝ)^3531 := by
    have hnat : (5433725821 : ℕ)^4555*100000000000000^3531 ≤ 45527657919157^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433725821 10000000000 45527657919157 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043204733/2000000000 : ℝ)^4555 ≤ (21594205368127/50000000000000 : ℝ)^3531 := by
    have hnat : (1043204733 : ℕ)^4555*50000000000000^3531 ≤ 21594205368127^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043204733 2000000000 21594205368127 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1842785633/10000000000 : ℝ), (5433725821/10000000000 : ℝ), (1043204733/2000000000 : ℝ)] ![(1410491416453/12500000000000 : ℝ), (45527657919157/100000000000000 : ℝ), (21594205368127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1842785633/10000000000 : ℝ)|^4555 ≤ (1410491416453/12500000000000 : ℝ)^3531
        have hw : |(-1842785633/10000000000 : ℝ)|=(1842785633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433725821/10000000000 : ℝ)|^4555 ≤ (45527657919157/100000000000000 : ℝ)^3531
        have hw : |(5433725821/10000000000 : ℝ)|=(5433725821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043204733/2000000000 : ℝ)|^4555 ≤ (21594205368127/50000000000000 : ℝ)^3531
        have hw : |(1043204733/2000000000 : ℝ)|=(1043204733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214053479/400000000 : ℝ)*x 0 + (-1954307497/10000000000 : ℝ)*x 1 + (5216023547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214053479/400000000 : ℝ)^4555 ≤ (44639117205781/100000000000000 : ℝ)^3531 := by
    have hnat : (214053479 : ℕ)^4555*100000000000000^3531 ≤ 44639117205781^3531*400000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214053479 400000000 44639117205781 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954307497/10000000000 : ℝ)^4555 ≤ (1217247329779/10000000000000 : ℝ)^3531 := by
    have hnat : (1954307497 : ℕ)^4555*10000000000000^3531 ≤ 1217247329779^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954307497 10000000000 1217247329779 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216023547/10000000000 : ℝ)^4555 ≤ (21594204737939/50000000000000 : ℝ)^3531 := by
    have hnat : (5216023547 : ℕ)^4555*50000000000000^3531 ≤ 21594204737939^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216023547 10000000000 21594204737939 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214053479/400000000 : ℝ), (-1954307497/10000000000 : ℝ), (5216023547/10000000000 : ℝ)] ![(44639117205781/100000000000000 : ℝ), (1217247329779/10000000000000 : ℝ), (21594204737939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214053479/400000000 : ℝ)|^4555 ≤ (44639117205781/100000000000000 : ℝ)^3531
        have hw : |(214053479/400000000 : ℝ)|=(214053479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954307497/10000000000 : ℝ)|^4555 ≤ (1217247329779/10000000000000 : ℝ)^3531
        have hw : |(-1954307497/10000000000 : ℝ)|=(1954307497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216023547/10000000000 : ℝ)|^4555 ≤ (21594204737939/50000000000000 : ℝ)^3531
        have hw : |(5216023547/10000000000 : ℝ)|=(5216023547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337834293/2500000000 : ℝ)*x 0 + (5216023281/10000000000 : ℝ)*x 1 + (-1954307587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337834293/2500000000 : ℝ)^4555 ≤ (8927823865131/20000000000000 : ℝ)^3531 := by
    have hnat : (1337834293 : ℕ)^4555*20000000000000^3531 ≤ 8927823865131^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337834293 2500000000 8927823865131 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216023281/10000000000 : ℝ)^4555 ≤ (4318840663469/10000000000000 : ℝ)^3531 := by
    have hnat : (5216023281 : ℕ)^4555*10000000000000^3531 ≤ 4318840663469^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216023281 10000000000 4318840663469 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954307587/10000000000 : ℝ)^4555 ≤ (3043118505231/25000000000000 : ℝ)^3531 := by
    have hnat : (1954307587 : ℕ)^4555*25000000000000^3531 ≤ 3043118505231^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954307587 10000000000 3043118505231 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337834293/2500000000 : ℝ), (5216023281/10000000000 : ℝ), (-1954307587/10000000000 : ℝ)] ![(8927823865131/20000000000000 : ℝ), (4318840663469/10000000000000 : ℝ), (3043118505231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337834293/2500000000 : ℝ)|^4555 ≤ (8927823865131/20000000000000 : ℝ)^3531
        have hw : |(1337834293/2500000000 : ℝ)|=(1337834293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216023281/10000000000 : ℝ)|^4555 ≤ (4318840663469/10000000000000 : ℝ)^3531
        have hw : |(5216023281/10000000000 : ℝ)|=(5216023281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954307587/10000000000 : ℝ)|^4555 ≤ (3043118505231/25000000000000 : ℝ)^3531
        have hw : |(-1954307587/10000000000 : ℝ)|=(1954307587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130832381/5000000000 : ℝ)*x 0 + (125562621/312500000 : ℝ)*x 1 + (4517582027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130832381/5000000000 : ℝ)^4555 ≤ (33277924088143/100000000000000 : ℝ)^3531 := by
    have hnat : (2130832381 : ℕ)^4555*100000000000000^3531 ≤ 33277924088143^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130832381 5000000000 33277924088143 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125562621/312500000 : ℝ)^4555 ≤ (15422054571709/50000000000000 : ℝ)^3531 := by
    have hnat : (125562621 : ℕ)^4555*50000000000000^3531 ≤ 15422054571709^3531*312500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125562621 312500000 15422054571709 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517582027/10000000000 : ℝ)^4555 ≤ (35877966761549/100000000000000 : ℝ)^3531 := by
    have hnat : (4517582027 : ℕ)^4555*100000000000000^3531 ≤ 35877966761549^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517582027 10000000000 35877966761549 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130832381/5000000000 : ℝ), (125562621/312500000 : ℝ), (4517582027/10000000000 : ℝ)] ![(33277924088143/100000000000000 : ℝ), (15422054571709/50000000000000 : ℝ), (35877966761549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130832381/5000000000 : ℝ)|^4555 ≤ (33277924088143/100000000000000 : ℝ)^3531
        have hw : |(2130832381/5000000000 : ℝ)|=(2130832381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125562621/312500000 : ℝ)|^4555 ≤ (15422054571709/50000000000000 : ℝ)^3531
        have hw : |(125562621/312500000 : ℝ)|=(125562621/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517582027/10000000000 : ℝ)|^4555 ≤ (35877966761549/100000000000000 : ℝ)^3531
        have hw : |(4517582027/10000000000 : ℝ)|=(4517582027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-921408043/5000000000 : ℝ)*x 0 + (2608587447/5000000000 : ℝ)*x 1 + (1086513167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921408043/5000000000 : ℝ)^4555 ≤ (2256834376551/20000000000000 : ℝ)^3531 := by
    have hnat : (921408043 : ℕ)^4555*20000000000000^3531 ≤ 2256834376551^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921408043 5000000000 2256834376551 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608587447/5000000000 : ℝ)^4555 ≤ (21600353794221/50000000000000 : ℝ)^3531 := by
    have hnat : (2608587447 : ℕ)^4555*50000000000000^3531 ≤ 21600353794221^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608587447 5000000000 21600353794221 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086513167/2000000000 : ℝ)^4555 ≤ (22757560258513/50000000000000 : ℝ)^3531 := by
    have hnat : (1086513167 : ℕ)^4555*50000000000000^3531 ≤ 22757560258513^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086513167 2000000000 22757560258513 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921408043/5000000000 : ℝ), (2608587447/5000000000 : ℝ), (1086513167/2000000000 : ℝ)] ![(2256834376551/20000000000000 : ℝ), (21600353794221/50000000000000 : ℝ), (22757560258513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921408043/5000000000 : ℝ)|^4555 ≤ (2256834376551/20000000000000 : ℝ)^3531
        have hw : |(-921408043/5000000000 : ℝ)|=(921408043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608587447/5000000000 : ℝ)|^4555 ≤ (21600353794221/50000000000000 : ℝ)^3531
        have hw : |(2608587447/5000000000 : ℝ)|=(2608587447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086513167/2000000000 : ℝ)|^4555 ≤ (22757560258513/50000000000000 : ℝ)^3531
        have hw : |(1086513167/2000000000 : ℝ)|=(1086513167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647022183/5000000000 : ℝ)*x 0 + (-1737764943/10000000000 : ℝ)*x 1 + (5432565947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647022183/5000000000 : ℝ)^4555 ≤ (22011781635221/50000000000000 : ℝ)^3531 := by
    have hnat : (2647022183 : ℕ)^4555*50000000000000^3531 ≤ 22011781635221^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647022183 5000000000 22011781635221 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737764943/10000000000 : ℝ)^4555 ≤ (5230657490101/50000000000000 : ℝ)^3531 := by
    have hnat : (1737764943 : ℕ)^4555*50000000000000^3531 ≤ 5230657490101^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737764943 10000000000 5230657490101 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432565947/10000000000 : ℝ)^4555 ≤ (45515121727511/100000000000000 : ℝ)^3531 := by
    have hnat : (5432565947 : ℕ)^4555*100000000000000^3531 ≤ 45515121727511^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432565947 10000000000 45515121727511 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647022183/5000000000 : ℝ), (-1737764943/10000000000 : ℝ), (5432565947/10000000000 : ℝ)] ![(22011781635221/50000000000000 : ℝ), (5230657490101/50000000000000 : ℝ), (45515121727511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647022183/5000000000 : ℝ)|^4555 ≤ (22011781635221/50000000000000 : ℝ)^3531
        have hw : |(2647022183/5000000000 : ℝ)|=(2647022183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737764943/10000000000 : ℝ)|^4555 ≤ (5230657490101/50000000000000 : ℝ)^3531
        have hw : |(-1737764943/10000000000 : ℝ)|=(1737764943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432565947/10000000000 : ℝ)|^4555 ≤ (45515121727511/100000000000000 : ℝ)^3531
        have hw : |(5432565947/10000000000 : ℝ)|=(5432565947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647022291/5000000000 : ℝ)*x 0 + (5432565713/10000000000 : ℝ)*x 1 + (-434441243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647022291/5000000000 : ℝ)^4555 ≤ (5502945698441/12500000000000 : ℝ)^3531 := by
    have hnat : (2647022291 : ℕ)^4555*12500000000000^3531 ≤ 5502945698441^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647022291 5000000000 5502945698441 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432565713/10000000000 : ℝ)^4555 ≤ (22757559599231/50000000000000 : ℝ)^3531 := by
    have hnat : (5432565713 : ℕ)^4555*50000000000000^3531 ≤ 22757559599231^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432565713 10000000000 22757559599231 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434441243/2500000000 : ℝ)^4555 ≤ (1046131520541/10000000000000 : ℝ)^3531 := by
    have hnat : (434441243 : ℕ)^4555*10000000000000^3531 ≤ 1046131520541^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434441243 2500000000 1046131520541 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647022291/5000000000 : ℝ), (5432565713/10000000000 : ℝ), (-434441243/2500000000 : ℝ)] ![(5502945698441/12500000000000 : ℝ), (22757559599231/50000000000000 : ℝ), (1046131520541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647022291/5000000000 : ℝ)|^4555 ≤ (5502945698441/12500000000000 : ℝ)^3531
        have hw : |(2647022291/5000000000 : ℝ)|=(2647022291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432565713/10000000000 : ℝ)|^4555 ≤ (22757559599231/50000000000000 : ℝ)^3531
        have hw : |(5432565713/10000000000 : ℝ)|=(5432565713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434441243/2500000000 : ℝ)|^4555 ≤ (1046131520541/10000000000000 : ℝ)^3531
        have hw : |(-434441243/2500000000 : ℝ)|=(434441243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s3_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130867431/5000000000 : ℝ)*x 0 + (2257469849/5000000000 : ℝ)*x 1 + (4020665751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130867431/5000000000 : ℝ)^4555 ≤ (33278630221391/100000000000000 : ℝ)^3531 := by
    have hnat : (2130867431 : ℕ)^4555*100000000000000^3531 ≤ 33278630221391^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130867431 5000000000 33278630221391 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257469849/5000000000 : ℝ)^4555 ≤ (35850898367409/100000000000000 : ℝ)^3531 := by
    have hnat : (2257469849 : ℕ)^4555*100000000000000^3531 ≤ 35850898367409^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257469849 5000000000 35850898367409 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020665751/10000000000 : ℝ)^4555 ≤ (30870471398903/100000000000000 : ℝ)^3531 := by
    have hnat : (4020665751 : ℕ)^4555*100000000000000^3531 ≤ 30870471398903^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020665751 10000000000 30870471398903 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130867431/5000000000 : ℝ), (2257469849/5000000000 : ℝ), (4020665751/10000000000 : ℝ)] ![(33278630221391/100000000000000 : ℝ), (35850898367409/100000000000000 : ℝ), (30870471398903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130867431/5000000000 : ℝ)|^4555 ≤ (33278630221391/100000000000000 : ℝ)^3531
        have hw : |(2130867431/5000000000 : ℝ)|=(2130867431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257469849/5000000000 : ℝ)|^4555 ≤ (35850898367409/100000000000000 : ℝ)^3531
        have hw : |(2257469849/5000000000 : ℝ)|=(2257469849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020665751/10000000000 : ℝ)|^4555 ≤ (30870471398903/100000000000000 : ℝ)^3531
        have hw : |(4020665751/10000000000 : ℝ)|=(4020665751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (683/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (777/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3187/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2641/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3187/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2641/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3187/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2641/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3187/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2641/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3187/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2641/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3187/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2641/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2641/25000 : ℝ) ^ (4553/1024 : ℝ) ≤ (1141823211450839/25000000000000000000 : ℝ) := by
    have hpowers : (2641/25000 : ℝ)^4553 ≤ (1141823211450839/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2641 : ℕ)^4553*25000000000000000000^1024 ≤ 1141823211450839^1024*25000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2641 25000 1141823211450839 25000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2641/25000 : ℝ)) (X := (1141823211450839/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3187/20000 : ℝ) ^ (4553/1024 : ℝ) ≤ (5681417688140519/20000000000000000000 : ℝ) := by
    have hpowers : (3187/20000 : ℝ)^4553 ≤ (5681417688140519/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3187 : ℕ)^4553*20000000000000000000^1024 ≤ 5681417688140519^1024*20000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3187 20000 5681417688140519 20000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3187/20000 : ℝ)) (X := (5681417688140519/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501141823211450839/12500000000000000000 : ℝ) ≤ (5000102717819391/5000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (12501141823211450839/12500000000000000000 : ℝ)^1024 ≤ (5000102717819391/5000000000000000 : ℝ)^4553 := by
      have hnat : (12501141823211450839 : ℕ)^1024*5000000000000000^4553 ≤ 5000102717819391^4553*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501141823211450839 12500000000000000000 5000102717819391 5000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000102717819391/5000000000000000 : ℝ)) (X := (12501141823211450839/12500000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032974381286505951/100000000000000000000 : ℝ) ≤ (5000370760513003/5000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (100032974381286505951/100000000000000000000 : ℝ)^1024 ≤ (5000370760513003/5000000000000000 : ℝ)^4553 := by
      have hnat : (100032974381286505951 : ℕ)^1024*5000000000000000^4553 ≤ 5000370760513003^4553*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032974381286505951 100000000000000000000 5000370760513003 5000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000370760513003/5000000000000000 : ℝ)) (X := (100032974381286505951/100000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005681417688140519/10000000000000000000 : ℝ) ≤ (1000127760641323/1000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (10005681417688140519/10000000000000000000 : ℝ)^1024 ≤ (1000127760641323/1000000000000000 : ℝ)^4553 := by
      have hnat : (10005681417688140519 : ℕ)^1024*1000000000000000^4553 ≤ 1000127760641323^4553*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005681417688140519 10000000000000000000 1000127760641323 1000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127760641323/1000000000000000 : ℝ)) (X := (10005681417688140519/10000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1141823211450839/25000000000000000000 : ℝ) ≤ ((1073995539655092589/1074200000000000000 : ℝ)+2*(67010673403/67137500000000 : ℝ)*(2641/25000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (1073995539655092589/1074200000000000000 : ℝ)+2*(67010673403/67137500000000 : ℝ)*(2641/25000 : ℝ)=(5000102717819391/5000000000000000 : ℝ) by norm_num, show 1+2*(1141823211450839/25000000000000000000 : ℝ)=(12501141823211450839/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5681417688140519/20000000000000000000 : ℝ)+(1141823211450839/25000000000000000000 : ℝ) ≤ ((1073995539655092589/1074200000000000000 : ℝ)+(67010673403/67137500000000 : ℝ)*((3187/20000 : ℝ)+(2641/25000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (1073995539655092589/1074200000000000000 : ℝ)+(67010673403/67137500000000 : ℝ)*((3187/20000 : ℝ)+(2641/25000 : ℝ))=(5000370760513003/5000000000000000 : ℝ) by norm_num, show 1+(5681417688140519/20000000000000000000 : ℝ)+(1141823211450839/25000000000000000000 : ℝ)=(100032974381286505951/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5681417688140519/20000000000000000000 : ℝ) ≤ ((1073995539655092589/1074200000000000000 : ℝ)+2*(67010673403/67137500000000 : ℝ)*(3187/20000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (1073995539655092589/1074200000000000000 : ℝ)+2*(67010673403/67137500000000 : ℝ)*(3187/20000 : ℝ)=(1000127760641323/1000000000000000 : ℝ) by norm_num, show 1+2*(5681417688140519/20000000000000000000 : ℝ)=(10005681417688140519/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1073995539655092589/1074200000000000000 : ℝ)*(X 1 0+X 2 0)+(67010673403/67137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3187/20000 : ℝ)) (c := (1073995539655092589/1074200000000000000 : ℝ)) (alpha := (67010673403/67137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1073995539655092589/1074200000000000000 : ℝ)*(X 0 1+X 2 1)+(67010673403/67137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3187/20000 : ℝ)) (c := (1073995539655092589/1074200000000000000 : ℝ)) (alpha := (67010673403/67137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1073995539655092589/1074200000000000000 : ℝ)*(X 0 2+X 1 2)+(67010673403/67137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (2641/25000 : ℝ)) (hi := (3187/20000 : ℝ)) (c := (1073995539655092589/1074200000000000000 : ℝ)) (alpha := (67010673403/67137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1842785633/10000000000 : ℝ)*X 0 0+(5433725821/10000000000 : ℝ)*X 0 1+(1043204733/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214053479/400000000 : ℝ)*X 1 0+(-1954307497/10000000000 : ℝ)*X 1 1+(5216023547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337834293/2500000000 : ℝ)*X 2 0+(5216023281/10000000000 : ℝ)*X 2 1+(-1954307587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130832381/5000000000 : ℝ)*X 0 0+(125562621/312500000 : ℝ)*X 0 1+(4517582027/10000000000 : ℝ)*X 0 2+(2130832381/5000000000 : ℝ)*X 1 0+(125562621/312500000 : ℝ)*X 1 1+(4517582027/10000000000 : ℝ)*X 1 2+(2130832381/5000000000 : ℝ)*X 2 0+(125562621/312500000 : ℝ)*X 2 1+(4517582027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-921408043/5000000000 : ℝ)*X 0 0+(2608587447/5000000000 : ℝ)*X 0 1+(1086513167/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647022183/5000000000 : ℝ)*X 1 0+(-1737764943/10000000000 : ℝ)*X 1 1+(5432565947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647022291/5000000000 : ℝ)*X 2 0+(5432565713/10000000000 : ℝ)*X 2 1+(-434441243/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2130867431/5000000000 : ℝ)*X 0 0+(2257469849/5000000000 : ℝ)*X 0 1+(4020665751/10000000000 : ℝ)*X 0 2+(2130867431/5000000000 : ℝ)*X 1 0+(2257469849/5000000000 : ℝ)*X 1 1+(4020665751/10000000000 : ℝ)*X 1 2+(2130867431/5000000000 : ℝ)*X 2 0+(2257469849/5000000000 : ℝ)*X 2 1+(4020665751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40620560076487259378257671/5371000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483030467/50000000000000 : ℝ)*(base19) + (990355669/100000000000000 : ℝ)*(base23) + (113801407/100000000000000 : ℝ)*(lower2) + (264501/160000000000 : ℝ)*(upper3) + (36311263/100000000000000 : ℝ)*(lower4) + (329757958117371/10000000000000 : ℝ)*(major0) + (329757958117371/10000000000000 : ℝ)*(major1) + (329757958117371/10000000000000 : ℝ)*(major2) + (1148361343113073/25000000000000 : ℝ)*(sp0) + (4593455611846753/100000000000000 : ℝ)*(sp1) + (2296727793776009/50000000000000 : ℝ)*(sp2) + (500423559331061/25000000000000 : ℝ)*(sp3) + (5602727697/50000000000000 : ℝ)*(sp4) + (8095017419/100000000000000 : ℝ)*(sp7) + (2001702332341663/100000000000000 : ℝ)*(f.failure) + (2296728288953843/50000000000000 : ℝ)*(f.sum) + (2692315130501/2685500000000000000000000000 : ℝ)*base65 + (144114756100444481/10742000000000000000000000000000 : ℝ)*base68 + (20248230202362481/10742000000000000000000000000000 : ℝ)*base70 + (204991400454030481/10742000000000000000000000000000 : ℝ)*base72 + (11966239680289/5371000000000000000000000000 : ℝ)*base73 + (155459274343344481/10742000000000000000000000000000 : ℝ)*base76 + (173242569987412481/10742000000000000000000000000000 : ℝ)*base78 + (263800198249224481/10742000000000000000000000000000 : ℝ)*base80 + (27542925446847/5371000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (126616217/10000000000000000000000 : ℝ)*base89 + (126616217/10000000000000000000000 : ℝ)*base91 + (126616217/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171305157816964060646758203/26855000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (997806823/100000000000000 : ℝ)*(base19) + (802775867/50000000000000 : ℝ)*(base23) + (63850717/50000000000000 : ℝ)*(upper3) + (93937239/50000000000000 : ℝ)*(lower4) + (112670193/100000000000000 : ℝ)*(upper5) + (1666471877036303/50000000000000 : ℝ)*(major0) + (1666471877036303/50000000000000 : ℝ)*(major1) + (1666471877036303/50000000000000 : ℝ)*(major2) + (4387578329/25000000000000 : ℝ)*(sp1) + (936498213/4000000000000 : ℝ)*(sp2) + (290169883947067/6250000000000 : ℝ)*(sp4) + (4642699595032933/100000000000000 : ℝ)*(sp5) + (2321346562573007/50000000000000 : ℝ)*(sp6) + (1011584576181191/50000000000000 : ℝ)*(sp7) + (1011584576181191/50000000000000 : ℝ)*(f.failure) + (290169883947067/6250000000000 : ℝ)*(f.sum) + (23201123539979/6713750000000000000000000000 : ℝ)*base66 + (530990286699837533/53710000000000000000000000000000 : ℝ)*base68 + (802352488482417533/53710000000000000000000000000000 : ℝ)*base70 + (271759554883017533/53710000000000000000000000000000 : ℝ)*base72 + (139349517668331/26855000000000000000000000000 : ℝ)*base74 + (132077967872347533/53710000000000000000000000000000 : ℝ)*base76 + (301765853246717533/53710000000000000000000000000000 : ℝ)*base78 + (483191874573527533/53710000000000000000000000000000 : ℝ)*base80 + (130472966244901/26855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (64481969/5000000000000000000000 : ℝ)*base89 + (64481969/5000000000000000000000 : ℝ)*base91 + (64481969/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1529_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (777/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1529_s4_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230393273/1250000000 : ℝ)*x 0 + (271566939/500000000 : ℝ)*x 1 + (5218172251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230393273/1250000000 : ℝ)^4555 ≤ (11286779432093/100000000000000 : ℝ)^3531 := by
    have hnat : (230393273 : ℕ)^4555*100000000000000^3531 ≤ 11286779432093^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230393273 1250000000 11286779432093 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271566939/500000000 : ℝ)^4555 ≤ (2843866191393/6250000000000 : ℝ)^3531 := by
    have hnat : (271566939 : ℕ)^4555*6250000000000^3531 ≤ 2843866191393^3531*500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271566939 500000000 2843866191393 6250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218172251/10000000000 : ℝ)^4555 ≤ (8642272298621/20000000000000 : ℝ)^3531 := by
    have hnat : (5218172251 : ℕ)^4555*20000000000000^3531 ≤ 8642272298621^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218172251 10000000000 8642272298621 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230393273/1250000000 : ℝ), (271566939/500000000 : ℝ), (5218172251/10000000000 : ℝ)] ![(11286779432093/100000000000000 : ℝ), (2843866191393/6250000000000 : ℝ), (8642272298621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230393273/1250000000 : ℝ)|^4555 ≤ (11286779432093/100000000000000 : ℝ)^3531
        have hw : |(-230393273/1250000000 : ℝ)|=(230393273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271566939/500000000 : ℝ)|^4555 ≤ (2843866191393/6250000000000 : ℝ)^3531
        have hw : |(271566939/500000000 : ℝ)|=(271566939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218172251/10000000000 : ℝ)|^4555 ≤ (8642272298621/20000000000000 : ℝ)^3531
        have hw : |(5218172251/10000000000 : ℝ)|=(5218172251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668838757/1250000000 : ℝ)*x 0 + (-390457983/2000000000 : ℝ)*x 1 + (2609086243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668838757/1250000000 : ℝ)^4555 ≤ (44632371179697/100000000000000 : ℝ)^3531 := by
    have hnat : (668838757 : ℕ)^4555*100000000000000^3531 ≤ 44632371179697^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668838757 1250000000 44632371179697 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390457983/2000000000 : ℝ)^4555 ≤ (6078132400153/50000000000000 : ℝ)^3531 := by
    have hnat : (390457983 : ℕ)^4555*50000000000000^3531 ≤ 6078132400153^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390457983 2000000000 6078132400153 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609086243/5000000000 : ℝ)^4555 ≤ (43211364003477/100000000000000 : ℝ)^3531 := by
    have hnat : (2609086243 : ℕ)^4555*100000000000000^3531 ≤ 43211364003477^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609086243 5000000000 43211364003477 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668838757/1250000000 : ℝ), (-390457983/2000000000 : ℝ), (2609086243/5000000000 : ℝ)] ![(44632371179697/100000000000000 : ℝ), (6078132400153/50000000000000 : ℝ), (43211364003477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668838757/1250000000 : ℝ)|^4555 ≤ (44632371179697/100000000000000 : ℝ)^3531
        have hw : |(668838757/1250000000 : ℝ)|=(668838757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390457983/2000000000 : ℝ)|^4555 ≤ (6078132400153/50000000000000 : ℝ)^3531
        have hw : |(-390457983/2000000000 : ℝ)|=(390457983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609086243/5000000000 : ℝ)|^4555 ≤ (43211364003477/100000000000000 : ℝ)^3531
        have hw : |(2609086243/5000000000 : ℝ)|=(2609086243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675355203/5000000000 : ℝ)*x 0 + (1304543039/2500000000 : ℝ)*x 1 + (-390457977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675355203/5000000000 : ℝ)^4555 ≤ (11158093736461/25000000000000 : ℝ)^3531 := by
    have hnat : (2675355203 : ℕ)^4555*25000000000000^3531 ≤ 11158093736461^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675355203 5000000000 11158093736461 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304543039/2500000000 : ℝ)^4555 ≤ (21605680239137/50000000000000 : ℝ)^3531 := by
    have hnat : (1304543039 : ℕ)^4555*50000000000000^3531 ≤ 21605680239137^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304543039 2500000000 21605680239137 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390457977/2000000000 : ℝ)^4555 ≤ (12156264559333/100000000000000 : ℝ)^3531 := by
    have hnat : (390457977 : ℕ)^4555*100000000000000^3531 ≤ 12156264559333^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390457977 2000000000 12156264559333 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675355203/5000000000 : ℝ), (1304543039/2500000000 : ℝ), (-390457977/2000000000 : ℝ)] ![(11158093736461/25000000000000 : ℝ), (21605680239137/50000000000000 : ℝ), (12156264559333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675355203/5000000000 : ℝ)|^4555 ≤ (11158093736461/25000000000000 : ℝ)^3531
        have hw : |(2675355203/5000000000 : ℝ)|=(2675355203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304543039/2500000000 : ℝ)|^4555 ≤ (21605680239137/50000000000000 : ℝ)^3531
        have hw : |(1304543039/2500000000 : ℝ)|=(1304543039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390457977/2000000000 : ℝ)|^4555 ≤ (12156264559333/100000000000000 : ℝ)^3531
        have hw : |(-390457977/2000000000 : ℝ)|=(390457977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106547297/250000000 : ℝ)*x 0 + (125724443/312500000 : ℝ)*x 1 + (451235163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106547297/250000000 : ℝ)^4555 ≤ (665604238233/2000000000000 : ℝ)^3531 := by
    have hnat : (106547297 : ℕ)^4555*2000000000000^3531 ≤ 665604238233^3531*250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106547297 250000000 665604238233 2000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125724443/312500000 : ℝ)^4555 ≤ (1930962361683/6250000000000 : ℝ)^3531 := by
    have hnat : (125724443 : ℕ)^4555*6250000000000^3531 ≤ 1930962361683^3531*312500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125724443 312500000 1930962361683 6250000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451235163/1000000000 : ℝ)^4555 ≤ (35824390283829/100000000000000 : ℝ)^3531 := by
    have hnat : (451235163 : ℕ)^4555*100000000000000^3531 ≤ 35824390283829^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451235163 1000000000 35824390283829 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106547297/250000000 : ℝ), (125724443/312500000 : ℝ), (451235163/1000000000 : ℝ)] ![(665604238233/2000000000000 : ℝ), (1930962361683/6250000000000 : ℝ), (35824390283829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106547297/250000000 : ℝ)|^4555 ≤ (665604238233/2000000000000 : ℝ)^3531
        have hw : |(106547297/250000000 : ℝ)|=(106547297/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125724443/312500000 : ℝ)|^4555 ≤ (1930962361683/6250000000000 : ℝ)^3531
        have hw : |(125724443/312500000 : ℝ)|=(125724443/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451235163/1000000000 : ℝ)|^4555 ≤ (35824390283829/100000000000000 : ℝ)^3531
        have hw : |(451235163/1000000000 : ℝ)|=(451235163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-921587257/5000000000 : ℝ)*x 0 + (652409527/1250000000 : ℝ)*x 1 + (169694587/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921587257/5000000000 : ℝ)^4555 ≤ (5643501613053/50000000000000 : ℝ)^3531 := by
    have hnat : (921587257 : ℕ)^4555*50000000000000^3531 ≤ 5643501613053^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921587257 5000000000 5643501613053 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652409527/1250000000 : ℝ)^4555 ≤ (43223154887693/100000000000000 : ℝ)^3531 := by
    have hnat : (652409527 : ℕ)^4555*100000000000000^3531 ≤ 43223154887693^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652409527 1250000000 43223154887693 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169694587/312500000 : ℝ)^4555 ≤ (1137246046589/2500000000000 : ℝ)^3531 := by
    have hnat : (169694587 : ℕ)^4555*2500000000000^3531 ≤ 1137246046589^3531*312500000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169694587 312500000 1137246046589 2500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921587257/5000000000 : ℝ), (652409527/1250000000 : ℝ), (169694587/312500000 : ℝ)] ![(5643501613053/50000000000000 : ℝ), (43223154887693/100000000000000 : ℝ), (1137246046589/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921587257/5000000000 : ℝ)|^4555 ≤ (5643501613053/50000000000000 : ℝ)^3531
        have hw : |(-921587257/5000000000 : ℝ)|=(921587257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652409527/1250000000 : ℝ)|^4555 ≤ (43223154887693/100000000000000 : ℝ)^3531
        have hw : |(652409527/1250000000 : ℝ)|=(652409527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169694587/312500000 : ℝ)|^4555 ≤ (1137246046589/2500000000000 : ℝ)^3531
        have hw : |(169694587/312500000 : ℝ)|=(169694587/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529461231/1000000000 : ℝ)*x 0 + (-1740235239/10000000000 : ℝ)*x 1 + (271511337/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529461231/1000000000 : ℝ)^4555 ≤ (11007413960189/25000000000000 : ℝ)^3531 := by
    have hnat : (529461231 : ℕ)^4555*25000000000000^3531 ≤ 11007413960189^3531*1000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529461231 1000000000 11007413960189 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740235239/10000000000 : ℝ)^4555 ≤ (5240251372477/50000000000000 : ℝ)^3531 := by
    have hnat : (1740235239 : ℕ)^4555*50000000000000^3531 ≤ 5240251372477^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740235239 10000000000 5240251372477 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271511337/500000000 : ℝ)^4555 ≤ (5686230173509/12500000000000 : ℝ)^3531 := by
    have hnat : (271511337 : ℕ)^4555*12500000000000^3531 ≤ 5686230173509^3531*500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271511337 500000000 5686230173509 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529461231/1000000000 : ℝ), (-1740235239/10000000000 : ℝ), (271511337/500000000 : ℝ)] ![(11007413960189/25000000000000 : ℝ), (5240251372477/50000000000000 : ℝ), (5686230173509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529461231/1000000000 : ℝ)|^4555 ≤ (11007413960189/25000000000000 : ℝ)^3531
        have hw : |(529461231/1000000000 : ℝ)|=(529461231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1740235239/10000000000 : ℝ)|^4555 ≤ (5240251372477/50000000000000 : ℝ)^3531
        have hw : |(-1740235239/10000000000 : ℝ)|=(1740235239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271511337/500000000 : ℝ)|^4555 ≤ (5686230173509/12500000000000 : ℝ)^3531
        have hw : |(271511337/500000000 : ℝ)|=(271511337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647306129/5000000000 : ℝ)*x 0 + (1357556681/2500000000 : ℝ)*x 1 + (-217529417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647306129/5000000000 : ℝ)^4555 ≤ (22014827641461/50000000000000 : ℝ)^3531 := by
    have hnat : (2647306129 : ℕ)^4555*50000000000000^3531 ≤ 22014827641461^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647306129 5000000000 22014827641461 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357556681/2500000000 : ℝ)^4555 ≤ (45489841215167/100000000000000 : ℝ)^3531 := by
    have hnat : (1357556681 : ℕ)^4555*100000000000000^3531 ≤ 45489841215167^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357556681 2500000000 45489841215167 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217529417/1250000000 : ℝ)^4555 ≤ (5240251749273/50000000000000 : ℝ)^3531 := by
    have hnat : (217529417 : ℕ)^4555*50000000000000^3531 ≤ 5240251749273^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217529417 1250000000 5240251749273 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647306129/5000000000 : ℝ), (1357556681/2500000000 : ℝ), (-217529417/1250000000 : ℝ)] ![(22014827641461/50000000000000 : ℝ), (45489841215167/100000000000000 : ℝ), (5240251749273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647306129/5000000000 : ℝ)|^4555 ≤ (22014827641461/50000000000000 : ℝ)^3531
        have hw : |(2647306129/5000000000 : ℝ)|=(2647306129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357556681/2500000000 : ℝ)|^4555 ≤ (45489841215167/100000000000000 : ℝ)^3531
        have hw : |(1357556681/2500000000 : ℝ)|=(1357556681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217529417/1250000000 : ℝ)|^4555 ≤ (5240251749273/50000000000000 : ℝ)^3531
        have hw : |(-217529417/1250000000 : ℝ)|=(217529417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s4_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261956943/10000000000 : ℝ)*x 0 + (4509818431/10000000000 : ℝ)*x 1 + (2012867241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261956943/10000000000 : ℝ)^4555 ≤ (8320216829017/25000000000000 : ℝ)^3531 := by
    have hnat : (4261956943 : ℕ)^4555*25000000000000^3531 ≤ 8320216829017^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261956943 10000000000 8320216829017 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509818431/10000000000 : ℝ)^4555 ≤ (35798448461223/100000000000000 : ℝ)^3531 := by
    have hnat : (4509818431 : ℕ)^4555*100000000000000^3531 ≤ 35798448461223^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509818431 10000000000 35798448461223 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012867241/5000000000 : ℝ)^4555 ≤ (618413684247/2000000000000 : ℝ)^3531 := by
    have hnat : (2012867241 : ℕ)^4555*2000000000000^3531 ≤ 618413684247^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012867241 5000000000 618413684247 2000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261956943/10000000000 : ℝ), (4509818431/10000000000 : ℝ), (2012867241/5000000000 : ℝ)] ![(8320216829017/25000000000000 : ℝ), (35798448461223/100000000000000 : ℝ), (618413684247/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261956943/10000000000 : ℝ)|^4555 ≤ (8320216829017/25000000000000 : ℝ)^3531
        have hw : |(4261956943/10000000000 : ℝ)|=(4261956943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509818431/10000000000 : ℝ)|^4555 ≤ (35798448461223/100000000000000 : ℝ)^3531
        have hw : |(4509818431/10000000000 : ℝ)|=(4509818431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012867241/5000000000 : ℝ)|^4555 ≤ (618413684247/2000000000000 : ℝ)^3531
        have hw : |(2012867241/5000000000 : ℝ)|=(2012867241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (777/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (777/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (777/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (777/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (777/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (777/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (777/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (683/6250 : ℝ) ^ (4553/1024 : ℝ) ≤ (5309748728882231/100000000000000000000 : ℝ) := by
    have hpowers : (683/6250 : ℝ)^4553 ≤ (5309748728882231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (683 : ℕ)^4553*100000000000000000000^1024 ≤ 5309748728882231^1024*6250^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 6250 5309748728882231 100000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/6250 : ℝ)) (X := (5309748728882231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (777/5000 : ℝ) ^ (4553/1024 : ℝ) ≤ (3175904993518027/12500000000000000000 : ℝ) := by
    have hpowers : (777/5000 : ℝ)^4553 ≤ (3175904993518027/12500000000000000000 : ℝ)^1024 := by
      have hnat : (777 : ℕ)^4553*12500000000000000000^1024 ≤ 3175904993518027^1024*5000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        777 5000 3175904993518027 12500000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (777/5000 : ℝ)) (X := (3175904993518027/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005309748728882231/50000000000000000000 : ℝ) ≤ (2000047765947221/2000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (50005309748728882231/50000000000000000000 : ℝ)^1024 ≤ (2000047765947221/2000000000000000 : ℝ)^4553 := by
      have hnat : (50005309748728882231 : ℕ)^1024*2000000000000000^4553 ≤ 2000047765947221^4553*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005309748728882231 50000000000000000000 2000047765947221 2000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000047765947221/2000000000000000 : ℝ)) (X := (50005309748728882231/50000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030716988677026447/100000000000000000000 : ℝ) ≤ (10000690763292209/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (100030716988677026447/100000000000000000000 : ℝ)^1024 ≤ (10000690763292209/10000000000000000 : ℝ)^4553 := by
      have hnat : (100030716988677026447 : ℕ)^1024*10000000000000000^4553 ≤ 10000690763292209^4553*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030716988677026447 100000000000000000000 10000690763292209 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690763292209/10000000000000000 : ℝ)) (X := (100030716988677026447/100000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253175904993518027/6250000000000000000 : ℝ) ≤ (10001142696848313/10000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (6253175904993518027/6250000000000000000 : ℝ)^1024 ≤ (10001142696848313/10000000000000000 : ℝ)^4553 := by
      have hnat : (6253175904993518027 : ℕ)^1024*10000000000000000^4553 ≤ 10001142696848313^4553*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253175904993518027 6250000000000000000 10001142696848313 10000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001142696848313/10000000000000000 : ℝ)) (X := (6253175904993518027/6250000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5309748728882231/100000000000000000000 : ℝ) ≤ ((11527806005735176809/11530000000000000000 : ℝ)+2*(56491694513/57650000000000 : ℝ)*(683/6250 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (11527806005735176809/11530000000000000000 : ℝ)+2*(56491694513/57650000000000 : ℝ)*(683/6250 : ℝ)=(2000047765947221/2000000000000000 : ℝ) by norm_num, show 1+2*(5309748728882231/100000000000000000000 : ℝ)=(50005309748728882231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3175904993518027/12500000000000000000 : ℝ)+(5309748728882231/100000000000000000000 : ℝ) ≤ ((11527806005735176809/11530000000000000000 : ℝ)+(56491694513/57650000000000 : ℝ)*((777/5000 : ℝ)+(683/6250 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (11527806005735176809/11530000000000000000 : ℝ)+(56491694513/57650000000000 : ℝ)*((777/5000 : ℝ)+(683/6250 : ℝ))=(10000690763292209/10000000000000000 : ℝ) by norm_num, show 1+(3175904993518027/12500000000000000000 : ℝ)+(5309748728882231/100000000000000000000 : ℝ)=(100030716988677026447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3175904993518027/12500000000000000000 : ℝ) ≤ ((11527806005735176809/11530000000000000000 : ℝ)+2*(56491694513/57650000000000 : ℝ)*(777/5000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (11527806005735176809/11530000000000000000 : ℝ)+2*(56491694513/57650000000000 : ℝ)*(777/5000 : ℝ)=(10001142696848313/10000000000000000 : ℝ) by norm_num, show 1+2*(3175904993518027/12500000000000000000 : ℝ)=(6253175904993518027/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11527806005735176809/11530000000000000000 : ℝ)*(X 1 0+X 2 0)+(56491694513/57650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (777/5000 : ℝ)) (c := (11527806005735176809/11530000000000000000 : ℝ)) (alpha := (56491694513/57650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11527806005735176809/11530000000000000000 : ℝ)*(X 0 1+X 2 1)+(56491694513/57650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (777/5000 : ℝ)) (c := (11527806005735176809/11530000000000000000 : ℝ)) (alpha := (56491694513/57650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11527806005735176809/11530000000000000000 : ℝ)*(X 0 2+X 1 2)+(56491694513/57650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (777/5000 : ℝ)) (c := (11527806005735176809/11530000000000000000 : ℝ)) (alpha := (56491694513/57650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-230393273/1250000000 : ℝ)*X 0 0+(271566939/500000000 : ℝ)*X 0 1+(5218172251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668838757/1250000000 : ℝ)*X 1 0+(-390457983/2000000000 : ℝ)*X 1 1+(2609086243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675355203/5000000000 : ℝ)*X 2 0+(1304543039/2500000000 : ℝ)*X 2 1+(-390457977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((106547297/250000000 : ℝ)*X 0 0+(125724443/312500000 : ℝ)*X 0 1+(451235163/1000000000 : ℝ)*X 0 2+(106547297/250000000 : ℝ)*X 1 0+(125724443/312500000 : ℝ)*X 1 1+(451235163/1000000000 : ℝ)*X 1 2+(106547297/250000000 : ℝ)*X 2 0+(125724443/312500000 : ℝ)*X 2 1+(451235163/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-921587257/5000000000 : ℝ)*X 0 0+(652409527/1250000000 : ℝ)*X 0 1+(169694587/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529461231/1000000000 : ℝ)*X 1 0+(-1740235239/10000000000 : ℝ)*X 1 1+(271511337/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647306129/5000000000 : ℝ)*X 2 0+(1357556681/2500000000 : ℝ)*X 2 1+(-217529417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261956943/10000000000 : ℝ)*X 0 0+(4509818431/10000000000 : ℝ)*X 0 1+(2012867241/5000000000 : ℝ)*X 0 2+(4261956943/10000000000 : ℝ)*X 1 0+(4509818431/10000000000 : ℝ)*X 1 1+(2012867241/5000000000 : ℝ)*X 1 2+(4261956943/10000000000 : ℝ)*X 2 0+(4509818431/10000000000 : ℝ)*X 2 1+(2012867241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4089737635826198311230301791/576500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10789827/1000000000000 : ℝ)*(base19) + (81542227/6250000000000 : ℝ)*(base23) + (542879/1250000000000 : ℝ)*(lower2) + (218989183/100000000000000 : ℝ)*(upper3) + (237926289/100000000000000 : ℝ)*(upper5) + (3367750470565133/100000000000000 : ℝ)*(major0) + (3367750470565133/100000000000000 : ℝ)*(major1) + (3367750470565133/100000000000000 : ℝ)*(major2) + (18764735670257/400000000000 : ℝ)*(sp0) + (2345601020712669/50000000000000 : ℝ)*(sp1) + (4691201815732407/100000000000000 : ℝ)*(sp2) + (2044289030380369/100000000000000 : ℝ)*(sp3) + (19202843789/100000000000000 : ℝ)*(sp4) + (4276936243/50000000000000 : ℝ)*(sp7) + (255537198031607/12500000000000 : ℝ)*(f.failure) + (4691203120408039/100000000000000 : ℝ)*(f.sum) + (5942850419689/2882500000000000000000000000 : ℝ)*base65 + (11876175732349400597/1153000000000000000000000000000000 : ℝ)*base67 + (7757748429392599403/1153000000000000000000000000000000 : ℝ)*base70 + (1945230875786599403/1153000000000000000000000000000000 : ℝ)*base72 + (22608693866679/2882500000000000000000000000 : ℝ)*base73 + (5940607650481400597/1153000000000000000000000000000000 : ℝ)*base75 + (1987348021828599403/1153000000000000000000000000000000 : ℝ)*base78 + (8066829512054599403/1153000000000000000000000000000000 : ℝ)*base80 + (11284134257697/5765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17455713/1250000000000000000000 : ℝ)*base89 + (17455713/1250000000000000000000 : ℝ)*base91 + (17455713/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14712663199488281756643/2882500000000000000000000000 : ℝ) := by norm_num
    linear_combination (169243179/20000000000000 : ℝ)*(base19) + (171907601/20000000000000 : ℝ)*(base23) + (44162179/50000000000000 : ℝ)*(upper3) + (20973961/50000000000000 : ℝ)*(lower4) + (121127221/100000000000000 : ℝ)*(upper5) + (850775455194717/25000000000000 : ℝ)*(major0) + (850775455194717/25000000000000 : ℝ)*(major1) + (850775455194717/25000000000000 : ℝ)*(major2) + (2617435389/20000000000000 : ℝ)*(sp1) + (11260986777/100000000000000 : ℝ)*(sp2) + (2370223425397207/50000000000000 : ℝ)*(sp4) + (2370216458700787/50000000000000 : ℝ)*(sp5) + (74069292660463/1562500000000 : ℝ)*(sp6) + (41315132412511/2000000000000 : ℝ)*(sp7) + (41315132412511/2000000000000 : ℝ)*(f.failure) + (2370223425397207/50000000000000 : ℝ)*(f.sum) + (14328943470371/2882500000000000000000000000 : ℝ)*base66 + (2044305993798581947/288250000000000000000000000000000 : ℝ)*base68 + (304980450474918053/288250000000000000000000000000000 : ℝ)*base69 + (4205880935925581947/288250000000000000000000000000000 : ℝ)*base72 + (6397306272983/5765000000000000000000000000 : ℝ)*base73 + (5007767827859418053/288250000000000000000000000000000 : ℝ)*base75 + (2931243949344081947/288250000000000000000000000000000 : ℝ)*base78 + (682028989334418053/288250000000000000000000000000000 : ℝ)*base79 + (20414258588773/5765000000000000000000000000 : ℝ)*base81 + (2213849/200000000000000000000 : ℝ)*base89 + (2213849/200000000000000000000 : ℝ)*base91 + (2213849/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1529_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (777/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1529_s5_0 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46079707/250000000 : ℝ)*x 0 + (1357765209/2500000000 : ℝ)*x 1 + (5218422307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46079707/250000000 : ℝ)^4555 ≤ (2257422394311/20000000000000 : ℝ)^3531 := by
    have hnat : (46079707 : ℕ)^4555*20000000000000^3531 ≤ 2257422394311^3531*250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46079707 250000000 2257422394311 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357765209/2500000000 : ℝ)^4555 ≤ (9099771058019/20000000000000 : ℝ)^3531 := by
    have hnat : (1357765209 : ℕ)^4555*20000000000000^3531 ≤ 9099771058019^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357765209 2500000000 9099771058019 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218422307/10000000000 : ℝ)^4555 ≤ (43214032718287/100000000000000 : ℝ)^3531 := by
    have hnat : (5218422307 : ℕ)^4555*100000000000000^3531 ≤ 43214032718287^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218422307 10000000000 43214032718287 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46079707/250000000 : ℝ), (1357765209/2500000000 : ℝ), (5218422307/10000000000 : ℝ)] ![(2257422394311/20000000000000 : ℝ), (9099771058019/20000000000000 : ℝ), (43214032718287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46079707/250000000 : ℝ)|^4555 ≤ (2257422394311/20000000000000 : ℝ)^3531
        have hw : |(-46079707/250000000 : ℝ)|=(46079707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357765209/2500000000 : ℝ)|^4555 ≤ (9099771058019/20000000000000 : ℝ)^3531
        have hw : |(1357765209/2500000000 : ℝ)|=(1357765209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218422307/10000000000 : ℝ)|^4555 ≤ (43214032718287/100000000000000 : ℝ)^3531
        have hw : |(5218422307/10000000000 : ℝ)|=(5218422307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_1 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337659291/2500000000 : ℝ)*x 0 + (-976027659/5000000000 : ℝ)*x 1 + (2609211153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337659291/2500000000 : ℝ)^4555 ≤ (44631586832743/100000000000000 : ℝ)^3531 := by
    have hnat : (1337659291 : ℕ)^4555*100000000000000^3531 ≤ 44631586832743^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337659291 2500000000 44631586832743 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976027659/5000000000 : ℝ)^4555 ≤ (1215438045109/10000000000000 : ℝ)^3531 := by
    have hnat : (976027659 : ℕ)^4555*10000000000000^3531 ≤ 1215438045109^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976027659 5000000000 1215438045109 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609211153/5000000000 : ℝ)^4555 ≤ (8642806541521/20000000000000 : ℝ)^3531 := by
    have hnat : (2609211153 : ℕ)^4555*20000000000000^3531 ≤ 8642806541521^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609211153 5000000000 8642806541521 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337659291/2500000000 : ℝ), (-976027659/5000000000 : ℝ), (2609211153/5000000000 : ℝ)] ![(44631586832743/100000000000000 : ℝ), (1215438045109/10000000000000 : ℝ), (8642806541521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337659291/2500000000 : ℝ)|^4555 ≤ (44631586832743/100000000000000 : ℝ)^3531
        have hw : |(1337659291/2500000000 : ℝ)|=(1337659291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976027659/5000000000 : ℝ)|^4555 ≤ (1215438045109/10000000000000 : ℝ)^3531
        have hw : |(-976027659/5000000000 : ℝ)|=(976027659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609211153/5000000000 : ℝ)|^4555 ≤ (8642806541521/20000000000000 : ℝ)^3531
        have hw : |(2609211153/5000000000 : ℝ)|=(2609211153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_2 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675318581/5000000000 : ℝ)*x 0 + (1304605577/2500000000 : ℝ)*x 1 + (-1952055317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675318581/5000000000 : ℝ)^4555 ≤ (22315793405611/50000000000000 : ℝ)^3531 := by
    have hnat : (2675318581 : ℕ)^4555*50000000000000^3531 ≤ 22315793405611^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675318581 5000000000 22315793405611 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304605577/2500000000 : ℝ)^4555 ≤ (4321403272897/10000000000000 : ℝ)^3531 := by
    have hnat : (1304605577 : ℕ)^4555*10000000000000^3531 ≤ 4321403272897^3531*2500000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304605577 2500000000 4321403272897 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952055317/10000000000 : ℝ)^4555 ≤ (6077190221529/50000000000000 : ℝ)^3531 := by
    have hnat : (1952055317 : ℕ)^4555*50000000000000^3531 ≤ 6077190221529^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952055317 10000000000 6077190221529 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675318581/5000000000 : ℝ), (1304605577/2500000000 : ℝ), (-1952055317/10000000000 : ℝ)] ![(22315793405611/50000000000000 : ℝ), (4321403272897/10000000000000 : ℝ), (6077190221529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675318581/5000000000 : ℝ)|^4555 ≤ (22315793405611/50000000000000 : ℝ)^3531
        have hw : |(2675318581/5000000000 : ℝ)|=(2675318581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304605577/2500000000 : ℝ)|^4555 ≤ (4321403272897/10000000000000 : ℝ)^3531
        have hw : |(1304605577/2500000000 : ℝ)|=(1304605577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952055317/10000000000 : ℝ)|^4555 ≤ (6077190221529/50000000000000 : ℝ)^3531
        have hw : |(-1952055317/10000000000 : ℝ)|=(1952055317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_3 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130958783/5000000000 : ℝ)*x 0 + (100594633/250000000 : ℝ)*x 1 + (2255871469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130958783/5000000000 : ℝ)^4555 ≤ (1664023532809/5000000000000 : ℝ)^3531 := by
    have hnat : (2130958783 : ℕ)^4555*5000000000000^3531 ≤ 1664023532809^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130958783 5000000000 1664023532809 5000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100594633/250000000 : ℝ)^4555 ≤ (30901372887349/100000000000000 : ℝ)^3531 := by
    have hnat : (100594633 : ℕ)^4555*100000000000000^3531 ≤ 30901372887349^3531*250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100594633 250000000 30901372887349 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255871469/5000000000 : ℝ)^4555 ≤ (1119317388877/3125000000000 : ℝ)^3531 := by
    have hnat : (2255871469 : ℕ)^4555*3125000000000^3531 ≤ 1119317388877^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255871469 5000000000 1119317388877 3125000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130958783/5000000000 : ℝ), (100594633/250000000 : ℝ), (2255871469/5000000000 : ℝ)] ![(1664023532809/5000000000000 : ℝ), (30901372887349/100000000000000 : ℝ), (1119317388877/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130958783/5000000000 : ℝ)|^4555 ≤ (1664023532809/5000000000000 : ℝ)^3531
        have hw : |(2130958783/5000000000 : ℝ)|=(2130958783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100594633/250000000 : ℝ)|^4555 ≤ (30901372887349/100000000000000 : ℝ)^3531
        have hw : |(100594633/250000000 : ℝ)|=(100594633/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255871469/5000000000 : ℝ)|^4555 ≤ (1119317388877/3125000000000 : ℝ)^3531
        have hw : |(2255871469/5000000000 : ℝ)|=(2255871469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_4 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1843216677/10000000000 : ℝ)*x 0 + (5219520717/10000000000 : ℝ)*x 1 + (5429954253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843216677/10000000000 : ℝ)^4555 ≤ (11287336296323/100000000000000 : ℝ)^3531 := by
    have hnat : (1843216677 : ℕ)^4555*100000000000000^3531 ≤ 11287336296323^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843216677 10000000000 11287336296323 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219520717/10000000000 : ℝ)^4555 ≤ (43225766931373/100000000000000 : ℝ)^3531 := by
    have hnat : (5219520717 : ℕ)^4555*100000000000000^3531 ≤ 43225766931373^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219520717 10000000000 43225766931373 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429954253/10000000000 : ℝ)^4555 ≤ (22743448382367/50000000000000 : ℝ)^3531 := by
    have hnat : (5429954253 : ℕ)^4555*50000000000000^3531 ≤ 22743448382367^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429954253 10000000000 22743448382367 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1843216677/10000000000 : ℝ), (5219520717/10000000000 : ℝ), (5429954253/10000000000 : ℝ)] ![(11287336296323/100000000000000 : ℝ), (43225766931373/100000000000000 : ℝ), (22743448382367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1843216677/10000000000 : ℝ)|^4555 ≤ (11287336296323/100000000000000 : ℝ)^3531
        have hw : |(-1843216677/10000000000 : ℝ)|=(1843216677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219520717/10000000000 : ℝ)|^4555 ≤ (43225766931373/100000000000000 : ℝ)^3531
        have hw : |(5219520717/10000000000 : ℝ)|=(5219520717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429954253/10000000000 : ℝ)|^4555 ≤ (22743448382367/50000000000000 : ℝ)^3531
        have hw : |(5429954253/10000000000 : ℝ)|=(5429954253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_5 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647339211/5000000000 : ℝ)*x 0 + (-348104679/2000000000 : ℝ)*x 1 + (1085990789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647339211/5000000000 : ℝ)^4555 ≤ (8806073012771/20000000000000 : ℝ)^3531 := by
    have hnat : (2647339211 : ℕ)^4555*20000000000000^3531 ≤ 8806073012771^3531*5000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647339211 5000000000 8806073012771 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348104679/2000000000 : ℝ)^4555 ≤ (5241370740559/50000000000000 : ℝ)^3531 := by
    have hnat : (348104679 : ℕ)^4555*50000000000000^3531 ≤ 5241370740559^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348104679 2000000000 5241370740559 50000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085990789/2000000000 : ℝ)^4555 ≤ (9097378687273/20000000000000 : ℝ)^3531 := by
    have hnat : (1085990789 : ℕ)^4555*20000000000000^3531 ≤ 9097378687273^3531*2000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085990789 2000000000 9097378687273 20000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647339211/5000000000 : ℝ), (-348104679/2000000000 : ℝ), (1085990789/2000000000 : ℝ)] ![(8806073012771/20000000000000 : ℝ), (5241370740559/50000000000000 : ℝ), (9097378687273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647339211/5000000000 : ℝ)|^4555 ≤ (8806073012771/20000000000000 : ℝ)^3531
        have hw : |(2647339211/5000000000 : ℝ)|=(2647339211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348104679/2000000000 : ℝ)|^4555 ≤ (5241370740559/50000000000000 : ℝ)^3531
        have hw : |(-348104679/2000000000 : ℝ)|=(348104679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085990789/2000000000 : ℝ)|^4555 ≤ (9097378687273/20000000000000 : ℝ)^3531
        have hw : |(1085990789/2000000000 : ℝ)|=(1085990789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_6 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330917391/625000000 : ℝ)*x 0 + (5429953991/10000000000 : ℝ)*x 1 + (-43513089/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330917391/625000000 : ℝ)^4555 ≤ (4403036328307/10000000000000 : ℝ)^3531 := by
    have hnat : (330917391 : ℕ)^4555*10000000000000^3531 ≤ 4403036328307^3531*625000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330917391 625000000 4403036328307 10000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429953991/10000000000 : ℝ)^4555 ≤ (45486893933459/100000000000000 : ℝ)^3531 := by
    have hnat : (5429953991 : ℕ)^4555*100000000000000^3531 ≤ 45486893933459^3531*10000000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429953991 10000000000 45486893933459 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43513089/250000000 : ℝ)^4555 ≤ (1310342845383/12500000000000 : ℝ)^3531 := by
    have hnat : (43513089 : ℕ)^4555*12500000000000^3531 ≤ 1310342845383^3531*250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43513089 250000000 1310342845383 12500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330917391/625000000 : ℝ), (5429953991/10000000000 : ℝ), (-43513089/250000000 : ℝ)] ![(4403036328307/10000000000000 : ℝ), (45486893933459/100000000000000 : ℝ), (1310342845383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330917391/625000000 : ℝ)|^4555 ≤ (4403036328307/10000000000000 : ℝ)^3531
        have hw : |(330917391/625000000 : ℝ)|=(330917391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429953991/10000000000 : ℝ)|^4555 ≤ (45486893933459/100000000000000 : ℝ)^3531
        have hw : |(5429953991/10000000000 : ℝ)|=(5429953991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43513089/250000000 : ℝ)|^4555 ≤ (1310342845383/12500000000000 : ℝ)^3531
        have hw : |(-43513089/250000000 : ℝ)|=(43513089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1529_s5_7 (p : ℝ) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266373911/625000000 : ℝ)*x 0 + (281826381/625000000 : ℝ)*x 1 + (503290587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266373911/625000000 : ℝ)^4555 ≤ (8320281381963/25000000000000 : ℝ)^3531 := by
    have hnat : (266373911 : ℕ)^4555*25000000000000^3531 ≤ 8320281381963^3531*625000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266373911 625000000 8320281381963 25000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281826381/625000000 : ℝ)^4555 ≤ (178961710831/500000000000 : ℝ)^3531 := by
    have hnat : (281826381 : ℕ)^4555*500000000000^3531 ≤ 178961710831^3531*625000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281826381 625000000 178961710831 500000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503290587/1250000000 : ℝ)^4555 ≤ (30926532293233/100000000000000 : ℝ)^3531 := by
    have hnat : (503290587 : ℕ)^4555*100000000000000^3531 ≤ 30926532293233^3531*1250000000^4555 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503290587 1250000000 30926532293233 100000000000000 4555 3531 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4555/1024 : ℝ)) 4555 3531 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266373911/625000000 : ℝ), (281826381/625000000 : ℝ), (503290587/1250000000 : ℝ)] ![(8320281381963/25000000000000 : ℝ), (178961710831/500000000000 : ℝ), (30926532293233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266373911/625000000 : ℝ)|^4555 ≤ (8320281381963/25000000000000 : ℝ)^3531
        have hw : |(266373911/625000000 : ℝ)|=(266373911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281826381/625000000 : ℝ)|^4555 ≤ (178961710831/500000000000 : ℝ)^3531
        have hw : |(281826381/625000000 : ℝ)|=(281826381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503290587/1250000000 : ℝ)|^4555 ≤ (30926532293233/100000000000000 : ℝ)^3531
        have hw : |(503290587/1250000000 : ℝ)|=(503290587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1529_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5487/50000 : ℝ) ^ (4553/1024 : ℝ) ≤ (2704924848937713/50000000000000000000 : ℝ) := by
    have hpowers : (5487/50000 : ℝ)^4553 ≤ (2704924848937713/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5487 : ℕ)^4553*50000000000000000000^1024 ≤ 2704924848937713^1024*50000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5487 50000 2704924848937713 50000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5487/50000 : ℝ)) (X := (2704924848937713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4553/1024 : ℝ) ≤ (12522887581860261/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4553 ≤ (12522887581860261/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4553*50000000000000000000^1024 ≤ 12522887581860261^1024*10000^4553 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 12522887581860261 50000000000000000000 4553 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (12522887581860261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002704924848937713/25000000000000000000 : ℝ) ≤ (5000121666018423/5000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (25002704924848937713/25000000000000000000 : ℝ)^1024 ≤ (5000121666018423/5000000000000000 : ℝ)^4553 := by
      have hnat : (25002704924848937713 : ℕ)^1024*5000000000000000^4553 ≤ 5000121666018423^4553*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002704924848937713 25000000000000000000 5000121666018423 5000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000121666018423/5000000000000000 : ℝ)) (X := (25002704924848937713/25000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007613906215398987/25000000000000000000 : ℝ) ≤ (2000136977287851/2000000000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (25007613906215398987/25000000000000000000 : ℝ)^1024 ≤ (2000136977287851/2000000000000000 : ℝ)^4553 := by
      have hnat : (25007613906215398987 : ℕ)^1024*2000000000000000^4553 ≤ 2000136977287851^4553*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007613906215398987 25000000000000000000 2000136977287851 2000000000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136977287851/2000000000000000 : ℝ)) (X := (25007613906215398987/25000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012522887581860261/25000000000000000000 : ℝ) ≤ (156267600638151/156250000000000 : ℝ) ^ (4553/1024 : ℝ) := by
    have hpowers : (25012522887581860261/25000000000000000000 : ℝ)^1024 ≤ (156267600638151/156250000000000 : ℝ)^4553 := by
      have hnat : (25012522887581860261 : ℕ)^1024*156250000000000^4553 ≤ 156267600638151^4553*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012522887581860261 25000000000000000000 156267600638151 156250000000000 1024 4553 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156267600638151/156250000000000 : ℝ)) (X := (25012522887581860261/25000000000000000000 : ℝ)) (by norm_num) 4553 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2704924848937713/50000000000000000000 : ℝ) ≤ ((11287851912863580951/11290000000000000000 : ℝ)+2*(441554402409/451600000000000 : ℝ)*(5487/50000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (11287851912863580951/11290000000000000000 : ℝ)+2*(441554402409/451600000000000 : ℝ)*(5487/50000 : ℝ)=(5000121666018423/5000000000000000 : ℝ) by norm_num, show 1+2*(2704924848937713/50000000000000000000 : ℝ)=(25002704924848937713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12522887581860261/50000000000000000000 : ℝ)+(2704924848937713/50000000000000000000 : ℝ) ≤ ((11287851912863580951/11290000000000000000 : ℝ)+(441554402409/451600000000000 : ℝ)*((1549/10000 : ℝ)+(5487/50000 : ℝ)))^(4553/1024 : ℝ) := by
    rw [show (11287851912863580951/11290000000000000000 : ℝ)+(441554402409/451600000000000 : ℝ)*((1549/10000 : ℝ)+(5487/50000 : ℝ))=(2000136977287851/2000000000000000 : ℝ) by norm_num, show 1+(12522887581860261/50000000000000000000 : ℝ)+(2704924848937713/50000000000000000000 : ℝ)=(25007613906215398987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12522887581860261/50000000000000000000 : ℝ) ≤ ((11287851912863580951/11290000000000000000 : ℝ)+2*(441554402409/451600000000000 : ℝ)*(1549/10000 : ℝ))^(4553/1024 : ℝ) := by
    rw [show (11287851912863580951/11290000000000000000 : ℝ)+2*(441554402409/451600000000000 : ℝ)*(1549/10000 : ℝ)=(156267600638151/156250000000000 : ℝ) by norm_num, show 1+2*(12522887581860261/50000000000000000000 : ℝ)=(25012522887581860261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11287851912863580951/11290000000000000000 : ℝ)*(X 1 0+X 2 0)+(441554402409/451600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11287851912863580951/11290000000000000000 : ℝ)) (alpha := (441554402409/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11287851912863580951/11290000000000000000 : ℝ)*(X 0 1+X 2 1)+(441554402409/451600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11287851912863580951/11290000000000000000 : ℝ)) (alpha := (441554402409/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11287851912863580951/11290000000000000000 : ℝ)*(X 0 2+X 1 2)+(441554402409/451600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4553/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11287851912863580951/11290000000000000000 : ℝ)) (alpha := (441554402409/451600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-46079707/250000000 : ℝ)*X 0 0+(1357765209/2500000000 : ℝ)*X 0 1+(5218422307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337659291/2500000000 : ℝ)*X 1 0+(-976027659/5000000000 : ℝ)*X 1 1+(2609211153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675318581/5000000000 : ℝ)*X 2 0+(1304605577/2500000000 : ℝ)*X 2 1+(-1952055317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130958783/5000000000 : ℝ)*X 0 0+(100594633/250000000 : ℝ)*X 0 1+(2255871469/5000000000 : ℝ)*X 0 2+(2130958783/5000000000 : ℝ)*X 1 0+(100594633/250000000 : ℝ)*X 1 1+(2255871469/5000000000 : ℝ)*X 1 2+(2130958783/5000000000 : ℝ)*X 2 0+(100594633/250000000 : ℝ)*X 2 1+(2255871469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1843216677/10000000000 : ℝ)*X 0 0+(5219520717/10000000000 : ℝ)*X 0 1+(5429954253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647339211/5000000000 : ℝ)*X 1 0+(-348104679/2000000000 : ℝ)*X 1 1+(1085990789/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330917391/625000000 : ℝ)*X 2 0+(5429953991/10000000000 : ℝ)*X 2 1+(-43513089/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266373911/625000000 : ℝ)*X 0 0+(281826381/625000000 : ℝ)*X 0 1+(503290587/1250000000 : ℝ)*X 0 2+(266373911/625000000 : ℝ)*X 1 0+(281826381/625000000 : ℝ)*X 1 1+(503290587/1250000000 : ℝ)*X 1 2+(266373911/625000000 : ℝ)*X 2 0+(281826381/625000000 : ℝ)*X 2 1+(503290587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1529_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3046658241866334134540046063/282250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1870855877/100000000000000 : ℝ)*(base19) + (109021017/6250000000000 : ℝ)*(base23) + (2670219/4000000000000 : ℝ)*(lower2) + (53575813/20000000000000 : ℝ)*(upper3) + (22176007/12500000000000 : ℝ)*(upper5) + (1688065515430143/50000000000000 : ℝ)*(major0) + (1688065515430143/50000000000000 : ℝ)*(major1) + (1688065515430143/50000000000000 : ℝ)*(major2) + (940569466396773/20000000000000 : ℝ)*(sp0) + (940575012985391/20000000000000 : ℝ)*(sp1) + (29392969946541/625000000000 : ℝ)*(sp2) + (2049370787436017/100000000000000 : ℝ)*(sp3) + (3700474871/12500000000000 : ℝ)*(sp4) + (3494673901/25000000000000 : ℝ)*(sp7) + (1024692383065811/50000000000000 : ℝ)*(f.failure) + (293929808486427/6250000000000 : ℝ)*(f.sum) + (66104548617387/11290000000000000000000000000 : ℝ)*base65 + (62171622938180993/564500000000000000000000000000000 : ℝ)*base67 + (1496140394537680993/564500000000000000000000000000000 : ℝ)*base69 + (4028259135011180993/564500000000000000000000000000000 : ℝ)*base71 + (1182975817627/11290000000000000000000000000 : ℝ)*base73 + (5276048894308180993/564500000000000000000000000000000 : ℝ)*base75 + (3969151977061180993/564500000000000000000000000000000 : ℝ)*base77 + (8682521692120180993/564500000000000000000000000000000 : ℝ)*base79 + (23315495809587/11290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (19468549/5000000000000000000000 : ℝ)*base89 + (19468549/5000000000000000000000 : ℝ)*base91 + (19468549/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120421486604410577642231811/56450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (869810903/100000000000000 : ℝ)*(base19) + (176255747/25000000000000 : ℝ)*(base23) + (99201943/100000000000000 : ℝ)*(lower1) + (9250621/50000000000000 : ℝ)*(upper2) + (12595597/25000000000000 : ℝ)*(upper3) + (19474581/20000000000000 : ℝ)*(upper5) + (341145984738713/10000000000000 : ℝ)*(major0) + (341145984738713/10000000000000 : ℝ)*(major1) + (341145984738713/10000000000000 : ℝ)*(major2) + (2400560571/50000000000000 : ℝ)*(sp1) + (1188022374899649/25000000000000 : ℝ)*(sp4) + (4752083828666551/100000000000000 : ℝ)*(sp5) + (594011099321951/12500000000000 : ℝ)*(sp6) + (2070830124067603/100000000000000 : ℝ)*(sp7) + (2070830124067603/100000000000000 : ℝ)*(f.failure) + (1188022374899649/25000000000000 : ℝ)*(f.sum) + (3412515329929/2258000000000000000000000000 : ℝ)*base65 + (692709939311481063/112900000000000000000000000000000 : ℝ)*base67 + (1932100270290918937/112900000000000000000000000000000 : ℝ)*base70 + (764627248569281063/112900000000000000000000000000000 : ℝ)*base71 + (2749877567171/2258000000000000000000000000 : ℝ)*base73 + (325528569022018937/112900000000000000000000000000000 : ℝ)*base76 + (927045658459081063/112900000000000000000000000000000 : ℝ)*base77 + (1053454996983081063/112900000000000000000000000000000 : ℝ)*base79 + (19832692747953/2258000000000000000000000000 : ℝ)*base81 + (49675323/10000000000000000000000 : ℝ)*base90 + (49675323/10000000000000000000000 : ℝ)*base92 + (49675323/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1529_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1529_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1529_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1529_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1529_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1529_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4553/1024 : ℝ) ≤ p) (hpb : p ≤ (4555/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164738759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3187/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2641/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1529_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

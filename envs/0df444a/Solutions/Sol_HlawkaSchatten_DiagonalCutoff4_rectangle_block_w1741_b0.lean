-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:10.277085+00:00
-- url     : https://prove2.me/submissions/a44cb4c8-cdc6-4616-8c7c-49e0dd06165b

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
theorem support_rectangle_w1741_s0_0 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1221589913/10000000000 : ℝ)*x 0 + (2829609029/5000000000 : ℝ)*x 1 + (496351523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221589913/10000000000 : ℝ)^5631 ≤ (1913885470991/25000000000000 : ℝ)^4607 := by
    have hnat : (1221589913 : ℕ)^5631*25000000000000^4607 ≤ 1913885470991^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221589913 10000000000 1913885470991 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829609029/5000000000 : ℝ)^5631 ≤ (49865650216251/100000000000000 : ℝ)^4607 := by
    have hnat : (2829609029 : ℕ)^5631*100000000000000^4607 ≤ 49865650216251^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829609029 5000000000 49865650216251 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496351523/1000000000 : ℝ)^5631 ≤ (21239403939873/50000000000000 : ℝ)^4607 := by
    have hnat : (496351523 : ℕ)^5631*50000000000000^4607 ≤ 21239403939873^4607*1000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496351523 1000000000 21239403939873 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1221589913/10000000000 : ℝ), (2829609029/5000000000 : ℝ), (496351523/1000000000 : ℝ)] ![(1913885470991/25000000000000 : ℝ), (49865650216251/100000000000000 : ℝ), (21239403939873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1221589913/10000000000 : ℝ)|^5631 ≤ (1913885470991/25000000000000 : ℝ)^4607
        have hw : |(-1221589913/10000000000 : ℝ)|=(1221589913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829609029/5000000000 : ℝ)|^5631 ≤ (49865650216251/100000000000000 : ℝ)^4607
        have hw : |(2829609029/5000000000 : ℝ)|=(2829609029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496351523/1000000000 : ℝ)|^5631 ≤ (21239403939873/50000000000000 : ℝ)^4607
        have hw : |(496351523/1000000000 : ℝ)|=(496351523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_1 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691286597/5000000000 : ℝ)*x 0 + (-399132287/2500000000 : ℝ)*x 1 + (4963515617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691286597/5000000000 : ℝ)^5631 ≤ (1465706377689/3125000000000 : ℝ)^4607 := by
    have hnat : (2691286597 : ℕ)^5631*3125000000000^4607 ≤ 1465706377689^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691286597 5000000000 1465706377689 3125000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399132287/2500000000 : ℝ)^5631 ≤ (5309291986351/50000000000000 : ℝ)^4607 := by
    have hnat : (399132287 : ℕ)^5631*50000000000000^4607 ≤ 5309291986351^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399132287 2500000000 5309291986351 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4963515617/10000000000 : ℝ)^5631 ≤ (42478811927939/100000000000000 : ℝ)^4607 := by
    have hnat : (4963515617 : ℕ)^5631*100000000000000^4607 ≤ 42478811927939^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963515617 10000000000 42478811927939 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691286597/5000000000 : ℝ), (-399132287/2500000000 : ℝ), (4963515617/10000000000 : ℝ)] ![(1465706377689/3125000000000 : ℝ), (5309291986351/50000000000000 : ℝ), (42478811927939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691286597/5000000000 : ℝ)|^5631 ≤ (1465706377689/3125000000000 : ℝ)^4607
        have hw : |(2691286597/5000000000 : ℝ)|=(2691286597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399132287/2500000000 : ℝ)|^5631 ≤ (5309291986351/50000000000000 : ℝ)^4607
        have hw : |(-399132287/2500000000 : ℝ)|=(399132287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4963515617/10000000000 : ℝ)|^5631 ≤ (42478811927939/100000000000000 : ℝ)^4607
        have hw : |(4963515617/10000000000 : ℝ)|=(4963515617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_2 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345643029/2500000000 : ℝ)*x 0 + (620439571/1250000000 : ℝ)*x 1 + (-1596529337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345643029/2500000000 : ℝ)^5631 ≤ (23451296302347/50000000000000 : ℝ)^4607 := by
    have hnat : (1345643029 : ℕ)^5631*50000000000000^4607 ≤ 23451296302347^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345643029 2500000000 23451296302347 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620439571/1250000000 : ℝ)^5631 ≤ (1699152875033/4000000000000 : ℝ)^4607 := by
    have hnat : (620439571 : ℕ)^5631*4000000000000^4607 ≤ 1699152875033^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620439571 1250000000 1699152875033 4000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596529337/10000000000 : ℝ)^5631 ≤ (10618585509153/100000000000000 : ℝ)^4607 := by
    have hnat : (1596529337 : ℕ)^5631*100000000000000^4607 ≤ 10618585509153^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596529337 10000000000 10618585509153 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345643029/2500000000 : ℝ), (620439571/1250000000 : ℝ), (-1596529337/10000000000 : ℝ)] ![(23451296302347/50000000000000 : ℝ), (1699152875033/4000000000000 : ℝ), (10618585509153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345643029/2500000000 : ℝ)|^5631 ≤ (23451296302347/50000000000000 : ℝ)^4607
        have hw : |(1345643029/2500000000 : ℝ)|=(1345643029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620439571/1250000000 : ℝ)|^5631 ≤ (1699152875033/4000000000000 : ℝ)^4607
        have hw : |(620439571/1250000000 : ℝ)|=(620439571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1596529337/10000000000 : ℝ)|^5631 ≤ (10618585509153/100000000000000 : ℝ)^4607
        have hw : |(-1596529337/10000000000 : ℝ)|=(1596529337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_3 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (399101527/1000000000 : ℝ)*x 0 + (2975763017/10000000000 : ℝ)*x 1 + (2588871517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399101527/1000000000 : ℝ)^5631 ≤ (32539884846641/100000000000000 : ℝ)^4607 := by
    have hnat : (399101527 : ℕ)^5631*100000000000000^4607 ≤ 32539884846641^4607*1000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399101527 1000000000 32539884846641 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2975763017/10000000000 : ℝ)^5631 ≤ (11364878804501/50000000000000 : ℝ)^4607 := by
    have hnat : (2975763017 : ℕ)^5631*50000000000000^4607 ≤ 11364878804501^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975763017 10000000000 11364878804501 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588871517/5000000000 : ℝ)^5631 ≤ (447303575313/1000000000000 : ℝ)^4607 := by
    have hnat : (2588871517 : ℕ)^5631*1000000000000^4607 ≤ 447303575313^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588871517 5000000000 447303575313 1000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399101527/1000000000 : ℝ), (2975763017/10000000000 : ℝ), (2588871517/5000000000 : ℝ)] ![(32539884846641/100000000000000 : ℝ), (11364878804501/50000000000000 : ℝ), (447303575313/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399101527/1000000000 : ℝ)|^5631 ≤ (32539884846641/100000000000000 : ℝ)^4607
        have hw : |(399101527/1000000000 : ℝ)|=(399101527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2975763017/10000000000 : ℝ)|^5631 ≤ (11364878804501/50000000000000 : ℝ)^4607
        have hw : |(2975763017/10000000000 : ℝ)|=(2975763017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588871517/5000000000 : ℝ)|^5631 ≤ (447303575313/1000000000000 : ℝ)^4607
        have hw : |(2588871517/5000000000 : ℝ)|=(2588871517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_4 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-611578979/5000000000 : ℝ)*x 0 + (4981496189/10000000000 : ℝ)*x 1 + (705078071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (611578979/5000000000 : ℝ)^5631 ≤ (7667554518509/100000000000000 : ℝ)^4607 := by
    have hnat : (611578979 : ℕ)^5631*100000000000000^4607 ≤ 7667554518509^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611578979 5000000000 7667554518509 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4981496189/10000000000 : ℝ)^5631 ≤ (21333486208289/50000000000000 : ℝ)^4607 := by
    have hnat : (4981496189 : ℕ)^5631*50000000000000^4607 ≤ 21333486208289^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981496189 10000000000 21333486208289 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705078071/1250000000 : ℝ)^5631 ≤ (4966547304571/10000000000000 : ℝ)^4607 := by
    have hnat : (705078071 : ℕ)^5631*10000000000000^4607 ≤ 4966547304571^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705078071 1250000000 4966547304571 10000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-611578979/5000000000 : ℝ), (4981496189/10000000000 : ℝ), (705078071/1250000000 : ℝ)] ![(7667554518509/100000000000000 : ℝ), (21333486208289/50000000000000 : ℝ), (4966547304571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-611578979/5000000000 : ℝ)|^5631 ≤ (7667554518509/100000000000000 : ℝ)^4607
        have hw : |(-611578979/5000000000 : ℝ)|=(611578979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4981496189/10000000000 : ℝ)|^5631 ≤ (21333486208289/50000000000000 : ℝ)^4607
        have hw : |(4981496189/10000000000 : ℝ)|=(4981496189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705078071/1250000000 : ℝ)|^5631 ≤ (4966547304571/10000000000000 : ℝ)^4607
        have hw : |(705078071/1250000000 : ℝ)|=(705078071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_5 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598098773/5000000000 : ℝ)*x 0 + (-229855351/2500000000 : ℝ)*x 1 + (5640625469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598098773/5000000000 : ℝ)^5631 ≤ (22462649355953/50000000000000 : ℝ)^4607 := by
    have hnat : (2598098773 : ℕ)^5631*50000000000000^4607 ≤ 22462649355953^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598098773 5000000000 22462649355953 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229855351/2500000000 : ℝ)^5631 ≤ (1081843706919/20000000000000 : ℝ)^4607 := by
    have hnat : (229855351 : ℕ)^5631*20000000000000^4607 ≤ 1081843706919^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229855351 2500000000 1081843706919 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5640625469/10000000000 : ℝ)^5631 ≤ (49665482742311/100000000000000 : ℝ)^4607 := by
    have hnat : (5640625469 : ℕ)^5631*100000000000000^4607 ≤ 49665482742311^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640625469 10000000000 49665482742311 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598098773/5000000000 : ℝ), (-229855351/2500000000 : ℝ), (5640625469/10000000000 : ℝ)] ![(22462649355953/50000000000000 : ℝ), (1081843706919/20000000000000 : ℝ), (49665482742311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598098773/5000000000 : ℝ)|^5631 ≤ (22462649355953/50000000000000 : ℝ)^4607
        have hw : |(2598098773/5000000000 : ℝ)|=(2598098773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-229855351/2500000000 : ℝ)|^5631 ≤ (1081843706919/20000000000000 : ℝ)^4607
        have hw : |(-229855351/2500000000 : ℝ)|=(229855351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5640625469/10000000000 : ℝ)|^5631 ≤ (49665482742311/100000000000000 : ℝ)^4607
        have hw : |(5640625469/10000000000 : ℝ)|=(5640625469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_6 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598099509/5000000000 : ℝ)*x 0 + (1128124783/2000000000 : ℝ)*x 1 + (-919421567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598099509/5000000000 : ℝ)^5631 ≤ (561566428341/1250000000000 : ℝ)^4607 := by
    have hnat : (2598099509 : ℕ)^5631*1250000000000^4607 ≤ 561566428341^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598099509 5000000000 561566428341 1250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128124783/2000000000 : ℝ)^5631 ≤ (49665466018097/100000000000000 : ℝ)^4607 := by
    have hnat : (1128124783 : ℕ)^5631*100000000000000^4607 ≤ 49665466018097^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128124783 2000000000 49665466018097 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919421567/10000000000 : ℝ)^5631 ≤ (5409219706723/100000000000000 : ℝ)^4607 := by
    have hnat : (919421567 : ℕ)^5631*100000000000000^4607 ≤ 5409219706723^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919421567 10000000000 5409219706723 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598099509/5000000000 : ℝ), (1128124783/2000000000 : ℝ), (-919421567/10000000000 : ℝ)] ![(561566428341/1250000000000 : ℝ), (49665466018097/100000000000000 : ℝ), (5409219706723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598099509/5000000000 : ℝ)|^5631 ≤ (561566428341/1250000000000 : ℝ)^4607
        have hw : |(2598099509/5000000000 : ℝ)|=(2598099509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128124783/2000000000 : ℝ)|^5631 ≤ (49665466018097/100000000000000 : ℝ)^4607
        have hw : |(1128124783/2000000000 : ℝ)|=(1128124783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919421567/10000000000 : ℝ)|^5631 ≤ (5409219706723/100000000000000 : ℝ)^4607
        have hw : |(-919421567/10000000000 : ℝ)|=(919421567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s0_7 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3995983891/10000000000 : ℝ)*x 0 + (5120834581/10000000000 : ℝ)*x 1 + (606923001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3995983891/10000000000 : ℝ)^5631 ≤ (16294703291999/50000000000000 : ℝ)^4607 := by
    have hnat : (3995983891 : ℕ)^5631*50000000000000^4607 ≤ 16294703291999^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3995983891 10000000000 16294703291999 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5120834581/10000000000 : ℝ)^5631 ≤ (11032547104191/25000000000000 : ℝ)^4607 := by
    have hnat : (5120834581 : ℕ)^5631*25000000000000^4607 ≤ 11032547104191^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120834581 10000000000 11032547104191 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606923001/2000000000 : ℝ)^5631 ≤ (23280404989069/100000000000000 : ℝ)^4607 := by
    have hnat : (606923001 : ℕ)^5631*100000000000000^4607 ≤ 23280404989069^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606923001 2000000000 23280404989069 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3995983891/10000000000 : ℝ), (5120834581/10000000000 : ℝ), (606923001/2000000000 : ℝ)] ![(16294703291999/50000000000000 : ℝ), (11032547104191/25000000000000 : ℝ), (23280404989069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3995983891/10000000000 : ℝ)|^5631 ≤ (16294703291999/50000000000000 : ℝ)^4607
        have hw : |(3995983891/10000000000 : ℝ)|=(3995983891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5120834581/10000000000 : ℝ)|^5631 ≤ (11032547104191/25000000000000 : ℝ)^4607
        have hw : |(5120834581/10000000000 : ℝ)|=(5120834581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606923001/2000000000 : ℝ)|^5631 ≤ (23280404989069/100000000000000 : ℝ)^4607
        have hw : |(606923001/2000000000 : ℝ)|=(606923001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1741_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4269/20000 : ℝ)*pair X 0 0 := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5615/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5615 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5615*1^1024 ≤ 0^1024*1^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5615/1024 : ℝ) ≤ (328780750564316891/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5615 ≤ (328780750564316891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5615*50000000000000000000^1024 ≤ 328780750564316891^1024*5^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 328780750564316891 50000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (328780750564316891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5615 := by
      have hnat : (1 : ℕ)^1024*1^5615 ≤ 1^5615*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50328780750564316891/50000000000000000000 : ℝ) ≤ (5005979875912829/5000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50328780750564316891/50000000000000000000 : ℝ)^1024 ≤ (5005979875912829/5000000000000000 : ℝ)^5615 := by
      have hnat : (50328780750564316891 : ℕ)^1024*5000000000000000^5615 ≤ 5005979875912829^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50328780750564316891 50000000000000000000 5005979875912829 5000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005979875912829/5000000000000000 : ℝ)) (X := (50328780750564316891/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25328780750564316891/25000000000000000000 : ℝ) ≤ (2505979875912829/2500000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (25328780750564316891/25000000000000000000 : ℝ)^1024 ≤ (2505979875912829/2500000000000000 : ℝ)^5615 := by
      have hnat : (25328780750564316891 : ℕ)^1024*2500000000000000^5615 ≤ 2505979875912829^5615*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25328780750564316891 25000000000000000000 2505979875912829 2500000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505979875912829/2500000000000000 : ℝ)) (X := (25328780750564316891/25000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5979875912829/2000000000000000 : ℝ)*(0 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5979875912829/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(328780750564316891/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5979875912829/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5615/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5979875912829/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5005979875912829/5000000000000000 : ℝ) by norm_num, show 1+(328780750564316891/50000000000000000000 : ℝ)+(0 : ℝ)=(50328780750564316891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(328780750564316891/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5979875912829/2000000000000000 : ℝ)*(2/5 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5979875912829/2000000000000000 : ℝ)*(2/5 : ℝ)=(2505979875912829/2500000000000000 : ℝ) by norm_num, show 1+2*(328780750564316891/50000000000000000000 : ℝ)=(25328780750564316891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5979875912829/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5979875912829/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5979875912829/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5979875912829/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5979875912829/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5979875912829/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1221589913/10000000000 : ℝ)*X 0 0+(2829609029/5000000000 : ℝ)*X 0 1+(496351523/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2691286597/5000000000 : ℝ)*X 1 0+(-399132287/2500000000 : ℝ)*X 1 1+(4963515617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345643029/2500000000 : ℝ)*X 2 0+(620439571/1250000000 : ℝ)*X 2 1+(-1596529337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((399101527/1000000000 : ℝ)*X 0 0+(2975763017/10000000000 : ℝ)*X 0 1+(2588871517/5000000000 : ℝ)*X 0 2+(399101527/1000000000 : ℝ)*X 1 0+(2975763017/10000000000 : ℝ)*X 1 1+(2588871517/5000000000 : ℝ)*X 1 2+(399101527/1000000000 : ℝ)*X 2 0+(2975763017/10000000000 : ℝ)*X 2 1+(2588871517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-611578979/5000000000 : ℝ)*X 0 0+(4981496189/10000000000 : ℝ)*X 0 1+(705078071/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598098773/5000000000 : ℝ)*X 1 0+(-229855351/2500000000 : ℝ)*X 1 1+(5640625469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2598099509/5000000000 : ℝ)*X 2 0+(1128124783/2000000000 : ℝ)*X 2 1+(-919421567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3995983891/10000000000 : ℝ)*X 0 0+(5120834581/10000000000 : ℝ)*X 0 1+(606923001/2000000000 : ℝ)*X 0 2+(3995983891/10000000000 : ℝ)*X 1 0+(5120834581/10000000000 : ℝ)*X 1 1+(606923001/2000000000 : ℝ)*X 1 2+(3995983891/10000000000 : ℝ)*X 2 0+(5120834581/10000000000 : ℝ)*X 2 1+(606923001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312869446937345642652249/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13396643/100000000000000 : ℝ)*(base1) + (55504303/6250000000000 : ℝ)*(base19) + (15004783/2500000000000 : ℝ)*(base23) + (28253201/12500000000000 : ℝ)*(upper3) + (90326701/100000000000000 : ℝ)*(upper5) + (945771981758673/100000000000000 : ℝ)*(major0) + (945771981758673/100000000000000 : ℝ)*(major1) + (945771981758673/100000000000000 : ℝ)*(major2) + (1437400948124251/100000000000000 : ℝ)*(sp0) + (718702018775257/50000000000000 : ℝ)*(sp1) + (718702162714021/50000000000000 : ℝ)*(sp2) + (227068824295511/50000000000000 : ℝ)*(sp3) + (1995445877/50000000000000 : ℝ)*(sp4) + (1271620501/100000000000000 : ℝ)*(sp7) + (227069466804083/50000000000000 : ℝ)*(f.failure) + (718702462809681/50000000000000 : ℝ)*(f.sum) + (183612979115917/100000000000000000000000000000 : ℝ)*base65 + (316116958915917/200000000000000000000000000000 : ℝ)*base67 + (500459988284083/200000000000000000000000000000 : ℝ)*base70 + (28072746684083/200000000000000000000000000000 : ℝ)*base72 + (363863024415917/100000000000000000000000000000 : ℝ)*base73 + (488835584515917/200000000000000000000000000000 : ℝ)*base75 + (539343777884083/200000000000000000000000000000 : ℝ)*base78 + (1434247000515917/200000000000000000000000000000 : ℝ)*base79 + (56976347184083/100000000000000000000000000000 : ℝ)*base82 + (4811387/5000000000000000000000 : ℝ)*base89 + (4811387/5000000000000000000000 : ℝ)*base91 + (4811387/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (232158664851914143231509/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14933129/25000000000000 : ℝ)*(base19) + (493876663/100000000000000 : ℝ)*(base23) + (545420053/100000000000000 : ℝ)*(base32) + (100984369/50000000000000 : ℝ)*(base37) + (79629453/100000000000000 : ℝ)*(upper3) + (499122626343307/50000000000000 : ℝ)*(major0) + (499122626343307/50000000000000 : ℝ)*(major1) + (499122626343307/50000000000000 : ℝ)*(major2) + (1227361131/100000000000000 : ℝ)*(sp1) + (1348895927/100000000000000 : ℝ)*(sp2) + (151715474999337/10000000000000 : ℝ)*(sp4) + (379288365724931/25000000000000 : ℝ)*(sp5) + (75857645361039/5000000000000 : ℝ)*(sp6) + (19173387937847/4000000000000 : ℝ)*(sp7) + (239667722917483/50000000000000 : ℝ)*(f.failure) + (151715474999337/10000000000000 : ℝ)*(f.sum) + (62562463664497/50000000000000000000000000000 : ℝ)*base66 + (457084499085503/100000000000000000000000000000 : ℝ)*base67 + (59068043914497/100000000000000000000000000000 : ℝ)*base70 + (609327704714497/100000000000000000000000000000 : ℝ)*base72 + (141222020035503/50000000000000000000000000000 : ℝ)*base73 + (113631966214497/100000000000000000000000000000 : ℝ)*base76 + (132364290114497/100000000000000000000000000000 : ℝ)*base78 + (497593968485503/100000000000000000000000000000 : ℝ)*base79 + (92270201214497/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20696013/5000000000000000000000 : ℝ)*base90 + (20696013/5000000000000000000000 : ℝ)*base92 + (20696013/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1741_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4269/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1741_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1741_s1_0 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-159087557/1250000000 : ℝ)*x 0 + (5514427591/10000000000 : ℝ)*x 1 + (1268572703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159087557/1250000000 : ℝ)^5631 ≤ (1609767954771/20000000000000 : ℝ)^4607 := by
    have hnat : (159087557 : ℕ)^5631*20000000000000^4607 ≤ 1609767954771^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159087557 1250000000 1609767954771 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514427591/10000000000 : ℝ)^5631 ≤ (1932429300391/4000000000000 : ℝ)^4607 := by
    have hnat : (5514427591 : ℕ)^5631*4000000000000^4607 ≤ 1932429300391^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514427591 10000000000 1932429300391 4000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268572703/2500000000 : ℝ)^5631 ≤ (43640427699239/100000000000000 : ℝ)^4607 := by
    have hnat : (1268572703 : ℕ)^5631*100000000000000^4607 ≤ 43640427699239^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268572703 2500000000 43640427699239 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159087557/1250000000 : ℝ), (5514427591/10000000000 : ℝ), (1268572703/2500000000 : ℝ)] ![(1609767954771/20000000000000 : ℝ), (1932429300391/4000000000000 : ℝ), (43640427699239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159087557/1250000000 : ℝ)|^5631 ≤ (1609767954771/20000000000000 : ℝ)^4607
        have hw : |(-159087557/1250000000 : ℝ)|=(159087557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514427591/10000000000 : ℝ)|^5631 ≤ (1932429300391/4000000000000 : ℝ)^4607
        have hw : |(5514427591/10000000000 : ℝ)|=(5514427591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268572703/2500000000 : ℝ)|^5631 ≤ (43640427699239/100000000000000 : ℝ)^4607
        have hw : |(1268572703/2500000000 : ℝ)|=(1268572703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_1 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33399929/62500000 : ℝ)*x 0 + (-375884411/2500000000 : ℝ)*x 1 + (2537145331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33399929/62500000 : ℝ)^5631 ≤ (46491983194993/100000000000000 : ℝ)^4607 := by
    have hnat : (33399929 : ℕ)^5631*100000000000000^4607 ≤ 46491983194993^4607*62500000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33399929 62500000 46491983194993 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375884411/2500000000 : ℝ)^5631 ≤ (9867590674999/100000000000000 : ℝ)^4607 := by
    have hnat : (375884411 : ℕ)^5631*100000000000000^4607 ≤ 9867590674999^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375884411 2500000000 9867590674999 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537145331/5000000000 : ℝ)^5631 ≤ (8728085224491/20000000000000 : ℝ)^4607 := by
    have hnat : (2537145331 : ℕ)^5631*20000000000000^4607 ≤ 8728085224491^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537145331 5000000000 8728085224491 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33399929/62500000 : ℝ), (-375884411/2500000000 : ℝ), (2537145331/5000000000 : ℝ)] ![(46491983194993/100000000000000 : ℝ), (9867590674999/100000000000000 : ℝ), (8728085224491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33399929/62500000 : ℝ)|^5631 ≤ (46491983194993/100000000000000 : ℝ)^4607
        have hw : |(33399929/62500000 : ℝ)|=(33399929/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375884411/2500000000 : ℝ)|^5631 ≤ (9867590674999/100000000000000 : ℝ)^4607
        have hw : |(-375884411/2500000000 : ℝ)|=(375884411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537145331/5000000000 : ℝ)|^5631 ≤ (8728085224491/20000000000000 : ℝ)^4607
        have hw : |(2537145331/5000000000 : ℝ)|=(2537145331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_2 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343988193/10000000000 : ℝ)*x 0 + (2537145509/5000000000 : ℝ)*x 1 + (-150353777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343988193/10000000000 : ℝ)^5631 ≤ (23245989220889/50000000000000 : ℝ)^4607 := by
    have hnat : (5343988193 : ℕ)^5631*50000000000000^4607 ≤ 23245989220889^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343988193 10000000000 23245989220889 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537145509/5000000000 : ℝ)^5631 ≤ (43640429864689/100000000000000 : ℝ)^4607 := by
    have hnat : (2537145509 : ℕ)^5631*100000000000000^4607 ≤ 43640429864689^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537145509 5000000000 43640429864689 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150353777/1000000000 : ℝ)^5631 ≤ (9867591685727/100000000000000 : ℝ)^4607 := by
    have hnat : (150353777 : ℕ)^5631*100000000000000^4607 ≤ 9867591685727^4607*1000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150353777 1000000000 9867591685727 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343988193/10000000000 : ℝ), (2537145509/5000000000 : ℝ), (-150353777/1000000000 : ℝ)] ![(23245989220889/50000000000000 : ℝ), (43640429864689/100000000000000 : ℝ), (9867591685727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343988193/10000000000 : ℝ)|^5631 ≤ (23245989220889/50000000000000 : ℝ)^4607
        have hw : |(5343988193/10000000000 : ℝ)|=(5343988193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537145509/5000000000 : ℝ)|^5631 ≤ (43640429864689/100000000000000 : ℝ)^4607
        have hw : |(2537145509/5000000000 : ℝ)|=(2537145509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150353777/1000000000 : ℝ)|^5631 ≤ (9867591685727/100000000000000 : ℝ)^4607
        have hw : |(-150353777/1000000000 : ℝ)|=(150353777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_3 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4038870479/10000000000 : ℝ)*x 0 + (3376412673/10000000000 : ℝ)*x 1 + (4769497919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4038870479/10000000000 : ℝ)^5631 ≤ (8254355102473/25000000000000 : ℝ)^4607 := by
    have hnat : (4038870479 : ℕ)^5631*25000000000000^4607 ≤ 8254355102473^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038870479 10000000000 8254355102473 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3376412673/10000000000 : ℝ)^5631 ≤ (26524372264003/100000000000000 : ℝ)^4607 := by
    have hnat : (3376412673 : ℕ)^5631*100000000000000^4607 ≤ 26524372264003^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376412673 10000000000 26524372264003 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769497919/10000000000 : ℝ)^5631 ≤ (2528637956337/6250000000000 : ℝ)^4607 := by
    have hnat : (4769497919 : ℕ)^5631*6250000000000^4607 ≤ 2528637956337^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769497919 10000000000 2528637956337 6250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4038870479/10000000000 : ℝ), (3376412673/10000000000 : ℝ), (4769497919/10000000000 : ℝ)] ![(8254355102473/25000000000000 : ℝ), (26524372264003/100000000000000 : ℝ), (2528637956337/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4038870479/10000000000 : ℝ)|^5631 ≤ (8254355102473/25000000000000 : ℝ)^4607
        have hw : |(4038870479/10000000000 : ℝ)|=(4038870479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3376412673/10000000000 : ℝ)|^5631 ≤ (26524372264003/100000000000000 : ℝ)^4607
        have hw : |(3376412673/10000000000 : ℝ)|=(3376412673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769497919/10000000000 : ℝ)|^5631 ≤ (2528637956337/6250000000000 : ℝ)^4607
        have hw : |(4769497919/10000000000 : ℝ)|=(4769497919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_4 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1273096299/10000000000 : ℝ)*x 0 + (5081487441/10000000000 : ℝ)*x 1 + (344192177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1273096299/10000000000 : ℝ)^5631 ≤ (503243731881/6250000000000 : ℝ)^4607 := by
    have hnat : (1273096299 : ℕ)^5631*6250000000000^4607 ≤ 503243731881^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273096299 10000000000 503243731881 6250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081487441/10000000000 : ℝ)^5631 ≤ (43716089817633/100000000000000 : ℝ)^4607 := by
    have hnat : (5081487441 : ℕ)^5631*100000000000000^4607 ≤ 43716089817633^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081487441 10000000000 43716089817633 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344192177/625000000 : ℝ)^5631 ≤ (24116005225087/50000000000000 : ℝ)^4607 := by
    have hnat : (344192177 : ℕ)^5631*50000000000000^4607 ≤ 24116005225087^4607*625000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344192177 625000000 24116005225087 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1273096299/10000000000 : ℝ), (5081487441/10000000000 : ℝ), (344192177/625000000 : ℝ)] ![(503243731881/6250000000000 : ℝ), (43716089817633/100000000000000 : ℝ), (24116005225087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1273096299/10000000000 : ℝ)|^5631 ≤ (503243731881/6250000000000 : ℝ)^4607
        have hw : |(-1273096299/10000000000 : ℝ)|=(1273096299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081487441/10000000000 : ℝ)|^5631 ≤ (43716089817633/100000000000000 : ℝ)^4607
        have hw : |(5081487441/10000000000 : ℝ)|=(5081487441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(344192177/625000000 : ℝ)|^5631 ≤ (24116005225087/50000000000000 : ℝ)^4607
        have hw : |(344192177/625000000 : ℝ)|=(344192177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_5 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181631/8000000 : ℝ)*x 0 + (-133844323/1250000000 : ℝ)*x 1 + (1376768643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181631/8000000 : ℝ)^5631 ≤ (2828214254437/6250000000000 : ℝ)^4607 := by
    have hnat : (4181631 : ℕ)^5631*6250000000000^4607 ≤ 2828214254437^4607*8000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181631 8000000 2828214254437 6250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133844323/1250000000 : ℝ)^5631 ≤ (6516564248057/100000000000000 : ℝ)^4607 := by
    have hnat : (133844323 : ℕ)^5631*100000000000000^4607 ≤ 6516564248057^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133844323 1250000000 6516564248057 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376768643/2500000000 : ℝ)^5631 ≤ (24116003833453/50000000000000 : ℝ)^4607 := by
    have hnat : (1376768643 : ℕ)^5631*50000000000000^4607 ≤ 24116003833453^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376768643 2500000000 24116003833453 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181631/8000000 : ℝ), (-133844323/1250000000 : ℝ), (1376768643/2500000000 : ℝ)] ![(2828214254437/6250000000000 : ℝ), (6516564248057/100000000000000 : ℝ), (24116003833453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181631/8000000 : ℝ)|^5631 ≤ (2828214254437/6250000000000 : ℝ)^4607
        have hw : |(4181631/8000000 : ℝ)|=(4181631/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133844323/1250000000 : ℝ)|^5631 ≤ (6516564248057/100000000000000 : ℝ)^4607
        have hw : |(-133844323/1250000000 : ℝ)|=(133844323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376768643/2500000000 : ℝ)|^5631 ≤ (24116003833453/50000000000000 : ℝ)^4607
        have hw : |(1376768643/2500000000 : ℝ)|=(1376768643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_6 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227037789/10000000000 : ℝ)*x 0 + (1376768871/2500000000 : ℝ)*x 1 + (-1070754639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227037789/10000000000 : ℝ)^5631 ≤ (181005671609/400000000000 : ℝ)^4607 := by
    have hnat : (5227037789 : ℕ)^5631*400000000000^4607 ≤ 181005671609^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227037789 10000000000 181005671609 400000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376768871/2500000000 : ℝ)^5631 ≤ (9646403485951/20000000000000 : ℝ)^4607 := by
    have hnat : (1376768871 : ℕ)^5631*20000000000000^4607 ≤ 9646403485951^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376768871 2500000000 9646403485951 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070754639/10000000000 : ℝ)^5631 ≤ (203642645537/3125000000000 : ℝ)^4607 := by
    have hnat : (1070754639 : ℕ)^5631*3125000000000^4607 ≤ 203642645537^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070754639 10000000000 203642645537 3125000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227037789/10000000000 : ℝ), (1376768871/2500000000 : ℝ), (-1070754639/10000000000 : ℝ)] ![(181005671609/400000000000 : ℝ), (9646403485951/20000000000000 : ℝ), (203642645537/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227037789/10000000000 : ℝ)|^5631 ≤ (181005671609/400000000000 : ℝ)^4607
        have hw : |(5227037789/10000000000 : ℝ)|=(5227037789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376768871/2500000000 : ℝ)|^5631 ≤ (9646403485951/20000000000000 : ℝ)^4607
        have hw : |(1376768871/2500000000 : ℝ)|=(1376768871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070754639/10000000000 : ℝ)|^5631 ≤ (203642645537/3125000000000 : ℝ)^4607
        have hw : |(-1070754639/10000000000 : ℝ)|=(1070754639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s1_7 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808023023/2000000000 : ℝ)*x 0 + (2373357809/5000000000 : ℝ)*x 1 + (849921737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808023023/2000000000 : ℝ)^5631 ≤ (8257464296093/25000000000000 : ℝ)^4607 := by
    have hnat : (808023023 : ℕ)^5631*25000000000000^4607 ≤ 8257464296093^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808023023 2000000000 8257464296093 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2373357809/5000000000 : ℝ)^5631 ≤ (10055530632081/25000000000000 : ℝ)^4607 := by
    have hnat : (2373357809 : ℕ)^5631*25000000000000^4607 ≤ 10055530632081^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373357809 5000000000 10055530632081 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849921737/2500000000 : ℝ)^5631 ≤ (13374010140741/50000000000000 : ℝ)^4607 := by
    have hnat : (849921737 : ℕ)^5631*50000000000000^4607 ≤ 13374010140741^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849921737 2500000000 13374010140741 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808023023/2000000000 : ℝ), (2373357809/5000000000 : ℝ), (849921737/2500000000 : ℝ)] ![(8257464296093/25000000000000 : ℝ), (10055530632081/25000000000000 : ℝ), (13374010140741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808023023/2000000000 : ℝ)|^5631 ≤ (8257464296093/25000000000000 : ℝ)^4607
        have hw : |(808023023/2000000000 : ℝ)|=(808023023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2373357809/5000000000 : ℝ)|^5631 ≤ (10055530632081/25000000000000 : ℝ)^4607
        have hw : |(2373357809/5000000000 : ℝ)|=(2373357809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849921737/2500000000 : ℝ)|^5631 ≤ (13374010140741/50000000000000 : ℝ)^4607
        have hw : |(849921737/2500000000 : ℝ)|=(849921737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1741_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2207/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18257/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6341/100000 : ℝ) ^ (5615/1024 : ℝ) ≤ (27024252835723/100000000000000000000 : ℝ) := by
    have hpowers : (6341/100000 : ℝ)^5615 ≤ (27024252835723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6341 : ℕ)^5615*100000000000000000000^1024 ≤ 27024252835723^1024*100000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6341 100000 27024252835723 100000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6341/100000 : ℝ)) (X := (27024252835723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4269/20000 : ℝ) ^ (5615/1024 : ℝ) ≤ (1050107139874139/5000000000000000000 : ℝ) := by
    have hpowers : (4269/20000 : ℝ)^5615 ≤ (1050107139874139/5000000000000000000 : ℝ)^1024 := by
      have hnat : (4269 : ℕ)^5615*5000000000000000000^1024 ≤ 1050107139874139^1024*20000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4269 20000 1050107139874139 5000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4269/20000 : ℝ)) (X := (1050107139874139/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000027024252835723/50000000000000000000 : ℝ) ≤ (10000000985675113/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50000027024252835723/50000000000000000000 : ℝ)^1024 ≤ (10000000985675113/10000000000000000 : ℝ)^5615 := by
      have hnat : (50000027024252835723 : ℕ)^1024*10000000000000000^5615 ≤ 10000000985675113^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000027024252835723 50000000000000000000 10000000985675113 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000985675113/10000000000000000 : ℝ)) (X := (50000027024252835723/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021029167050318503/100000000000000000000 : ℝ) ≤ (10000383473125867/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (100021029167050318503/100000000000000000000 : ℝ)^1024 ≤ (10000383473125867/10000000000000000 : ℝ)^5615 := by
      have hnat : (100021029167050318503 : ℕ)^1024*10000000000000000^5615 ≤ 10000383473125867^5615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021029167050318503 100000000000000000000 10000383473125867 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000383473125867/10000000000000000 : ℝ)) (X := (100021029167050318503/100000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501050107139874139/2500000000000000000 : ℝ) ≤ (10000765960576621/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (2501050107139874139/2500000000000000000 : ℝ)^1024 ≤ (10000765960576621/10000000000000000 : ℝ)^5615 := by
      have hnat : (2501050107139874139 : ℕ)^1024*10000000000000000^5615 ≤ 10000765960576621^5615*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501050107139874139 2500000000000000000 10000765960576621 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000765960576621/10000000000000000 : ℝ)) (X := (2501050107139874139/2500000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27024252835723/100000000000000000000 : ℝ) ≤ ((18754395510402366653/18755000000000000000 : ℝ)+2*(191243725377/750200000000000 : ℝ)*(6341/100000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (18754395510402366653/18755000000000000000 : ℝ)+2*(191243725377/750200000000000 : ℝ)*(6341/100000 : ℝ)=(10000000985675113/10000000000000000 : ℝ) by norm_num, show 1+2*(27024252835723/100000000000000000000 : ℝ)=(50000027024252835723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1050107139874139/5000000000000000000 : ℝ)+(27024252835723/100000000000000000000 : ℝ) ≤ ((18754395510402366653/18755000000000000000 : ℝ)+(191243725377/750200000000000 : ℝ)*((4269/20000 : ℝ)+(6341/100000 : ℝ)))^(5615/1024 : ℝ) := by
    rw [show (18754395510402366653/18755000000000000000 : ℝ)+(191243725377/750200000000000 : ℝ)*((4269/20000 : ℝ)+(6341/100000 : ℝ))=(10000383473125867/10000000000000000 : ℝ) by norm_num, show 1+(1050107139874139/5000000000000000000 : ℝ)+(27024252835723/100000000000000000000 : ℝ)=(100021029167050318503/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1050107139874139/5000000000000000000 : ℝ) ≤ ((18754395510402366653/18755000000000000000 : ℝ)+2*(191243725377/750200000000000 : ℝ)*(4269/20000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (18754395510402366653/18755000000000000000 : ℝ)+2*(191243725377/750200000000000 : ℝ)*(4269/20000 : ℝ)=(10000765960576621/10000000000000000 : ℝ) by norm_num, show 1+2*(1050107139874139/5000000000000000000 : ℝ)=(2501050107139874139/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18754395510402366653/18755000000000000000 : ℝ)*(X 1 0+X 2 0)+(191243725377/750200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (4269/20000 : ℝ)) (c := (18754395510402366653/18755000000000000000 : ℝ)) (alpha := (191243725377/750200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18754395510402366653/18755000000000000000 : ℝ)*(X 0 1+X 2 1)+(191243725377/750200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (4269/20000 : ℝ)) (c := (18754395510402366653/18755000000000000000 : ℝ)) (alpha := (191243725377/750200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18754395510402366653/18755000000000000000 : ℝ)*(X 0 2+X 1 2)+(191243725377/750200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (4269/20000 : ℝ)) (c := (18754395510402366653/18755000000000000000 : ℝ)) (alpha := (191243725377/750200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-159087557/1250000000 : ℝ)*X 0 0+(5514427591/10000000000 : ℝ)*X 0 1+(1268572703/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33399929/62500000 : ℝ)*X 1 0+(-375884411/2500000000 : ℝ)*X 1 1+(2537145331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343988193/10000000000 : ℝ)*X 2 0+(2537145509/5000000000 : ℝ)*X 2 1+(-150353777/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4038870479/10000000000 : ℝ)*X 0 0+(3376412673/10000000000 : ℝ)*X 0 1+(4769497919/10000000000 : ℝ)*X 0 2+(4038870479/10000000000 : ℝ)*X 1 0+(3376412673/10000000000 : ℝ)*X 1 1+(4769497919/10000000000 : ℝ)*X 1 2+(4038870479/10000000000 : ℝ)*X 2 0+(3376412673/10000000000 : ℝ)*X 2 1+(4769497919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1273096299/10000000000 : ℝ)*X 0 0+(5081487441/10000000000 : ℝ)*X 0 1+(344192177/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4181631/8000000 : ℝ)*X 1 0+(-133844323/1250000000 : ℝ)*X 1 1+(1376768643/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5227037789/10000000000 : ℝ)*X 2 0+(1376768871/2500000000 : ℝ)*X 2 1+(-1070754639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((808023023/2000000000 : ℝ)*X 0 0+(2373357809/5000000000 : ℝ)*X 0 1+(849921737/2500000000 : ℝ)*X 0 2+(808023023/2000000000 : ℝ)*X 1 0+(2373357809/5000000000 : ℝ)*X 1 1+(849921737/2500000000 : ℝ)*X 1 2+(808023023/2000000000 : ℝ)*X 2 0+(2373357809/5000000000 : ℝ)*X 2 1+(849921737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3138356630647460508101379543/234437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1031477027/50000000000000 : ℝ)*(base19) + (1677045763/100000000000000 : ℝ)*(base23) + (2093367/2000000000000 : ℝ)*(lower2) + (388784341/100000000000000 : ℝ)*(upper3) + (148220081/100000000000000 : ℝ)*(upper5) + (747472874869623/50000000000000 : ℝ)*(major0) + (747472874869623/50000000000000 : ℝ)*(major1) + (747472874869623/50000000000000 : ℝ)*(major2) + (227203722919367/10000000000000 : ℝ)*(sp0) + (284006109354371/12500000000000 : ℝ)*(sp1) + (1136024630371629/50000000000000 : ℝ)*(sp2) + (143567000290357/20000000000000 : ℝ)*(sp3) + (13708595351/100000000000000 : ℝ)*(sp4) + (639251577/12500000000000 : ℝ)*(sp7) + (717840115464401/100000000000000 : ℝ)*(f.failure) + (1136025468894511/50000000000000 : ℝ)*(f.sum) + (110814116346559/18755000000000000000000000000 : ℝ)*base66 + (1057538796888741529/85250000000000000000000000000000 : ℝ)*base67 + (53353416121508471/85250000000000000000000000000000 : ℝ)*base70 + (111249677698491529/85250000000000000000000000000000 : ℝ)*base71 + (28558909847779/4688750000000000000000000000 : ℝ)*base73 + (159805449952491529/85250000000000000000000000000000 : ℝ)*base75 + (257062192089991529/85250000000000000000000000000000 : ℝ)*base77 + (1084356666612991529/85250000000000000000000000000000 : ℝ)*base79 + (34498893558497/9377500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (29012311/10000000000000000000000 : ℝ)*base90 + (29012311/10000000000000000000000 : ℝ)*base92 + (29012311/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5394269481325769784101755077/468875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1374300253/100000000000000 : ℝ)*(base19) + (384725627/20000000000000 : ℝ)*(base23) + (514611439/100000000000000 : ℝ)*(upper2) + (71363069/50000000000000 : ℝ)*(upper3) + (5307009/800000000000 : ℝ)*(upper5) + (773016632122399/50000000000000 : ℝ)*(major0) + (773016632122399/50000000000000 : ℝ)*(major1) + (773016632122399/50000000000000 : ℝ)*(major2) + (9557764043/100000000000000 : ℝ)*(sp1) + (4707457719/50000000000000 : ℝ)*(sp2) + (1174847463553377/50000000000000 : ℝ)*(sp4) + (1174841997521229/50000000000000 : ℝ)*(sp5) + (2349683588563181/100000000000000 : ℝ)*(sp6) + (3711856089463/500000000000 : ℝ)*(sp7) + (3711856089463/500000000000 : ℝ)*(f.failure) + (1174847463553377/50000000000000 : ℝ)*(f.sum) + (76506220554153/18755000000000000000000000000 : ℝ)*base65 + (366286283159457777/85250000000000000000000000000000 : ℝ)*base67 + (474852429765957777/85250000000000000000000000000000 : ℝ)*base69 + (461513541972957777/85250000000000000000000000000000 : ℝ)*base71 + (62308327671243/18755000000000000000000000000 : ℝ)*base73 + (647412997797457777/85250000000000000000000000000000 : ℝ)*base75 + (579776491687207777/85250000000000000000000000000000 : ℝ)*base77 + (517535641875957777/85250000000000000000000000000000 : ℝ)*base79 + (9350514544067/4688750000000000000000000000 : ℝ)*base81 + (509793/50000000000000000000 : ℝ)*base90 + (509793/50000000000000000000 : ℝ)*base92 + (509793/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1741_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18257/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1741_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1741_s2_0 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-254843937/2000000000 : ℝ)*x 0 + (5509574379/10000000000 : ℝ)*x 1 + (5078116473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254843937/2000000000 : ℝ)^5631 ≤ (8060584833657/100000000000000 : ℝ)^4607 := by
    have hnat : (254843937 : ℕ)^5631*100000000000000^4607 ≤ 8060584833657^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254843937 2000000000 8060584833657 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509574379/10000000000 : ℝ)^5631 ≤ (48258769144169/100000000000000 : ℝ)^4607 := by
    have hnat : (5509574379 : ℕ)^5631*100000000000000^4607 ≤ 48258769144169^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509574379 10000000000 48258769144169 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078116473/10000000000 : ℝ)^5631 ≤ (5460080751229/12500000000000 : ℝ)^4607 := by
    have hnat : (5078116473 : ℕ)^5631*12500000000000^4607 ≤ 5460080751229^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078116473 10000000000 5460080751229 12500000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254843937/2000000000 : ℝ), (5509574379/10000000000 : ℝ), (5078116473/10000000000 : ℝ)] ![(8060584833657/100000000000000 : ℝ), (48258769144169/100000000000000 : ℝ), (5460080751229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254843937/2000000000 : ℝ)|^5631 ≤ (8060584833657/100000000000000 : ℝ)^4607
        have hw : |(-254843937/2000000000 : ℝ)|=(254843937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509574379/10000000000 : ℝ)|^5631 ≤ (48258769144169/100000000000000 : ℝ)^4607
        have hw : |(5509574379/10000000000 : ℝ)|=(5509574379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078116473/10000000000 : ℝ)|^5631 ≤ (5460080751229/12500000000000 : ℝ)^4607
        have hw : |(5078116473/10000000000 : ℝ)|=(5078116473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_1 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068530423/2000000000 : ℝ)*x 0 + (-750147519/5000000000 : ℝ)*x 1 + (101562323/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068530423/2000000000 : ℝ)^5631 ≤ (46477771532807/100000000000000 : ℝ)^4607 := by
    have hnat : (1068530423 : ℕ)^5631*100000000000000^4607 ≤ 46477771532807^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068530423 2000000000 46477771532807 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750147519/5000000000 : ℝ)^5631 ≤ (9841585836883/100000000000000 : ℝ)^4607 := by
    have hnat : (750147519 : ℕ)^5631*100000000000000^4607 ≤ 9841585836883^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750147519 5000000000 9841585836883 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101562323/200000000 : ℝ)^5631 ≤ (43680642613921/100000000000000 : ℝ)^4607 := by
    have hnat : (101562323 : ℕ)^5631*100000000000000^4607 ≤ 43680642613921^4607*200000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101562323 200000000 43680642613921 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068530423/2000000000 : ℝ), (-750147519/5000000000 : ℝ), (101562323/200000000 : ℝ)] ![(46477771532807/100000000000000 : ℝ), (9841585836883/100000000000000 : ℝ), (43680642613921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068530423/2000000000 : ℝ)|^5631 ≤ (46477771532807/100000000000000 : ℝ)^4607
        have hw : |(1068530423/2000000000 : ℝ)|=(1068530423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-750147519/5000000000 : ℝ)|^5631 ≤ (9841585836883/100000000000000 : ℝ)^4607
        have hw : |(-750147519/5000000000 : ℝ)|=(750147519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101562323/200000000 : ℝ)|^5631 ≤ (43680642613921/100000000000000 : ℝ)^4607
        have hw : |(101562323/200000000 : ℝ)|=(101562323/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_2 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671325511/5000000000 : ℝ)*x 0 + (317382271/625000000 : ℝ)*x 1 + (-375074061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671325511/5000000000 : ℝ)^5631 ≤ (46477759910941/100000000000000 : ℝ)^4607 := by
    have hnat : (2671325511 : ℕ)^5631*100000000000000^4607 ≤ 46477759910941^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671325511 5000000000 46477759910941 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317382271/625000000 : ℝ)^5631 ≤ (43680644569461/100000000000000 : ℝ)^4607 := by
    have hnat : (317382271 : ℕ)^5631*100000000000000^4607 ≤ 43680644569461^4607*625000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317382271 625000000 43680644569461 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375074061/2500000000 : ℝ)^5631 ≤ (4920797753181/50000000000000 : ℝ)^4607 := by
    have hnat : (375074061 : ℕ)^5631*50000000000000^4607 ≤ 4920797753181^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375074061 2500000000 4920797753181 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671325511/5000000000 : ℝ), (317382271/625000000 : ℝ), (-375074061/2500000000 : ℝ)] ![(46477759910941/100000000000000 : ℝ), (43680644569461/100000000000000 : ℝ), (4920797753181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671325511/5000000000 : ℝ)|^5631 ≤ (46477759910941/100000000000000 : ℝ)^4607
        have hw : |(2671325511/5000000000 : ℝ)|=(2671325511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(317382271/625000000 : ℝ)|^5631 ≤ (43680644569461/100000000000000 : ℝ)^4607
        have hw : |(317382271/625000000 : ℝ)|=(317382271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375074061/2500000000 : ℝ)|^5631 ≤ (4920797753181/50000000000000 : ℝ)^4607
        have hw : |(-375074061/2500000000 : ℝ)|=(375074061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_3 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808021653/2000000000 : ℝ)*x 0 + (67800979/200000000 : ℝ)*x 1 + (4755666391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808021653/2000000000 : ℝ)^5631 ≤ (8257447183699/25000000000000 : ℝ)^4607 := by
    have hnat : (808021653 : ℕ)^5631*25000000000000^4607 ≤ 8257447183699^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808021653 2000000000 8257447183699 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67800979/200000000 : ℝ)^5631 ≤ (2665536505761/10000000000000 : ℝ)^4607 := by
    have hnat : (67800979 : ℕ)^5631*10000000000000^4607 ≤ 2665536505761^4607*200000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67800979 200000000 2665536505761 10000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4755666391/10000000000 : ℝ)^5631 ≤ (20157423096591/50000000000000 : ℝ)^4607 := by
    have hnat : (4755666391 : ℕ)^5631*50000000000000^4607 ≤ 20157423096591^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755666391 10000000000 20157423096591 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808021653/2000000000 : ℝ), (67800979/200000000 : ℝ), (4755666391/10000000000 : ℝ)] ![(8257447183699/25000000000000 : ℝ), (2665536505761/10000000000000 : ℝ), (20157423096591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808021653/2000000000 : ℝ)|^5631 ≤ (8257447183699/25000000000000 : ℝ)^4607
        have hw : |(808021653/2000000000 : ℝ)|=(808021653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67800979/200000000 : ℝ)|^5631 ≤ (2665536505761/10000000000000 : ℝ)^4607
        have hw : |(67800979/200000000 : ℝ)|=(67800979/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4755666391/10000000000 : ℝ)|^5631 ≤ (20157423096591/50000000000000 : ℝ)^4607
        have hw : |(4755666391/10000000000 : ℝ)|=(4755666391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_4 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1274590531/10000000000 : ℝ)*x 0 + (5085033829/10000000000 : ℝ)*x 1 + (2751255701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1274590531/10000000000 : ℝ)^5631 ≤ (2015863073141/25000000000000 : ℝ)^4607 := by
    have hnat : (1274590531 : ℕ)^5631*25000000000000^4607 ≤ 2015863073141^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274590531 10000000000 2015863073141 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085033829/10000000000 : ℝ)^5631 ≤ (43753383708369/100000000000000 : ℝ)^4607 := by
    have hnat : (5085033829 : ℕ)^5631*100000000000000^4607 ≤ 43753383708369^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085033829 10000000000 43753383708369 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751255701/5000000000 : ℝ)^5631 ≤ (48183163990761/100000000000000 : ℝ)^4607 := by
    have hnat : (2751255701 : ℕ)^5631*100000000000000^4607 ≤ 48183163990761^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751255701 5000000000 48183163990761 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1274590531/10000000000 : ℝ), (5085033829/10000000000 : ℝ), (2751255701/5000000000 : ℝ)] ![(2015863073141/25000000000000 : ℝ), (43753383708369/100000000000000 : ℝ), (48183163990761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1274590531/10000000000 : ℝ)|^5631 ≤ (2015863073141/25000000000000 : ℝ)^4607
        have hw : |(-1274590531/10000000000 : ℝ)|=(1274590531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085033829/10000000000 : ℝ)|^5631 ≤ (43753383708369/100000000000000 : ℝ)^4607
        have hw : |(5085033829/10000000000 : ℝ)|=(5085033829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751255701/5000000000 : ℝ)|^5631 ≤ (48183163990761/100000000000000 : ℝ)^4607
        have hw : |(2751255701/5000000000 : ℝ)|=(2751255701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_5 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228035229/10000000000 : ℝ)*x 0 + (-1075900773/10000000000 : ℝ)*x 1 + (1100502243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228035229/10000000000 : ℝ)^5631 ≤ (11315493113887/25000000000000 : ℝ)^4607 := by
    have hnat : (5228035229 : ℕ)^5631*25000000000000^4607 ≤ 11315493113887^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228035229 10000000000 11315493113887 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075900773/10000000000 : ℝ)^5631 ≤ (6554865538477/100000000000000 : ℝ)^4607 := by
    have hnat : (1075900773 : ℕ)^5631*100000000000000^4607 ≤ 6554865538477^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075900773 10000000000 6554865538477 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100502243/2000000000 : ℝ)^5631 ≤ (48183161989317/100000000000000 : ℝ)^4607 := by
    have hnat : (1100502243 : ℕ)^5631*100000000000000^4607 ≤ 48183161989317^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100502243 2000000000 48183161989317 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228035229/10000000000 : ℝ), (-1075900773/10000000000 : ℝ), (1100502243/2000000000 : ℝ)] ![(11315493113887/25000000000000 : ℝ), (6554865538477/100000000000000 : ℝ), (48183161989317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228035229/10000000000 : ℝ)|^5631 ≤ (11315493113887/25000000000000 : ℝ)^4607
        have hw : |(5228035229/10000000000 : ℝ)|=(5228035229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075900773/10000000000 : ℝ)|^5631 ≤ (6554865538477/100000000000000 : ℝ)^4607
        have hw : |(-1075900773/10000000000 : ℝ)|=(1075900773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100502243/2000000000 : ℝ)|^5631 ≤ (48183161989317/100000000000000 : ℝ)^4607
        have hw : |(1100502243/2000000000 : ℝ)|=(1100502243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_6 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228035159/10000000000 : ℝ)*x 0 + (550251127/1000000000 : ℝ)*x 1 + (-537950397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228035159/10000000000 : ℝ)^5631 ≤ (45261971714817/100000000000000 : ℝ)^4607 := by
    have hnat : (5228035159 : ℕ)^5631*100000000000000^4607 ≤ 45261971714817^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228035159 10000000000 45261971714817 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550251127/1000000000 : ℝ)^5631 ≤ (48183162577977/100000000000000 : ℝ)^4607 := by
    have hnat : (550251127 : ℕ)^5631*100000000000000^4607 ≤ 48183162577977^4607*1000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550251127 1000000000 48183162577977 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537950397/5000000000 : ℝ)^5631 ≤ (1310973138971/20000000000000 : ℝ)^4607 := by
    have hnat : (537950397 : ℕ)^5631*20000000000000^4607 ≤ 1310973138971^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537950397 5000000000 1310973138971 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228035159/10000000000 : ℝ), (550251127/1000000000 : ℝ), (-537950397/5000000000 : ℝ)] ![(45261971714817/100000000000000 : ℝ), (48183162577977/100000000000000 : ℝ), (1310973138971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228035159/10000000000 : ℝ)|^5631 ≤ (45261971714817/100000000000000 : ℝ)^4607
        have hw : |(5228035159/10000000000 : ℝ)|=(5228035159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550251127/1000000000 : ℝ)|^5631 ≤ (48183162577977/100000000000000 : ℝ)^4607
        have hw : |(550251127/1000000000 : ℝ)|=(550251127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537950397/5000000000 : ℝ)|^5631 ≤ (1310973138971/20000000000000 : ℝ)^4607
        have hw : |(-537950397/5000000000 : ℝ)|=(537950397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s2_7 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041282261/10000000000 : ℝ)*x 0 + (1183442999/2500000000 : ℝ)*x 1 + (3412404997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041282261/10000000000 : ℝ)^5631 ≤ (16520760214697/50000000000000 : ℝ)^4607 := by
    have hnat : (4041282261 : ℕ)^5631*50000000000000^4607 ≤ 16520760214697^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041282261 10000000000 16520760214697 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183442999/2500000000 : ℝ)^5631 ≤ (40088104513109/100000000000000 : ℝ)^4607 := by
    have hnat : (1183442999 : ℕ)^5631*100000000000000^4607 ≤ 40088104513109^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183442999 2500000000 40088104513109 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3412404997/10000000000 : ℝ)^5631 ≤ (13435187520953/50000000000000 : ℝ)^4607 := by
    have hnat : (3412404997 : ℕ)^5631*50000000000000^4607 ≤ 13435187520953^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412404997 10000000000 13435187520953 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041282261/10000000000 : ℝ), (1183442999/2500000000 : ℝ), (3412404997/10000000000 : ℝ)] ![(16520760214697/50000000000000 : ℝ), (40088104513109/100000000000000 : ℝ), (13435187520953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041282261/10000000000 : ℝ)|^5631 ≤ (16520760214697/50000000000000 : ℝ)^4607
        have hw : |(4041282261/10000000000 : ℝ)|=(4041282261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1183442999/2500000000 : ℝ)|^5631 ≤ (40088104513109/100000000000000 : ℝ)^4607
        have hw : |(1183442999/2500000000 : ℝ)|=(1183442999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3412404997/10000000000 : ℝ)|^5631 ≤ (13435187520953/50000000000000 : ℝ)^4607
        have hw : |(3412404997/10000000000 : ℝ)|=(3412404997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1741_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9077/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2207/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2207/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2207/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2207/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2207/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2207/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2207/25000 : ℝ) ^ (5615/1024 : ℝ) ≤ (165860556114537/100000000000000000000 : ℝ) := by
    have hpowers : (2207/25000 : ℝ)^5615 ≤ (165860556114537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2207 : ℕ)^5615*100000000000000000000^1024 ≤ 165860556114537^1024*25000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2207 25000 165860556114537 100000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2207/25000 : ℝ)) (X := (165860556114537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18257/100000 : ℝ) ^ (5615/1024 : ℝ) ≤ (8915038258990689/100000000000000000000 : ℝ) := by
    have hpowers : (18257/100000 : ℝ)^5615 ≤ (8915038258990689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18257 : ℕ)^5615*100000000000000000000^1024 ≤ 8915038258990689^1024*100000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18257 100000 8915038258990689 100000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18257/100000 : ℝ)) (X := (8915038258990689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000165860556114537/50000000000000000000 : ℝ) ≤ (10000006049545117/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50000165860556114537/50000000000000000000 : ℝ)^1024 ≤ (10000006049545117/10000000000000000 : ℝ)^5615 := by
      have hnat : (50000165860556114537 : ℕ)^1024*10000000000000000^5615 ≤ 10000006049545117^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000165860556114537 50000000000000000000 10000006049545117 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006049545117/10000000000000000 : ℝ)) (X := (50000165860556114537/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50004540449407552613/50000000000000000000 : ℝ) ≤ (10000165600982979/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50004540449407552613/50000000000000000000 : ℝ)^1024 ≤ (10000165600982979/10000000000000000 : ℝ)^5615 := by
      have hnat : (50004540449407552613 : ℕ)^1024*10000000000000000^5615 ≤ 10000165600982979^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004540449407552613 50000000000000000000 10000165600982979 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000165600982979/10000000000000000 : ℝ)) (X := (50004540449407552613/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008915038258990689/50000000000000000000 : ℝ) ≤ (10000325152420841/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50008915038258990689/50000000000000000000 : ℝ)^1024 ≤ (10000325152420841/10000000000000000 : ℝ)^5615 := by
      have hnat : (50008915038258990689 : ℕ)^1024*10000000000000000^5615 ≤ 10000325152420841^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008915038258990689 50000000000000000000 10000325152420841 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000325152420841/10000000000000000 : ℝ)) (X := (50008915038258990689/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(165860556114537/100000000000000000000 : ℝ) ≤ ((94287240000974016721/94290000000000000000 : ℝ)+2*(79775718931/471450000000000 : ℝ)*(2207/25000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (94287240000974016721/94290000000000000000 : ℝ)+2*(79775718931/471450000000000 : ℝ)*(2207/25000 : ℝ)=(10000006049545117/10000000000000000 : ℝ) by norm_num, show 1+2*(165860556114537/100000000000000000000 : ℝ)=(50000165860556114537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8915038258990689/100000000000000000000 : ℝ)+(165860556114537/100000000000000000000 : ℝ) ≤ ((94287240000974016721/94290000000000000000 : ℝ)+(79775718931/471450000000000 : ℝ)*((18257/100000 : ℝ)+(2207/25000 : ℝ)))^(5615/1024 : ℝ) := by
    rw [show (94287240000974016721/94290000000000000000 : ℝ)+(79775718931/471450000000000 : ℝ)*((18257/100000 : ℝ)+(2207/25000 : ℝ))=(10000165600982979/10000000000000000 : ℝ) by norm_num, show 1+(8915038258990689/100000000000000000000 : ℝ)+(165860556114537/100000000000000000000 : ℝ)=(50004540449407552613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8915038258990689/100000000000000000000 : ℝ) ≤ ((94287240000974016721/94290000000000000000 : ℝ)+2*(79775718931/471450000000000 : ℝ)*(18257/100000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (94287240000974016721/94290000000000000000 : ℝ)+2*(79775718931/471450000000000 : ℝ)*(18257/100000 : ℝ)=(10000325152420841/10000000000000000 : ℝ) by norm_num, show 1+2*(8915038258990689/100000000000000000000 : ℝ)=(50008915038258990689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (94287240000974016721/94290000000000000000 : ℝ)*(X 1 0+X 2 0)+(79775718931/471450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (18257/100000 : ℝ)) (c := (94287240000974016721/94290000000000000000 : ℝ)) (alpha := (79775718931/471450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (94287240000974016721/94290000000000000000 : ℝ)*(X 0 1+X 2 1)+(79775718931/471450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (18257/100000 : ℝ)) (c := (94287240000974016721/94290000000000000000 : ℝ)) (alpha := (79775718931/471450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (94287240000974016721/94290000000000000000 : ℝ)*(X 0 2+X 1 2)+(79775718931/471450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (2207/25000 : ℝ)) (hi := (18257/100000 : ℝ)) (c := (94287240000974016721/94290000000000000000 : ℝ)) (alpha := (79775718931/471450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-254843937/2000000000 : ℝ)*X 0 0+(5509574379/10000000000 : ℝ)*X 0 1+(5078116473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068530423/2000000000 : ℝ)*X 1 0+(-750147519/5000000000 : ℝ)*X 1 1+(101562323/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671325511/5000000000 : ℝ)*X 2 0+(317382271/625000000 : ℝ)*X 2 1+(-375074061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((808021653/2000000000 : ℝ)*X 0 0+(67800979/200000000 : ℝ)*X 0 1+(4755666391/10000000000 : ℝ)*X 0 2+(808021653/2000000000 : ℝ)*X 1 0+(67800979/200000000 : ℝ)*X 1 1+(4755666391/10000000000 : ℝ)*X 1 2+(808021653/2000000000 : ℝ)*X 2 0+(67800979/200000000 : ℝ)*X 2 1+(4755666391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1274590531/10000000000 : ℝ)*X 0 0+(5085033829/10000000000 : ℝ)*X 0 1+(2751255701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5228035229/10000000000 : ℝ)*X 1 0+(-1075900773/10000000000 : ℝ)*X 1 1+(1100502243/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5228035159/10000000000 : ℝ)*X 2 0+(550251127/1000000000 : ℝ)*X 2 1+(-537950397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4041282261/10000000000 : ℝ)*X 0 0+(1183442999/2500000000 : ℝ)*X 0 1+(3412404997/10000000000 : ℝ)*X 0 2+(4041282261/10000000000 : ℝ)*X 1 0+(1183442999/2500000000 : ℝ)*X 1 1+(3412404997/10000000000 : ℝ)*X 1 2+(4041282261/10000000000 : ℝ)*X 2 0+(1183442999/2500000000 : ℝ)*X 2 1+(3412404997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1770941203725860023354036003/224500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1511793503/100000000000000 : ℝ)*(base19) + (1012768899/100000000000000 : ℝ)*(base23) + (365361907/100000000000000 : ℝ)*(upper3) + (10924411/50000000000000 : ℝ)*(lower4) + (1525010428820233/100000000000000 : ℝ)*(major0) + (1525010428820233/100000000000000 : ℝ)*(major1) + (1525010428820233/100000000000000 : ℝ)*(major2) + (579434230188961/25000000000000 : ℝ)*(sp0) + (579435642213443/25000000000000 : ℝ)*(sp1) + (2317740002771191/100000000000000 : ℝ)*(sp2) + (366136212022573/50000000000000 : ℝ)*(sp3) + (7159891431/100000000000000 : ℝ)*(sp4) + (191569199/6250000000000 : ℝ)*(sp6) + (4090002053/100000000000000 : ℝ)*(sp7) + (732276514047199/100000000000000 : ℝ)*(f.failure) + (1158872040323637/50000000000000 : ℝ)*(f.sum) + (42472568106961/11786250000000000000000000000 : ℝ)*base66 + (4826352982000905331/3143000000000000000000000000000000 : ℝ)*base67 + (13274998674466905331/3143000000000000000000000000000000 : ℝ)*base69 + (1687449442480905331/3143000000000000000000000000000000 : ℝ)*base71 + (17391651825403/23572500000000000000000000000 : ℝ)*base73 + (2605760420848905331/3143000000000000000000000000000000 : ℝ)*base75 + (25630000988526905331/3143000000000000000000000000000000 : ℝ)*base77 + (23728041684617905331/3143000000000000000000000000000000 : ℝ)*base79 + (150650859439931/47145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (74855289/10000000000000000000000 : ℝ)*base90 + (74855289/10000000000000000000000 : ℝ)*base92 + (74855289/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (377064657318675212695839549/49109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24858337/2500000000000 : ℝ)*(base19) + (1037420777/100000000000000 : ℝ)*(base23) + (16874081/12500000000000 : ℝ)*(upper3) + (37248191/100000000000000 : ℝ)*(lower4) + (151774163/100000000000000 : ℝ)*(upper5) + (49252033502253/3125000000000 : ℝ)*(major0) + (49252033502253/3125000000000 : ℝ)*(major1) + (49252033502253/3125000000000 : ℝ)*(major2) + (6301084041/100000000000000 : ℝ)*(sp1) + (6479593693/100000000000000 : ℝ)*(sp2) + (598834513946893/25000000000000 : ℝ)*(sp4) + (598832690092513/25000000000000 : ℝ)*(sp5) + (1197665269386551/50000000000000 : ℝ)*(sp6) + (75679183242133/10000000000000 : ℝ)*(sp7) + (75679183242133/10000000000000 : ℝ)*(f.failure) + (598834513946893/25000000000000 : ℝ)*(f.sum) + (13411489527507/7857500000000000000000000000 : ℝ)*base65 + (122581655772132471/98218750000000000000000000000000 : ℝ)*base67 + (955895648512819971/98218750000000000000000000000000 : ℝ)*base69 + (48943337879788721/98218750000000000000000000000000 : ℝ)*base71 + (8531282688753/7857500000000000000000000000 : ℝ)*base74 + (298318441180867529/98218750000000000000000000000000 : ℝ)*base76 + (180876769840319971/98218750000000000000000000000000 : ℝ)*base77 + (521747055972132471/98218750000000000000000000000000 : ℝ)*base79 + (28879704844817/7857500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1402163/1000000000000000000000 : ℝ)*base90 + (1402163/1000000000000000000000 : ℝ)*base92 + (1402163/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1741_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2207/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1741_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1741_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1741_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1741_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1741_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

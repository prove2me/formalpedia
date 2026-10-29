-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1666_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:34.717226+00:00
-- url     : https://prove2.me/submissions/79748937-6e95-437c-b624-ff5c3c29d6a3

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
theorem support_rectangle_w1666_s0_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-732494839/5000000000 : ℝ)*x 0 + (1441455993/2500000000 : ℝ)*x 1 + (77065847/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732494839/5000000000 : ℝ)^4983 ≤ (891408344413/10000000000000 : ℝ)^3959 := by
    have hnat : (732494839 : ℕ)^4983*10000000000000^3959 ≤ 891408344413^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732494839 5000000000 891408344413 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1441455993/2500000000 : ℝ)^4983 ≤ (50004362439933/100000000000000 : ℝ)^3959 := by
    have hnat : (1441455993 : ℕ)^4983*100000000000000^3959 ≤ 50004362439933^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441455993 2500000000 50004362439933 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77065847/156250000 : ℝ)^4983 ≤ (641899282983/1562500000000 : ℝ)^3959 := by
    have hnat : (77065847 : ℕ)^4983*1562500000000^3959 ≤ 641899282983^3959*156250000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77065847 156250000 641899282983 1562500000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-732494839/5000000000 : ℝ), (1441455993/2500000000 : ℝ), (77065847/156250000 : ℝ)] ![(891408344413/10000000000000 : ℝ), (50004362439933/100000000000000 : ℝ), (641899282983/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-732494839/5000000000 : ℝ)|^4983 ≤ (891408344413/10000000000000 : ℝ)^3959
        have hw : |(-732494839/5000000000 : ℝ)|=(732494839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1441455993/2500000000 : ℝ)|^4983 ≤ (50004362439933/100000000000000 : ℝ)^3959
        have hw : |(1441455993/2500000000 : ℝ)|=(1441455993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(77065847/156250000 : ℝ)|^4983 ≤ (641899282983/1562500000000 : ℝ)^3959
        have hw : |(77065847/156250000 : ℝ)|=(77065847/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2715622761/5000000000 : ℝ)*x 0 + (-960556373/5000000000 : ℝ)*x 1 + (986443013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715622761/5000000000 : ℝ)^4983 ≤ (1449375397469/3125000000000 : ℝ)^3959 := by
    have hnat : (2715622761 : ℕ)^4983*3125000000000^3959 ≤ 1449375397469^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715622761 5000000000 1449375397469 3125000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960556373/5000000000 : ℝ)^4983 ≤ (501536966457/4000000000000 : ℝ)^3959 := by
    have hnat : (960556373 : ℕ)^4983*4000000000000^3959 ≤ 501536966457^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960556373 5000000000 501536966457 4000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986443013/2000000000 : ℝ)^4983 ≤ (8216312619071/20000000000000 : ℝ)^3959 := by
    have hnat : (986443013 : ℕ)^4983*20000000000000^3959 ≤ 8216312619071^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986443013 2000000000 8216312619071 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715622761/5000000000 : ℝ), (-960556373/5000000000 : ℝ), (986443013/2000000000 : ℝ)] ![(1449375397469/3125000000000 : ℝ), (501536966457/4000000000000 : ℝ), (8216312619071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715622761/5000000000 : ℝ)|^4983 ≤ (1449375397469/3125000000000 : ℝ)^3959
        have hw : |(2715622761/5000000000 : ℝ)|=(2715622761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960556373/5000000000 : ℝ)|^4983 ≤ (501536966457/4000000000000 : ℝ)^3959
        have hw : |(-960556373/5000000000 : ℝ)|=(960556373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(986443013/2000000000 : ℝ)|^4983 ≤ (8216312619071/20000000000000 : ℝ)^3959
        have hw : |(986443013/2000000000 : ℝ)|=(986443013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2715623719/5000000000 : ℝ)*x 0 + (4932213849/10000000000 : ℝ)*x 1 + (-1921111793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715623719/5000000000 : ℝ)^4983 ≤ (46380033312611/100000000000000 : ℝ)^3959 := by
    have hnat : (2715623719 : ℕ)^4983*100000000000000^3959 ≤ 46380033312611^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715623719 5000000000 46380033312611 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4932213849/10000000000 : ℝ)^4983 ≤ (41081550347301/100000000000000 : ℝ)^3959 := by
    have hnat : (4932213849 : ℕ)^4983*100000000000000^3959 ≤ 41081550347301^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4932213849 10000000000 41081550347301 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921111793/10000000000 : ℝ)^4983 ≤ (3134604083187/25000000000000 : ℝ)^3959 := by
    have hnat : (1921111793 : ℕ)^4983*25000000000000^3959 ≤ 3134604083187^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921111793 10000000000 3134604083187 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715623719/5000000000 : ℝ), (4932213849/10000000000 : ℝ), (-1921111793/10000000000 : ℝ)] ![(46380033312611/100000000000000 : ℝ), (41081550347301/100000000000000 : ℝ), (3134604083187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715623719/5000000000 : ℝ)|^4983 ≤ (46380033312611/100000000000000 : ℝ)^3959
        have hw : |(2715623719/5000000000 : ℝ)|=(2715623719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4932213849/10000000000 : ℝ)|^4983 ≤ (41081550347301/100000000000000 : ℝ)^3959
        have hw : |(4932213849/10000000000 : ℝ)|=(4932213849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921111793/10000000000 : ℝ)|^4983 ≤ (3134604083187/25000000000000 : ℝ)^3959
        have hw : |(-1921111793/10000000000 : ℝ)|=(1921111793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083189401/10000000000 : ℝ)*x 0 + (3086823619/10000000000 : ℝ)*x 1 + (2643557299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083189401/10000000000 : ℝ)^4983 ≤ (32387997398733/100000000000000 : ℝ)^3959 := by
    have hnat : (4083189401 : ℕ)^4983*100000000000000^3959 ≤ 32387997398733^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083189401 10000000000 32387997398733 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3086823619/10000000000 : ℝ)^4983 ≤ (2846973724151/12500000000000 : ℝ)^3959 := by
    have hnat : (3086823619 : ℕ)^4983*12500000000000^3959 ≤ 2846973724151^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3086823619 10000000000 2846973724151 12500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2643557299/5000000000 : ℝ)^4983 ≤ (44836212791647/100000000000000 : ℝ)^3959 := by
    have hnat : (2643557299 : ℕ)^4983*100000000000000^3959 ≤ 44836212791647^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643557299 5000000000 44836212791647 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083189401/10000000000 : ℝ), (3086823619/10000000000 : ℝ), (2643557299/5000000000 : ℝ)] ![(32387997398733/100000000000000 : ℝ), (2846973724151/12500000000000 : ℝ), (44836212791647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083189401/10000000000 : ℝ)|^4983 ≤ (32387997398733/100000000000000 : ℝ)^3959
        have hw : |(4083189401/10000000000 : ℝ)|=(4083189401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3086823619/10000000000 : ℝ)|^4983 ≤ (2846973724151/12500000000000 : ℝ)^3959
        have hw : |(3086823619/10000000000 : ℝ)|=(3086823619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2643557299/5000000000 : ℝ)|^4983 ≤ (44836212791647/100000000000000 : ℝ)^3959
        have hw : |(2643557299/5000000000 : ℝ)|=(2643557299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1467112613/10000000000 : ℝ)*x 0 + (2476356187/5000000000 : ℝ)*x 1 + (143615671/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1467112613/10000000000 : ℝ)^4983 ≤ (8930345129953/100000000000000 : ℝ)^3959 := by
    have hnat : (1467112613 : ℕ)^4983*100000000000000^3959 ≤ 8930345129953^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467112613 10000000000 8930345129953 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2476356187/5000000000 : ℝ)^4983 ≤ (206482820027/500000000000 : ℝ)^3959 := by
    have hnat : (2476356187 : ℕ)^4983*500000000000^3959 ≤ 206482820027^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476356187 5000000000 206482820027 500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143615671/250000000 : ℝ)^4983 ≤ (49773090850861/100000000000000 : ℝ)^3959 := by
    have hnat : (143615671 : ℕ)^4983*100000000000000^3959 ≤ 49773090850861^3959*250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143615671 250000000 49773090850861 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1467112613/10000000000 : ℝ), (2476356187/5000000000 : ℝ), (143615671/250000000 : ℝ)] ![(8930345129953/100000000000000 : ℝ), (206482820027/500000000000 : ℝ), (49773090850861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1467112613/10000000000 : ℝ)|^4983 ≤ (8930345129953/100000000000000 : ℝ)^3959
        have hw : |(-1467112613/10000000000 : ℝ)|=(1467112613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2476356187/5000000000 : ℝ)|^4983 ≤ (206482820027/500000000000 : ℝ)^3959
        have hw : |(2476356187/5000000000 : ℝ)|=(2476356187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143615671/250000000 : ℝ)|^4983 ≤ (49773090850861/100000000000000 : ℝ)^3959
        have hw : |(143615671/250000000 : ℝ)|=(143615671/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520390433/1000000000 : ℝ)*x 0 + (-277175063/2500000000 : ℝ)*x 1 + (5744628141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520390433/1000000000 : ℝ)^4983 ≤ (21974932480571/50000000000000 : ℝ)^3959 := by
    have hnat : (520390433 : ℕ)^4983*50000000000000^3959 ≤ 21974932480571^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520390433 1000000000 21974932480571 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277175063/2500000000 : ℝ)^4983 ≤ (39231437407/625000000000 : ℝ)^3959 := by
    have hnat : (277175063 : ℕ)^4983*625000000000^3959 ≤ 39231437407^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277175063 2500000000 39231437407 625000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5744628141/10000000000 : ℝ)^4983 ≤ (24886552519337/50000000000000 : ℝ)^3959 := by
    have hnat : (5744628141 : ℕ)^4983*50000000000000^3959 ≤ 24886552519337^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5744628141 10000000000 24886552519337 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520390433/1000000000 : ℝ), (-277175063/2500000000 : ℝ), (5744628141/10000000000 : ℝ)] ![(21974932480571/50000000000000 : ℝ), (39231437407/625000000000 : ℝ), (24886552519337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520390433/1000000000 : ℝ)|^4983 ≤ (21974932480571/50000000000000 : ℝ)^3959
        have hw : |(520390433/1000000000 : ℝ)|=(520390433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277175063/2500000000 : ℝ)|^4983 ≤ (39231437407/625000000000 : ℝ)^3959
        have hw : |(-277175063/2500000000 : ℝ)|=(277175063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5744628141/10000000000 : ℝ)|^4983 ≤ (24886552519337/50000000000000 : ℝ)^3959
        have hw : |(5744628141/10000000000 : ℝ)|=(5744628141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203904599/10000000000 : ℝ)*x 0 + (718078481/1250000000 : ℝ)*x 1 + (-11087003/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203904599/10000000000 : ℝ)^4983 ≤ (21974933910307/50000000000000 : ℝ)^3959 := by
    have hnat : (5203904599 : ℕ)^4983*50000000000000^3959 ≤ 21974933910307^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203904599 10000000000 21974933910307 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718078481/1250000000 : ℝ)^4983 ≤ (49773101843417/100000000000000 : ℝ)^3959 := by
    have hnat : (718078481 : ℕ)^4983*100000000000000^3959 ≤ 49773101843417^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718078481 1250000000 49773101843417 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11087003/100000000 : ℝ)^4983 ≤ (49039299431/781250000000 : ℝ)^3959 := by
    have hnat : (11087003 : ℕ)^4983*781250000000^3959 ≤ 49039299431^3959*100000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11087003 100000000 49039299431 781250000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203904599/10000000000 : ℝ), (718078481/1250000000 : ℝ), (-11087003/100000000 : ℝ)] ![(21974933910307/50000000000000 : ℝ), (49773101843417/100000000000000 : ℝ), (49039299431/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203904599/10000000000 : ℝ)|^4983 ≤ (21974933910307/50000000000000 : ℝ)^3959
        have hw : |(5203904599/10000000000 : ℝ)|=(5203904599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(718078481/1250000000 : ℝ)|^4983 ≤ (49773101843417/100000000000000 : ℝ)^3959
        have hw : |(718078481/1250000000 : ℝ)|=(718078481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11087003/100000000 : ℝ)|^4983 ≤ (49039299431/781250000000 : ℝ)^3959
        have hw : |(-11087003/100000000 : ℝ)|=(11087003/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s0_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4088791709/10000000000 : ℝ)*x 0 + (5233009761/10000000000 : ℝ)*x 1 + (3142771663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4088791709/10000000000 : ℝ)^4983 ≤ (4055492360061/12500000000000 : ℝ)^3959 := by
    have hnat : (4088791709 : ℕ)^4983*12500000000000^3959 ≤ 4055492360061^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088791709 10000000000 4055492360061 12500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233009761/10000000000 : ℝ)^4983 ≤ (22129739715067/50000000000000 : ℝ)^3959 := by
    have hnat : (5233009761 : ℕ)^4983*50000000000000^3959 ≤ 22129739715067^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233009761 10000000000 22129739715067 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3142771663/10000000000 : ℝ)^4983 ≤ (23296581675361/100000000000000 : ℝ)^3959 := by
    have hnat : (3142771663 : ℕ)^4983*100000000000000^3959 ≤ 23296581675361^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142771663 10000000000 23296581675361 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4088791709/10000000000 : ℝ), (5233009761/10000000000 : ℝ), (3142771663/10000000000 : ℝ)] ![(4055492360061/12500000000000 : ℝ), (22129739715067/50000000000000 : ℝ), (23296581675361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4088791709/10000000000 : ℝ)|^4983 ≤ (4055492360061/12500000000000 : ℝ)^3959
        have hw : |(4088791709/10000000000 : ℝ)|=(4088791709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233009761/10000000000 : ℝ)|^4983 ≤ (22129739715067/50000000000000 : ℝ)^3959
        have hw : |(5233009761/10000000000 : ℝ)|=(5233009761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3142771663/10000000000 : ℝ)|^4983 ≤ (23296581675361/100000000000000 : ℝ)^3959
        have hw : |(3142771663/10000000000 : ℝ)|=(3142771663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11511/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4979/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4979 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4979*1^1024 ≤ 0^1024*1^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4979/1024 : ℝ) ≤ (1161701179993063761/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4979 ≤ (1161701179993063761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4979*100000000000000000000^1024 ≤ 1161701179993063761^1024*5^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1161701179993063761 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1161701179993063761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4979 := by
      have hnat : (1 : ℕ)^1024*1^4979 ≤ 1^4979*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101161701179993063761/100000000000000000000 : ℝ) ≤ (2004756502180017/2000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (101161701179993063761/100000000000000000000 : ℝ)^1024 ≤ (2004756502180017/2000000000000000 : ℝ)^4979 := by
      have hnat : (101161701179993063761 : ℕ)^1024*2000000000000000^4979 ≤ 2004756502180017^4979*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101161701179993063761 100000000000000000000 2004756502180017 2000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004756502180017/2000000000000000 : ℝ)) (X := (101161701179993063761/100000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51161701179993063761/50000000000000000000 : ℝ) ≤ (1004756502180017/1000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (51161701179993063761/50000000000000000000 : ℝ)^1024 ≤ (1004756502180017/1000000000000000 : ℝ)^4979 := by
      have hnat : (51161701179993063761 : ℕ)^1024*1000000000000000^4979 ≤ 1004756502180017^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51161701179993063761 50000000000000000000 1004756502180017 1000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004756502180017/1000000000000000 : ℝ)) (X := (51161701179993063761/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4756502180017/800000000000000 : ℝ)*(0 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4756502180017/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1161701179993063761/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4756502180017/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4756502180017/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2004756502180017/2000000000000000 : ℝ) by norm_num, show 1+(1161701179993063761/100000000000000000000 : ℝ)+(0 : ℝ)=(101161701179993063761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1161701179993063761/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4756502180017/800000000000000 : ℝ)*(2/5 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4756502180017/800000000000000 : ℝ)*(2/5 : ℝ)=(1004756502180017/1000000000000000 : ℝ) by norm_num, show 1+2*(1161701179993063761/100000000000000000000 : ℝ)=(51161701179993063761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4756502180017/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4756502180017/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4756502180017/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4756502180017/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4756502180017/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4756502180017/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-732494839/5000000000 : ℝ)*X 0 0+(1441455993/2500000000 : ℝ)*X 0 1+(77065847/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2715622761/5000000000 : ℝ)*X 1 0+(-960556373/5000000000 : ℝ)*X 1 1+(986443013/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2715623719/5000000000 : ℝ)*X 2 0+(4932213849/10000000000 : ℝ)*X 2 1+(-1921111793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4083189401/10000000000 : ℝ)*X 0 0+(3086823619/10000000000 : ℝ)*X 0 1+(2643557299/5000000000 : ℝ)*X 0 2+(4083189401/10000000000 : ℝ)*X 1 0+(3086823619/10000000000 : ℝ)*X 1 1+(2643557299/5000000000 : ℝ)*X 1 2+(4083189401/10000000000 : ℝ)*X 2 0+(3086823619/10000000000 : ℝ)*X 2 1+(2643557299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1467112613/10000000000 : ℝ)*X 0 0+(2476356187/5000000000 : ℝ)*X 0 1+(143615671/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((520390433/1000000000 : ℝ)*X 1 0+(-277175063/2500000000 : ℝ)*X 1 1+(5744628141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203904599/10000000000 : ℝ)*X 2 0+(718078481/1250000000 : ℝ)*X 2 1+(-11087003/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4088791709/10000000000 : ℝ)*X 0 0+(5233009761/10000000000 : ℝ)*X 0 1+(3142771663/10000000000 : ℝ)*X 0 2+(4088791709/10000000000 : ℝ)*X 1 0+(5233009761/10000000000 : ℝ)*X 1 1+(3142771663/10000000000 : ℝ)*X 1 2+(4088791709/10000000000 : ℝ)*X 2 0+(5233009761/10000000000 : ℝ)*X 2 1+(3142771663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11076408078053991018117/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114862009/100000000000000 : ℝ)*(base1) + (185850333/50000000000000 : ℝ)*(base19) + (85006597/12500000000000 : ℝ)*(base23) + (2296741/2000000000000 : ℝ)*(base24) + (57564747/100000000000000 : ℝ)*(upper5) + (82704687574233/10000000000000 : ℝ)*(major0) + (82704687574233/10000000000000 : ℝ)*(major1) + (82704687574233/10000000000000 : ℝ)*(major2) + (239920713778433/20000000000000 : ℝ)*(sp0) + (599802984543113/50000000000000 : ℝ)*(sp1) + (1199605545897067/100000000000000 : ℝ)*(sp2) + (454486195217689/100000000000000 : ℝ)*(sp3) + (22552787/781250000000 : ℝ)*(sp4) + (1008314663/100000000000000 : ℝ)*(sp7) + (454487318394361/100000000000000 : ℝ)*(f.failure) + (299901585196723/25000000000000 : ℝ)*(f.sum) + (4170620570039/4000000000000000000000000000 : ℝ)*base66 + (12593995277961/8000000000000000000000000000 : ℝ)*base67 + (41973671493961/8000000000000000000000000000 : ℝ)*base69 + (31000630077961/8000000000000000000000000000 : ℝ)*base71 + (16438325050039/4000000000000000000000000000 : ℝ)*base74 + (50358310453961/8000000000000000000000000000 : ℝ)*base75 + (21711955085961/8000000000000000000000000000 : ℝ)*base77 + (14852806634039/8000000000000000000000000000 : ℝ)*base80 + (10613186861961/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48257093/10000000000000000000000 : ℝ)*base90 + (48257093/10000000000000000000000 : ℝ)*base92 + (48257093/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4745025387119649704481/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58225329/6250000000000 : ℝ)*(base19) + (1018310857/100000000000000 : ℝ)*(base23) + (13878579/20000000000000 : ℝ)*(base32) + (132507679/50000000000000 : ℝ)*(upper3) + (137926093/100000000000000 : ℝ)*(upper5) + (17411763043269/2000000000000 : ℝ)*(major0) + (17411763043269/2000000000000 : ℝ)*(major1) + (17411763043269/2000000000000 : ℝ)*(major2) + (454975753/12500000000000 : ℝ)*(sp1) + (2065169223/50000000000000 : ℝ)*(sp2) + (315690384373663/25000000000000 : ℝ)*(sp4) + (315689241520841/25000000000000 : ℝ)*(sp5) + (315689097211337/25000000000000 : ℝ)*(sp6) + (239207249864979/50000000000000 : ℝ)*(sp7) + (478414569122853/100000000000000 : ℝ)*(f.failure) + (315690384373663/25000000000000 : ℝ)*(f.sum) + (1520740118773/800000000000000000000000000 : ℝ)*base65 + (3637047937973/1600000000000000000000000000 : ℝ)*base67 + (8191585578827/1600000000000000000000000000 : ℝ)*base70 + (7356816036427/1600000000000000000000000000 : ℝ)*base72 + (4205333830773/800000000000000000000000000 : ℝ)*base73 + (2433566705227/1600000000000000000000000000 : ℝ)*base76 + (5750118120373/1600000000000000000000000000 : ℝ)*base77 + (4940782481973/1600000000000000000000000000 : ℝ)*base79 + (752387505227/800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4083711/10000000000000000000000 : ℝ)*base89 + (4083711/10000000000000000000000 : ℝ)*base91 + (4083711/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1666_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11511/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1666_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1666_s1_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-312884771/2000000000 : ℝ)*x 0 + (548476953/1000000000 : ℝ)*x 1 + (5148505269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312884771/2000000000 : ℝ)^4983 ≤ (9682182325617/100000000000000 : ℝ)^3959 := by
    have hnat : (312884771 : ℕ)^4983*100000000000000^3959 ≤ 9682182325617^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312884771 2000000000 9682182325617 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548476953/1000000000 : ℝ)^4983 ≤ (46956032300877/100000000000000 : ℝ)^3959 := by
    have hnat : (548476953 : ℕ)^4983*100000000000000^3959 ≤ 46956032300877^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548476953 1000000000 46956032300877 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148505269/10000000000 : ℝ)^4983 ≤ (21680892678439/50000000000000 : ℝ)^3959 := by
    have hnat : (5148505269 : ℕ)^4983*50000000000000^3959 ≤ 21680892678439^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148505269 10000000000 21680892678439 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-312884771/2000000000 : ℝ), (548476953/1000000000 : ℝ), (5148505269/10000000000 : ℝ)] ![(9682182325617/100000000000000 : ℝ), (46956032300877/100000000000000 : ℝ), (21680892678439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-312884771/2000000000 : ℝ)|^4983 ≤ (9682182325617/100000000000000 : ℝ)^3959
        have hw : |(-312884771/2000000000 : ℝ)|=(312884771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548476953/1000000000 : ℝ)|^4983 ≤ (46956032300877/100000000000000 : ℝ)^3959
        have hw : |(548476953/1000000000 : ℝ)|=(548476953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148505269/10000000000 : ℝ)|^4983 ≤ (21680892678439/50000000000000 : ℝ)^3959
        have hw : |(5148505269/10000000000 : ℝ)|=(5148505269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356480049/10000000000 : ℝ)*x 0 + (-869447793/5000000000 : ℝ)*x 1 + (2574252649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356480049/10000000000 : ℝ)^4983 ≤ (1139446299747/2500000000000 : ℝ)^3959 := by
    have hnat : (5356480049 : ℕ)^4983*2500000000000^3959 ≤ 1139446299747^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356480049 10000000000 1139446299747 2500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869447793/5000000000 : ℝ)^4983 ≤ (553018117051/5000000000000 : ℝ)^3959 := by
    have hnat : (869447793 : ℕ)^4983*5000000000000^3959 ≤ 553018117051^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869447793 5000000000 553018117051 5000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574252649/5000000000 : ℝ)^4983 ≤ (5420223208037/12500000000000 : ℝ)^3959 := by
    have hnat : (2574252649 : ℕ)^4983*12500000000000^3959 ≤ 5420223208037^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574252649 5000000000 5420223208037 12500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356480049/10000000000 : ℝ), (-869447793/5000000000 : ℝ), (2574252649/5000000000 : ℝ)] ![(1139446299747/2500000000000 : ℝ), (553018117051/5000000000000 : ℝ), (5420223208037/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356480049/10000000000 : ℝ)|^4983 ≤ (1139446299747/2500000000000 : ℝ)^3959
        have hw : |(5356480049/10000000000 : ℝ)|=(5356480049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-869447793/5000000000 : ℝ)|^4983 ≤ (553018117051/5000000000000 : ℝ)^3959
        have hw : |(-869447793/5000000000 : ℝ)|=(869447793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574252649/5000000000 : ℝ)|^4983 ≤ (5420223208037/12500000000000 : ℝ)^3959
        have hw : |(2574252649/5000000000 : ℝ)|=(2574252649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356480049/10000000000 : ℝ)*x 0 + (2574252701/5000000000 : ℝ)*x 1 + (-1738895447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356480049/10000000000 : ℝ)^4983 ≤ (1139446299747/2500000000000 : ℝ)^3959 := by
    have hnat : (5356480049 : ℕ)^4983*2500000000000^3959 ≤ 1139446299747^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356480049 10000000000 1139446299747 2500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574252701/5000000000 : ℝ)^4983 ≤ (43361786766761/100000000000000 : ℝ)^3959 := by
    have hnat : (2574252701 : ℕ)^4983*100000000000000^3959 ≤ 43361786766761^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574252701 5000000000 43361786766761 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1738895447/10000000000 : ℝ)^4983 ≤ (11060361228223/100000000000000 : ℝ)^3959 := by
    have hnat : (1738895447 : ℕ)^4983*100000000000000^3959 ≤ 11060361228223^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738895447 10000000000 11060361228223 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356480049/10000000000 : ℝ), (2574252701/5000000000 : ℝ), (-1738895447/10000000000 : ℝ)] ![(1139446299747/2500000000000 : ℝ), (43361786766761/100000000000000 : ℝ), (11060361228223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356480049/10000000000 : ℝ)|^4983 ≤ (1139446299747/2500000000000 : ℝ)^3959
        have hw : |(5356480049/10000000000 : ℝ)|=(5356480049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574252701/5000000000 : ℝ)|^4983 ≤ (43361786766761/100000000000000 : ℝ)^3959
        have hw : |(2574252701/5000000000 : ℝ)|=(2574252701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1738895447/10000000000 : ℝ)|^4983 ≤ (11060361228223/100000000000000 : ℝ)^3959
        have hw : |(-1738895447/10000000000 : ℝ)|=(1738895447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162372099/10000000000 : ℝ)*x 0 + (747064663/2000000000 : ℝ)*x 1 + (72232551/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162372099/10000000000 : ℝ)^4983 ≤ (33180504029127/100000000000000 : ℝ)^3959 := by
    have hnat : (4162372099 : ℕ)^4983*100000000000000^3959 ≤ 33180504029127^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162372099 10000000000 33180504029127 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747064663/2000000000 : ℝ)^4983 ≤ (28954120991407/100000000000000 : ℝ)^3959 := by
    have hnat : (747064663 : ℕ)^4983*100000000000000^3959 ≤ 28954120991407^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747064663 2000000000 28954120991407 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72232551/156250000 : ℝ)^4983 ≤ (9466343741559/25000000000000 : ℝ)^3959 := by
    have hnat : (72232551 : ℕ)^4983*25000000000000^3959 ≤ 9466343741559^3959*156250000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72232551 156250000 9466343741559 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162372099/10000000000 : ℝ), (747064663/2000000000 : ℝ), (72232551/156250000 : ℝ)] ![(33180504029127/100000000000000 : ℝ), (28954120991407/100000000000000 : ℝ), (9466343741559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162372099/10000000000 : ℝ)|^4983 ≤ (33180504029127/100000000000000 : ℝ)^3959
        have hw : |(4162372099/10000000000 : ℝ)|=(4162372099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747064663/2000000000 : ℝ)|^4983 ≤ (28954120991407/100000000000000 : ℝ)^3959
        have hw : |(747064663/2000000000 : ℝ)|=(747064663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(72232551/156250000 : ℝ)|^4983 ≤ (9466343741559/25000000000000 : ℝ)^3959
        have hw : |(72232551/156250000 : ℝ)|=(72232551/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-312912343/2000000000 : ℝ)*x 0 + (160994863/312500000 : ℝ)*x 1 + (1096278607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312912343/2000000000 : ℝ)^4983 ≤ (4841628117251/50000000000000 : ℝ)^3959 := by
    have hnat : (312912343 : ℕ)^4983*50000000000000^3959 ≤ 4841628117251^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312912343 2000000000 4841628117251 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160994863/312500000 : ℝ)^4983 ≤ (5424636507739/12500000000000 : ℝ)^3959 := by
    have hnat : (160994863 : ℕ)^4983*12500000000000^3959 ≤ 5424636507739^3959*312500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160994863 312500000 5424636507739 12500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096278607/2000000000 : ℝ)^4983 ≤ (4691965169537/10000000000000 : ℝ)^3959 := by
    have hnat : (1096278607 : ℕ)^4983*10000000000000^3959 ≤ 4691965169537^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096278607 2000000000 4691965169537 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-312912343/2000000000 : ℝ), (160994863/312500000 : ℝ), (1096278607/2000000000 : ℝ)] ![(4841628117251/50000000000000 : ℝ), (5424636507739/12500000000000 : ℝ), (4691965169537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-312912343/2000000000 : ℝ)|^4983 ≤ (4841628117251/50000000000000 : ℝ)^3959
        have hw : |(-312912343/2000000000 : ℝ)|=(312912343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160994863/312500000 : ℝ)|^4983 ≤ (5424636507739/12500000000000 : ℝ)^3959
        have hw : |(160994863/312500000 : ℝ)|=(160994863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096278607/2000000000 : ℝ)|^4983 ≤ (4691965169537/10000000000000 : ℝ)^3959
        have hw : |(1096278607/2000000000 : ℝ)|=(1096278607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266436023/10000000000 : ℝ)*x 0 + (-1406007609/10000000000 : ℝ)*x 1 + (2740696509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266436023/10000000000 : ℝ)^4983 ≤ (22307803667023/50000000000000 : ℝ)^3959 := by
    have hnat : (5266436023 : ℕ)^4983*50000000000000^3959 ≤ 22307803667023^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266436023 10000000000 22307803667023 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406007609/10000000000 : ℝ)^4983 ≤ (4232370568783/50000000000000 : ℝ)^3959 := by
    have hnat : (1406007609 : ℕ)^4983*50000000000000^3959 ≤ 4232370568783^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406007609 10000000000 4232370568783 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740696509/5000000000 : ℝ)^4983 ≤ (9383930302443/20000000000000 : ℝ)^3959 := by
    have hnat : (2740696509 : ℕ)^4983*20000000000000^3959 ≤ 9383930302443^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740696509 5000000000 9383930302443 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266436023/10000000000 : ℝ), (-1406007609/10000000000 : ℝ), (2740696509/5000000000 : ℝ)] ![(22307803667023/50000000000000 : ℝ), (4232370568783/50000000000000 : ℝ), (9383930302443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266436023/10000000000 : ℝ)|^4983 ≤ (22307803667023/50000000000000 : ℝ)^3959
        have hw : |(5266436023/10000000000 : ℝ)|=(5266436023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1406007609/10000000000 : ℝ)|^4983 ≤ (4232370568783/50000000000000 : ℝ)^3959
        have hw : |(-1406007609/10000000000 : ℝ)|=(1406007609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740696509/5000000000 : ℝ)|^4983 ≤ (9383930302443/20000000000000 : ℝ)^3959
        have hw : |(2740696509/5000000000 : ℝ)|=(2740696509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633218009/5000000000 : ℝ)*x 0 + (5481393023/10000000000 : ℝ)*x 1 + (-1406007609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633218009/5000000000 : ℝ)^4983 ≤ (11153901820183/25000000000000 : ℝ)^3959 := by
    have hnat : (2633218009 : ℕ)^4983*25000000000000^3959 ≤ 11153901820183^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633218009 5000000000 11153901820183 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481393023/10000000000 : ℝ)^4983 ≤ (11729912891521/25000000000000 : ℝ)^3959 := by
    have hnat : (5481393023 : ℕ)^4983*25000000000000^3959 ≤ 11729912891521^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481393023 10000000000 11729912891521 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406007609/10000000000 : ℝ)^4983 ≤ (4232370568783/50000000000000 : ℝ)^3959 := by
    have hnat : (1406007609 : ℕ)^4983*50000000000000^3959 ≤ 4232370568783^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406007609 10000000000 4232370568783 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633218009/5000000000 : ℝ), (5481393023/10000000000 : ℝ), (-1406007609/10000000000 : ℝ)] ![(11153901820183/25000000000000 : ℝ), (11729912891521/25000000000000 : ℝ), (4232370568783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633218009/5000000000 : ℝ)|^4983 ≤ (11153901820183/25000000000000 : ℝ)^3959
        have hw : |(2633218009/5000000000 : ℝ)|=(2633218009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481393023/10000000000 : ℝ)|^4983 ≤ (11729912891521/25000000000000 : ℝ)^3959
        have hw : |(5481393023/10000000000 : ℝ)|=(5481393023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1406007609/10000000000 : ℝ)|^4983 ≤ (4232370568783/50000000000000 : ℝ)^3959
        have hw : |(-1406007609/10000000000 : ℝ)|=(1406007609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s1_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162734127/10000000000 : ℝ)*x 0 + (922818503/2000000000 : ℝ)*x 1 + (234014691/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162734127/10000000000 : ℝ)^4983 ≤ (16592068218083/50000000000000 : ℝ)^3959 := by
    have hnat : (4162734127 : ℕ)^4983*50000000000000^3959 ≤ 16592068218083^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162734127 10000000000 16592068218083 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922818503/2000000000 : ℝ)^4983 ≤ (9443692409691/25000000000000 : ℝ)^3959 := by
    have hnat : (922818503 : ℕ)^4983*25000000000000^3959 ≤ 9443692409691^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922818503 2000000000 9443692409691 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234014691/625000000 : ℝ)^4983 ≤ (1161643756269/4000000000000 : ℝ)^3959 := by
    have hnat : (234014691 : ℕ)^4983*4000000000000^3959 ≤ 1161643756269^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234014691 625000000 1161643756269 4000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162734127/10000000000 : ℝ), (922818503/2000000000 : ℝ), (234014691/625000000 : ℝ)] ![(16592068218083/50000000000000 : ℝ), (9443692409691/25000000000000 : ℝ), (1161643756269/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162734127/10000000000 : ℝ)|^4983 ≤ (16592068218083/50000000000000 : ℝ)^3959
        have hw : |(4162734127/10000000000 : ℝ)|=(4162734127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922818503/2000000000 : ℝ)|^4983 ≤ (9443692409691/25000000000000 : ℝ)^3959
        have hw : |(922818503/2000000000 : ℝ)|=(922818503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234014691/625000000 : ℝ)|^4983 ≤ (1161643756269/4000000000000 : ℝ)^3959
        have hw : |(234014691/625000000 : ℝ)|=(234014691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11511/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9963/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3423/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11511/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11511/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11511/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11511/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11511/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11511/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5147/100000 : ℝ) ^ (4979/1024 : ℝ) ≤ (27174014138571/50000000000000000000 : ℝ) := by
    have hpowers : (5147/100000 : ℝ)^4979 ≤ (27174014138571/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5147 : ℕ)^4979*50000000000000000000^1024 ≤ 27174014138571^1024*100000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5147 100000 27174014138571 50000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5147/100000 : ℝ)) (X := (27174014138571/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11511/50000 : ℝ) ^ (4979/1024 : ℝ) ≤ (79167177218078647/100000000000000000000 : ℝ) := by
    have hpowers : (11511/50000 : ℝ)^4979 ≤ (79167177218078647/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11511 : ℕ)^4979*100000000000000000000^1024 ≤ 79167177218078647^1024*50000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11511 50000 79167177218078647 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11511/50000 : ℝ)) (X := (79167177218078647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000027174014138571/25000000000000000000 : ℝ) ≤ (2500000558870827/2500000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (25000027174014138571/25000000000000000000 : ℝ)^1024 ≤ (2500000558870827/2500000000000000 : ℝ)^4979 := by
      have hnat : (25000027174014138571 : ℕ)^1024*2500000000000000^4979 ≤ 2500000558870827^4979*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000027174014138571 25000000000000000000 2500000558870827 2500000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000558870827/2500000000000000 : ℝ)) (X := (25000027174014138571/25000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100079221525246355789/100000000000000000000 : ℝ) ≤ (500081439374609/500000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (100079221525246355789/100000000000000000000 : ℝ)^1024 ≤ (500081439374609/500000000000000 : ℝ)^4979 := by
      have hnat : (100079221525246355789 : ℕ)^1024*500000000000000^4979 ≤ 500081439374609^4979*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100079221525246355789 100000000000000000000 500081439374609 500000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500081439374609/500000000000000 : ℝ)) (X := (100079221525246355789/100000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50079167177218078647/50000000000000000000 : ℝ) ≤ (2500813834875263/2500000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50079167177218078647/50000000000000000000 : ℝ)^1024 ≤ (2500813834875263/2500000000000000 : ℝ)^4979 := by
      have hnat : (50079167177218078647 : ℕ)^1024*2500000000000000^4979 ≤ 2500813834875263^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50079167177218078647 50000000000000000000 2500813834875263 2500000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500813834875263/2500000000000000 : ℝ)) (X := (50079167177218078647/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27174014138571/50000000000000000000 : ℝ) ≤ ((44683324058221200533/44687500000000000000 : ℝ)+2*(203319001109/223437500000000 : ℝ)*(5147/100000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (44683324058221200533/44687500000000000000 : ℝ)+2*(203319001109/223437500000000 : ℝ)*(5147/100000 : ℝ)=(2500000558870827/2500000000000000 : ℝ) by norm_num, show 1+2*(27174014138571/50000000000000000000 : ℝ)=(25000027174014138571/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79167177218078647/100000000000000000000 : ℝ)+(27174014138571/50000000000000000000 : ℝ) ≤ ((44683324058221200533/44687500000000000000 : ℝ)+(203319001109/223437500000000 : ℝ)*((11511/50000 : ℝ)+(5147/100000 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (44683324058221200533/44687500000000000000 : ℝ)+(203319001109/223437500000000 : ℝ)*((11511/50000 : ℝ)+(5147/100000 : ℝ))=(500081439374609/500000000000000 : ℝ) by norm_num, show 1+(79167177218078647/100000000000000000000 : ℝ)+(27174014138571/50000000000000000000 : ℝ)=(100079221525246355789/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79167177218078647/100000000000000000000 : ℝ) ≤ ((44683324058221200533/44687500000000000000 : ℝ)+2*(203319001109/223437500000000 : ℝ)*(11511/50000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (44683324058221200533/44687500000000000000 : ℝ)+2*(203319001109/223437500000000 : ℝ)*(11511/50000 : ℝ)=(2500813834875263/2500000000000000 : ℝ) by norm_num, show 1+2*(79167177218078647/100000000000000000000 : ℝ)=(50079167177218078647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44683324058221200533/44687500000000000000 : ℝ)*(X 1 0+X 2 0)+(203319001109/223437500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (5147/100000 : ℝ)) (hi := (11511/50000 : ℝ)) (c := (44683324058221200533/44687500000000000000 : ℝ)) (alpha := (203319001109/223437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44683324058221200533/44687500000000000000 : ℝ)*(X 0 1+X 2 1)+(203319001109/223437500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (5147/100000 : ℝ)) (hi := (11511/50000 : ℝ)) (c := (44683324058221200533/44687500000000000000 : ℝ)) (alpha := (203319001109/223437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44683324058221200533/44687500000000000000 : ℝ)*(X 0 2+X 1 2)+(203319001109/223437500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (5147/100000 : ℝ)) (hi := (11511/50000 : ℝ)) (c := (44683324058221200533/44687500000000000000 : ℝ)) (alpha := (203319001109/223437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-312884771/2000000000 : ℝ)*X 0 0+(548476953/1000000000 : ℝ)*X 0 1+(5148505269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356480049/10000000000 : ℝ)*X 1 0+(-869447793/5000000000 : ℝ)*X 1 1+(2574252649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356480049/10000000000 : ℝ)*X 2 0+(2574252701/5000000000 : ℝ)*X 2 1+(-1738895447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162372099/10000000000 : ℝ)*X 0 0+(747064663/2000000000 : ℝ)*X 0 1+(72232551/156250000 : ℝ)*X 0 2+(4162372099/10000000000 : ℝ)*X 1 0+(747064663/2000000000 : ℝ)*X 1 1+(72232551/156250000 : ℝ)*X 1 2+(4162372099/10000000000 : ℝ)*X 2 0+(747064663/2000000000 : ℝ)*X 2 1+(72232551/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-312912343/2000000000 : ℝ)*X 0 0+(160994863/312500000 : ℝ)*X 0 1+(1096278607/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266436023/10000000000 : ℝ)*X 1 0+(-1406007609/10000000000 : ℝ)*X 1 1+(2740696509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633218009/5000000000 : ℝ)*X 2 0+(5481393023/10000000000 : ℝ)*X 2 1+(-1406007609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4162734127/10000000000 : ℝ)*X 0 0+(922818503/2000000000 : ℝ)*X 0 1+(234014691/625000000 : ℝ)*X 0 2+(4162734127/10000000000 : ℝ)*X 1 0+(922818503/2000000000 : ℝ)*X 1 1+(234014691/625000000 : ℝ)*X 1 2+(4162734127/10000000000 : ℝ)*X 2 0+(922818503/2000000000 : ℝ)*X 2 1+(234014691/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (329677049627407274798013/44687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (223150303/25000000000000 : ℝ)*(base19) + (33024973/6250000000000 : ℝ)*(base23) + (110163031/50000000000000 : ℝ)*(lower2) + (8195441/4000000000000 : ℝ)*(upper3) + (12621089/50000000000000 : ℝ)*(lower4) + (1025139531820557/50000000000000 : ℝ)*(major0) + (1025139531820557/50000000000000 : ℝ)*(major1) + (1025139531820557/50000000000000 : ℝ)*(major2) + (29738602978187/1000000000000 : ℝ)*(sp0) + (371733314777663/12500000000000 : ℝ)*(sp1) + (743466720605737/25000000000000 : ℝ)*(sp2) + (70417899578691/6250000000000 : ℝ)*(sp3) + (7113003817/100000000000000 : ℝ)*(sp4) + (2038643851/50000000000000 : ℝ)*(sp7) + (563345235273379/50000000000000 : ℝ)*(f.failure) + (743466852705629/25000000000000 : ℝ)*(f.sum) + (439651320629717/89375000000000000000000000000 : ℝ)*base66 + (3756856860632393119/2234375000000000000000000000000000 : ℝ)*base68 + (1887472568945731881/2234375000000000000000000000000000 : ℝ)*base69 + (6376550169007393119/2234375000000000000000000000000000 : ℝ)*base72 + (34868646382329/44687500000000000000000000000 : ℝ)*base73 + (565786808461356881/2234375000000000000000000000000000 : ℝ)*base75 + (6150879536319893119/2234375000000000000000000000000000 : ℝ)*base78 + (9117594407617606881/2234375000000000000000000000000000 : ℝ)*base79 + (82125616956477/22343750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2240473/5000000000000000000000 : ℝ)*base89 + (2240473/5000000000000000000000 : ℝ)*base91 + (2240473/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17240380560307305368267709/6347656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (88432747/20000000000000 : ℝ)*(base19) + (23367799/5000000000000 : ℝ)*(base23) + (61826361/100000000000000 : ℝ)*(upper3) + (3198761/25000000000000 : ℝ)*(lower4) + (63221831/100000000000000 : ℝ)*(upper5) + (130749566810773/6250000000000 : ℝ)*(major0) + (130749566810773/6250000000000 : ℝ)*(major1) + (130749566810773/6250000000000 : ℝ)*(major2) + (1994841091/50000000000000 : ℝ)*(sp1) + (4210626789/100000000000000 : ℝ)*(sp2) + (151718623348351/5000000000000 : ℝ)*(sp4) + (189648002195069/6250000000000 : ℝ)*(sp5) + (3034367788984251/100000000000000 : ℝ)*(sp6) + (114961358044361/10000000000000 : ℝ)*(sp7) + (114961358044361/10000000000000 : ℝ)*(f.failure) + (151718623348351/5000000000000 : ℝ)*(f.sum) + (62636279015073/44687500000000000000000000000 : ℝ)*base65 + (72900112638985759/279296875000000000000000000000000 : ℝ)*base67 + (288715156443045491/279296875000000000000000000000000 : ℝ)*base70 + (1612162538396170491/279296875000000000000000000000000 : ℝ)*base72 + (39800475310073/44687500000000000000000000000 : ℝ)*base73 + (99354889760079509/279296875000000000000000000000000 : ℝ)*base75 + (428736457103672567/139648437500000000000000000000000 : ℝ)*base77 + (1219647888123203817/139648437500000000000000000000000 : ℝ)*base79 + (429288192427/44687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3707093/1000000000000000000000 : ℝ)*base90 + (3707093/1000000000000000000000 : ℝ)*base92 + (3707093/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1666_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11511/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9963/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3423/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1666_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1666_s2_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393079969/2500000000 : ℝ)*x 0 + (680693701/1250000000 : ℝ)*x 1 + (1295625069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393079969/2500000000 : ℝ)^4983 ≤ (608983159497/6250000000000 : ℝ)^3959 := by
    have hnat : (393079969 : ℕ)^4983*6250000000000^3959 ≤ 608983159497^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393079969 2500000000 608983159497 6250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680693701/1250000000 : ℝ)^4983 ≤ (23266904303717/50000000000000 : ℝ)^3959 := by
    have hnat : (680693701 : ℕ)^4983*50000000000000^3959 ≤ 23266904303717^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680693701 1250000000 23266904303717 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295625069/2500000000 : ℝ)^4983 ≤ (43722460827241/100000000000000 : ℝ)^3959 := by
    have hnat : (1295625069 : ℕ)^4983*100000000000000^3959 ≤ 43722460827241^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295625069 2500000000 43722460827241 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393079969/2500000000 : ℝ), (680693701/1250000000 : ℝ), (1295625069/2500000000 : ℝ)] ![(608983159497/6250000000000 : ℝ), (23266904303717/50000000000000 : ℝ), (43722460827241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393079969/2500000000 : ℝ)|^4983 ≤ (608983159497/6250000000000 : ℝ)^3959
        have hw : |(-393079969/2500000000 : ℝ)|=(393079969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680693701/1250000000 : ℝ)|^4983 ≤ (23266904303717/50000000000000 : ℝ)^3959
        have hw : |(680693701/1250000000 : ℝ)|=(680693701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295625069/2500000000 : ℝ)|^4983 ≤ (43722460827241/100000000000000 : ℝ)^3959
        have hw : |(1295625069/2500000000 : ℝ)|=(1295625069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346046293/10000000000 : ℝ)*x 0 + (-170772501/1000000000 : ℝ)*x 1 + (323906279/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346046293/10000000000 : ℝ)^4983 ≤ (45466137127703/100000000000000 : ℝ)^3959 := by
    have hnat : (5346046293 : ℕ)^4983*100000000000000^3959 ≤ 45466137127703^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346046293 10000000000 45466137127703 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170772501/1000000000 : ℝ)^4983 ≤ (10811400036213/100000000000000 : ℝ)^3959 := by
    have hnat : (170772501 : ℕ)^4983*100000000000000^3959 ≤ 10811400036213^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170772501 1000000000 10811400036213 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323906279/625000000 : ℝ)^4983 ≤ (43722462823553/100000000000000 : ℝ)^3959 := by
    have hnat : (323906279 : ℕ)^4983*100000000000000^3959 ≤ 43722462823553^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323906279 625000000 43722462823553 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346046293/10000000000 : ℝ), (-170772501/1000000000 : ℝ), (323906279/625000000 : ℝ)] ![(45466137127703/100000000000000 : ℝ), (10811400036213/100000000000000 : ℝ), (43722462823553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346046293/10000000000 : ℝ)|^4983 ≤ (45466137127703/100000000000000 : ℝ)^3959
        have hw : |(5346046293/10000000000 : ℝ)|=(5346046293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170772501/1000000000 : ℝ)|^4983 ≤ (10811400036213/100000000000000 : ℝ)^3959
        have hw : |(-170772501/1000000000 : ℝ)|=(170772501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323906279/625000000 : ℝ)|^4983 ≤ (43722462823553/100000000000000 : ℝ)^3959
        have hw : |(323906279/625000000 : ℝ)|=(323906279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66825579/125000000 : ℝ)*x 0 + (32390627/62500000 : ℝ)*x 1 + (-853862583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66825579/125000000 : ℝ)^4983 ≤ (45466137416721/100000000000000 : ℝ)^3959 := by
    have hnat : (66825579 : ℕ)^4983*100000000000000^3959 ≤ 45466137416721^3959*125000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66825579 125000000 45466137416721 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32390627/62500000 : ℝ)^4983 ≤ (43722461294463/100000000000000 : ℝ)^3959 := by
    have hnat : (32390627 : ℕ)^4983*100000000000000^3959 ≤ 43722461294463^3959*62500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32390627 62500000 43722461294463 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853862583/5000000000 : ℝ)^4983 ≤ (10811401279279/100000000000000 : ℝ)^3959 := by
    have hnat : (853862583 : ℕ)^4983*100000000000000^3959 ≤ 10811401279279^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853862583 5000000000 10811401279279 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66825579/125000000 : ℝ), (32390627/62500000 : ℝ), (-853862583/5000000000 : ℝ)] ![(45466137416721/100000000000000 : ℝ), (43722461294463/100000000000000 : ℝ), (10811401279279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66825579/125000000 : ℝ)|^4983 ≤ (45466137416721/100000000000000 : ℝ)^3959
        have hw : |(66825579/125000000 : ℝ)|=(66825579/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32390627/62500000 : ℝ)|^4983 ≤ (43722461294463/100000000000000 : ℝ)^3959
        have hw : |(32390627/62500000 : ℝ)|=(32390627/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-853862583/5000000000 : ℝ)|^4983 ≤ (10811401279279/100000000000000 : ℝ)^3959
        have hw : |(-853862583/5000000000 : ℝ)|=(853862583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521034857/1250000000 : ℝ)*x 0 + (3831366199/10000000000 : ℝ)*x 1 + (4525677151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521034857/1250000000 : ℝ)^4983 ≤ (8309944916723/25000000000000 : ℝ)^3959 := by
    have hnat : (521034857 : ℕ)^4983*25000000000000^3959 ≤ 8309944916723^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521034857 1250000000 8309944916723 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3831366199/10000000000 : ℝ)^4983 ≤ (1868390354259/6250000000000 : ℝ)^3959 := by
    have hnat : (3831366199 : ℕ)^4983*6250000000000^3959 ≤ 1868390354259^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3831366199 10000000000 1868390354259 6250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525677151/10000000000 : ℝ)^4983 ≤ (36865974656209/100000000000000 : ℝ)^3959 := by
    have hnat : (4525677151 : ℕ)^4983*100000000000000^3959 ≤ 36865974656209^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525677151 10000000000 36865974656209 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521034857/1250000000 : ℝ), (3831366199/10000000000 : ℝ), (4525677151/10000000000 : ℝ)] ![(8309944916723/25000000000000 : ℝ), (1868390354259/6250000000000 : ℝ), (36865974656209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521034857/1250000000 : ℝ)|^4983 ≤ (8309944916723/25000000000000 : ℝ)^3959
        have hw : |(521034857/1250000000 : ℝ)|=(521034857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3831366199/10000000000 : ℝ)|^4983 ≤ (1868390354259/6250000000000 : ℝ)^3959
        have hw : |(3831366199/10000000000 : ℝ)|=(3831366199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525677151/10000000000 : ℝ)|^4983 ≤ (36865974656209/100000000000000 : ℝ)^3959
        have hw : |(4525677151/10000000000 : ℝ)|=(4525677151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1572385639/10000000000 : ℝ)*x 0 + (5184543593/10000000000 : ℝ)*x 1 + (1088696879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1572385639/10000000000 : ℝ)^4983 ≤ (9744243500391/100000000000000 : ℝ)^3959 := by
    have hnat : (1572385639 : ℕ)^4983*100000000000000^3959 ≤ 9744243500391^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572385639 10000000000 9744243500391 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184543593/10000000000 : ℝ)^4983 ≤ (8748831853721/20000000000000 : ℝ)^3959 := by
    have hnat : (5184543593 : ℕ)^4983*20000000000000^3959 ≤ 8748831853721^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184543593 10000000000 8748831853721 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088696879/2000000000 : ℝ)^4983 ≤ (11627899303397/25000000000000 : ℝ)^3959 := by
    have hnat : (1088696879 : ℕ)^4983*25000000000000^3959 ≤ 11627899303397^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088696879 2000000000 11627899303397 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1572385639/10000000000 : ℝ), (5184543593/10000000000 : ℝ), (1088696879/2000000000 : ℝ)] ![(9744243500391/100000000000000 : ℝ), (8748831853721/20000000000000 : ℝ), (11627899303397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1572385639/10000000000 : ℝ)|^4983 ≤ (9744243500391/100000000000000 : ℝ)^3959
        have hw : |(-1572385639/10000000000 : ℝ)|=(1572385639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184543593/10000000000 : ℝ)|^4983 ≤ (8748831853721/20000000000000 : ℝ)^3959
        have hw : |(5184543593/10000000000 : ℝ)|=(5184543593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088696879/2000000000 : ℝ)|^4983 ≤ (11627899303397/25000000000000 : ℝ)^3959
        have hw : |(1088696879/2000000000 : ℝ)|=(1088696879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329727973/625000000 : ℝ)*x 0 + (-90421309/625000000 : ℝ)*x 1 + (1360871129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329727973/625000000 : ℝ)^4983 ≤ (2794615708507/6250000000000 : ℝ)^3959 := by
    have hnat : (329727973 : ℕ)^4983*6250000000000^3959 ≤ 2794615708507^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329727973 625000000 2794615708507 6250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90421309/625000000 : ℝ)^4983 ≤ (438727506717/5000000000000 : ℝ)^3959 := by
    have hnat : (90421309 : ℕ)^4983*5000000000000^3959 ≤ 438727506717^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90421309 625000000 438727506717 5000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360871129/2500000000 : ℝ)^4983 ≤ (46511598514881/100000000000000 : ℝ)^3959 := by
    have hnat : (1360871129 : ℕ)^4983*100000000000000^3959 ≤ 46511598514881^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360871129 2500000000 46511598514881 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329727973/625000000 : ℝ), (-90421309/625000000 : ℝ), (1360871129/2500000000 : ℝ)] ![(2794615708507/6250000000000 : ℝ), (438727506717/5000000000000 : ℝ), (46511598514881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329727973/625000000 : ℝ)|^4983 ≤ (2794615708507/6250000000000 : ℝ)^3959
        have hw : |(329727973/625000000 : ℝ)|=(329727973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90421309/625000000 : ℝ)|^4983 ≤ (438727506717/5000000000000 : ℝ)^3959
        have hw : |(-90421309/625000000 : ℝ)|=(90421309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360871129/2500000000 : ℝ)|^4983 ≤ (46511598514881/100000000000000 : ℝ)^3959
        have hw : |(1360871129/2500000000 : ℝ)|=(1360871129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329727981/625000000 : ℝ)*x 0 + (1360871081/2500000000 : ℝ)*x 1 + (-361685259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329727981/625000000 : ℝ)^4983 ≤ (44713852701581/100000000000000 : ℝ)^3959 := by
    have hnat : (329727981 : ℕ)^4983*100000000000000^3959 ≤ 44713852701581^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329727981 625000000 44713852701581 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360871081/2500000000 : ℝ)^4983 ≤ (46511596450019/100000000000000 : ℝ)^3959 := by
    have hnat : (1360871081 : ℕ)^4983*100000000000000^3959 ≤ 46511596450019^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360871081 2500000000 46511596450019 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361685259/2500000000 : ℝ)^4983 ≤ (8774550836647/100000000000000 : ℝ)^3959 := by
    have hnat : (361685259 : ℕ)^4983*100000000000000^3959 ≤ 8774550836647^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361685259 2500000000 8774550836647 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329727981/625000000 : ℝ), (1360871081/2500000000 : ℝ), (-361685259/2500000000 : ℝ)] ![(44713852701581/100000000000000 : ℝ), (46511596450019/100000000000000 : ℝ), (8774550836647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329727981/625000000 : ℝ)|^4983 ≤ (44713852701581/100000000000000 : ℝ)^3959
        have hw : |(329727981/625000000 : ℝ)|=(329727981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360871081/2500000000 : ℝ)|^4983 ≤ (46511596450019/100000000000000 : ℝ)^3959
        have hw : |(1360871081/2500000000 : ℝ)|=(1360871081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-361685259/2500000000 : ℝ)|^4983 ≤ (8774550836647/100000000000000 : ℝ)^3959
        have hw : |(-361685259/2500000000 : ℝ)|=(361685259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s2_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042113163/2500000000 : ℝ)*x 0 + (565035531/1250000000 : ℝ)*x 1 + (119900531/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042113163/2500000000 : ℝ)^4983 ≤ (16620762039063/50000000000000 : ℝ)^3959 := by
    have hnat : (1042113163 : ℕ)^4983*50000000000000^3959 ≤ 16620762039063^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042113163 2500000000 16620762039063 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565035531/1250000000 : ℝ)^4983 ≤ (9202672545223/25000000000000 : ℝ)^3959 := by
    have hnat : (565035531 : ℕ)^4983*25000000000000^3959 ≤ 9202672545223^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565035531 1250000000 9202672545223 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119900531/312500000 : ℝ)^4983 ≤ (598955714629/2000000000000 : ℝ)^3959 := by
    have hnat : (119900531 : ℕ)^4983*2000000000000^3959 ≤ 598955714629^3959*312500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119900531 312500000 598955714629 2000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042113163/2500000000 : ℝ), (565035531/1250000000 : ℝ), (119900531/312500000 : ℝ)] ![(16620762039063/50000000000000 : ℝ), (9202672545223/25000000000000 : ℝ), (598955714629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042113163/2500000000 : ℝ)|^4983 ≤ (16620762039063/50000000000000 : ℝ)^3959
        have hw : |(1042113163/2500000000 : ℝ)|=(1042113163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565035531/1250000000 : ℝ)|^4983 ≤ (9202672545223/25000000000000 : ℝ)^3959
        have hw : |(565035531/1250000000 : ℝ)|=(565035531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119900531/312500000 : ℝ)|^4983 ≤ (598955714629/2000000000000 : ℝ)^3959
        have hw : |(119900531/312500000 : ℝ)|=(119900531/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3423/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3259/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3423/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3423/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9963/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3423/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3423/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9963/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3423/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3423/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9963/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9963/100000 : ℝ) ^ (4979/1024 : ℝ) ≤ (1348551807931681/100000000000000000000 : ℝ) := by
    have hpowers : (9963/100000 : ℝ)^4979 ≤ (1348551807931681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9963 : ℕ)^4979*100000000000000000000^1024 ≤ 1348551807931681^1024*100000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9963 100000 1348551807931681 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9963/100000 : ℝ)) (X := (1348551807931681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3423/20000 : ℝ) ^ (4979/1024 : ℝ) ≤ (9362997955472383/50000000000000000000 : ℝ) := by
    have hpowers : (3423/20000 : ℝ)^4979 ≤ (9362997955472383/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3423 : ℕ)^4979*50000000000000000000^1024 ≤ 9362997955472383^1024*20000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3423 20000 9362997955472383 50000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3423/20000 : ℝ)) (X := (9362997955472383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001348551807931681/50000000000000000000 : ℝ) ≤ (10000055469060419/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50001348551807931681/50000000000000000000 : ℝ)^1024 ≤ (10000055469060419/10000000000000000 : ℝ)^4979 := by
      have hnat : (50001348551807931681 : ℕ)^1024*10000000000000000^4979 ≤ 10000055469060419^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001348551807931681 50000000000000000000 10000055469060419 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000055469060419/10000000000000000 : ℝ)) (X := (50001348551807931681/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020074547718876447/100000000000000000000 : ℝ) ≤ (10000412827839131/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (100020074547718876447/100000000000000000000 : ℝ)^1024 ≤ (10000412827839131/10000000000000000 : ℝ)^4979 := by
      have hnat : (100020074547718876447 : ℕ)^1024*10000000000000000^4979 ≤ 10000412827839131^4979*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020074547718876447 100000000000000000000 10000412827839131 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000412827839131/10000000000000000 : ℝ)) (X := (100020074547718876447/100000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009362997955472383/25000000000000000000 : ℝ) ≤ (10000770186617843/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (25009362997955472383/25000000000000000000 : ℝ)^1024 ≤ (10000770186617843/10000000000000000 : ℝ)^4979 := by
      have hnat : (25009362997955472383 : ℕ)^1024*10000000000000000^4979 ≤ 10000770186617843^4979*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009362997955472383 25000000000000000000 10000770186617843 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000770186617843/10000000000000000 : ℝ)) (X := (25009362997955472383/25000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1348551807931681/100000000000000000000 : ℝ) ≤ ((372464979081747403/372500000000000000 : ℝ)+2*(14889949113/29800000000000 : ℝ)*(9963/100000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (372464979081747403/372500000000000000 : ℝ)+2*(14889949113/29800000000000 : ℝ)*(9963/100000 : ℝ)=(10000055469060419/10000000000000000 : ℝ) by norm_num, show 1+2*(1348551807931681/100000000000000000000 : ℝ)=(50001348551807931681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9362997955472383/50000000000000000000 : ℝ)+(1348551807931681/100000000000000000000 : ℝ) ≤ ((372464979081747403/372500000000000000 : ℝ)+(14889949113/29800000000000 : ℝ)*((3423/20000 : ℝ)+(9963/100000 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (372464979081747403/372500000000000000 : ℝ)+(14889949113/29800000000000 : ℝ)*((3423/20000 : ℝ)+(9963/100000 : ℝ))=(10000412827839131/10000000000000000 : ℝ) by norm_num, show 1+(9362997955472383/50000000000000000000 : ℝ)+(1348551807931681/100000000000000000000 : ℝ)=(100020074547718876447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9362997955472383/50000000000000000000 : ℝ) ≤ ((372464979081747403/372500000000000000 : ℝ)+2*(14889949113/29800000000000 : ℝ)*(3423/20000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (372464979081747403/372500000000000000 : ℝ)+2*(14889949113/29800000000000 : ℝ)*(3423/20000 : ℝ)=(10000770186617843/10000000000000000 : ℝ) by norm_num, show 1+2*(9362997955472383/50000000000000000000 : ℝ)=(25009362997955472383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (372464979081747403/372500000000000000 : ℝ)*(X 1 0+X 2 0)+(14889949113/29800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (9963/100000 : ℝ)) (hi := (3423/20000 : ℝ)) (c := (372464979081747403/372500000000000000 : ℝ)) (alpha := (14889949113/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (372464979081747403/372500000000000000 : ℝ)*(X 0 1+X 2 1)+(14889949113/29800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (9963/100000 : ℝ)) (hi := (3423/20000 : ℝ)) (c := (372464979081747403/372500000000000000 : ℝ)) (alpha := (14889949113/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (372464979081747403/372500000000000000 : ℝ)*(X 0 2+X 1 2)+(14889949113/29800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (9963/100000 : ℝ)) (hi := (3423/20000 : ℝ)) (c := (372464979081747403/372500000000000000 : ℝ)) (alpha := (14889949113/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393079969/2500000000 : ℝ)*X 0 0+(680693701/1250000000 : ℝ)*X 0 1+(1295625069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346046293/10000000000 : ℝ)*X 1 0+(-170772501/1000000000 : ℝ)*X 1 1+(323906279/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66825579/125000000 : ℝ)*X 2 0+(32390627/62500000 : ℝ)*X 2 1+(-853862583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((521034857/1250000000 : ℝ)*X 0 0+(3831366199/10000000000 : ℝ)*X 0 1+(4525677151/10000000000 : ℝ)*X 0 2+(521034857/1250000000 : ℝ)*X 1 0+(3831366199/10000000000 : ℝ)*X 1 1+(4525677151/10000000000 : ℝ)*X 1 2+(521034857/1250000000 : ℝ)*X 2 0+(3831366199/10000000000 : ℝ)*X 2 1+(4525677151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1572385639/10000000000 : ℝ)*X 0 0+(5184543593/10000000000 : ℝ)*X 0 1+(1088696879/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((329727973/625000000 : ℝ)*X 1 0+(-90421309/625000000 : ℝ)*X 1 1+(1360871129/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329727981/625000000 : ℝ)*X 2 0+(1360871081/2500000000 : ℝ)*X 2 1+(-361685259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042113163/2500000000 : ℝ)*X 0 0+(565035531/1250000000 : ℝ)*X 0 1+(119900531/312500000 : ℝ)*X 0 2+(1042113163/2500000000 : ℝ)*X 1 0+(565035531/1250000000 : ℝ)*X 1 1+(119900531/312500000 : ℝ)*X 1 2+(1042113163/2500000000 : ℝ)*X 2 0+(565035531/1250000000 : ℝ)*X 2 1+(119900531/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23116018391626541730600243/2328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765417251/50000000000000 : ℝ)*(base19) + (296269751/20000000000000 : ℝ)*(base23) + (36719651/100000000000000 : ℝ)*(lower2) + (307502223/100000000000000 : ℝ)*(upper3) + (135359571/100000000000000 : ℝ)*(upper5) + (163809450397967/6250000000000 : ℝ)*(major0) + (163809450397967/6250000000000 : ℝ)*(major1) + (163809450397967/6250000000000 : ℝ)*(major2) + (3801590763258713/100000000000000 : ℝ)*(sp0) + (380160844614101/10000000000000 : ℝ)*(sp1) + (950402123906689/25000000000000 : ℝ)*(sp2) + (72014183317413/5000000000000 : ℝ)*(sp3) + (19213716799/100000000000000 : ℝ)*(sp4) + (210961089/2500000000000 : ℝ)*(sp7) + (72014605239591/5000000000000 : ℝ)*(f.failure) + (475201247121939/12500000000000 : ℝ)*(f.sum) + (3099237759427/745000000000000000000000000 : ℝ)*base66 + (23495372839871087/1164062500000000000000000000000 : ℝ)*base68 + (685837956328857/72753906250000000000000000000 : ℝ)*base70 + (19007911682414049/2328125000000000000000000000000 : ℝ)*base72 + (38669659619/5820312500000000000000000 : ℝ)*base74 + (15536723427570299/2328125000000000000000000000000 : ℝ)*base76 + (38428110690382799/2328125000000000000000000000000 : ℝ)*base78 + (19562892285070299/2328125000000000000000000000000 : ℝ)*base80 + (212977887603/186250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8682917/500000000000000000000 : ℝ)*base89 + (8682917/500000000000000000000 : ℝ)*base91 + (8682917/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14645219861369364855651/1490000000000000000000000000 : ℝ) := by norm_num
    linear_combination (707386563/50000000000000 : ℝ)*(base19) + (1652259869/100000000000000 : ℝ)*(base23) + (230297807/100000000000000 : ℝ)*(upper3) + (67599089/100000000000000 : ℝ)*(lower4) + (18797859/10000000000000 : ℝ)*(upper5) + (2662506573163821/100000000000000 : ℝ)*(major0) + (2662506573163821/100000000000000 : ℝ)*(major1) + (2662506573163821/100000000000000 : ℝ)*(major2) + (17666771631/100000000000000 : ℝ)*(sp1) + (18839894159/100000000000000 : ℝ)*(sp2) + (1930942390343609/50000000000000 : ℝ)*(sp4) + (3861865699142461/100000000000000 : ℝ)*(sp5) + (386186428853319/10000000000000 : ℝ)*(sp6) + (365782009501717/25000000000000 : ℝ)*(sp7) + (365782009501717/25000000000000 : ℝ)*(f.failure) + (1930942390343609/50000000000000 : ℝ)*(f.sum) + (4439722706113/1490000000000000000000000000 : ℝ)*base65 + (236248408579469363/37250000000000000000000000000000 : ℝ)*base67 + (17988601313530637/37250000000000000000000000000000 : ℝ)*base70 + (12563082975780637/37250000000000000000000000000000 : ℝ)*base72 + (9019015493473/1490000000000000000000000000 : ℝ)*base73 + (78406667448969363/37250000000000000000000000000000 : ℝ)*base75 + (1729903466030637/37250000000000000000000000000000 : ℝ)*base78 + (76689889895969363/37250000000000000000000000000000 : ℝ)*base79 + (117679484007/1490000000000000000000000000 : ℝ)*base82 + (148879/2500000000000000000000 : ℝ)*base89 + (148879/2500000000000000000000 : ℝ)*base91 + (148879/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1666_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3423/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9963/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1666_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1666_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1666_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1666_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1666_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1666_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

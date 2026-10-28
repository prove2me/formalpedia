-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:31.289979+00:00
-- url     : https://prove2.me/submissions/4f6235ce-d7e7-4bad-a8b6-8c3399e9e5ad

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
theorem support_rectangle_w1225_s9_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106390947/500000000 : ℝ)*x 0 + (673933351/1250000000 : ℝ)*x 1 + (2633513637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106390947/500000000 : ℝ)^4209 ≤ (2587562894351/20000000000000 : ℝ)^3185 := by
    have hnat : (106390947 : ℕ)^4209*20000000000000^3185 ≤ 2587562894351^3185*500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106390947 500000000 2587562894351 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673933351/1250000000 : ℝ)^4209 ≤ (22101351149423/50000000000000 : ℝ)^3185 := by
    have hnat : (673933351 : ℕ)^4209*50000000000000^3185 ≤ 22101351149423^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673933351 1250000000 22101351149423 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633513637/5000000000 : ℝ)^4209 ≤ (21429741607289/50000000000000 : ℝ)^3185 := by
    have hnat : (2633513637 : ℕ)^4209*50000000000000^3185 ≤ 21429741607289^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633513637 5000000000 21429741607289 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106390947/500000000 : ℝ), (673933351/1250000000 : ℝ), (2633513637/5000000000 : ℝ)] ![(2587562894351/20000000000000 : ℝ), (22101351149423/50000000000000 : ℝ), (21429741607289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106390947/500000000 : ℝ)|^4209 ≤ (2587562894351/20000000000000 : ℝ)^3185
        have hw : |(-106390947/500000000 : ℝ)|=(106390947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673933351/1250000000 : ℝ)|^4209 ≤ (22101351149423/50000000000000 : ℝ)^3185
        have hw : |(673933351/1250000000 : ℝ)|=(673933351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633513637/5000000000 : ℝ)|^4209 ≤ (21429741607289/50000000000000 : ℝ)^3185
        have hw : |(2633513637/5000000000 : ℝ)|=(2633513637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344384731/10000000000 : ℝ)*x 0 + (-2190916433/10000000000 : ℝ)*x 1 + (1053405371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344384731/10000000000 : ℝ)^4209 ≤ (43693306123153/100000000000000 : ℝ)^3185 := by
    have hnat : (5344384731 : ℕ)^4209*100000000000000^3185 ≤ 43693306123153^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344384731 10000000000 43693306123153 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190916433/10000000000 : ℝ)^4209 ≤ (1680901894119/12500000000000 : ℝ)^3185 := by
    have hnat : (2190916433 : ℕ)^4209*12500000000000^3185 ≤ 1680901894119^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190916433 10000000000 1680901894119 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053405371/2000000000 : ℝ)^4209 ≤ (42859478708851/100000000000000 : ℝ)^3185 := by
    have hnat : (1053405371 : ℕ)^4209*100000000000000^3185 ≤ 42859478708851^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053405371 2000000000 42859478708851 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344384731/10000000000 : ℝ), (-2190916433/10000000000 : ℝ), (1053405371/2000000000 : ℝ)] ![(43693306123153/100000000000000 : ℝ), (1680901894119/12500000000000 : ℝ), (42859478708851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344384731/10000000000 : ℝ)|^4209 ≤ (43693306123153/100000000000000 : ℝ)^3185
        have hw : |(5344384731/10000000000 : ℝ)|=(5344384731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190916433/10000000000 : ℝ)|^4209 ≤ (1680901894119/12500000000000 : ℝ)^3185
        have hw : |(-2190916433/10000000000 : ℝ)|=(2190916433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053405371/2000000000 : ℝ)|^4209 ≤ (42859478708851/100000000000000 : ℝ)^3185
        have hw : |(1053405371/2000000000 : ℝ)|=(1053405371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344384871/10000000000 : ℝ)*x 0 + (263351347/500000000 : ℝ)*x 1 + (-1095458067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344384871/10000000000 : ℝ)^4209 ≤ (1092332690893/2500000000000 : ℝ)^3185 := by
    have hnat : (5344384871 : ℕ)^4209*2500000000000^3185 ≤ 1092332690893^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344384871 10000000000 1092332690893 2500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263351347/500000000 : ℝ)^4209 ≤ (428594796229/1000000000000 : ℝ)^3185 := by
    have hnat : (263351347 : ℕ)^4209*1000000000000^3185 ≤ 428594796229^3185*500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263351347 500000000 428594796229 1000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095458067/5000000000 : ℝ)^4209 ≤ (6723606363877/50000000000000 : ℝ)^3185 := by
    have hnat : (1095458067 : ℕ)^4209*50000000000000^3185 ≤ 6723606363877^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095458067 5000000000 6723606363877 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344384871/10000000000 : ℝ), (263351347/500000000 : ℝ), (-1095458067/5000000000 : ℝ)] ![(1092332690893/2500000000000 : ℝ), (428594796229/1000000000000 : ℝ), (6723606363877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344384871/10000000000 : ℝ)|^4209 ≤ (1092332690893/2500000000000 : ℝ)^3185
        have hw : |(5344384871/10000000000 : ℝ)|=(5344384871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263351347/500000000 : ℝ)|^4209 ≤ (428594796229/1000000000000 : ℝ)^3185
        have hw : |(263351347/500000000 : ℝ)|=(263351347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095458067/5000000000 : ℝ)|^4209 ≤ (6723606363877/50000000000000 : ℝ)^3185
        have hw : |(-1095458067/5000000000 : ℝ)|=(1095458067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088278019/2500000000 : ℝ)*x 0 + (4229083251/10000000000 : ℝ)*x 1 + (280043129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088278019/2500000000 : ℝ)^4209 ≤ (1041169578421/3125000000000 : ℝ)^3185 := by
    have hnat : (1088278019 : ℕ)^4209*3125000000000^3185 ≤ 1041169578421^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088278019 2500000000 1041169578421 3125000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229083251/10000000000 : ℝ)^4209 ≤ (32068729806111/100000000000000 : ℝ)^3185 := by
    have hnat : (4229083251 : ℕ)^4209*100000000000000^3185 ≤ 32068729806111^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229083251 10000000000 32068729806111 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280043129/625000000 : ℝ)^4209 ≤ (17306921831727/50000000000000 : ℝ)^3185 := by
    have hnat : (280043129 : ℕ)^4209*50000000000000^3185 ≤ 17306921831727^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280043129 625000000 17306921831727 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088278019/2500000000 : ℝ), (4229083251/10000000000 : ℝ), (280043129/625000000 : ℝ)] ![(1041169578421/3125000000000 : ℝ), (32068729806111/100000000000000 : ℝ), (17306921831727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088278019/2500000000 : ℝ)|^4209 ≤ (1041169578421/3125000000000 : ℝ)^3185
        have hw : |(1088278019/2500000000 : ℝ)|=(1088278019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229083251/10000000000 : ℝ)|^4209 ≤ (32068729806111/100000000000000 : ℝ)^3185
        have hw : |(4229083251/10000000000 : ℝ)|=(4229083251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280043129/625000000 : ℝ)|^4209 ≤ (17306921831727/50000000000000 : ℝ)^3185
        have hw : |(280043129/625000000 : ℝ)|=(280043129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127823403/10000000000 : ℝ)*x 0 + (52673403/100000000 : ℝ)*x 1 + (5391152807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127823403/10000000000 : ℝ)^4209 ≤ (6468925166393/50000000000000 : ℝ)^3185 := by
    have hnat : (2127823403 : ℕ)^4209*50000000000000^3185 ≤ 6468925166393^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127823403 10000000000 6468925166393 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52673403/100000000 : ℝ)^4209 ≤ (10715712344919/25000000000000 : ℝ)^3185 := by
    have hnat : (52673403 : ℕ)^4209*25000000000000^3185 ≤ 10715712344919^3185*100000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52673403 100000000 10715712344919 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391152807/10000000000 : ℝ)^4209 ≤ (22099650133641/50000000000000 : ℝ)^3185 := by
    have hnat : (5391152807 : ℕ)^4209*50000000000000^3185 ≤ 22099650133641^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391152807 10000000000 22099650133641 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127823403/10000000000 : ℝ), (52673403/100000000 : ℝ), (5391152807/10000000000 : ℝ)] ![(6468925166393/50000000000000 : ℝ), (10715712344919/25000000000000 : ℝ), (22099650133641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127823403/10000000000 : ℝ)|^4209 ≤ (6468925166393/50000000000000 : ℝ)^3185
        have hw : |(-2127823403/10000000000 : ℝ)|=(2127823403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52673403/100000000 : ℝ)|^4209 ≤ (10715712344919/25000000000000 : ℝ)^3185
        have hw : |(52673403/100000000 : ℝ)|=(52673403/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391152807/10000000000 : ℝ)|^4209 ≤ (22099650133641/50000000000000 : ℝ)^3185
        have hw : |(5391152807/10000000000 : ℝ)|=(5391152807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062534009/2000000000 : ℝ)*x 0 + (-2066791093/10000000000 : ℝ)*x 1 + (5391152169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062534009/2000000000 : ℝ)^4209 ≤ (43350986299813/100000000000000 : ℝ)^3185 := by
    have hnat : (1062534009 : ℕ)^4209*100000000000000^3185 ≤ 43350986299813^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062534009 2000000000 43350986299813 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066791093/10000000000 : ℝ)^4209 ≤ (2489944063483/20000000000000 : ℝ)^3185 := by
    have hnat : (2066791093 : ℕ)^4209*20000000000000^3185 ≤ 2489944063483^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066791093 10000000000 2489944063483 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391152169/10000000000 : ℝ)^4209 ≤ (44199293354961/100000000000000 : ℝ)^3185 := by
    have hnat : (5391152169 : ℕ)^4209*100000000000000^3185 ≤ 44199293354961^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391152169 10000000000 44199293354961 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062534009/2000000000 : ℝ), (-2066791093/10000000000 : ℝ), (5391152169/10000000000 : ℝ)] ![(43350986299813/100000000000000 : ℝ), (2489944063483/20000000000000 : ℝ), (44199293354961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062534009/2000000000 : ℝ)|^4209 ≤ (43350986299813/100000000000000 : ℝ)^3185
        have hw : |(1062534009/2000000000 : ℝ)|=(1062534009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066791093/10000000000 : ℝ)|^4209 ≤ (2489944063483/20000000000000 : ℝ)^3185
        have hw : |(-2066791093/10000000000 : ℝ)|=(2066791093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391152169/10000000000 : ℝ)|^4209 ≤ (44199293354961/100000000000000 : ℝ)^3185
        have hw : |(5391152169/10000000000 : ℝ)|=(5391152169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s9_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353121857/10000000000 : ℝ)*x 0 + (4480056077/10000000000 : ℝ)*x 1 + (2114859613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353121857/10000000000 : ℝ)^4209 ≤ (16658762719337/50000000000000 : ℝ)^3185 := by
    have hnat : (4353121857 : ℕ)^4209*50000000000000^3185 ≤ 16658762719337^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353121857 10000000000 16658762719337 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480056077/10000000000 : ℝ)^4209 ≤ (8651842892101/25000000000000 : ℝ)^3185 := by
    have hnat : (4480056077 : ℕ)^4209*25000000000000^3185 ≤ 8651842892101^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480056077 10000000000 8651842892101 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114859613/5000000000 : ℝ)^4209 ≤ (16037551488439/50000000000000 : ℝ)^3185 := by
    have hnat : (2114859613 : ℕ)^4209*50000000000000^3185 ≤ 16037551488439^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114859613 5000000000 16037551488439 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353121857/10000000000 : ℝ), (4480056077/10000000000 : ℝ), (2114859613/5000000000 : ℝ)] ![(16658762719337/50000000000000 : ℝ), (8651842892101/25000000000000 : ℝ), (16037551488439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353121857/10000000000 : ℝ)|^4209 ≤ (16658762719337/50000000000000 : ℝ)^3185
        have hw : |(4353121857/10000000000 : ℝ)|=(4353121857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480056077/10000000000 : ℝ)|^4209 ≤ (8651842892101/25000000000000 : ℝ)^3185
        have hw : |(4480056077/10000000000 : ℝ)|=(4480056077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114859613/5000000000 : ℝ)|^4209 ≤ (16037551488439/50000000000000 : ℝ)^3185
        have hw : |(2114859613/5000000000 : ℝ)|=(2114859613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11459/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5729/50000 : ℝ) ^ (8417/2048 : ℝ) ≤ (1698149384735909/12500000000000000000 : ℝ) := by
    have hpowers : (5729/50000 : ℝ)^8417 ≤ (1698149384735909/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5729 : ℕ)^8417*12500000000000000000^2048 ≤ 1698149384735909^2048*50000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5729 50000 1698149384735909 12500000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5729/50000 : ℝ)) (X := (1698149384735909/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (8417/2048 : ℝ) ≤ (31825396159221831/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^8417 ≤ (31825396159221831/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8417*100000000000000000000^2048 ≤ 31825396159221831^2048*20000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 31825396159221831 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (31825396159221831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251698149384735909/6250000000000000000 : ℝ) ≤ (10000661034095551/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (6251698149384735909/6250000000000000000 : ℝ)^2048 ≤ (10000661034095551/10000000000000000 : ℝ)^8417 := by
      have hnat : (6251698149384735909 : ℕ)^2048*10000000000000000^8417 ≤ 10000661034095551^8417*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251698149384735909 6250000000000000000 10000661034095551 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000661034095551/10000000000000000 : ℝ)) (X := (6251698149384735909/6250000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045410591237109103/100000000000000000000 : ℝ) ≤ (500055236376909/500000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100045410591237109103/100000000000000000000 : ℝ)^2048 ≤ (500055236376909/500000000000000 : ℝ)^8417 := by
      have hnat : (100045410591237109103 : ℕ)^2048*500000000000000^8417 ≤ 500055236376909^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045410591237109103 100000000000000000000 500055236376909 500000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500055236376909/500000000000000 : ℝ)) (X := (100045410591237109103/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031825396159221831/50000000000000000000 : ℝ) ≤ (10001548420980809/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50031825396159221831/50000000000000000000 : ℝ)^2048 ≤ (10001548420980809/10000000000000000 : ℝ)^8417 := by
      have hnat : (50031825396159221831 : ℕ)^2048*10000000000000000^8417 ≤ 10001548420980809^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031825396159221831 50000000000000000000 10001548420980809 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001548420980809/10000000000000000 : ℝ)) (X := (50031825396159221831/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1698149384735909/12500000000000000000 : ℝ) ≤ ((26361575467978681823/26370000000000000000 : ℝ)+2*(443693442629/263700000000000 : ℝ)*(5729/50000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (26361575467978681823/26370000000000000000 : ℝ)+2*(443693442629/263700000000000 : ℝ)*(5729/50000 : ℝ)=(10000661034095551/10000000000000000 : ℝ) by norm_num, show 1+2*(1698149384735909/12500000000000000000 : ℝ)=(6251698149384735909/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31825396159221831/100000000000000000000 : ℝ)+(1698149384735909/12500000000000000000 : ℝ) ≤ ((26361575467978681823/26370000000000000000 : ℝ)+(443693442629/263700000000000 : ℝ)*((2819/20000 : ℝ)+(5729/50000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (26361575467978681823/26370000000000000000 : ℝ)+(443693442629/263700000000000 : ℝ)*((2819/20000 : ℝ)+(5729/50000 : ℝ))=(500055236376909/500000000000000 : ℝ) by norm_num, show 1+(31825396159221831/100000000000000000000 : ℝ)+(1698149384735909/12500000000000000000 : ℝ)=(100045410591237109103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31825396159221831/100000000000000000000 : ℝ) ≤ ((26361575467978681823/26370000000000000000 : ℝ)+2*(443693442629/263700000000000 : ℝ)*(2819/20000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (26361575467978681823/26370000000000000000 : ℝ)+2*(443693442629/263700000000000 : ℝ)*(2819/20000 : ℝ)=(10001548420980809/10000000000000000 : ℝ) by norm_num, show 1+2*(31825396159221831/100000000000000000000 : ℝ)=(50031825396159221831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26361575467978681823/26370000000000000000 : ℝ)*(X 1 0+X 2 0)+(443693442629/263700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (26361575467978681823/26370000000000000000 : ℝ)) (alpha := (443693442629/263700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26361575467978681823/26370000000000000000 : ℝ)*(X 0 1+X 2 1)+(443693442629/263700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (26361575467978681823/26370000000000000000 : ℝ)) (alpha := (443693442629/263700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26361575467978681823/26370000000000000000 : ℝ)*(X 0 2+X 1 2)+(443693442629/263700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (26361575467978681823/26370000000000000000 : ℝ)) (alpha := (443693442629/263700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106390947/500000000 : ℝ)*X 0 0+(673933351/1250000000 : ℝ)*X 0 1+(2633513637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344384731/10000000000 : ℝ)*X 1 0+(-2190916433/10000000000 : ℝ)*X 1 1+(1053405371/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344384871/10000000000 : ℝ)*X 2 0+(263351347/500000000 : ℝ)*X 2 1+(-1095458067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088278019/2500000000 : ℝ)*X 0 0+(4229083251/10000000000 : ℝ)*X 0 1+(280043129/625000000 : ℝ)*X 0 2+(1088278019/2500000000 : ℝ)*X 1 0+(4229083251/10000000000 : ℝ)*X 1 1+(280043129/625000000 : ℝ)*X 1 2+(1088278019/2500000000 : ℝ)*X 2 0+(4229083251/10000000000 : ℝ)*X 2 1+(280043129/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2127823403/10000000000 : ℝ)*X 0 0+(52673403/100000000 : ℝ)*X 0 1+(5391152807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062534009/2000000000 : ℝ)*X 1 0+(-2066791093/10000000000 : ℝ)*X 1 1+(5391152169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4353121857/10000000000 : ℝ)*X 0 0+(4480056077/10000000000 : ℝ)*X 0 1+(2114859613/5000000000 : ℝ)*X 0 2+(4353121857/10000000000 : ℝ)*X 1 0+(4480056077/10000000000 : ℝ)*X 1 1+(2114859613/5000000000 : ℝ)*X 1 2+(4353121857/10000000000 : ℝ)*X 2 0+(4480056077/10000000000 : ℝ)*X 2 1+(2114859613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19174744435477433358546919/439500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198412263/20000000000000 : ℝ)*(base19) + (109252899/10000000000000 : ℝ)*(base23) + (1577289/20000000000000 : ℝ)*(lower3) + (108176549/100000000000000 : ℝ)*(upper4) + (6005284559763847/100000000000000 : ℝ)*(major0) + (6005284559763847/100000000000000 : ℝ)*(major1) + (6005284559763847/100000000000000 : ℝ)*(major2) + (1607210259143477/20000000000000 : ℝ)*(sp0) + (2009015410028389/25000000000000 : ℝ)*(sp1) + (4018038552536367/50000000000000 : ℝ)*(sp2) + (1987235891659737/50000000000000 : ℝ)*(sp3) + (13450942169/50000000000000 : ℝ)*(sp4) + (3891356713/25000000000000 : ℝ)*(sp5) + (19137152201/100000000000000 : ℝ)*(sp6) + (158979636818867/4000000000000 : ℝ)*(f.failure) + (2009019549400431/25000000000000 : ℝ)*(f.sum) + (1980278449217/3296250000000000000000000000 : ℝ)*base65 + (21299392040560753081/2637000000000000000000000000000000 : ℝ)*base67 + (8071867546858246919/2637000000000000000000000000000000 : ℝ)*base70 + (101957566497298753081/2637000000000000000000000000000000 : ℝ)*base71 + (174840540419/103007812500000000000000000 : ℝ)*base74 + (36243447783202246919/2637000000000000000000000000000000 : ℝ)*base76 + (31041660213592753081/2637000000000000000000000000000000 : ℝ)*base77 + (1851054299800753081/2637000000000000000000000000000000 : ℝ)*base79 + (54378554939347/13185000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5241/100000000000000000000 : ℝ)*base89 + (5241/100000000000000000000 : ℝ)*base91 + (5241/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1225_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_box_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003593717/10000000000 : ℝ)*x 0 + (1343774221/2500000000 : ℝ)*x 1 + (107501951/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003593717/10000000000 : ℝ)^4209 ≤ (5974568423721/50000000000000 : ℝ)^3185 := by
    have hnat : (2003593717 : ℕ)^4209*50000000000000^3185 ≤ 5974568423721^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003593717 10000000000 5974568423721 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343774221/2500000000 : ℝ)^4209 ≤ (8805085592823/20000000000000 : ℝ)^3185 := by
    have hnat : (1343774221 : ℕ)^4209*20000000000000^3185 ≤ 8805085592823^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343774221 2500000000 8805085592823 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107501951/200000000 : ℝ)^4209 ≤ (44025435172883/100000000000000 : ℝ)^3185 := by
    have hnat : (107501951 : ℕ)^4209*100000000000000^3185 ≤ 44025435172883^3185*200000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107501951 200000000 44025435172883 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003593717/10000000000 : ℝ), (1343774221/2500000000 : ℝ), (107501951/200000000 : ℝ)] ![(5974568423721/50000000000000 : ℝ), (8805085592823/20000000000000 : ℝ), (44025435172883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003593717/10000000000 : ℝ)|^4209 ≤ (5974568423721/50000000000000 : ℝ)^3185
        have hw : |(-2003593717/10000000000 : ℝ)|=(2003593717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343774221/2500000000 : ℝ)|^4209 ≤ (8805085592823/20000000000000 : ℝ)^3185
        have hw : |(1343774221/2500000000 : ℝ)|=(1343774221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107501951/200000000 : ℝ)|^4209 ≤ (44025435172883/100000000000000 : ℝ)^3185
        have hw : |(107501951/200000000 : ℝ)|=(107501951/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059334963/2000000000 : ℝ)*x 0 + (-422028557/2000000000 : ℝ)*x 1 + (5375097969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059334963/2000000000 : ℝ)^4209 ≤ (43178586908589/100000000000000 : ℝ)^3185 := by
    have hnat : (1059334963 : ℕ)^4209*100000000000000^3185 ≤ 43178586908589^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059334963 2000000000 43178586908589 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422028557/2000000000 : ℝ)^4209 ≤ (12795973369787/100000000000000 : ℝ)^3185 := by
    have hnat : (422028557 : ℕ)^4209*100000000000000^3185 ≤ 12795973369787^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422028557 2000000000 12795973369787 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375097969/10000000000 : ℝ)^4209 ≤ (44025439708129/100000000000000 : ℝ)^3185 := by
    have hnat : (5375097969 : ℕ)^4209*100000000000000^3185 ≤ 44025439708129^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375097969 10000000000 44025439708129 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059334963/2000000000 : ℝ), (-422028557/2000000000 : ℝ), (5375097969/10000000000 : ℝ)] ![(43178586908589/100000000000000 : ℝ), (12795973369787/100000000000000 : ℝ), (44025439708129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059334963/2000000000 : ℝ)|^4209 ≤ (43178586908589/100000000000000 : ℝ)^3185
        have hw : |(1059334963/2000000000 : ℝ)|=(1059334963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422028557/2000000000 : ℝ)|^4209 ≤ (12795973369787/100000000000000 : ℝ)^3185
        have hw : |(-422028557/2000000000 : ℝ)|=(422028557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375097969/10000000000 : ℝ)|^4209 ≤ (44025439708129/100000000000000 : ℝ)^3185
        have hw : |(5375097969/10000000000 : ℝ)|=(5375097969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2648337693/5000000000 : ℝ)*x 0 + (5375097353/10000000000 : ℝ)*x 1 + (-2110142849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648337693/5000000000 : ℝ)^4209 ≤ (43178593059943/100000000000000 : ℝ)^3185 := by
    have hnat : (2648337693 : ℕ)^4209*100000000000000^3185 ≤ 43178593059943^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648337693 5000000000 43178593059943 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375097353/10000000000 : ℝ)^4209 ≤ (550317913007/1250000000000 : ℝ)^3185 := by
    have hnat : (5375097353 : ℕ)^4209*1250000000000^3185 ≤ 550317913007^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375097353 10000000000 550317913007 1250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110142849/10000000000 : ℝ)^4209 ≤ (12795973882661/100000000000000 : ℝ)^3185 := by
    have hnat : (2110142849 : ℕ)^4209*100000000000000^3185 ≤ 12795973882661^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110142849 10000000000 12795973882661 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648337693/5000000000 : ℝ), (5375097353/10000000000 : ℝ), (-2110142849/10000000000 : ℝ)] ![(43178593059943/100000000000000 : ℝ), (550317913007/1250000000000 : ℝ), (12795973882661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648337693/5000000000 : ℝ)|^4209 ≤ (43178593059943/100000000000000 : ℝ)^3185
        have hw : |(2648337693/5000000000 : ℝ)|=(2648337693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375097353/10000000000 : ℝ)|^4209 ≤ (550317913007/1250000000000 : ℝ)^3185
        have hw : |(5375097353/10000000000 : ℝ)|=(5375097353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110142849/10000000000 : ℝ)|^4209 ≤ (12795973882661/100000000000000 : ℝ)^3185
        have hw : |(-2110142849/10000000000 : ℝ)|=(2110142849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4459804199/10000000000 : ℝ)*x 0 + (1075454669/2500000000 : ℝ)*x 1 + (4301818517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4459804199/10000000000 : ℝ)^4209 ≤ (3440078412241/10000000000000 : ℝ)^3185 := by
    have hnat : (4459804199 : ℕ)^4209*10000000000000^3185 ≤ 3440078412241^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4459804199 10000000000 3440078412241 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075454669/2500000000 : ℝ)^4209 ≤ (1024987772923/3125000000000 : ℝ)^3185 := by
    have hnat : (1075454669 : ℕ)^4209*3125000000000^3185 ≤ 1024987772923^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075454669 2500000000 1024987772923 3125000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301818517/10000000000 : ℝ)^4209 ≤ (32799607131459/100000000000000 : ℝ)^3185 := by
    have hnat : (4301818517 : ℕ)^4209*100000000000000^3185 ≤ 32799607131459^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301818517 10000000000 32799607131459 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4459804199/10000000000 : ℝ), (1075454669/2500000000 : ℝ), (4301818517/10000000000 : ℝ)] ![(3440078412241/10000000000000 : ℝ), (1024987772923/3125000000000 : ℝ), (32799607131459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4459804199/10000000000 : ℝ)|^4209 ≤ (3440078412241/10000000000000 : ℝ)^3185
        have hw : |(4459804199/10000000000 : ℝ)|=(4459804199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075454669/2500000000 : ℝ)|^4209 ≤ (1024987772923/3125000000000 : ℝ)^3185
        have hw : |(1075454669/2500000000 : ℝ)|=(1075454669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301818517/10000000000 : ℝ)|^4209 ≤ (32799607131459/100000000000000 : ℝ)^3185
        have hw : |(4301818517/10000000000 : ℝ)|=(4301818517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-563354867/2500000000 : ℝ)*x 0 + (1320527599/2500000000 : ℝ)*x 1 + (2641055271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563354867/2500000000 : ℝ)^4209 ≤ (6978244646673/50000000000000 : ℝ)^3185 := by
    have hnat : (563354867 : ℕ)^4209*50000000000000^3185 ≤ 6978244646673^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563354867 2500000000 6978244646673 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320527599/2500000000 : ℝ)^4209 ≤ (4302175456379/10000000000000 : ℝ)^3185 := by
    have hnat : (1320527599 : ℕ)^4209*10000000000000^3185 ≤ 4302175456379^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320527599 2500000000 4302175456379 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641055271/5000000000 : ℝ)^4209 ≤ (43021756135249/100000000000000 : ℝ)^3185 := by
    have hnat : (2641055271 : ℕ)^4209*100000000000000^3185 ≤ 43021756135249^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641055271 5000000000 43021756135249 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563354867/2500000000 : ℝ), (1320527599/2500000000 : ℝ), (2641055271/5000000000 : ℝ)] ![(6978244646673/50000000000000 : ℝ), (4302175456379/10000000000000 : ℝ), (43021756135249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563354867/2500000000 : ℝ)|^4209 ≤ (6978244646673/50000000000000 : ℝ)^3185
        have hw : |(-563354867/2500000000 : ℝ)|=(563354867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320527599/2500000000 : ℝ)|^4209 ≤ (4302175456379/10000000000000 : ℝ)^3185
        have hw : |(1320527599/2500000000 : ℝ)|=(1320527599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641055271/5000000000 : ℝ)|^4209 ≤ (43021756135249/100000000000000 : ℝ)^3185
        have hw : |(2641055271/5000000000 : ℝ)|=(2641055271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681124431/5000000000 : ℝ)*x 0 + (-134184923/625000000 : ℝ)*x 1 + (1056422121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681124431/5000000000 : ℝ)^4209 ≤ (43886414760603/100000000000000 : ℝ)^3185 := by
    have hnat : (2681124431 : ℕ)^4209*100000000000000^3185 ≤ 43886414760603^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681124431 5000000000 43886414760603 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134184923/625000000 : ℝ)^4209 ≤ (13091828410447/100000000000000 : ℝ)^3185 := by
    have hnat : (134184923 : ℕ)^4209*100000000000000^3185 ≤ 13091828410447^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134184923 625000000 13091828410447 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056422121/2000000000 : ℝ)^4209 ≤ (1344429900417/3125000000000 : ℝ)^3185 := by
    have hnat : (1056422121 : ℕ)^4209*3125000000000^3185 ≤ 1344429900417^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056422121 2000000000 1344429900417 3125000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681124431/5000000000 : ℝ), (-134184923/625000000 : ℝ), (1056422121/2000000000 : ℝ)] ![(43886414760603/100000000000000 : ℝ), (13091828410447/100000000000000 : ℝ), (1344429900417/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681124431/5000000000 : ℝ)|^4209 ≤ (43886414760603/100000000000000 : ℝ)^3185
        have hw : |(2681124431/5000000000 : ℝ)|=(2681124431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134184923/625000000 : ℝ)|^4209 ≤ (13091828410447/100000000000000 : ℝ)^3185
        have hw : |(-134184923/625000000 : ℝ)|=(134184923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056422121/2000000000 : ℝ)|^4209 ≤ (1344429900417/3125000000000 : ℝ)^3185
        have hw : |(1056422121/2000000000 : ℝ)|=(1056422121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362249133/10000000000 : ℝ)*x 0 + (1320527569/2500000000 : ℝ)*x 1 + (-429391769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362249133/10000000000 : ℝ)^4209 ≤ (10971604422911/25000000000000 : ℝ)^3185 := by
    have hnat : (5362249133 : ℕ)^4209*25000000000000^3185 ≤ 10971604422911^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362249133 10000000000 10971604422911 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320527569/2500000000 : ℝ)^4209 ≤ (2151087663609/5000000000000 : ℝ)^3185 := by
    have hnat : (1320527569 : ℕ)^4209*5000000000000^3185 ≤ 2151087663609^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320527569 2500000000 2151087663609 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429391769/2000000000 : ℝ)^4209 ≤ (654591451547/5000000000000 : ℝ)^3185 := by
    have hnat : (429391769 : ℕ)^4209*5000000000000^3185 ≤ 654591451547^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429391769 2000000000 654591451547 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362249133/10000000000 : ℝ), (1320527569/2500000000 : ℝ), (-429391769/2000000000 : ℝ)] ![(10971604422911/25000000000000 : ℝ), (2151087663609/5000000000000 : ℝ), (654591451547/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362249133/10000000000 : ℝ)|^4209 ≤ (10971604422911/25000000000000 : ℝ)^3185
        have hw : |(5362249133/10000000000 : ℝ)|=(5362249133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320527569/2500000000 : ℝ)|^4209 ≤ (2151087663609/5000000000000 : ℝ)^3185
        have hw : |(1320527569/2500000000 : ℝ)|=(1320527569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429391769/2000000000 : ℝ)|^4209 ≤ (654591451547/5000000000000 : ℝ)^3185
        have hw : |(-429391769/2000000000 : ℝ)|=(429391769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265376573/625000000 : ℝ)*x 0 + (881737573/2000000000 : ℝ)*x 1 + (4408687929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265376573/625000000 : ℝ)^4209 ≤ (32238611624081/100000000000000 : ℝ)^3185 := by
    have hnat : (265376573 : ℕ)^4209*100000000000000^3185 ≤ 32238611624081^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265376573 625000000 32238611624081 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881737573/2000000000 : ℝ)^4209 ≤ (21175433657/62500000000 : ℝ)^3185 := by
    have hnat : (881737573 : ℕ)^4209*62500000000^3185 ≤ 21175433657^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881737573 2000000000 21175433657 62500000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408687929/10000000000 : ℝ)^4209 ≤ (33880694501169/100000000000000 : ℝ)^3185 := by
    have hnat : (4408687929 : ℕ)^4209*100000000000000^3185 ≤ 33880694501169^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408687929 10000000000 33880694501169 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265376573/625000000 : ℝ), (881737573/2000000000 : ℝ), (4408687929/10000000000 : ℝ)] ![(32238611624081/100000000000000 : ℝ), (21175433657/62500000000 : ℝ), (33880694501169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265376573/625000000 : ℝ)|^4209 ≤ (32238611624081/100000000000000 : ℝ)^3185
        have hw : |(265376573/625000000 : ℝ)|=(265376573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881737573/2000000000 : ℝ)|^4209 ≤ (21175433657/62500000000 : ℝ)^3185
        have hw : |(881737573/2000000000 : ℝ)|=(881737573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4408687929/10000000000 : ℝ)|^4209 ≤ (33880694501169/100000000000000 : ℝ)^3185
        have hw : |(4408687929/10000000000 : ℝ)|=(4408687929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_8 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1375679/6250000 : ℝ)*x 0 + (5218715021/10000000000 : ℝ)*x 1 + (673088757/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375679/6250000 : ℝ)^4209 ≤ (676488277659/5000000000000 : ℝ)^3185 := by
    have hnat : (1375679 : ℕ)^4209*5000000000000^3185 ≤ 676488277659^3185*6250000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375679 6250000 676488277659 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218715021/10000000000 : ℝ)^4209 ≤ (10585180960449/25000000000000 : ℝ)^3185 := by
    have hnat : (5218715021 : ℕ)^4209*25000000000000^3185 ≤ 10585180960449^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218715021 10000000000 10585180960449 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673088757/1250000000 : ℝ)^4209 ≤ (44129510600387/100000000000000 : ℝ)^3185 := by
    have hnat : (673088757 : ℕ)^4209*100000000000000^3185 ≤ 44129510600387^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673088757 1250000000 44129510600387 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1375679/6250000 : ℝ), (5218715021/10000000000 : ℝ), (673088757/1250000000 : ℝ)] ![(676488277659/5000000000000 : ℝ), (10585180960449/25000000000000 : ℝ), (44129510600387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1375679/6250000 : ℝ)|^4209 ≤ (676488277659/5000000000000 : ℝ)^3185
        have hw : |(-1375679/6250000 : ℝ)|=(1375679/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218715021/10000000000 : ℝ)|^4209 ≤ (10585180960449/25000000000000 : ℝ)^3185
        have hw : |(5218715021/10000000000 : ℝ)|=(5218715021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673088757/1250000000 : ℝ)|^4209 ≤ (44129510600387/100000000000000 : ℝ)^3185
        have hw : |(673088757/1250000000 : ℝ)|=(673088757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_9 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289893299/10000000000 : ℝ)*x 0 + (-2106269677/10000000000 : ℝ)*x 1 + (5384710019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289893299/10000000000 : ℝ)^4209 ≤ (43105545023417/100000000000000 : ℝ)^3185 := by
    have hnat : (5289893299 : ℕ)^4209*100000000000000^3185 ≤ 43105545023417^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289893299 10000000000 43105545023417 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106269677/10000000000 : ℝ)^4209 ≤ (12764944756543/100000000000000 : ℝ)^3185 := by
    have hnat : (2106269677 : ℕ)^4209*100000000000000^3185 ≤ 12764944756543^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106269677 10000000000 12764944756543 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384710019/10000000000 : ℝ)^4209 ≤ (4412951019967/10000000000000 : ℝ)^3185 := by
    have hnat : (5384710019 : ℕ)^4209*10000000000000^3185 ≤ 4412951019967^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384710019 10000000000 4412951019967 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289893299/10000000000 : ℝ), (-2106269677/10000000000 : ℝ), (5384710019/10000000000 : ℝ)] ![(43105545023417/100000000000000 : ℝ), (12764944756543/100000000000000 : ℝ), (4412951019967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289893299/10000000000 : ℝ)|^4209 ≤ (43105545023417/100000000000000 : ℝ)^3185
        have hw : |(5289893299/10000000000 : ℝ)|=(5289893299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106269677/10000000000 : ℝ)|^4209 ≤ (12764944756543/100000000000000 : ℝ)^3185
        have hw : |(-2106269677/10000000000 : ℝ)|=(2106269677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384710019/10000000000 : ℝ)|^4209 ≤ (4412951019967/10000000000000 : ℝ)^3185
        have hw : |(5384710019/10000000000 : ℝ)|=(5384710019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_10 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52898933/100000000 : ℝ)*x 0 + (2692355039/5000000000 : ℝ)*x 1 + (-2106269597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52898933/100000000 : ℝ)^4209 ≤ (8621109006837/20000000000000 : ℝ)^3185 := by
    have hnat : (52898933 : ℕ)^4209*20000000000000^3185 ≤ 8621109006837^3185*100000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52898933 100000000 8621109006837 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692355039/5000000000 : ℝ)^4209 ≤ (11032377709663/25000000000000 : ℝ)^3185 := by
    have hnat : (2692355039 : ℕ)^4209*25000000000000^3185 ≤ 11032377709663^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692355039 5000000000 11032377709663 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106269597/10000000000 : ℝ)^4209 ≤ (3191236028957/25000000000000 : ℝ)^3185 := by
    have hnat : (2106269597 : ℕ)^4209*25000000000000^3185 ≤ 3191236028957^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106269597 10000000000 3191236028957 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52898933/100000000 : ℝ), (2692355039/5000000000 : ℝ), (-2106269597/10000000000 : ℝ)] ![(8621109006837/20000000000000 : ℝ), (11032377709663/25000000000000 : ℝ), (3191236028957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52898933/100000000 : ℝ)|^4209 ≤ (8621109006837/20000000000000 : ℝ)^3185
        have hw : |(52898933/100000000 : ℝ)|=(52898933/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692355039/5000000000 : ℝ)|^4209 ≤ (11032377709663/25000000000000 : ℝ)^3185
        have hw : |(2692355039/5000000000 : ℝ)|=(2692355039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106269597/10000000000 : ℝ)|^4209 ≤ (3191236028957/25000000000000 : ℝ)^3185
        have hw : |(-2106269597/10000000000 : ℝ)|=(2106269597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_11 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240815317/5000000000 : ℝ)*x 0 + (4290764837/10000000000 : ℝ)*x 1 + (2145382431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240815317/5000000000 : ℝ)^4209 ≤ (34623446072219/100000000000000 : ℝ)^3185 := by
    have hnat : (2240815317 : ℕ)^4209*100000000000000^3185 ≤ 34623446072219^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240815317 5000000000 34623446072219 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4290764837/10000000000 : ℝ)^4209 ≤ (32688276825659/100000000000000 : ℝ)^3185 := by
    have hnat : (4290764837 : ℕ)^4209*100000000000000^3185 ≤ 32688276825659^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290764837 10000000000 32688276825659 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145382431/5000000000 : ℝ)^4209 ≤ (32688277077349/100000000000000 : ℝ)^3185 := by
    have hnat : (2145382431 : ℕ)^4209*100000000000000^3185 ≤ 32688277077349^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145382431 5000000000 32688277077349 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240815317/5000000000 : ℝ), (4290764837/10000000000 : ℝ), (2145382431/5000000000 : ℝ)] ![(34623446072219/100000000000000 : ℝ), (32688276825659/100000000000000 : ℝ), (32688277077349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240815317/5000000000 : ℝ)|^4209 ≤ (34623446072219/100000000000000 : ℝ)^3185
        have hw : |(2240815317/5000000000 : ℝ)|=(2240815317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4290764837/10000000000 : ℝ)|^4209 ≤ (32688276825659/100000000000000 : ℝ)^3185
        have hw : |(4290764837/10000000000 : ℝ)|=(4290764837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2145382431/5000000000 : ℝ)|^4209 ≤ (32688277077349/100000000000000 : ℝ)^3185
        have hw : |(2145382431/5000000000 : ℝ)|=(2145382431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_12 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056195811/10000000000 : ℝ)*x 0 + (5437273039/10000000000 : ℝ)*x 1 + (5274037411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056195811/10000000000 : ℝ)^4209 ≤ (12365447684991/100000000000000 : ℝ)^3185 := by
    have hnat : (2056195811 : ℕ)^4209*100000000000000^3185 ≤ 12365447684991^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056195811 10000000000 12365447684991 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437273039/10000000000 : ℝ)^4209 ≤ (5587458660861/12500000000000 : ℝ)^3185 := by
    have hnat : (5437273039 : ℕ)^4209*12500000000000^3185 ≤ 5587458660861^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437273039 10000000000 5587458660861 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274037411/10000000000 : ℝ)^4209 ≤ (42934883022389/100000000000000 : ℝ)^3185 := by
    have hnat : (5274037411 : ℕ)^4209*100000000000000^3185 ≤ 42934883022389^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274037411 10000000000 42934883022389 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056195811/10000000000 : ℝ), (5437273039/10000000000 : ℝ), (5274037411/10000000000 : ℝ)] ![(12365447684991/100000000000000 : ℝ), (5587458660861/12500000000000 : ℝ), (42934883022389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056195811/10000000000 : ℝ)|^4209 ≤ (12365447684991/100000000000000 : ℝ)^3185
        have hw : |(-2056195811/10000000000 : ℝ)|=(2056195811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437273039/10000000000 : ℝ)|^4209 ≤ (5587458660861/12500000000000 : ℝ)^3185
        have hw : |(5437273039/10000000000 : ℝ)|=(5437273039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274037411/10000000000 : ℝ)|^4209 ≤ (42934883022389/100000000000000 : ℝ)^3185
        have hw : |(5274037411/10000000000 : ℝ)|=(5274037411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_13 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367939549/10000000000 : ℝ)*x 0 + (-2150099013/10000000000 : ℝ)*x 1 + (5274037753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367939549/10000000000 : ℝ)^4209 ≤ (43947973737333/100000000000000 : ℝ)^3185 := by
    have hnat : (5367939549 : ℕ)^4209*100000000000000^3185 ≤ 43947973737333^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367939549 10000000000 43947973737333 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150099013/10000000000 : ℝ)^4209 ≤ (13117139549547/100000000000000 : ℝ)^3185 := by
    have hnat : (2150099013 : ℕ)^4209*100000000000000^3185 ≤ 13117139549547^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150099013 10000000000 13117139549547 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274037753/10000000000 : ℝ)^4209 ≤ (10733721675417/25000000000000 : ℝ)^3185 := by
    have hnat : (5274037753 : ℕ)^4209*25000000000000^3185 ≤ 10733721675417^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274037753 10000000000 10733721675417 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367939549/10000000000 : ℝ), (-2150099013/10000000000 : ℝ), (5274037753/10000000000 : ℝ)] ![(43947973737333/100000000000000 : ℝ), (13117139549547/100000000000000 : ℝ), (10733721675417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367939549/10000000000 : ℝ)|^4209 ≤ (43947973737333/100000000000000 : ℝ)^3185
        have hw : |(5367939549/10000000000 : ℝ)|=(5367939549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2150099013/10000000000 : ℝ)|^4209 ≤ (13117139549547/100000000000000 : ℝ)^3185
        have hw : |(-2150099013/10000000000 : ℝ)|=(2150099013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274037753/10000000000 : ℝ)|^4209 ≤ (10733721675417/25000000000000 : ℝ)^3185
        have hw : |(5274037753/10000000000 : ℝ)|=(5274037753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_14 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683970059/5000000000 : ℝ)*x 0 + (659254687/1250000000 : ℝ)*x 1 + (-67190581/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683970059/5000000000 : ℝ)^4209 ≤ (43947979893537/100000000000000 : ℝ)^3185 := by
    have hnat : (2683970059 : ℕ)^4209*100000000000000^3185 ≤ 43947979893537^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683970059 5000000000 43947979893537 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659254687/1250000000 : ℝ)^4209 ≤ (4293488393683/10000000000000 : ℝ)^3185 := by
    have hnat : (659254687 : ℕ)^4209*10000000000000^3185 ≤ 4293488393683^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659254687 1250000000 4293488393683 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67190581/312500000 : ℝ)^4209 ≤ (13117136155387/100000000000000 : ℝ)^3185 := by
    have hnat : (67190581 : ℕ)^4209*100000000000000^3185 ≤ 13117136155387^3185*312500000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67190581 312500000 13117136155387 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683970059/5000000000 : ℝ), (659254687/1250000000 : ℝ), (-67190581/312500000 : ℝ)] ![(43947979893537/100000000000000 : ℝ), (4293488393683/10000000000000 : ℝ), (13117136155387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683970059/5000000000 : ℝ)|^4209 ≤ (43947979893537/100000000000000 : ℝ)^3185
        have hw : |(2683970059/5000000000 : ℝ)|=(2683970059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659254687/1250000000 : ℝ)|^4209 ≤ (4293488393683/10000000000000 : ℝ)^3185
        have hw : |(659254687/1250000000 : ℝ)|=(659254687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67190581/312500000 : ℝ)|^4209 ≤ (13117136155387/100000000000000 : ℝ)^3185
        have hw : |(-67190581/312500000 : ℝ)|=(67190581/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_box_15 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422723291/1000000000 : ℝ)*x 0 + (4417961861/10000000000 : ℝ)*x 1 + (1104490233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422723291/1000000000 : ℝ)^4209 ≤ (8012547275369/25000000000000 : ℝ)^3185 := by
    have hnat : (422723291 : ℕ)^4209*25000000000000^3185 ≤ 8012547275369^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422723291 1000000000 8012547275369 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417961861/10000000000 : ℝ)^4209 ≤ (16987455081817/50000000000000 : ℝ)^3185 := by
    have hnat : (4417961861 : ℕ)^4209*50000000000000^3185 ≤ 16987455081817^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417961861 10000000000 16987455081817 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104490233/2500000000 : ℝ)^4209 ≤ (33974900722557/100000000000000 : ℝ)^3185 := by
    have hnat : (1104490233 : ℕ)^4209*100000000000000^3185 ≤ 33974900722557^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104490233 2500000000 33974900722557 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422723291/1000000000 : ℝ), (4417961861/10000000000 : ℝ), (1104490233/2500000000 : ℝ)] ![(8012547275369/25000000000000 : ℝ), (16987455081817/50000000000000 : ℝ), (33974900722557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422723291/1000000000 : ℝ)|^4209 ≤ (8012547275369/25000000000000 : ℝ)^3185
        have hw : |(422723291/1000000000 : ℝ)|=(422723291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417961861/10000000000 : ℝ)|^4209 ≤ (16987455081817/50000000000000 : ℝ)^3185
        have hw : |(4417961861/10000000000 : ℝ)|=(4417961861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104490233/2500000000 : ℝ)|^4209 ≤ (33974900722557/100000000000000 : ℝ)^3185
        have hw : |(1104490233/2500000000 : ℝ)|=(1104490233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62243/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14841/25000 : ℝ) ∧ (80059/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20827/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11459/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (1698758575605359/12500000000000000000 : ℝ) := by
    have hpowers : (11459/100000 : ℝ)^8417 ≤ (1698758575605359/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11459 : ℕ)^8417*12500000000000000000^2048 ≤ 1698758575605359^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11459 100000 1698758575605359 12500000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11459/100000 : ℝ)) (X := (1698758575605359/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (8417/2048 : ℝ) ≤ (31825396159221831/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^8417 ≤ (31825396159221831/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8417*100000000000000000000^2048 ≤ 31825396159221831^2048*20000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 31825396159221831 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (31825396159221831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251698758575605359/6250000000000000000 : ℝ) ≤ (31252066472529/31250000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (6251698758575605359/6250000000000000000 : ℝ)^2048 ≤ (31252066472529/31250000000000 : ℝ)^8417 := by
      have hnat : (6251698758575605359 : ℕ)^2048*31250000000000^8417 ≤ 31252066472529^8417*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251698758575605359 6250000000000000000 31252066472529 31250000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252066472529/31250000000000 : ℝ)) (X := (6251698758575605359/6250000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045415464764064703/100000000000000000000 : ℝ) ≤ (1000110484607869/1000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100045415464764064703/100000000000000000000 : ℝ)^2048 ≤ (1000110484607869/1000000000000000 : ℝ)^8417 := by
      have hnat : (100045415464764064703 : ℕ)^2048*1000000000000000^8417 ≤ 1000110484607869^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045415464764064703 100000000000000000000 1000110484607869 1000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000110484607869/1000000000000000 : ℝ)) (X := (100045415464764064703/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031825396159221831/50000000000000000000 : ℝ) ≤ (100015484209481/100000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50031825396159221831/50000000000000000000 : ℝ)^2048 ≤ (100015484209481/100000000000000 : ℝ)^8417 := by
      have hnat : (50031825396159221831 : ℕ)^2048*100000000000000^8417 ≤ 100015484209481^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031825396159221831 50000000000000000000 100015484209481 100000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100015484209481/100000000000000 : ℝ)) (X := (50031825396159221831/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1698758575605359/12500000000000000000 : ℝ) ≤ ((263515772620505237/263600000000000000 : ℝ)+2*(44357486941/26360000000000 : ℝ)*(11459/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (263515772620505237/263600000000000000 : ℝ)+2*(44357486941/26360000000000 : ℝ)*(11459/100000 : ℝ)=(31252066472529/31250000000000 : ℝ) by norm_num, show 1+2*(1698758575605359/12500000000000000000 : ℝ)=(6251698758575605359/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31825396159221831/100000000000000000000 : ℝ)+(1698758575605359/12500000000000000000 : ℝ) ≤ ((263515772620505237/263600000000000000 : ℝ)+(44357486941/26360000000000 : ℝ)*((2819/20000 : ℝ)+(11459/100000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (263515772620505237/263600000000000000 : ℝ)+(44357486941/26360000000000 : ℝ)*((2819/20000 : ℝ)+(11459/100000 : ℝ))=(1000110484607869/1000000000000000 : ℝ) by norm_num, show 1+(31825396159221831/100000000000000000000 : ℝ)+(1698758575605359/12500000000000000000 : ℝ)=(100045415464764064703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31825396159221831/100000000000000000000 : ℝ) ≤ ((263515772620505237/263600000000000000 : ℝ)+2*(44357486941/26360000000000 : ℝ)*(2819/20000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (263515772620505237/263600000000000000 : ℝ)+2*(44357486941/26360000000000 : ℝ)*(2819/20000 : ℝ)=(100015484209481/100000000000000 : ℝ) by norm_num, show 1+2*(31825396159221831/100000000000000000000 : ℝ)=(50031825396159221831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (263515772620505237/263600000000000000 : ℝ)*(X 1 0+X 2 0)+(44357486941/26360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (263515772620505237/263600000000000000 : ℝ)) (alpha := (44357486941/26360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (263515772620505237/263600000000000000 : ℝ)*(X 0 1+X 2 1)+(44357486941/26360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (263515772620505237/263600000000000000 : ℝ)) (alpha := (44357486941/26360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (263515772620505237/263600000000000000 : ℝ)*(X 0 2+X 1 2)+(44357486941/26360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (263515772620505237/263600000000000000 : ℝ)) (alpha := (44357486941/26360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2003593717/10000000000 : ℝ)*X 0 0+(1343774221/2500000000 : ℝ)*X 0 1+(107501951/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059334963/2000000000 : ℝ)*X 1 0+(-422028557/2000000000 : ℝ)*X 1 1+(5375097969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648337693/5000000000 : ℝ)*X 2 0+(5375097353/10000000000 : ℝ)*X 2 1+(-2110142849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4459804199/10000000000 : ℝ)*X 0 0+(1075454669/2500000000 : ℝ)*X 0 1+(4301818517/10000000000 : ℝ)*X 0 2+(4459804199/10000000000 : ℝ)*X 1 0+(1075454669/2500000000 : ℝ)*X 1 1+(4301818517/10000000000 : ℝ)*X 1 2+(4459804199/10000000000 : ℝ)*X 2 0+(1075454669/2500000000 : ℝ)*X 2 1+(4301818517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-563354867/2500000000 : ℝ)*X 0 0+(1320527599/2500000000 : ℝ)*X 0 1+(2641055271/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681124431/5000000000 : ℝ)*X 1 0+(-134184923/625000000 : ℝ)*X 1 1+(1056422121/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362249133/10000000000 : ℝ)*X 2 0+(1320527569/2500000000 : ℝ)*X 2 1+(-429391769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265376573/625000000 : ℝ)*X 0 0+(881737573/2000000000 : ℝ)*X 0 1+(4408687929/10000000000 : ℝ)*X 0 2+(265376573/625000000 : ℝ)*X 1 0+(881737573/2000000000 : ℝ)*X 1 1+(4408687929/10000000000 : ℝ)*X 1 2+(265376573/625000000 : ℝ)*X 2 0+(881737573/2000000000 : ℝ)*X 2 1+(4408687929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1375679/6250000 : ℝ)*X 0 0+(5218715021/10000000000 : ℝ)*X 0 1+(673088757/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289893299/10000000000 : ℝ)*X 1 0+(-2106269677/10000000000 : ℝ)*X 1 1+(5384710019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((52898933/100000000 : ℝ)*X 2 0+(2692355039/5000000000 : ℝ)*X 2 1+(-2106269597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2240815317/5000000000 : ℝ)*X 0 0+(4290764837/10000000000 : ℝ)*X 0 1+(2145382431/5000000000 : ℝ)*X 0 2+(2240815317/5000000000 : ℝ)*X 1 0+(4290764837/10000000000 : ℝ)*X 1 1+(2145382431/5000000000 : ℝ)*X 1 2+(2240815317/5000000000 : ℝ)*X 2 0+(4290764837/10000000000 : ℝ)*X 2 1+(2145382431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2056195811/10000000000 : ℝ)*X 0 0+(5437273039/10000000000 : ℝ)*X 0 1+(5274037411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367939549/10000000000 : ℝ)*X 1 0+(-2150099013/10000000000 : ℝ)*X 1 1+(5274037753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683970059/5000000000 : ℝ)*X 2 0+(659254687/1250000000 : ℝ)*X 2 1+(-67190581/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((422723291/1000000000 : ℝ)*X 0 0+(4417961861/10000000000 : ℝ)*X 0 1+(1104490233/2500000000 : ℝ)*X 0 2+(422723291/1000000000 : ℝ)*X 1 0+(4417961861/10000000000 : ℝ)*X 1 1+(1104490233/2500000000 : ℝ)*X 1 2+(422723291/1000000000 : ℝ)*X 2 0+(4417961861/10000000000 : ℝ)*X 2 1+(1104490233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62243/100000 : ℝ) ≤ (-1025419371479334287977072015293/1647500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7383123/50000000000000 : ℝ)*(lower2) + (13243293/100000000000000 : ℝ)*(lower3) + (35306333/100000000000000 : ℝ)*(upper5) + (997322033913063/25000000000000 : ℝ)*(major0) + (997322033913063/25000000000000 : ℝ)*(major1) + (997322033913063/25000000000000 : ℝ)*(major2) + (14638641989/100000000000000 : ℝ)*(sp2) + (40942513/10000000000000 : ℝ)*(sp3) + (2679540700564317/50000000000000 : ℝ)*(sp4) + (5359023174388629/100000000000000 : ℝ)*(sp5) + (5359069115186621/100000000000000 : ℝ)*(sp6) + (1320119542861791/50000000000000 : ℝ)*(sp7) + (294087497/12500000000000 : ℝ)*(sp12) + (30289719991/50000000000000 : ℝ)*(sp13) + (330029936893589/12500000000000 : ℝ)*(f.failure) + (535908375382861/10000000000000 : ℝ)*(f.sum) + (160399089179/164750000000000000000000000 : ℝ)*base66 + (62145700670620931/6590000000000000000000000000000 : ℝ)*base67 + (90015145350360931/6590000000000000000000000000000 : ℝ)*base69 + (13294791657460931/6590000000000000000000000000000 : ℝ)*base71 + (818042698741/329500000000000000000000000 : ℝ)*base74 + (41746655569069/6590000000000000000000000000000 : ℝ)*base76 + (51897732993170931/6590000000000000000000000000000 : ℝ)*base77 + (43133903993470931/6590000000000000000000000000000 : ℝ)*base79 + (8057920721/20593750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2579647/312500000000000000000 : ℝ)*base89 + (2579647/312500000000000000000 : ℝ)*base91 + (2579647/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14841/25000 : ℝ) ≤ (1956116069654170922070126611283/3295000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102510761/100000000000000 : ℝ)*(lower0) + (170249467/100000000000000 : ℝ)*(lower3) + (50418891/100000000000000 : ℝ)*(upper4) + (1013706818217551/25000000000000 : ℝ)*(major0) + (1013706818217551/25000000000000 : ℝ)*(major1) + (1013706818217551/25000000000000 : ℝ)*(major2) + (5406243022315893/100000000000000 : ℝ)*(sp0) + (5406199711943579/100000000000000 : ℝ)*(sp1) + (5406239099121781/100000000000000 : ℝ)*(sp2) + (67089891438573/2500000000000 : ℝ)*(sp3) + (1584177417/3125000000000 : ℝ)*(sp5) + (5653249571/50000000000000 : ℝ)*(sp6) + (19751472319/100000000000000 : ℝ)*(sp7) + (738330503/10000000000000 : ℝ)*(sp12) + (1341807704507619/50000000000000 : ℝ)*(f.failure) + (5406250405620923/100000000000000 : ℝ)*(f.sum) + (101327785217/659000000000000000000000000 : ℝ)*base66 + (21267285604105413/6590000000000000000000000000000 : ℝ)*base68 + (107068295028165413/6590000000000000000000000000000 : ℝ)*base70 + (5225542834425413/6590000000000000000000000000000 : ℝ)*base72 + (10275009431/13180000000000000000000000 : ℝ)*base74 + (73335961141855413/6590000000000000000000000000000 : ℝ)*base76 + (38468672222435413/6590000000000000000000000000000 : ℝ)*base78 + (60550705950875413/6590000000000000000000000000000 : ℝ)*base80 + (1806671495103/329500000000000000000000000 : ℝ)*base82 + (3019337/1250000000000000000000 : ℝ)*base89 + (3019337/1250000000000000000000 : ℝ)*base91 + (3019337/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80059/100000 : ℝ) ≤ (10552041875095689790385610027513/13180000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51998441/100000000000000 : ℝ)*(lower3) + (26333323/100000000000000 : ℝ)*(upper4) + (2754337/25000000000000 : ℝ)*(lower5) + (4521830217151417/100000000000000 : ℝ)*(major0) + (4521830217151417/100000000000000 : ℝ)*(major1) + (4521830217151417/100000000000000 : ℝ)*(major2) + (1322135973/100000000000000 : ℝ)*(sp0) + (8057466197/25000000000000 : ℝ)*(sp1) + (35083327913/50000000000000 : ℝ)*(sp2) + (7367757361/25000000000000 : ℝ)*(sp3) + (3012139547050907/50000000000000 : ℝ)*(sp8) + (6024248186372999/100000000000000 : ℝ)*(sp9) + (3012105124790981/50000000000000 : ℝ)*(sp10) + (1496331770893753/50000000000000 : ℝ)*(sp11) + (2992693012816949/100000000000000 : ℝ)*(f.failure) + (6024280416237787/100000000000000 : ℝ)*(f.sum) + (525341388369/263600000000000000000000000 : ℝ)*base66 + (43915133331320829/26360000000000000000000000000000 : ℝ)*base67 + (73837487997000829/26360000000000000000000000000000 : ℝ)*base69 + (104227783669280829/26360000000000000000000000000000 : ℝ)*base71 + (10542572651763/1318000000000000000000000000 : ℝ)*base73 + (1690568168160829/26360000000000000000000000000000 : ℝ)*base75 + (56905769706119171/26360000000000000000000000000000 : ℝ)*base78 + (149601149496359171/26360000000000000000000000000000 : ℝ)*base80 + (3931326886579/1318000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (19620927/2500000000000000000000 : ℝ)*base89 + (19620927/2500000000000000000000 : ℝ)*base91 + (19620927/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-20827/25000 : ℝ) ≤ (-2744933082979003486555772686689/3295000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13617251/12500000000000 : ℝ)*(lower0) + (79260941/20000000000000 : ℝ)*(lower2) + (26835753/10000000000000 : ℝ)*(upper3) + (16434669/5000000000000 : ℝ)*(upper5) + (2278608786218399/50000000000000 : ℝ)*(major0) + (2278608786218399/50000000000000 : ℝ)*(major1) + (2278608786218399/50000000000000 : ℝ)*(major2) + (438607109/50000000000000 : ℝ)*(sp0) + (20968543699/25000000000000 : ℝ)*(sp5) + (125541572799/50000000000000 : ℝ)*(sp7) + (6126089432835313/100000000000000 : ℝ)*(sp12) + (382875402242171/6250000000000 : ℝ)*(sp13) + (6126090310049531/100000000000000 : ℝ)*(sp14) + (376982802777433/12500000000000 : ℝ)*(sp15) + (1508056752682531/50000000000000 : ℝ)*(f.failure) + (6126090310049531/100000000000000 : ℝ)*(f.sum) + (401428995143/329500000000000000000000000 : ℝ)*base66 + (42464597393894437/13180000000000000000000000000000 : ℝ)*base68 + (153502577394905563/13180000000000000000000000000000 : ℝ)*base69 + (100961042674245563/13180000000000000000000000000000 : ℝ)*base71 + (19583863651857/659000000000000000000000000 : ℝ)*base73 + (150110582545805563/13180000000000000000000000000000 : ℝ)*base75 + (6097090608685563/13180000000000000000000000000000 : ℝ)*base77 + (568601173202845563/13180000000000000000000000000000 : ℝ)*base79 + (3947030753017/659000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5560887/1250000000000000000000 : ℝ)*base90 + (5560887/1250000000000000000000 : ℝ)*base92 + (5560887/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14841/25000 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20827/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1225_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1225_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14841/25000 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20827/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1225_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1225_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14841/25000 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20827/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

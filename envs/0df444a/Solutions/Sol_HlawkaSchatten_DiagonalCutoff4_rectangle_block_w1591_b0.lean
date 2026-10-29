-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:00.143967+00:00
-- url     : https://prove2.me/submissions/1fca17dc-d7d0-41d8-ad19-0192fe4a6e9c

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
theorem support_rectangle_w1591_s0_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1602088853/10000000000 : ℝ)*x 0 + (5863395753/10000000000 : ℝ)*x 1 + (609807213/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1602088853/10000000000 : ℝ)^4683 ≤ (1919295602421/20000000000000 : ℝ)^3659 := by
    have hnat : (1602088853 : ℕ)^4683*20000000000000^3659 ≤ 1919295602421^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602088853 10000000000 1919295602421 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5863395753/10000000000 : ℝ)^4683 ≤ (50496809108463/100000000000000 : ℝ)^3659 := by
    have hnat : (5863395753 : ℕ)^4683*100000000000000^3659 ≤ 50496809108463^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5863395753 10000000000 50496809108463 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609807213/1250000000 : ℝ)^4683 ≤ (19953356431311/50000000000000 : ℝ)^3659 := by
    have hnat : (609807213 : ℕ)^4683*50000000000000^3659 ≤ 19953356431311^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609807213 1250000000 19953356431311 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1602088853/10000000000 : ℝ), (5863395753/10000000000 : ℝ), (609807213/1250000000 : ℝ)] ![(1919295602421/20000000000000 : ℝ), (50496809108463/100000000000000 : ℝ), (19953356431311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1602088853/10000000000 : ℝ)|^4683 ≤ (1919295602421/20000000000000 : ℝ)^3659
        have hw : |(-1602088853/10000000000 : ℝ)|=(1602088853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5863395753/10000000000 : ℝ)|^4683 ≤ (50496809108463/100000000000000 : ℝ)^3659
        have hw : |(5863395753/10000000000 : ℝ)|=(5863395753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(609807213/1250000000 : ℝ)|^4683 ≤ (19953356431311/50000000000000 : ℝ)^3659
        have hw : |(609807213/1250000000 : ℝ)|=(609807213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546161439/1000000000 : ℝ)*x 0 + (-2149806293/10000000000 : ℝ)*x 1 + (4878457551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546161439/1000000000 : ℝ)^4683 ≤ (4611139428941/10000000000000 : ℝ)^3659 := by
    have hnat : (546161439 : ℕ)^4683*10000000000000^3659 ≤ 4611139428941^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546161439 1000000000 4611139428941 10000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149806293/10000000000 : ℝ)^4683 ≤ (13981894423787/100000000000000 : ℝ)^3659 := by
    have hnat : (2149806293 : ℕ)^4683*100000000000000^3659 ≤ 13981894423787^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149806293 10000000000 13981894423787 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4878457551/10000000000 : ℝ)^4683 ≤ (4988338907599/12500000000000 : ℝ)^3659 := by
    have hnat : (4878457551 : ℕ)^4683*12500000000000^3659 ≤ 4988338907599^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878457551 10000000000 4988338907599 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546161439/1000000000 : ℝ), (-2149806293/10000000000 : ℝ), (4878457551/10000000000 : ℝ)] ![(4611139428941/10000000000000 : ℝ), (13981894423787/100000000000000 : ℝ), (4988338907599/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546161439/1000000000 : ℝ)|^4683 ≤ (4611139428941/10000000000000 : ℝ)^3659
        have hw : |(546161439/1000000000 : ℝ)|=(546161439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149806293/10000000000 : ℝ)|^4683 ≤ (13981894423787/100000000000000 : ℝ)^3659
        have hw : |(-2149806293/10000000000 : ℝ)|=(2149806293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4878457551/10000000000 : ℝ)|^4683 ≤ (4988338907599/12500000000000 : ℝ)^3659
        have hw : |(4878457551/10000000000 : ℝ)|=(4878457551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5461614451/10000000000 : ℝ)*x 0 + (4878457467/10000000000 : ℝ)*x 1 + (-2149806321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5461614451/10000000000 : ℝ)^4683 ≤ (5763924368569/12500000000000 : ℝ)^3659 := by
    have hnat : (5461614451 : ℕ)^4683*12500000000000^3659 ≤ 5763924368569^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461614451 10000000000 5763924368569 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4878457467/10000000000 : ℝ)^4683 ≤ (7981342076271/20000000000000 : ℝ)^3659 := by
    have hnat : (4878457467 : ℕ)^4683*20000000000000^3659 ≤ 7981342076271^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878457467 10000000000 7981342076271 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149806321/10000000000 : ℝ)^4683 ≤ (13981894656857/100000000000000 : ℝ)^3659 := by
    have hnat : (2149806321 : ℕ)^4683*100000000000000^3659 ≤ 13981894656857^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149806321 10000000000 13981894656857 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5461614451/10000000000 : ℝ), (4878457467/10000000000 : ℝ), (-2149806321/10000000000 : ℝ)] ![(5763924368569/12500000000000 : ℝ), (7981342076271/20000000000000 : ℝ), (13981894656857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5461614451/10000000000 : ℝ)|^4683 ≤ (5763924368569/12500000000000 : ℝ)^3659
        have hw : |(5461614451/10000000000 : ℝ)|=(5461614451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4878457467/10000000000 : ℝ)|^4683 ≤ (7981342076271/20000000000000 : ℝ)^3659
        have hw : |(4878457467/10000000000 : ℝ)|=(4878457467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149806321/10000000000 : ℝ)|^4683 ≤ (13981894656857/100000000000000 : ℝ)^3659
        have hw : |(-2149806321/10000000000 : ℝ)|=(2149806321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119220487/10000000000 : ℝ)*x 0 + (76791237/250000000 : ℝ)*x 1 + (678942393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119220487/10000000000 : ℝ)^4683 ≤ (1606896832519/5000000000000 : ℝ)^3659 := by
    have hnat : (4119220487 : ℕ)^4683*5000000000000^3659 ≤ 1606896832519^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119220487 10000000000 1606896832519 5000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76791237/250000000 : ℝ)^4683 ≤ (220753994381/1000000000000 : ℝ)^3659 := by
    have hnat : (76791237 : ℕ)^4683*1000000000000^3659 ≤ 220753994381^3659*250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76791237 250000000 220753994381 1000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678942393/1250000000 : ℝ)^4683 ≤ (45786663893159/100000000000000 : ℝ)^3659 := by
    have hnat : (678942393 : ℕ)^4683*100000000000000^3659 ≤ 45786663893159^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678942393 1250000000 45786663893159 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119220487/10000000000 : ℝ), (76791237/250000000 : ℝ), (678942393/1250000000 : ℝ)] ![(1606896832519/5000000000000 : ℝ), (220753994381/1000000000000 : ℝ), (45786663893159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119220487/10000000000 : ℝ)|^4683 ≤ (1606896832519/5000000000000 : ℝ)^3659
        have hw : |(4119220487/10000000000 : ℝ)|=(4119220487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76791237/250000000 : ℝ)|^4683 ≤ (220753994381/1000000000000 : ℝ)^3659
        have hw : |(76791237/250000000 : ℝ)|=(76791237/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678942393/1250000000 : ℝ)|^4683 ≤ (45786663893159/100000000000000 : ℝ)^3659
        have hw : |(678942393/1250000000 : ℝ)|=(678942393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1605153843/10000000000 : ℝ)*x 0 + (1225900593/2500000000 : ℝ)*x 1 + (5837346687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605153843/10000000000 : ℝ)^4683 ≤ (9619981497851/100000000000000 : ℝ)^3659 := by
    have hnat : (1605153843 : ℕ)^4683*100000000000000^3659 ≤ 9619981497851^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605153843 10000000000 9619981497851 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225900593/2500000000 : ℝ)^4683 ≤ (8034030824059/20000000000000 : ℝ)^3659 := by
    have hnat : (1225900593 : ℕ)^4683*20000000000000^3659 ≤ 8034030824059^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225900593 2500000000 8034030824059 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5837346687/10000000000 : ℝ)^4683 ≤ (627623304527/1250000000000 : ℝ)^3659 := by
    have hnat : (5837346687 : ℕ)^4683*1250000000000^3659 ≤ 627623304527^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5837346687 10000000000 627623304527 1250000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1605153843/10000000000 : ℝ), (1225900593/2500000000 : ℝ), (5837346687/10000000000 : ℝ)] ![(9619981497851/100000000000000 : ℝ), (8034030824059/20000000000000 : ℝ), (627623304527/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1605153843/10000000000 : ℝ)|^4683 ≤ (9619981497851/100000000000000 : ℝ)^3659
        have hw : |(-1605153843/10000000000 : ℝ)|=(1605153843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1225900593/2500000000 : ℝ)|^4683 ≤ (8034030824059/20000000000000 : ℝ)^3659
        have hw : |(1225900593/2500000000 : ℝ)|=(1225900593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5837346687/10000000000 : ℝ)|^4683 ≤ (627623304527/1250000000000 : ℝ)^3659
        have hw : |(5837346687/10000000000 : ℝ)|=(5837346687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596297307/5000000000 : ℝ)*x 0 + (-297729399/2500000000 : ℝ)*x 1 + (5837346997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596297307/5000000000 : ℝ)^4683 ≤ (5403093922319/12500000000000 : ℝ)^3659 := by
    have hnat : (2596297307 : ℕ)^4683*12500000000000^3659 ≤ 5403093922319^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596297307 5000000000 5403093922319 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297729399/2500000000 : ℝ)^4683 ≤ (3282690415709/50000000000000 : ℝ)^3659 := by
    have hnat : (297729399 : ℕ)^4683*50000000000000^3659 ≤ 3282690415709^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297729399 2500000000 3282690415709 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5837346997/10000000000 : ℝ)^4683 ≤ (50209867774851/100000000000000 : ℝ)^3659 := by
    have hnat : (5837346997 : ℕ)^4683*100000000000000^3659 ≤ 50209867774851^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5837346997 10000000000 50209867774851 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596297307/5000000000 : ℝ), (-297729399/2500000000 : ℝ), (5837346997/10000000000 : ℝ)] ![(5403093922319/12500000000000 : ℝ), (3282690415709/50000000000000 : ℝ), (50209867774851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596297307/5000000000 : ℝ)|^4683 ≤ (5403093922319/12500000000000 : ℝ)^3659
        have hw : |(2596297307/5000000000 : ℝ)|=(2596297307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297729399/2500000000 : ℝ)|^4683 ≤ (3282690415709/50000000000000 : ℝ)^3659
        have hw : |(-297729399/2500000000 : ℝ)|=(297729399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5837346997/10000000000 : ℝ)|^4683 ≤ (50209867774851/100000000000000 : ℝ)^3659
        have hw : |(5837346997/10000000000 : ℝ)|=(5837346997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192593893/10000000000 : ℝ)*x 0 + (2918673981/5000000000 : ℝ)*x 1 + (-595458589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192593893/10000000000 : ℝ)^4683 ≤ (43224743697069/100000000000000 : ℝ)^3659 := by
    have hnat : (5192593893 : ℕ)^4683*100000000000000^3659 ≤ 43224743697069^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192593893 10000000000 43224743697069 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2918673981/5000000000 : ℝ)^4683 ≤ (50209878398229/100000000000000 : ℝ)^3659 := by
    have hnat : (2918673981 : ℕ)^4683*100000000000000^3659 ≤ 50209878398229^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2918673981 5000000000 50209878398229 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595458589/5000000000 : ℝ)^4683 ≤ (6565377882137/100000000000000 : ℝ)^3659 := by
    have hnat : (595458589 : ℕ)^4683*100000000000000^3659 ≤ 6565377882137^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595458589 5000000000 6565377882137 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192593893/10000000000 : ℝ), (2918673981/5000000000 : ℝ), (-595458589/5000000000 : ℝ)] ![(43224743697069/100000000000000 : ℝ), (50209878398229/100000000000000 : ℝ), (6565377882137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192593893/10000000000 : ℝ)|^4683 ≤ (43224743697069/100000000000000 : ℝ)^3659
        have hw : |(5192593893/10000000000 : ℝ)|=(5192593893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2918673981/5000000000 : ℝ)|^4683 ≤ (50209878398229/100000000000000 : ℝ)^3659
        have hw : |(2918673981/5000000000 : ℝ)|=(2918673981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595458589/5000000000 : ℝ)|^4683 ≤ (6565377882137/100000000000000 : ℝ)^3659
        have hw : |(-595458589/5000000000 : ℝ)|=(595458589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s0_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4126561723/10000000000 : ℝ)*x 0 + (167852803/312500000 : ℝ)*x 1 + (3134060883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4126561723/10000000000 : ℝ)^4683 ≤ (8052814992973/25000000000000 : ℝ)^3659 := by
    have hnat : (4126561723 : ℕ)^4683*25000000000000^3659 ≤ 8052814992973^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126561723 10000000000 8052814992973 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167852803/312500000 : ℝ)^4683 ≤ (1805505970839/4000000000000 : ℝ)^3659 := by
    have hnat : (167852803 : ℕ)^4683*4000000000000^3659 ≤ 1805505970839^3659*312500000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167852803 312500000 1805505970839 4000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134060883/10000000000 : ℝ)^4683 ≤ (5662772685283/25000000000000 : ℝ)^3659 := by
    have hnat : (3134060883 : ℕ)^4683*25000000000000^3659 ≤ 5662772685283^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134060883 10000000000 5662772685283 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4126561723/10000000000 : ℝ), (167852803/312500000 : ℝ), (3134060883/10000000000 : ℝ)] ![(8052814992973/25000000000000 : ℝ), (1805505970839/4000000000000 : ℝ), (5662772685283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4126561723/10000000000 : ℝ)|^4683 ≤ (8052814992973/25000000000000 : ℝ)^3659
        have hw : |(4126561723/10000000000 : ℝ)|=(4126561723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167852803/312500000 : ℝ)|^4683 ≤ (1805505970839/4000000000000 : ℝ)^3659
        have hw : |(167852803/312500000 : ℝ)|=(167852803/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134060883/10000000000 : ℝ)|^4683 ≤ (5662772685283/25000000000000 : ℝ)^3659
        have hw : |(3134060883/10000000000 : ℝ)|=(3134060883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3597/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1543/6250 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4679/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4679 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4679*1^1024 ≤ 0^1024*1^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4679/1024 : ℝ) ≤ (1519422024698837143/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4679 ≤ (1519422024698837143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4679*100000000000000000000^1024 ≤ 1519422024698837143^1024*5^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1519422024698837143 100000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1519422024698837143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4679 := by
      have hnat : (1 : ℕ)^1024*1^4679 ≤ 1^4679*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101519422024698837143/100000000000000000000 : ℝ) ≤ (401322280136187/400000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (101519422024698837143/100000000000000000000 : ℝ)^1024 ≤ (401322280136187/400000000000000 : ℝ)^4679 := by
      have hnat : (101519422024698837143 : ℕ)^1024*400000000000000^4679 ≤ 401322280136187^4679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101519422024698837143 100000000000000000000 401322280136187 400000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401322280136187/400000000000000 : ℝ)) (X := (101519422024698837143/100000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51519422024698837143/50000000000000000000 : ℝ) ≤ (201322280136187/200000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (51519422024698837143/50000000000000000000 : ℝ)^1024 ≤ (201322280136187/200000000000000 : ℝ)^4679 := by
      have hnat : (51519422024698837143 : ℕ)^1024*200000000000000^4679 ≤ 201322280136187^4679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51519422024698837143 50000000000000000000 201322280136187 200000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201322280136187/200000000000000 : ℝ)) (X := (51519422024698837143/50000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1322280136187/160000000000000 : ℝ)*(0 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1322280136187/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1519422024698837143/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1322280136187/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1322280136187/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401322280136187/400000000000000 : ℝ) by norm_num, show 1+(1519422024698837143/100000000000000000000 : ℝ)+(0 : ℝ)=(101519422024698837143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1519422024698837143/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1322280136187/160000000000000 : ℝ)*(2/5 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1322280136187/160000000000000 : ℝ)*(2/5 : ℝ)=(201322280136187/200000000000000 : ℝ) by norm_num, show 1+2*(1519422024698837143/100000000000000000000 : ℝ)=(51519422024698837143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1322280136187/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1322280136187/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1322280136187/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1322280136187/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1322280136187/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1322280136187/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1602088853/10000000000 : ℝ)*X 0 0+(5863395753/10000000000 : ℝ)*X 0 1+(609807213/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((546161439/1000000000 : ℝ)*X 1 0+(-2149806293/10000000000 : ℝ)*X 1 1+(4878457551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5461614451/10000000000 : ℝ)*X 2 0+(4878457467/10000000000 : ℝ)*X 2 1+(-2149806321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4119220487/10000000000 : ℝ)*X 0 0+(76791237/250000000 : ℝ)*X 0 1+(678942393/1250000000 : ℝ)*X 0 2+(4119220487/10000000000 : ℝ)*X 1 0+(76791237/250000000 : ℝ)*X 1 1+(678942393/1250000000 : ℝ)*X 1 2+(4119220487/10000000000 : ℝ)*X 2 0+(76791237/250000000 : ℝ)*X 2 1+(678942393/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1605153843/10000000000 : ℝ)*X 0 0+(1225900593/2500000000 : ℝ)*X 0 1+(5837346687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596297307/5000000000 : ℝ)*X 1 0+(-297729399/2500000000 : ℝ)*X 1 1+(5837346997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192593893/10000000000 : ℝ)*X 2 0+(2918673981/5000000000 : ℝ)*X 2 1+(-595458589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4126561723/10000000000 : ℝ)*X 0 0+(167852803/312500000 : ℝ)*X 0 1+(3134060883/10000000000 : ℝ)*X 0 2+(4126561723/10000000000 : ℝ)*X 1 0+(167852803/312500000 : ℝ)*X 1 1+(3134060883/10000000000 : ℝ)*X 1 2+(4126561723/10000000000 : ℝ)*X 2 0+(167852803/312500000 : ℝ)*X 2 1+(3134060883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36098465703638562279/4000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80403413/100000000000000 : ℝ)*(base1) + (1808013029/100000000000000 : ℝ)*(base19) + (227419101/12500000000000 : ℝ)*(base23) + (118592119/50000000000000 : ℝ)*(upper3) + (231974491/100000000000000 : ℝ)*(upper5) + (719529800781/100000000000 : ℝ)*(major0) + (719529800781/100000000000 : ℝ)*(major1) + (719529800781/100000000000 : ℝ)*(major2) + (253824644105559/25000000000000 : ℝ)*(sp0) + (1015303300227729/100000000000000 : ℝ)*(sp1) + (20306065777759/2000000000000 : ℝ)*(sp2) + (84750256966847/20000000000000 : ℝ)*(sp3) + (1322444387/20000000000000 : ℝ)*(sp4) + (8835197/312500000000 : ℝ)*(sp7) + (26484637031293/6250000000000 : ℝ)*(f.failure) + (507652554120379/50000000000000 : ℝ)*(f.sum) + (7446891231/8000000000000000000000000 : ℝ)*base65 + (79880127359/16000000000000000000000000 : ℝ)*base67 + (65314247663/16000000000000000000000000 : ℝ)*base69 + (107082791247/16000000000000000000000000 : ℝ)*base71 + (8903318297/8000000000000000000000000 : ℝ)*base74 + (87593508623/16000000000000000000000000 : ℝ)*base75 + (99781269007/16000000000000000000000000 : ℝ)*base77 + (101476461407/16000000000000000000000000 : ℝ)*base79 + (27130855633/8000000000000000000000000 : ℝ)*base82 + (3180141/625000000000000000000 : ℝ)*base90 + (3180141/625000000000000000000 : ℝ)*base92 + (3180141/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30155992920581926421067/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46768057/5000000000000 : ℝ)*(base19) + (629284123/50000000000000 : ℝ)*(base23) + (532845367/100000000000000 : ℝ)*(base39) + (23543277/20000000000000 : ℝ)*(upper3) + (493795371/100000000000000 : ℝ)*(upper5) + (151793517432531/20000000000000 : ℝ)*(major0) + (151793517432531/20000000000000 : ℝ)*(major1) + (94870881789661/12500000000000 : ℝ)*(major2) + (3179110797/100000000000000 : ℝ)*(sp1) + (1083319189/50000000000000 : ℝ)*(sp2) + (8567633161601/800000000000 : ℝ)*(sp4) + (1070950030728189/100000000000000 : ℝ)*(sp5) + (267737813209717/25000000000000 : ℝ)*(sp6) + (5587254632873/1250000000000 : ℝ)*(sp7) + (5587254632873/1250000000000 : ℝ)*(f.failure) + (267738669511373/25000000000000 : ℝ)*(f.sum) + (16084725877341/16000000000000000000000000000 : ℝ)*base65 + (1751718282607/2000000000000000000000000000 : ℝ)*base67 + (26889953395297/3200000000000000000000000000 : ℝ)*base69 + (1436254170607/2000000000000000000000000000 : ℝ)*base71 + (9774242602659/16000000000000000000000000000 : ℝ)*base74 + (483743139297/3200000000000000000000000000 : ℝ)*base75 + (10332630748897/3200000000000000000000000000 : ℝ)*base77 + (24771874716897/3200000000000000000000000000 : ℝ)*base79 + (8283365094497/1600000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (926601/125000000000000000000 : ℝ)*base90 + (926601/125000000000000000000 : ℝ)*base92 + (926601/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1591_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3597/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1543/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1591_s1_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43362927/250000000 : ℝ)*x 0 + (5548711403/10000000000 : ℝ)*x 1 + (2553839507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43362927/250000000 : ℝ)^4683 ≤ (10623233018571/100000000000000 : ℝ)^3659 := by
    have hnat : (43362927 : ℕ)^4683*100000000000000^3659 ≤ 10623233018571^3659*250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43362927 250000000 10623233018571 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5548711403/10000000000 : ℝ)^4683 ≤ (2352731103763/5000000000000 : ℝ)^3659 := by
    have hnat : (5548711403 : ℕ)^4683*5000000000000^3659 ≤ 2352731103763^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548711403 10000000000 2352731103763 5000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2553839507/5000000000 : ℝ)^4683 ≤ (338577159157/800000000000 : ℝ)^3659 := by
    have hnat : (2553839507 : ℕ)^4683*800000000000^3659 ≤ 338577159157^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553839507 5000000000 338577159157 800000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43362927/250000000 : ℝ), (5548711403/10000000000 : ℝ), (2553839507/5000000000 : ℝ)] ![(10623233018571/100000000000000 : ℝ), (2352731103763/5000000000000 : ℝ), (338577159157/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43362927/250000000 : ℝ)|^4683 ≤ (10623233018571/100000000000000 : ℝ)^3659
        have hw : |(-43362927/250000000 : ℝ)|=(43362927/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5548711403/10000000000 : ℝ)|^4683 ≤ (2352731103763/5000000000000 : ℝ)^3659
        have hw : |(5548711403/10000000000 : ℝ)|=(5548711403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2553839507/5000000000 : ℝ)|^4683 ≤ (338577159157/800000000000 : ℝ)^3659
        have hw : |(2553839507/5000000000 : ℝ)|=(2553839507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42014001/78125000 : ℝ)*x 0 + (-196595831/1000000000 : ℝ)*x 1 + (5107678881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42014001/78125000 : ℝ)^4683 ≤ (2825474790861/6250000000000 : ℝ)^3659 := by
    have hnat : (42014001 : ℕ)^4683*6250000000000^3659 ≤ 2825474790861^3659*78125000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42014001 78125000 2825474790861 6250000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196595831/1000000000 : ℝ)^4683 ≤ (12470259843857/100000000000000 : ℝ)^3659 := by
    have hnat : (196595831 : ℕ)^4683*100000000000000^3659 ≤ 12470259843857^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196595831 1000000000 12470259843857 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5107678881/10000000000 : ℝ)^4683 ≤ (2645133967761/6250000000000 : ℝ)^3659 := by
    have hnat : (5107678881 : ℕ)^4683*6250000000000^3659 ≤ 2645133967761^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107678881 10000000000 2645133967761 6250000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42014001/78125000 : ℝ), (-196595831/1000000000 : ℝ), (5107678881/10000000000 : ℝ)] ![(2825474790861/6250000000000 : ℝ), (12470259843857/100000000000000 : ℝ), (2645133967761/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42014001/78125000 : ℝ)|^4683 ≤ (2825474790861/6250000000000 : ℝ)^3659
        have hw : |(42014001/78125000 : ℝ)|=(42014001/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196595831/1000000000 : ℝ)|^4683 ≤ (12470259843857/100000000000000 : ℝ)^3659
        have hw : |(-196595831/1000000000 : ℝ)|=(196595831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5107678881/10000000000 : ℝ)|^4683 ≤ (2645133967761/6250000000000 : ℝ)^3659
        have hw : |(5107678881/10000000000 : ℝ)|=(5107678881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344447977/2500000000 : ℝ)*x 0 + (255383953/500000000 : ℝ)*x 1 + (-1965958369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344447977/2500000000 : ℝ)^4683 ≤ (45207594286811/100000000000000 : ℝ)^3659 := by
    have hnat : (1344447977 : ℕ)^4683*100000000000000^3659 ≤ 45207594286811^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344447977 2500000000 45207594286811 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255383953/500000000 : ℝ)^4683 ≤ (846442907649/2000000000000 : ℝ)^3659 := by
    have hnat : (255383953 : ℕ)^4683*2000000000000^3659 ≤ 846442907649^3659*500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255383953 500000000 846442907649 2000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965958369/10000000000 : ℝ)^4683 ≤ (6235130161417/50000000000000 : ℝ)^3659 := by
    have hnat : (1965958369 : ℕ)^4683*50000000000000^3659 ≤ 6235130161417^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965958369 10000000000 6235130161417 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344447977/2500000000 : ℝ), (255383953/500000000 : ℝ), (-1965958369/10000000000 : ℝ)] ![(45207594286811/100000000000000 : ℝ), (846442907649/2000000000000 : ℝ), (6235130161417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344447977/2500000000 : ℝ)|^4683 ≤ (45207594286811/100000000000000 : ℝ)^3659
        have hw : |(1344447977/2500000000 : ℝ)|=(1344447977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(255383953/500000000 : ℝ)|^4683 ≤ (846442907649/2000000000000 : ℝ)^3659
        have hw : |(255383953/500000000 : ℝ)|=(255383953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965958369/10000000000 : ℝ)|^4683 ≤ (6235130161417/50000000000000 : ℝ)^3659
        have hw : |(-1965958369/10000000000 : ℝ)|=(1965958369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842969349/2000000000 : ℝ)*x 0 + (928167909/2500000000 : ℝ)*x 1 + (4769375497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842969349/2000000000 : ℝ)^4683 ≤ (4136985758767/12500000000000 : ℝ)^3659 := by
    have hnat : (842969349 : ℕ)^4683*12500000000000^3659 ≤ 4136985758767^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842969349 2000000000 4136985758767 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (928167909/2500000000 : ℝ)^4683 ≤ (7033960646071/25000000000000 : ℝ)^3659 := by
    have hnat : (928167909 : ℕ)^4683*25000000000000^3659 ≤ 7033960646071^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928167909 2500000000 7033960646071 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769375497/10000000000 : ℝ)^4683 ≤ (4846033915109/12500000000000 : ℝ)^3659 := by
    have hnat : (4769375497 : ℕ)^4683*12500000000000^3659 ≤ 4846033915109^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769375497 10000000000 4846033915109 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842969349/2000000000 : ℝ), (928167909/2500000000 : ℝ), (4769375497/10000000000 : ℝ)] ![(4136985758767/12500000000000 : ℝ), (7033960646071/25000000000000 : ℝ), (4846033915109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842969349/2000000000 : ℝ)|^4683 ≤ (4136985758767/12500000000000 : ℝ)^3659
        have hw : |(842969349/2000000000 : ℝ)|=(842969349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(928167909/2500000000 : ℝ)|^4683 ≤ (7033960646071/25000000000000 : ℝ)^3659
        have hw : |(928167909/2500000000 : ℝ)|=(928167909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769375497/10000000000 : ℝ)|^4683 ≤ (4846033915109/12500000000000 : ℝ)^3659
        have hw : |(4769375497/10000000000 : ℝ)|=(4769375497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433696141/2500000000 : ℝ)*x 0 + (1022532161/2000000000 : ℝ)*x 1 + (692956157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433696141/2500000000 : ℝ)^4683 ≤ (265633244263/2500000000000 : ℝ)^3659 := by
    have hnat : (433696141 : ℕ)^4683*2500000000000^3659 ≤ 265633244263^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433696141 2500000000 265633244263 2500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022532161/2000000000 : ℝ)^4683 ≤ (42374983406727/100000000000000 : ℝ)^3659 := by
    have hnat : (1022532161 : ℕ)^4683*100000000000000^3659 ≤ 42374983406727^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022532161 2000000000 42374983406727 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692956157/1250000000 : ℝ)^4683 ≤ (9399937362749/20000000000000 : ℝ)^3659 := by
    have hnat : (692956157 : ℕ)^4683*20000000000000^3659 ≤ 9399937362749^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692956157 1250000000 9399937362749 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433696141/2500000000 : ℝ), (1022532161/2000000000 : ℝ), (692956157/1250000000 : ℝ)] ![(265633244263/2500000000000 : ℝ), (42374983406727/100000000000000 : ℝ), (9399937362749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433696141/2500000000 : ℝ)|^4683 ≤ (265633244263/2500000000000 : ℝ)^3659
        have hw : |(-433696141/2500000000 : ℝ)|=(433696141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1022532161/2000000000 : ℝ)|^4683 ≤ (42374983406727/100000000000000 : ℝ)^3659
        have hw : |(1022532161/2000000000 : ℝ)|=(1022532161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(692956157/1250000000 : ℝ)|^4683 ≤ (9399937362749/20000000000000 : ℝ)^3659
        have hw : |(692956157/1250000000 : ℝ)|=(692956157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260828931/10000000000 : ℝ)*x 0 + (-1529990947/10000000000 : ℝ)*x 1 + (5543648741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260828931/10000000000 : ℝ)^4683 ≤ (21976523764151/50000000000000 : ℝ)^3659 := by
    have hnat : (5260828931 : ℕ)^4683*50000000000000^3659 ≤ 21976523764151^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260828931 10000000000 21976523764151 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529990947/10000000000 : ℝ)^4683 ≤ (4523635616003/50000000000000 : ℝ)^3659 := by
    have hnat : (1529990947 : ℕ)^4683*50000000000000^3659 ≤ 4523635616003^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529990947 10000000000 4523635616003 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5543648741/10000000000 : ℝ)^4683 ≤ (46999681225593/100000000000000 : ℝ)^3659 := by
    have hnat : (5543648741 : ℕ)^4683*100000000000000^3659 ≤ 46999681225593^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543648741 10000000000 46999681225593 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260828931/10000000000 : ℝ), (-1529990947/10000000000 : ℝ), (5543648741/10000000000 : ℝ)] ![(21976523764151/50000000000000 : ℝ), (4523635616003/50000000000000 : ℝ), (46999681225593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260828931/10000000000 : ℝ)|^4683 ≤ (21976523764151/50000000000000 : ℝ)^3659
        have hw : |(5260828931/10000000000 : ℝ)|=(5260828931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1529990947/10000000000 : ℝ)|^4683 ≤ (4523635616003/50000000000000 : ℝ)^3659
        have hw : |(-1529990947/10000000000 : ℝ)|=(1529990947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5543648741/10000000000 : ℝ)|^4683 ≤ (46999681225593/100000000000000 : ℝ)^3659
        have hw : |(5543648741/10000000000 : ℝ)|=(5543648741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260831379/10000000000 : ℝ)*x 0 + (1385911989/2500000000 : ℝ)*x 1 + (-764994307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260831379/10000000000 : ℝ)^4683 ≤ (43953073704587/100000000000000 : ℝ)^3659 := by
    have hnat : (5260831379 : ℕ)^4683*100000000000000^3659 ≤ 43953073704587^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260831379 10000000000 43953073704587 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385911989/2500000000 : ℝ)^4683 ≤ (46999672707731/100000000000000 : ℝ)^3659 := by
    have hnat : (1385911989 : ℕ)^4683*100000000000000^3659 ≤ 46999672707731^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385911989 2500000000 46999672707731 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764994307/5000000000 : ℝ)^4683 ≤ (1809450715097/20000000000000 : ℝ)^3659 := by
    have hnat : (764994307 : ℕ)^4683*20000000000000^3659 ≤ 1809450715097^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764994307 5000000000 1809450715097 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260831379/10000000000 : ℝ), (1385911989/2500000000 : ℝ), (-764994307/5000000000 : ℝ)] ![(43953073704587/100000000000000 : ℝ), (46999672707731/100000000000000 : ℝ), (1809450715097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260831379/10000000000 : ℝ)|^4683 ≤ (43953073704587/100000000000000 : ℝ)^3659
        have hw : |(5260831379/10000000000 : ℝ)|=(5260831379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385911989/2500000000 : ℝ)|^4683 ≤ (46999672707731/100000000000000 : ℝ)^3659
        have hw : |(1385911989/2500000000 : ℝ)|=(1385911989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764994307/5000000000 : ℝ)|^4683 ≤ (1809450715097/20000000000000 : ℝ)^3659
        have hw : |(-764994307/5000000000 : ℝ)|=(764994307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s1_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526936011/1250000000 : ℝ)*x 0 + (4757438127/10000000000 : ℝ)*x 1 + (465600151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526936011/1250000000 : ℝ)^4683 ≤ (33102331525107/100000000000000 : ℝ)^3659 := by
    have hnat : (526936011 : ℕ)^4683*100000000000000^3659 ≤ 33102331525107^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526936011 1250000000 33102331525107 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4757438127/10000000000 : ℝ)^4683 ≤ (38644125214887/100000000000000 : ℝ)^3659 := by
    have hnat : (4757438127 : ℕ)^4683*100000000000000^3659 ≤ 38644125214887^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4757438127 10000000000 38644125214887 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465600151/1250000000 : ℝ)^4683 ≤ (882923226831/3125000000000 : ℝ)^3659 := by
    have hnat : (465600151 : ℕ)^4683*3125000000000^3659 ≤ 882923226831^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465600151 1250000000 882923226831 3125000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526936011/1250000000 : ℝ), (4757438127/10000000000 : ℝ), (465600151/1250000000 : ℝ)] ![(33102331525107/100000000000000 : ℝ), (38644125214887/100000000000000 : ℝ), (882923226831/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526936011/1250000000 : ℝ)|^4683 ≤ (33102331525107/100000000000000 : ℝ)^3659
        have hw : |(526936011/1250000000 : ℝ)|=(526936011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4757438127/10000000000 : ℝ)|^4683 ≤ (38644125214887/100000000000000 : ℝ)^3659
        have hw : |(4757438127/10000000000 : ℝ)|=(4757438127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(465600151/1250000000 : ℝ)|^4683 ≤ (882923226831/3125000000000 : ℝ)^3659
        have hw : |(465600151/1250000000 : ℝ)|=(465600151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1543/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3597/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (274/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2263/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1543/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3597/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1543/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3597/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1543/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3597/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1543/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3597/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1543/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3597/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1543/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3597/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3597/100000 : ℝ) ^ (4679/1024 : ℝ) ≤ (1260598398267/5000000000000000000 : ℝ) := by
    have hpowers : (3597/100000 : ℝ)^4679 ≤ (1260598398267/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3597 : ℕ)^4679*5000000000000000000^1024 ≤ 1260598398267^1024*100000^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3597 100000 1260598398267 5000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3597/100000 : ℝ)) (X := (1260598398267/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1543/6250 : ℝ) ^ (4679/1024 : ℝ) ≤ (167518983930123387/100000000000000000000 : ℝ) := by
    have hpowers : (1543/6250 : ℝ)^4679 ≤ (167518983930123387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1543 : ℕ)^4679*100000000000000000000^1024 ≤ 167518983930123387^1024*6250^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1543 6250 167518983930123387 100000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1543/6250 : ℝ)) (X := (167518983930123387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001260598398267/2500000000000000000 : ℝ) ≤ (10000001103528537/10000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (2500001260598398267/2500000000000000000 : ℝ)^1024 ≤ (10000001103528537/10000000000000000 : ℝ)^4679 := by
      have hnat : (2500001260598398267 : ℕ)^1024*10000000000000000^4679 ≤ 10000001103528537^4679*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001260598398267 2500000000000000000 10000001103528537 10000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001103528537/10000000000000000 : ℝ)) (X := (2500001260598398267/2500000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100167544195898088727/100000000000000000000 : ℝ) ≤ (1000366431071419/1000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (100167544195898088727/100000000000000000000 : ℝ)^1024 ≤ (1000366431071419/1000000000000000 : ℝ)^4679 := by
      have hnat : (100167544195898088727 : ℕ)^1024*1000000000000000^4679 ≤ 1000366431071419^4679*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100167544195898088727 100000000000000000000 1000366431071419 1000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000366431071419/1000000000000000 : ℝ)) (X := (100167544195898088727/100000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50167518983930123387/50000000000000000000 : ℝ) ≤ (10007327517899843/10000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (50167518983930123387/50000000000000000000 : ℝ)^1024 ≤ (10007327517899843/10000000000000000 : ℝ)^4679 := by
      have hnat : (50167518983930123387 : ℕ)^1024*10000000000000000^4679 ≤ 10007327517899843^4679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50167518983930123387 50000000000000000000 10007327517899843 10000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007327517899843/10000000000000000 : ℝ)) (X := (50167518983930123387/50000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1260598398267/5000000000000000000 : ℝ) ≤ ((42176734032405357237/42182000000000000000 : ℝ)+2*(3663207185653/2109100000000000 : ℝ)*(3597/100000 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (42176734032405357237/42182000000000000000 : ℝ)+2*(3663207185653/2109100000000000 : ℝ)*(3597/100000 : ℝ)=(10000001103528537/10000000000000000 : ℝ) by norm_num, show 1+2*(1260598398267/5000000000000000000 : ℝ)=(2500001260598398267/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(167518983930123387/100000000000000000000 : ℝ)+(1260598398267/5000000000000000000 : ℝ) ≤ ((42176734032405357237/42182000000000000000 : ℝ)+(3663207185653/2109100000000000 : ℝ)*((1543/6250 : ℝ)+(3597/100000 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (42176734032405357237/42182000000000000000 : ℝ)+(3663207185653/2109100000000000 : ℝ)*((1543/6250 : ℝ)+(3597/100000 : ℝ))=(1000366431071419/1000000000000000 : ℝ) by norm_num, show 1+(167518983930123387/100000000000000000000 : ℝ)+(1260598398267/5000000000000000000 : ℝ)=(100167544195898088727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(167518983930123387/100000000000000000000 : ℝ) ≤ ((42176734032405357237/42182000000000000000 : ℝ)+2*(3663207185653/2109100000000000 : ℝ)*(1543/6250 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (42176734032405357237/42182000000000000000 : ℝ)+2*(3663207185653/2109100000000000 : ℝ)*(1543/6250 : ℝ)=(10007327517899843/10000000000000000 : ℝ) by norm_num, show 1+2*(167518983930123387/100000000000000000000 : ℝ)=(50167518983930123387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42176734032405357237/42182000000000000000 : ℝ)*(X 1 0+X 2 0)+(3663207185653/2109100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (3597/100000 : ℝ)) (hi := (1543/6250 : ℝ)) (c := (42176734032405357237/42182000000000000000 : ℝ)) (alpha := (3663207185653/2109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42176734032405357237/42182000000000000000 : ℝ)*(X 0 1+X 2 1)+(3663207185653/2109100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (3597/100000 : ℝ)) (hi := (1543/6250 : ℝ)) (c := (42176734032405357237/42182000000000000000 : ℝ)) (alpha := (3663207185653/2109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42176734032405357237/42182000000000000000 : ℝ)*(X 0 2+X 1 2)+(3663207185653/2109100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (3597/100000 : ℝ)) (hi := (1543/6250 : ℝ)) (c := (42176734032405357237/42182000000000000000 : ℝ)) (alpha := (3663207185653/2109100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43362927/250000000 : ℝ)*X 0 0+(5548711403/10000000000 : ℝ)*X 0 1+(2553839507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42014001/78125000 : ℝ)*X 1 0+(-196595831/1000000000 : ℝ)*X 1 1+(5107678881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344447977/2500000000 : ℝ)*X 2 0+(255383953/500000000 : ℝ)*X 2 1+(-1965958369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((842969349/2000000000 : ℝ)*X 0 0+(928167909/2500000000 : ℝ)*X 0 1+(4769375497/10000000000 : ℝ)*X 0 2+(842969349/2000000000 : ℝ)*X 1 0+(928167909/2500000000 : ℝ)*X 1 1+(4769375497/10000000000 : ℝ)*X 1 2+(842969349/2000000000 : ℝ)*X 2 0+(928167909/2500000000 : ℝ)*X 2 1+(4769375497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-433696141/2500000000 : ℝ)*X 0 0+(1022532161/2000000000 : ℝ)*X 0 1+(692956157/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260828931/10000000000 : ℝ)*X 1 0+(-1529990947/10000000000 : ℝ)*X 1 1+(5543648741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260831379/10000000000 : ℝ)*X 2 0+(1385911989/2500000000 : ℝ)*X 2 1+(-764994307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526936011/1250000000 : ℝ)*X 0 0+(4757438127/10000000000 : ℝ)*X 0 1+(465600151/1250000000 : ℝ)*X 0 2+(526936011/1250000000 : ℝ)*X 1 0+(4757438127/10000000000 : ℝ)*X 1 1+(465600151/1250000000 : ℝ)*X 1 2+(526936011/1250000000 : ℝ)*X 2 0+(4757438127/10000000000 : ℝ)*X 2 1+(465600151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (659098161082034275421385147/263637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114233/625000000000 : ℝ)*(base1) + (770162433/100000000000000 : ℝ)*(base19) + (169351161/25000000000000 : ℝ)*(base23) + (89615301/100000000000000 : ℝ)*(upper3) + (20636961/50000000000000 : ℝ)*(upper5) + (401720470703023/25000000000000 : ℝ)*(major0) + (401720470703023/25000000000000 : ℝ)*(major1) + (401720470703023/25000000000000 : ℝ)*(major2) + (226741370685649/10000000000000 : ℝ)*(sp0) + (141713662472253/6250000000000 : ℝ)*(sp1) + (2267418692313837/100000000000000 : ℝ)*(sp2) + (946341500640877/100000000000000 : ℝ)*(sp3) + (5681139271/100000000000000 : ℝ)*(sp4) + (2793653647/100000000000000 : ℝ)*(sp7) + (473172156285903/50000000000000 : ℝ)*(f.failure) + (2267419369718481/100000000000000 : ℝ)*(f.sum) + (93324799235859/105455000000000000000000000000 : ℝ)*base66 + (561455088422272493/150650000000000000000000000000000 : ℝ)*base67 + (1880691547047522493/150650000000000000000000000000000 : ℝ)*base69 + (43874434150922493/150650000000000000000000000000000 : ℝ)*base71 + (132270891891679/105455000000000000000000000000 : ℝ)*base74 + (743104916363722493/150650000000000000000000000000000 : ℝ)*base75 + (769127509797122493/150650000000000000000000000000000 : ℝ)*base77 + (79956056814477507/150650000000000000000000000000000 : ℝ)*base80 + (99783443841679/26363750000000000000000000000 : ℝ)*base81 + (32328289/5000000000000000000000 : ℝ)*base89 + (32328289/5000000000000000000000 : ℝ)*base91 + (32328289/5000000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53135659310442164522511/6590937500000000000000000000 : ℝ) := by norm_num
    linear_combination (597689579/100000000000000 : ℝ)*(base19) + (438184999/25000000000000 : ℝ)*(base23) + (5450739/6250000000000 : ℝ)*(lower2) + (146858371/100000000000000 : ℝ)*(upper3) + (1451171/500000000000 : ℝ)*(upper5) + (1644325286686687/100000000000000 : ℝ)*(major0) + (1644325286686687/100000000000000 : ℝ)*(major1) + (1644325286686687/100000000000000 : ℝ)*(major2) + (10846928453/100000000000000 : ℝ)*(sp2) + (45091293/25000000000000 : ℝ)*(sp3) + (1160127184904129/50000000000000 : ℝ)*(sp4) + (58006344302967/2500000000000 : ℝ)*(sp5) + (232024177013981/10000000000000 : ℝ)*(sp6) + (30262367327157/3125000000000 : ℝ)*(sp7) + (968395934834197/100000000000000 : ℝ)*(f.failure) + (1160127184904129/50000000000000 : ℝ)*(f.sum) + (259650007909911/105455000000000000000000000000 : ℝ)*base65 + (6646278384941889117/602600000000000000000000000000000 : ℝ)*base67 + (1050406248482510883/602600000000000000000000000000000 : ℝ)*base70 + (1808957984216689117/602600000000000000000000000000000 : ℝ)*base71 + (862775864088211/105455000000000000000000000000 : ℝ)*base73 + (2834238334845710883/602600000000000000000000000000000 : ℝ)*base76 + (1778877361791710883/602600000000000000000000000000000 : ℝ)*base78 + (1701888228331889117/602600000000000000000000000000000 : ℝ)*base79 + (61244810295583/52727500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44118011/10000000000000000000000 : ℝ)*base89 + (44118011/10000000000000000000000 : ℝ)*base91 + (44118011/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1591_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1543/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3597/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (274/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2263/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1591_s2_0 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1751270687/10000000000 : ℝ)*x 0 + (684424701/1250000000 : ℝ)*x 1 + (1292516567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1751270687/10000000000 : ℝ)^4683 ≤ (2150947068443/20000000000000 : ℝ)^3659 := by
    have hnat : (1751270687 : ℕ)^4683*20000000000000^3659 ≤ 2150947068443^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751270687 10000000000 2150947068443 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684424701/1250000000 : ℝ)^4683 ≤ (23130191410043/50000000000000 : ℝ)^3659 := by
    have hnat : (684424701 : ℕ)^4683*50000000000000^3659 ≤ 23130191410043^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684424701 1250000000 23130191410043 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292516567/2500000000 : ℝ)^4683 ≤ (21492440911473/50000000000000 : ℝ)^3659 := by
    have hnat : (1292516567 : ℕ)^4683*50000000000000^3659 ≤ 21492440911473^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292516567 2500000000 21492440911473 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1751270687/10000000000 : ℝ), (684424701/1250000000 : ℝ), (1292516567/2500000000 : ℝ)] ![(2150947068443/20000000000000 : ℝ), (23130191410043/50000000000000 : ℝ), (21492440911473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1751270687/10000000000 : ℝ)|^4683 ≤ (2150947068443/20000000000000 : ℝ)^3659
        have hw : |(-1751270687/10000000000 : ℝ)|=(1751270687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684424701/1250000000 : ℝ)|^4683 ≤ (23130191410043/50000000000000 : ℝ)^3659
        have hw : |(684424701/1250000000 : ℝ)|=(684424701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292516567/2500000000 : ℝ)|^4683 ≤ (21492440911473/50000000000000 : ℝ)^3659
        have hw : |(1292516567/2500000000 : ℝ)|=(1292516567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_1 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071771441/2000000000 : ℝ)*x 0 + (-1909173353/10000000000 : ℝ)*x 1 + (258503311/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071771441/2000000000 : ℝ)^4683 ≤ (22501988780791/50000000000000 : ℝ)^3659 := by
    have hnat : (1071771441 : ℕ)^4683*50000000000000^3659 ≤ 22501988780791^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071771441 2000000000 22501988780791 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909173353/10000000000 : ℝ)^4683 ≤ (3002785276051/25000000000000 : ℝ)^3659 := by
    have hnat : (1909173353 : ℕ)^4683*25000000000000^3659 ≤ 3002785276051^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909173353 10000000000 3002785276051 25000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258503311/500000000 : ℝ)^4683 ≤ (42984881312179/100000000000000 : ℝ)^3659 := by
    have hnat : (258503311 : ℕ)^4683*100000000000000^3659 ≤ 42984881312179^3659*500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258503311 500000000 42984881312179 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071771441/2000000000 : ℝ), (-1909173353/10000000000 : ℝ), (258503311/500000000 : ℝ)] ![(22501988780791/50000000000000 : ℝ), (3002785276051/25000000000000 : ℝ), (42984881312179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071771441/2000000000 : ℝ)|^4683 ≤ (22501988780791/50000000000000 : ℝ)^3659
        have hw : |(1071771441/2000000000 : ℝ)|=(1071771441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909173353/10000000000 : ℝ)|^4683 ≤ (3002785276051/25000000000000 : ℝ)^3659
        have hw : |(-1909173353/10000000000 : ℝ)|=(1909173353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258503311/500000000 : ℝ)|^4683 ≤ (42984881312179/100000000000000 : ℝ)^3659
        have hw : |(258503311/500000000 : ℝ)|=(258503311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_2 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669857121/1250000000 : ℝ)*x 0 + (646258317/1250000000 : ℝ)*x 1 + (-477293313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669857121/1250000000 : ℝ)^4683 ≤ (45003975014231/100000000000000 : ℝ)^3659 := by
    have hnat : (669857121 : ℕ)^4683*100000000000000^3659 ≤ 45003975014231^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669857121 1250000000 45003975014231 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646258317/1250000000 : ℝ)^4683 ≤ (42984884674727/100000000000000 : ℝ)^3659 := by
    have hnat : (646258317 : ℕ)^4683*100000000000000^3659 ≤ 42984884674727^3659*1250000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646258317 1250000000 42984884674727 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477293313/2500000000 : ℝ)^4683 ≤ (6005570145479/50000000000000 : ℝ)^3659 := by
    have hnat : (477293313 : ℕ)^4683*50000000000000^3659 ≤ 6005570145479^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477293313 2500000000 6005570145479 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669857121/1250000000 : ℝ), (646258317/1250000000 : ℝ), (-477293313/2500000000 : ℝ)] ![(45003975014231/100000000000000 : ℝ), (42984884674727/100000000000000 : ℝ), (6005570145479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669857121/1250000000 : ℝ)|^4683 ≤ (45003975014231/100000000000000 : ℝ)^3659
        have hw : |(669857121/1250000000 : ℝ)|=(669857121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(646258317/1250000000 : ℝ)|^4683 ≤ (42984884674727/100000000000000 : ℝ)^3659
        have hw : |(646258317/1250000000 : ℝ)|=(646258317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477293313/2500000000 : ℝ)|^4683 ≤ (6005570145479/50000000000000 : ℝ)^3659
        have hw : |(-477293313/2500000000 : ℝ)|=(477293313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_3 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227142537/10000000000 : ℝ)*x 0 + (3873906867/10000000000 : ℝ)*x 1 + (1151368363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227142537/10000000000 : ℝ)^4683 ≤ (33219505746917/100000000000000 : ℝ)^3659 := by
    have hnat : (4227142537 : ℕ)^4683*100000000000000^3659 ≤ 33219505746917^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227142537 10000000000 33219505746917 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3873906867/10000000000 : ℝ)^4683 ≤ (3713637324501/12500000000000 : ℝ)^3659 := by
    have hnat : (3873906867 : ℕ)^4683*12500000000000^3659 ≤ 3713637324501^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3873906867 10000000000 3713637324501 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151368363/2500000000 : ℝ)^4683 ≤ (37071395638461/100000000000000 : ℝ)^3659 := by
    have hnat : (1151368363 : ℕ)^4683*100000000000000^3659 ≤ 37071395638461^3659*2500000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151368363 2500000000 37071395638461 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227142537/10000000000 : ℝ), (3873906867/10000000000 : ℝ), (1151368363/2500000000 : ℝ)] ![(33219505746917/100000000000000 : ℝ), (3713637324501/12500000000000 : ℝ), (37071395638461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227142537/10000000000 : ℝ)|^4683 ≤ (33219505746917/100000000000000 : ℝ)^3659
        have hw : |(4227142537/10000000000 : ℝ)|=(4227142537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3873906867/10000000000 : ℝ)|^4683 ≤ (3713637324501/12500000000000 : ℝ)^3659
        have hw : |(3873906867/10000000000 : ℝ)|=(3873906867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151368363/2500000000 : ℝ)|^4683 ≤ (37071395638461/100000000000000 : ℝ)^3659
        have hw : |(1151368363/2500000000 : ℝ)|=(1151368363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_4 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-875679653/5000000000 : ℝ)*x 0 + (5172462731/10000000000 : ℝ)*x 1 + (5472974603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875679653/5000000000 : ℝ)^4683 ≤ (5377715934737/50000000000000 : ℝ)^3659 := by
    have hnat : (875679653 : ℕ)^4683*50000000000000^3659 ≤ 5377715934737^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875679653 5000000000 5377715934737 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172462731/10000000000 : ℝ)^4683 ≤ (8602076835371/20000000000000 : ℝ)^3659 := by
    have hnat : (5172462731 : ℕ)^4683*20000000000000^3659 ≤ 8602076835371^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172462731 10000000000 8602076835371 20000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472974603/10000000000 : ℝ)^4683 ≤ (184936735761/400000000000 : ℝ)^3659 := by
    have hnat : (5472974603 : ℕ)^4683*400000000000^3659 ≤ 184936735761^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472974603 10000000000 184936735761 400000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-875679653/5000000000 : ℝ), (5172462731/10000000000 : ℝ), (5472974603/10000000000 : ℝ)] ![(5377715934737/50000000000000 : ℝ), (8602076835371/20000000000000 : ℝ), (184936735761/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-875679653/5000000000 : ℝ)|^4683 ≤ (5377715934737/50000000000000 : ℝ)^3659
        have hw : |(-875679653/5000000000 : ℝ)|=(875679653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172462731/10000000000 : ℝ)|^4683 ≤ (8602076835371/20000000000000 : ℝ)^3659
        have hw : |(5172462731/10000000000 : ℝ)|=(5172462731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472974603/10000000000 : ℝ)|^4683 ≤ (184936735761/400000000000 : ℝ)^3659
        have hw : |(5472974603/10000000000 : ℝ)|=(5472974603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_5 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278053197/10000000000 : ℝ)*x 0 + (-321252991/2000000000 : ℝ)*x 1 + (5472974731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278053197/10000000000 : ℝ)^4683 ≤ (44137309642163/100000000000000 : ℝ)^3659 := by
    have hnat : (5278053197 : ℕ)^4683*100000000000000^3659 ≤ 44137309642163^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278053197 10000000000 44137309642163 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321252991/2000000000 : ℝ)^4683 ≤ (481425251121/5000000000000 : ℝ)^3659 := by
    have hnat : (321252991 : ℕ)^4683*5000000000000^3659 ≤ 481425251121^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321252991 2000000000 481425251121 5000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472974731/10000000000 : ℝ)^4683 ≤ (46234185324171/100000000000000 : ℝ)^3659 := by
    have hnat : (5472974731 : ℕ)^4683*100000000000000^3659 ≤ 46234185324171^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472974731 10000000000 46234185324171 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278053197/10000000000 : ℝ), (-321252991/2000000000 : ℝ), (5472974731/10000000000 : ℝ)] ![(44137309642163/100000000000000 : ℝ), (481425251121/5000000000000 : ℝ), (46234185324171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278053197/10000000000 : ℝ)|^4683 ≤ (44137309642163/100000000000000 : ℝ)^3659
        have hw : |(5278053197/10000000000 : ℝ)|=(5278053197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321252991/2000000000 : ℝ)|^4683 ≤ (481425251121/5000000000000 : ℝ)^3659
        have hw : |(-321252991/2000000000 : ℝ)|=(321252991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472974731/10000000000 : ℝ)|^4683 ≤ (46234185324171/100000000000000 : ℝ)^3659
        have hw : |(5472974731/10000000000 : ℝ)|=(5472974731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_6 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278053343/10000000000 : ℝ)*x 0 + (1094594881/2000000000 : ℝ)*x 1 + (-160626521/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278053343/10000000000 : ℝ)^4683 ≤ (44137311204759/100000000000000 : ℝ)^3659 := by
    have hnat : (5278053343 : ℕ)^4683*100000000000000^3659 ≤ 44137311204759^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278053343 10000000000 44137311204759 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094594881/2000000000 : ℝ)^4683 ≤ (5779272724937/12500000000000 : ℝ)^3659 := by
    have hnat : (1094594881 : ℕ)^4683*12500000000000^3659 ≤ 5779272724937^3659*2000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094594881 2000000000 5779272724937 12500000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160626521/1000000000 : ℝ)^4683 ≤ (9628506978757/100000000000000 : ℝ)^3659 := by
    have hnat : (160626521 : ℕ)^4683*100000000000000^3659 ≤ 9628506978757^3659*1000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160626521 1000000000 9628506978757 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278053343/10000000000 : ℝ), (1094594881/2000000000 : ℝ), (-160626521/1000000000 : ℝ)] ![(44137311204759/100000000000000 : ℝ), (5779272724937/12500000000000 : ℝ), (9628506978757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278053343/10000000000 : ℝ)|^4683 ≤ (44137311204759/100000000000000 : ℝ)^3659
        have hw : |(5278053343/10000000000 : ℝ)|=(5278053343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094594881/2000000000 : ℝ)|^4683 ≤ (5779272724937/12500000000000 : ℝ)^3659
        have hw : |(1094594881/2000000000 : ℝ)|=(1094594881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160626521/1000000000 : ℝ)|^4683 ≤ (9628506978757/100000000000000 : ℝ)^3659
        have hw : |(-160626521/1000000000 : ℝ)|=(160626521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1591_s2_7 (p : ℝ) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113677731/5000000000 : ℝ)*x 0 + (4599732407/10000000000 : ℝ)*x 1 + (3879712217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113677731/5000000000 : ℝ)^4683 ≤ (16610823671933/50000000000000 : ℝ)^3659 := by
    have hnat : (2113677731 : ℕ)^4683*50000000000000^3659 ≤ 16610823671933^3659*5000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113677731 5000000000 16610823671933 50000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4599732407/10000000000 : ℝ)^4683 ≤ (37012261051371/100000000000000 : ℝ)^3659 := by
    have hnat : (4599732407 : ℕ)^4683*100000000000000^3659 ≤ 37012261051371^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599732407 10000000000 37012261051371 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3879712217/10000000000 : ℝ)^4683 ≤ (29766091591383/100000000000000 : ℝ)^3659 := by
    have hnat : (3879712217 : ℕ)^4683*100000000000000^3659 ≤ 29766091591383^3659*10000000000^4683 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879712217 10000000000 29766091591383 100000000000000 4683 3659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4683/1024 : ℝ)) 4683 3659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113677731/5000000000 : ℝ), (4599732407/10000000000 : ℝ), (3879712217/10000000000 : ℝ)] ![(16610823671933/50000000000000 : ℝ), (37012261051371/100000000000000 : ℝ), (29766091591383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113677731/5000000000 : ℝ)|^4683 ≤ (16610823671933/50000000000000 : ℝ)^3659
        have hw : |(2113677731/5000000000 : ℝ)|=(2113677731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4599732407/10000000000 : ℝ)|^4683 ≤ (37012261051371/100000000000000 : ℝ)^3659
        have hw : |(4599732407/10000000000 : ℝ)|=(4599732407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3879712217/10000000000 : ℝ)|^4683 ≤ (29766091591383/100000000000000 : ℝ)^3659
        have hw : |(3879712217/10000000000 : ℝ)|=(3879712217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1591_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2263/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (274/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2529/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16581/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2263/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (274/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2263/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (274/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2263/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (274/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2263/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (274/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2263/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (274/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2263/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (274/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (274/3125 : ℝ) ^ (4679/1024 : ℝ) ≤ (739141279600461/50000000000000000000 : ℝ) := by
    have hpowers : (274/3125 : ℝ)^4679 ≤ (739141279600461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (274 : ℕ)^4679*50000000000000000000^1024 ≤ 739141279600461^1024*3125^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        274 3125 739141279600461 50000000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (274/3125 : ℝ)) (X := (739141279600461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2263/12500 : ℝ) ^ (4679/1024 : ℝ) ≤ (2537479565690969/6250000000000000000 : ℝ) := by
    have hpowers : (2263/12500 : ℝ)^4679 ≤ (2537479565690969/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^4679*6250000000000000000^1024 ≤ 2537479565690969^1024*12500^4679 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 12500 2537479565690969 6250000000000000000 4679 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/12500 : ℝ)) (X := (2537479565690969/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000739141279600461/25000000000000000000 : ℝ) ≤ (5000032351867079/5000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (25000739141279600461/25000000000000000000 : ℝ)^1024 ≤ (5000032351867079/5000000000000000 : ℝ)^4679 := by
      have hnat : (25000739141279600461 : ℕ)^1024*5000000000000000^4679 ≤ 5000032351867079^4679*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000739141279600461 25000000000000000000 5000032351867079 5000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032351867079/5000000000000000 : ℝ)) (X := (25000739141279600461/25000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021038977805128213/50000000000000000000 : ℝ) ≤ (2500230181379591/2500000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (50021038977805128213/50000000000000000000 : ℝ)^1024 ≤ (2500230181379591/2500000000000000 : ℝ)^4679 := by
      have hnat : (50021038977805128213 : ℕ)^1024*2500000000000000^4679 ≤ 2500230181379591^4679*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021038977805128213 50000000000000000000 2500230181379591 2500000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500230181379591/2500000000000000 : ℝ)) (X := (50021038977805128213/50000000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127537479565690969/3125000000000000000 : ℝ) ≤ (1000177674730257/1000000000000000 : ℝ) ^ (4679/1024 : ℝ) := by
    have hpowers : (3127537479565690969/3125000000000000000 : ℝ)^1024 ≤ (1000177674730257/1000000000000000 : ℝ)^4679 := by
      have hnat : (3127537479565690969 : ℕ)^1024*1000000000000000^4679 ≤ 1000177674730257^4679*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127537479565690969 3125000000000000000 1000177674730257 1000000000000000 1024 4679 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000177674730257/1000000000000000 : ℝ)) (X := (3127537479565690969/3125000000000000000 : ℝ)) (by norm_num) 4679 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(739141279600461/50000000000000000000 : ℝ) ≤ ((5834099554753391417/5835000000000000000 : ℝ)+2*(428010892103/466800000000000 : ℝ)*(274/3125 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (5834099554753391417/5835000000000000000 : ℝ)+2*(428010892103/466800000000000 : ℝ)*(274/3125 : ℝ)=(5000032351867079/5000000000000000 : ℝ) by norm_num, show 1+2*(739141279600461/50000000000000000000 : ℝ)=(25000739141279600461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2537479565690969/6250000000000000000 : ℝ)+(739141279600461/50000000000000000000 : ℝ) ≤ ((5834099554753391417/5835000000000000000 : ℝ)+(428010892103/466800000000000 : ℝ)*((2263/12500 : ℝ)+(274/3125 : ℝ)))^(4679/1024 : ℝ) := by
    rw [show (5834099554753391417/5835000000000000000 : ℝ)+(428010892103/466800000000000 : ℝ)*((2263/12500 : ℝ)+(274/3125 : ℝ))=(2500230181379591/2500000000000000 : ℝ) by norm_num, show 1+(2537479565690969/6250000000000000000 : ℝ)+(739141279600461/50000000000000000000 : ℝ)=(50021038977805128213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2537479565690969/6250000000000000000 : ℝ) ≤ ((5834099554753391417/5835000000000000000 : ℝ)+2*(428010892103/466800000000000 : ℝ)*(2263/12500 : ℝ))^(4679/1024 : ℝ) := by
    rw [show (5834099554753391417/5835000000000000000 : ℝ)+2*(428010892103/466800000000000 : ℝ)*(2263/12500 : ℝ)=(1000177674730257/1000000000000000 : ℝ) by norm_num, show 1+2*(2537479565690969/6250000000000000000 : ℝ)=(3127537479565690969/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5834099554753391417/5835000000000000000 : ℝ)*(X 1 0+X 2 0)+(428010892103/466800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (274/3125 : ℝ)) (hi := (2263/12500 : ℝ)) (c := (5834099554753391417/5835000000000000000 : ℝ)) (alpha := (428010892103/466800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5834099554753391417/5835000000000000000 : ℝ)*(X 0 1+X 2 1)+(428010892103/466800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (274/3125 : ℝ)) (hi := (2263/12500 : ℝ)) (c := (5834099554753391417/5835000000000000000 : ℝ)) (alpha := (428010892103/466800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5834099554753391417/5835000000000000000 : ℝ)*(X 0 2+X 1 2)+(428010892103/466800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4679/1024 : ℝ)) (lo := (274/3125 : ℝ)) (hi := (2263/12500 : ℝ)) (c := (5834099554753391417/5835000000000000000 : ℝ)) (alpha := (428010892103/466800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1751270687/10000000000 : ℝ)*X 0 0+(684424701/1250000000 : ℝ)*X 0 1+(1292516567/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071771441/2000000000 : ℝ)*X 1 0+(-1909173353/10000000000 : ℝ)*X 1 1+(258503311/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669857121/1250000000 : ℝ)*X 2 0+(646258317/1250000000 : ℝ)*X 2 1+(-477293313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4227142537/10000000000 : ℝ)*X 0 0+(3873906867/10000000000 : ℝ)*X 0 1+(1151368363/2500000000 : ℝ)*X 0 2+(4227142537/10000000000 : ℝ)*X 1 0+(3873906867/10000000000 : ℝ)*X 1 1+(1151368363/2500000000 : ℝ)*X 1 2+(4227142537/10000000000 : ℝ)*X 2 0+(3873906867/10000000000 : ℝ)*X 2 1+(1151368363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-875679653/5000000000 : ℝ)*X 0 0+(5172462731/10000000000 : ℝ)*X 0 1+(5472974603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278053197/10000000000 : ℝ)*X 1 0+(-321252991/2000000000 : ℝ)*X 1 1+(5472974731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278053343/10000000000 : ℝ)*X 2 0+(1094594881/2000000000 : ℝ)*X 2 1+(-160626521/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2113677731/5000000000 : ℝ)*X 0 0+(4599732407/10000000000 : ℝ)*X 0 1+(3879712217/10000000000 : ℝ)*X 0 2+(2113677731/5000000000 : ℝ)*X 1 0+(4599732407/10000000000 : ℝ)*X 1 1+(3879712217/10000000000 : ℝ)*X 1 2+(2113677731/5000000000 : ℝ)*X 2 0+(4599732407/10000000000 : ℝ)*X 2 1+(3879712217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1591_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60376946685899950132490151/19450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17273943/3125000000000 : ℝ)*(base19) + (390485571/100000000000000 : ℝ)*(base23) + (9342991/100000000000000 : ℝ)*(lower2) + (31846429/50000000000000 : ℝ)*(upper3) + (24479793/25000000000000 : ℝ)*(upper5) + (464207658647703/20000000000000 : ℝ)*(major0) + (464207658647703/20000000000000 : ℝ)*(major1) + (464207658647703/20000000000000 : ℝ)*(major2) + (1637568173850547/50000000000000 : ℝ)*(sp0) + (818785496799927/25000000000000 : ℝ)*(sp1) + (3275142149480313/100000000000000 : ℝ)*(sp2) + (683465981108433/50000000000000 : ℝ)*(sp3) + (6192264791/100000000000000 : ℝ)*(sp4) + (3961641/200000000000 : ℝ)*(sp7) + (683466971518683/50000000000000 : ℝ)*(f.failure) + (818785634991471/25000000000000 : ℝ)*(f.sum) + (1831511058279/311200000000000000000000000 : ℝ)*base65 + (504448336590640783/38900000000000000000000000000000 : ℝ)*base68 + (460154478228440783/38900000000000000000000000000000 : ℝ)*base70 + (241871254934940783/38900000000000000000000000000000 : ℝ)*base72 + (1320200545097/311200000000000000000000000 : ℝ)*base74 + (275270887926059217/38900000000000000000000000000000 : ℝ)*base75 + (150661843633459217/38900000000000000000000000000000 : ℝ)*base77 + (26543102156140783/38900000000000000000000000000000 : ℝ)*base80 + (5427655269333/1556000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6657429/5000000000000000000000 : ℝ)*base89 + (6657429/5000000000000000000000 : ℝ)*base91 + (6657429/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116977514972855145036204093/24312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46049111/12500000000000 : ℝ)*(base19) + (661206849/100000000000000 : ℝ)*(base23) + (42516279/50000000000000 : ℝ)*(upper3) + (20388567/20000000000000 : ℝ)*(lower4) + (20511151/100000000000000 : ℝ)*(upper5) + (1179125843215279/50000000000000 : ℝ)*(major0) + (1179125843215279/50000000000000 : ℝ)*(major1) + (1179125843215279/50000000000000 : ℝ)*(major2) + (410466491/10000000000000 : ℝ)*(sp1) + (4602459811/100000000000000 : ℝ)*(sp2) + (3327653107853861/100000000000000 : ℝ)*(sp4) + (3327648634796063/100000000000000 : ℝ)*(sp5) + (1663823922093601/50000000000000 : ℝ)*(sp6) + (694425052313383/50000000000000 : ℝ)*(sp7) + (694425052313383/50000000000000 : ℝ)*(f.failure) + (3327653107853861/100000000000000 : ℝ)*(f.sum) + (5320246979683/11670000000000000000000000000 : ℝ)*base66 + (473254484744725719/97250000000000000000000000000000 : ℝ)*base68 + (541128396251725719/97250000000000000000000000000000 : ℝ)*base70 + (409554203430274281/97250000000000000000000000000000 : ℝ)*base71 + (97556133541153/11670000000000000000000000000 : ℝ)*base74 + (21728990059225719/97250000000000000000000000000000 : ℝ)*base76 + (555835788093975719/97250000000000000000000000000000 : ℝ)*base78 + (210056609678475719/97250000000000000000000000000000 : ℝ)*base80 + (61782822916363/11670000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (53083529/5000000000000000000000 : ℝ)*base89 + (53083529/5000000000000000000000 : ℝ)*base91 + (53083529/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1591_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2263/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (274/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1591_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1591_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1591_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1591_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1591_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4679/1024 : ℝ) ≤ p) (hpb : p ≤ (4683/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169798863/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2529/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1591_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

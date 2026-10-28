-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:50.265145+00:00
-- url     : https://prove2.me/submissions/bbabef10-3a1a-48a1-8117-e34646ca070c

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
theorem support_rectangle_w1096_s0_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906455461/10000000000 : ℝ)*x 0 + (303251161/500000000 : ℝ)*x 1 + (4774627091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906455461/10000000000 : ℝ)^8289 ≤ (11067033265327/100000000000000 : ℝ)^6241 := by
    have hnat : (1906455461 : ℕ)^8289*100000000000000^6241 ≤ 11067033265327^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906455461 10000000000 11067033265327 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303251161/500000000 : ℝ)^8289 ≤ (12867921397507/25000000000000 : ℝ)^6241 := by
    have hnat : (303251161 : ℕ)^8289*25000000000000^6241 ≤ 12867921397507^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303251161 500000000 12867921397507 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774627091/10000000000 : ℝ)^8289 ≤ (18730640563483/50000000000000 : ℝ)^6241 := by
    have hnat : (4774627091 : ℕ)^8289*50000000000000^6241 ≤ 18730640563483^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774627091 10000000000 18730640563483 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906455461/10000000000 : ℝ), (303251161/500000000 : ℝ), (4774627091/10000000000 : ℝ)] ![(11067033265327/100000000000000 : ℝ), (12867921397507/25000000000000 : ℝ), (18730640563483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906455461/10000000000 : ℝ)|^8289 ≤ (11067033265327/100000000000000 : ℝ)^6241
        have hw : |(-1906455461/10000000000 : ℝ)|=(1906455461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303251161/500000000 : ℝ)|^8289 ≤ (12867921397507/25000000000000 : ℝ)^6241
        have hw : |(303251161/500000000 : ℝ)|=(303251161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774627091/10000000000 : ℝ)|^8289 ≤ (18730640563483/50000000000000 : ℝ)^6241
        have hw : |(4774627091/10000000000 : ℝ)|=(4774627091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5519384353/10000000000 : ℝ)*x 0 + (-1324165381/5000000000 : ℝ)*x 1 + (2387313557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519384353/10000000000 : ℝ)^8289 ≤ (2838385717107/6250000000000 : ℝ)^6241 := by
    have hnat : (5519384353 : ℕ)^8289*6250000000000^6241 ≤ 2838385717107^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519384353 10000000000 2838385717107 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1324165381/5000000000 : ℝ)^8289 ≤ (1070284196309/6250000000000 : ℝ)^6241 := by
    have hnat : (1324165381 : ℕ)^8289*6250000000000^6241 ≤ 1070284196309^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324165381 5000000000 1070284196309 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387313557/5000000000 : ℝ)^8289 ≤ (37461281366639/100000000000000 : ℝ)^6241 := by
    have hnat : (2387313557 : ℕ)^8289*100000000000000^6241 ≤ 37461281366639^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387313557 5000000000 37461281366639 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519384353/10000000000 : ℝ), (-1324165381/5000000000 : ℝ), (2387313557/5000000000 : ℝ)] ![(2838385717107/6250000000000 : ℝ), (1070284196309/6250000000000 : ℝ), (37461281366639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519384353/10000000000 : ℝ)|^8289 ≤ (2838385717107/6250000000000 : ℝ)^6241
        have hw : |(5519384353/10000000000 : ℝ)|=(5519384353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1324165381/5000000000 : ℝ)|^8289 ≤ (1070284196309/6250000000000 : ℝ)^6241
        have hw : |(-1324165381/5000000000 : ℝ)|=(1324165381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387313557/5000000000 : ℝ)|^8289 ≤ (37461281366639/100000000000000 : ℝ)^6241
        have hw : |(2387313557/5000000000 : ℝ)|=(2387313557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103876903/2000000000 : ℝ)*x 0 + (1193656761/2500000000 : ℝ)*x 1 + (-1324165321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103876903/2000000000 : ℝ)^8289 ≤ (45414173244081/100000000000000 : ℝ)^6241 := by
    have hnat : (1103876903 : ℕ)^8289*100000000000000^6241 ≤ 45414173244081^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103876903 2000000000 45414173244081 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193656761/2500000000 : ℝ)^8289 ≤ (37461280637199/100000000000000 : ℝ)^6241 := by
    have hnat : (1193656761 : ℕ)^8289*100000000000000^6241 ≤ 37461280637199^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193656761 2500000000 37461280637199 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324165321/5000000000 : ℝ)^8289 ≤ (17124546110377/100000000000000 : ℝ)^6241 := by
    have hnat : (1324165321 : ℕ)^8289*100000000000000^6241 ≤ 17124546110377^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324165321 5000000000 17124546110377 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103876903/2000000000 : ℝ), (1193656761/2500000000 : ℝ), (-1324165321/5000000000 : ℝ)] ![(45414173244081/100000000000000 : ℝ), (37461280637199/100000000000000 : ℝ), (17124546110377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103876903/2000000000 : ℝ)|^8289 ≤ (45414173244081/100000000000000 : ℝ)^6241
        have hw : |(1103876903/2000000000 : ℝ)|=(1103876903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193656761/2500000000 : ℝ)|^8289 ≤ (37461280637199/100000000000000 : ℝ)^6241
        have hw : |(1193656761/2500000000 : ℝ)|=(1193656761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1324165321/5000000000 : ℝ)|^8289 ≤ (17124546110377/100000000000000 : ℝ)^6241
        have hw : |(-1324165321/5000000000 : ℝ)|=(1324165321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840947467/2000000000 : ℝ)*x 0 + (1561653319/5000000000 : ℝ)*x 1 + (708421749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840947467/2000000000 : ℝ)^8289 ≤ (494410689711/1562500000000 : ℝ)^6241 := by
    have hnat : (840947467 : ℕ)^8289*1562500000000^6241 ≤ 494410689711^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840947467 2000000000 494410689711 1562500000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561653319/5000000000 : ℝ)^8289 ≤ (21319211085201/100000000000000 : ℝ)^6241 := by
    have hnat : (1561653319 : ℕ)^8289*100000000000000^6241 ≤ 21319211085201^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561653319 5000000000 21319211085201 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708421749/1250000000 : ℝ)^8289 ≤ (940770095109/2000000000000 : ℝ)^6241 := by
    have hnat : (708421749 : ℕ)^8289*2000000000000^6241 ≤ 940770095109^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708421749 1250000000 940770095109 2000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840947467/2000000000 : ℝ), (1561653319/5000000000 : ℝ), (708421749/1250000000 : ℝ)] ![(494410689711/1562500000000 : ℝ), (21319211085201/100000000000000 : ℝ), (940770095109/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840947467/2000000000 : ℝ)|^8289 ≤ (494410689711/1562500000000 : ℝ)^6241
        have hw : |(840947467/2000000000 : ℝ)|=(840947467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1561653319/5000000000 : ℝ)|^8289 ≤ (21319211085201/100000000000000 : ℝ)^6241
        have hw : |(1561653319/5000000000 : ℝ)|=(1561653319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708421749/1250000000 : ℝ)|^8289 ≤ (940770095109/2000000000000 : ℝ)^6241
        have hw : |(708421749/1250000000 : ℝ)|=(708421749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-382347719/2000000000 : ℝ)*x 0 + (4807935911/10000000000 : ℝ)*x 1 + (753818299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382347719/2000000000 : ℝ)^8289 ≤ (2221556912451/20000000000000 : ℝ)^6241 := by
    have hnat : (382347719 : ℕ)^8289*20000000000000^6241 ≤ 2221556912451^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382347719 2000000000 2221556912451 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4807935911/10000000000 : ℝ)^8289 ≤ (7561754883187/20000000000000 : ℝ)^6241 := by
    have hnat : (4807935911 : ℕ)^8289*20000000000000^6241 ≤ 7561754883187^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807935911 10000000000 7561754883187 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753818299/1250000000 : ℝ)^8289 ≤ (51083441002029/100000000000000 : ℝ)^6241 := by
    have hnat : (753818299 : ℕ)^8289*100000000000000^6241 ≤ 51083441002029^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753818299 1250000000 51083441002029 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382347719/2000000000 : ℝ), (4807935911/10000000000 : ℝ), (753818299/1250000000 : ℝ)] ![(2221556912451/20000000000000 : ℝ), (7561754883187/20000000000000 : ℝ), (51083441002029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382347719/2000000000 : ℝ)|^8289 ≤ (2221556912451/20000000000000 : ℝ)^6241
        have hw : |(-382347719/2000000000 : ℝ)|=(382347719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4807935911/10000000000 : ℝ)|^8289 ≤ (7561754883187/20000000000000 : ℝ)^6241
        have hw : |(4807935911/10000000000 : ℝ)|=(4807935911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753818299/1250000000 : ℝ)|^8289 ≤ (51083441002029/100000000000000 : ℝ)^6241
        have hw : |(753818299/1250000000 : ℝ)|=(753818299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168989149/10000000000 : ℝ)*x 0 + (-139241323/1000000000 : ℝ)*x 1 + (6030546507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168989149/10000000000 : ℝ)^8289 ≤ (5203181314927/12500000000000 : ℝ)^6241 := by
    have hnat : (5168989149 : ℕ)^8289*12500000000000^6241 ≤ 5203181314927^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168989149 10000000000 5203181314927 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139241323/1000000000 : ℝ)^8289 ≤ (3645553586483/50000000000000 : ℝ)^6241 := by
    have hnat : (139241323 : ℕ)^8289*50000000000000^6241 ≤ 3645553586483^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139241323 1000000000 3645553586483 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6030546507/10000000000 : ℝ)^8289 ≤ (12770860573959/25000000000000 : ℝ)^6241 := by
    have hnat : (6030546507 : ℕ)^8289*25000000000000^6241 ≤ 12770860573959^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6030546507 10000000000 12770860573959 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168989149/10000000000 : ℝ), (-139241323/1000000000 : ℝ), (6030546507/10000000000 : ℝ)] ![(5203181314927/12500000000000 : ℝ), (3645553586483/50000000000000 : ℝ), (12770860573959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168989149/10000000000 : ℝ)|^8289 ≤ (5203181314927/12500000000000 : ℝ)^6241
        have hw : |(5168989149/10000000000 : ℝ)|=(5168989149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139241323/1000000000 : ℝ)|^8289 ≤ (3645553586483/50000000000000 : ℝ)^6241
        have hw : |(-139241323/1000000000 : ℝ)|=(139241323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6030546507/10000000000 : ℝ)|^8289 ≤ (12770860573959/25000000000000 : ℝ)^6241
        have hw : |(6030546507/10000000000 : ℝ)|=(6030546507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (103379803/200000000 : ℝ)*x 0 + (3015273357/5000000000 : ℝ)*x 1 + (-278482271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103379803/200000000 : ℝ)^8289 ≤ (41625461225617/100000000000000 : ℝ)^6241 := by
    have hnat : (103379803 : ℕ)^8289*100000000000000^6241 ≤ 41625461225617^6241*200000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103379803 200000000 41625461225617 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015273357/5000000000 : ℝ)^8289 ≤ (51083444624687/100000000000000 : ℝ)^6241 := by
    have hnat : (3015273357 : ℕ)^8289*100000000000000^6241 ≤ 51083444624687^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015273357 5000000000 51083444624687 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278482271/2000000000 : ℝ)^8289 ≤ (364554706653/5000000000000 : ℝ)^6241 := by
    have hnat : (278482271 : ℕ)^8289*5000000000000^6241 ≤ 364554706653^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278482271 2000000000 364554706653 5000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103379803/200000000 : ℝ), (3015273357/5000000000 : ℝ), (-278482271/2000000000 : ℝ)] ![(41625461225617/100000000000000 : ℝ), (51083444624687/100000000000000 : ℝ), (364554706653/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103379803/200000000 : ℝ)|^8289 ≤ (41625461225617/100000000000000 : ℝ)^6241
        have hw : |(103379803/200000000 : ℝ)|=(103379803/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015273357/5000000000 : ℝ)|^8289 ≤ (51083444624687/100000000000000 : ℝ)^6241
        have hw : |(3015273357/5000000000 : ℝ)|=(3015273357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278482271/2000000000 : ℝ)|^8289 ≤ (364554706653/5000000000000 : ℝ)^6241
        have hw : |(-278482271/2000000000 : ℝ)|=(278482271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s0_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1053787619/2500000000 : ℝ)*x 0 + (5601704523/10000000000 : ℝ)*x 1 + (1595639293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053787619/2500000000 : ℝ)^8289 ≤ (15873202171313/50000000000000 : ℝ)^6241 := by
    have hnat : (1053787619 : ℕ)^8289*50000000000000^6241 ≤ 15873202171313^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053787619 2500000000 15873202171313 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5601704523/10000000000 : ℝ)^8289 ≤ (11578994275343/25000000000000 : ℝ)^6241 := by
    have hnat : (5601704523 : ℕ)^8289*25000000000000^6241 ≤ 11578994275343^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601704523 10000000000 11578994275343 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595639293/5000000000 : ℝ)^8289 ≤ (21937618538797/100000000000000 : ℝ)^6241 := by
    have hnat : (1595639293 : ℕ)^8289*100000000000000^6241 ≤ 21937618538797^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595639293 5000000000 21937618538797 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053787619/2500000000 : ℝ), (5601704523/10000000000 : ℝ), (1595639293/5000000000 : ℝ)] ![(15873202171313/50000000000000 : ℝ), (11578994275343/25000000000000 : ℝ), (21937618538797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053787619/2500000000 : ℝ)|^8289 ≤ (15873202171313/50000000000000 : ℝ)^6241
        have hw : |(1053787619/2500000000 : ℝ)|=(1053787619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5601704523/10000000000 : ℝ)|^8289 ≤ (11578994275343/25000000000000 : ℝ)^6241
        have hw : |(5601704523/10000000000 : ℝ)|=(5601704523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595639293/5000000000 : ℝ)|^8289 ≤ (21937618538797/100000000000000 : ℝ)^6241
        have hw : |(1595639293/5000000000 : ℝ)|=(1595639293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (259/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^259 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^259*1^64 ≤ 0^64*1^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (259/64 : ℝ) ≤ (613093251969443649/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^259 ≤ (613093251969443649/25000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^259*25000000000000000000^64 ≤ 613093251969443649^64*5^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 613093251969443649 25000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (613093251969443649/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^259 := by
      have hnat : (1 : ℕ)^64*1^259 ≤ 1^259*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25613093251969443649/25000000000000000000 : ℝ) ≤ (10060047616191543/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (25613093251969443649/25000000000000000000 : ℝ)^64 ≤ (10060047616191543/10000000000000000 : ℝ)^259 := by
      have hnat : (25613093251969443649 : ℕ)^64*10000000000000000^259 ≤ 10060047616191543^259*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25613093251969443649 25000000000000000000 10060047616191543 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060047616191543/10000000000000000 : ℝ)) (X := (25613093251969443649/25000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (13113093251969443649/12500000000000000000 : ℝ) ≤ (5060047616191543/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (13113093251969443649/12500000000000000000 : ℝ)^64 ≤ (5060047616191543/5000000000000000 : ℝ)^259 := by
      have hnat : (13113093251969443649 : ℕ)^64*5000000000000000^259 ≤ 5060047616191543^259*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13113093251969443649 12500000000000000000 5060047616191543 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060047616191543/5000000000000000 : ℝ)) (X := (13113093251969443649/12500000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60047616191543/4000000000000000 : ℝ)*(0 : ℝ))^(259/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(60047616191543/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(613093251969443649/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60047616191543/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(259/64 : ℝ) := by
    rw [show (1 : ℝ)+(60047616191543/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060047616191543/10000000000000000 : ℝ) by norm_num, show 1+(613093251969443649/25000000000000000000 : ℝ)+(0 : ℝ)=(25613093251969443649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(613093251969443649/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60047616191543/4000000000000000 : ℝ)*(2/5 : ℝ))^(259/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(60047616191543/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060047616191543/5000000000000000 : ℝ) by norm_num, show 1+2*(613093251969443649/25000000000000000000 : ℝ)=(13113093251969443649/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60047616191543/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60047616191543/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60047616191543/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60047616191543/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60047616191543/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60047616191543/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1906455461/10000000000 : ℝ)*X 0 0+(303251161/500000000 : ℝ)*X 0 1+(4774627091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5519384353/10000000000 : ℝ)*X 1 0+(-1324165381/5000000000 : ℝ)*X 1 1+(2387313557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103876903/2000000000 : ℝ)*X 2 0+(1193656761/2500000000 : ℝ)*X 2 1+(-1324165321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840947467/2000000000 : ℝ)*X 0 0+(1561653319/5000000000 : ℝ)*X 0 1+(708421749/1250000000 : ℝ)*X 0 2+(840947467/2000000000 : ℝ)*X 1 0+(1561653319/5000000000 : ℝ)*X 1 1+(708421749/1250000000 : ℝ)*X 1 2+(840947467/2000000000 : ℝ)*X 2 0+(1561653319/5000000000 : ℝ)*X 2 1+(708421749/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-382347719/2000000000 : ℝ)*X 0 0+(4807935911/10000000000 : ℝ)*X 0 1+(753818299/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168989149/10000000000 : ℝ)*X 1 0+(-139241323/1000000000 : ℝ)*X 1 1+(6030546507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103379803/200000000 : ℝ)*X 2 0+(3015273357/5000000000 : ℝ)*X 2 1+(-278482271/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053787619/2500000000 : ℝ)*X 0 0+(5601704523/10000000000 : ℝ)*X 0 1+(1595639293/5000000000 : ℝ)*X 0 2+(1053787619/2500000000 : ℝ)*X 1 0+(5601704523/10000000000 : ℝ)*X 1 1+(1595639293/5000000000 : ℝ)*X 1 2+(1053787619/2500000000 : ℝ)*X 2 0+(5601704523/10000000000 : ℝ)*X 2 1+(1595639293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103634211230366702890989/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7727183/50000000000000 : ℝ)*(base1) + (268172631/50000000000000 : ℝ)*(base19) + (510514493/100000000000000 : ℝ)*(base23) + (9715329/20000000000000 : ℝ)*(base24) + (31403779/25000000000000 : ℝ)*(upper3) + (584015866817159/100000000000000 : ℝ)*(major0) + (584015866817159/100000000000000 : ℝ)*(major1) + (584015866817159/100000000000000 : ℝ)*(major2) + (154991519809719/20000000000000 : ℝ)*(sp0) + (774958234019521/100000000000000 : ℝ)*(sp1) + (154991642254729/20000000000000 : ℝ)*(sp2) + (196535954739409/50000000000000 : ℝ)*(sp3) + (593385277/50000000000000 : ℝ)*(sp4) + (310159/32000000000 : ℝ)*(sp7) + (393072894180059/100000000000000 : ℝ)*(f.failure) + (774958770364783/100000000000000 : ℝ)*(f.sum) + (232905982086337/200000000000000000000000000000 : ℝ)*base65 + (42279338113663/400000000000000000000000000000 : ℝ)*base68 + (772201295486337/400000000000000000000000000000 : ℝ)*base69 + (273825725886337/400000000000000000000000000000 : ℝ)*base71 + (337399801686337/200000000000000000000000000000 : ℝ)*base73 + (68944336913663/400000000000000000000000000000 : ℝ)*base76 + (1019164821086337/400000000000000000000000000000 : ℝ)*base77 + (828074747486337/400000000000000000000000000000 : ℝ)*base79 + (1208522679886337/200000000000000000000000000000 : ℝ)*base81 + (1029427/2500000000000000000000 : ℝ)*base90 + (1029427/2500000000000000000000 : ℝ)*base92 + (1029427/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173191659692336610375849/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444415241/100000000000000 : ℝ)*(base23) + (167646611/50000000000000 : ℝ)*(base39) + (9406089/100000000000000 : ℝ)*(upper3) + (19509173/50000000000000 : ℝ)*(upper4) + (186341297/100000000000000 : ℝ)*(upper5) + (154098167642349/25000000000000 : ℝ)*(major0) + (154098167642349/25000000000000 : ℝ)*(major1) + (308196167638087/50000000000000 : ℝ)*(major2) + (265171621/50000000000000 : ℝ)*(sp2) + (2573551/10000000000000 : ℝ)*(sp3) + (408960394949333/50000000000000 : ℝ)*(sp4) + (408960394949333/50000000000000 : ℝ)*(sp5) + (408960075216703/50000000000000 : ℝ)*(sp6) + (414864132480833/100000000000000 : ℝ)*(sp7) + (207432079108171/50000000000000 : ℝ)*(f.failure) + (817921125191889/100000000000000 : ℝ)*(f.sum) + (175171543718549/40000000000000000000000000000 : ℝ)*base66 + (502764941098241/200000000000000000000000000000 : ℝ)*base67 + (48903589454507/100000000000000000000000000000 : ℝ)*base69 + (381645024301759/200000000000000000000000000000 : ℝ)*base72 + (1675294558549/40000000000000000000000000000 : ℝ)*base74 + (34931069545493/100000000000000000000000000000 : ℝ)*base76 + (315359386345493/100000000000000000000000000000 : ℝ)*base78 + (649304054645493/100000000000000000000000000000 : ℝ)*base80 + (86647875745493/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6657763/1250000000000000000000 : ℝ)*base90 + (6657763/1250000000000000000000 : ℝ)*base92 + (6657763/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1096_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s1_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132152539/625000000 : ℝ)*x 0 + (5713971367/10000000000 : ℝ)*x 1 + (1248126083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132152539/625000000 : ℝ)^8289 ≤ (6349312257967/50000000000000 : ℝ)^6241 := by
    have hnat : (132152539 : ℕ)^8289*50000000000000^6241 ≤ 6349312257967^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132152539 625000000 6349312257967 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5713971367/10000000000 : ℝ)^8289 ≤ (11888215676477/25000000000000 : ℝ)^6241 := by
    have hnat : (5713971367 : ℕ)^8289*25000000000000^6241 ≤ 11888215676477^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713971367 10000000000 11888215676477 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248126083/2500000000 : ℝ)^8289 ≤ (9937128191751/25000000000000 : ℝ)^6241 := by
    have hnat : (1248126083 : ℕ)^8289*25000000000000^6241 ≤ 9937128191751^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248126083 2500000000 9937128191751 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132152539/625000000 : ℝ), (5713971367/10000000000 : ℝ), (1248126083/2500000000 : ℝ)] ![(6349312257967/50000000000000 : ℝ), (11888215676477/25000000000000 : ℝ), (9937128191751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132152539/625000000 : ℝ)|^8289 ≤ (6349312257967/50000000000000 : ℝ)^6241
        have hw : |(-132152539/625000000 : ℝ)|=(132152539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5713971367/10000000000 : ℝ)|^8289 ≤ (11888215676477/25000000000000 : ℝ)^6241
        have hw : |(5713971367/10000000000 : ℝ)|=(5713971367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1248126083/2500000000 : ℝ)|^8289 ≤ (9937128191751/25000000000000 : ℝ)^6241
        have hw : |(1248126083/2500000000 : ℝ)|=(1248126083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (84713319/156250000 : ℝ)*x 0 + (-626177427/2500000000 : ℝ)*x 1 + (998500899/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84713319/156250000 : ℝ)^8289 ≤ (22174626242469/50000000000000 : ℝ)^6241 := by
    have hnat : (84713319 : ℕ)^8289*50000000000000^6241 ≤ 22174626242469^6241*156250000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84713319 156250000 22174626242469 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626177427/2500000000 : ℝ)^8289 ≤ (1987779125661/12500000000000 : ℝ)^6241 := by
    have hnat : (626177427 : ℕ)^8289*12500000000000^6241 ≤ 1987779125661^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626177427 2500000000 1987779125661 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998500899/2000000000 : ℝ)^8289 ≤ (3974851449061/10000000000000 : ℝ)^6241 := by
    have hnat : (998500899 : ℕ)^8289*10000000000000^6241 ≤ 3974851449061^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998500899 2000000000 3974851449061 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84713319/156250000 : ℝ), (-626177427/2500000000 : ℝ), (998500899/2000000000 : ℝ)] ![(22174626242469/50000000000000 : ℝ), (1987779125661/12500000000000 : ℝ), (3974851449061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84713319/156250000 : ℝ)|^8289 ≤ (22174626242469/50000000000000 : ℝ)^6241
        have hw : |(84713319/156250000 : ℝ)|=(84713319/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-626177427/2500000000 : ℝ)|^8289 ≤ (1987779125661/12500000000000 : ℝ)^6241
        have hw : |(-626177427/2500000000 : ℝ)|=(626177427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998500899/2000000000 : ℝ)|^8289 ≤ (3974851449061/10000000000000 : ℝ)^6241
        have hw : |(998500899/2000000000 : ℝ)|=(998500899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710826709/5000000000 : ℝ)*x 0 + (4992503493/10000000000 : ℝ)*x 1 + (-2504709673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710826709/5000000000 : ℝ)^8289 ≤ (11087315842747/25000000000000 : ℝ)^6241 := by
    have hnat : (2710826709 : ℕ)^8289*25000000000000^6241 ≤ 11087315842747^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710826709 5000000000 11087315842747 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992503493/10000000000 : ℝ)^8289 ≤ (4968562986899/12500000000000 : ℝ)^6241 := by
    have hnat : (4992503493 : ℕ)^8289*12500000000000^6241 ≤ 4968562986899^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992503493 10000000000 4968562986899 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504709673/10000000000 : ℝ)^8289 ≤ (3180446542031/20000000000000 : ℝ)^6241 := by
    have hnat : (2504709673 : ℕ)^8289*20000000000000^6241 ≤ 3180446542031^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504709673 10000000000 3180446542031 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710826709/5000000000 : ℝ), (4992503493/10000000000 : ℝ), (-2504709673/10000000000 : ℝ)] ![(11087315842747/25000000000000 : ℝ), (4968562986899/12500000000000 : ℝ), (3180446542031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710826709/5000000000 : ℝ)|^8289 ≤ (11087315842747/25000000000000 : ℝ)^6241
        have hw : |(2710826709/5000000000 : ℝ)|=(2710826709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992503493/10000000000 : ℝ)|^8289 ≤ (4968562986899/12500000000000 : ℝ)^6241
        have hw : |(4992503493/10000000000 : ℝ)|=(4992503493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2504709673/10000000000 : ℝ)|^8289 ≤ (3180446542031/20000000000000 : ℝ)^6241
        have hw : |(-2504709673/10000000000 : ℝ)|=(2504709673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080327869/2500000000 : ℝ)*x 0 + (917085219/2500000000 : ℝ)*x 1 + (1018148063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080327869/2500000000 : ℝ)^8289 ≤ (32812694507431/100000000000000 : ℝ)^6241 := by
    have hnat : (1080327869 : ℕ)^8289*100000000000000^6241 ≤ 32812694507431^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080327869 2500000000 32812694507431 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917085219/2500000000 : ℝ)^8289 ≤ (26396679915819/100000000000000 : ℝ)^6241 := by
    have hnat : (917085219 : ℕ)^8289*100000000000000^6241 ≤ 26396679915819^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917085219 2500000000 26396679915819 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018148063/2000000000 : ℝ)^8289 ≤ (40790625564219/100000000000000 : ℝ)^6241 := by
    have hnat : (1018148063 : ℕ)^8289*100000000000000^6241 ≤ 40790625564219^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018148063 2000000000 40790625564219 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080327869/2500000000 : ℝ), (917085219/2500000000 : ℝ), (1018148063/2000000000 : ℝ)] ![(32812694507431/100000000000000 : ℝ), (26396679915819/100000000000000 : ℝ), (40790625564219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080327869/2500000000 : ℝ)|^8289 ≤ (32812694507431/100000000000000 : ℝ)^6241
        have hw : |(1080327869/2500000000 : ℝ)|=(1080327869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917085219/2500000000 : ℝ)|^8289 ≤ (26396679915819/100000000000000 : ℝ)^6241
        have hw : |(917085219/2500000000 : ℝ)|=(917085219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1018148063/2000000000 : ℝ)|^8289 ≤ (40790625564219/100000000000000 : ℝ)^6241
        have hw : |(1018148063/2000000000 : ℝ)|=(1018148063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115313133/10000000000 : ℝ)*x 0 + (312658089/625000000 : ℝ)*x 1 + (5703744779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115313133/10000000000 : ℝ)^8289 ≤ (2541116900689/20000000000000 : ℝ)^6241 := by
    have hnat : (2115313133 : ℕ)^8289*20000000000000^6241 ≤ 2541116900689^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115313133 10000000000 2541116900689 20000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312658089/625000000 : ℝ)^8289 ≤ (9963638926533/25000000000000 : ℝ)^6241 := by
    have hnat : (312658089 : ℕ)^8289*25000000000000^6241 ≤ 9963638926533^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312658089 625000000 9963638926533 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5703744779/10000000000 : ℝ)^8289 ≤ (23719929885783/50000000000000 : ℝ)^6241 := by
    have hnat : (5703744779 : ℕ)^8289*50000000000000^6241 ≤ 23719929885783^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5703744779 10000000000 23719929885783 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115313133/10000000000 : ℝ), (312658089/625000000 : ℝ), (5703744779/10000000000 : ℝ)] ![(2541116900689/20000000000000 : ℝ), (9963638926533/25000000000000 : ℝ), (23719929885783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115313133/10000000000 : ℝ)|^8289 ≤ (2541116900689/20000000000000 : ℝ)^6241
        have hw : |(-2115313133/10000000000 : ℝ)|=(2115313133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312658089/625000000 : ℝ)|^8289 ≤ (9963638926533/25000000000000 : ℝ)^6241
        have hw : |(312658089/625000000 : ℝ)|=(312658089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5703744779/10000000000 : ℝ)|^8289 ≤ (23719929885783/50000000000000 : ℝ)^6241
        have hw : |(5703744779/10000000000 : ℝ)|=(5703744779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2618556641/5000000000 : ℝ)*x 0 + (-896734571/5000000000 : ℝ)*x 1 + (2851872307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618556641/5000000000 : ℝ)^8289 ≤ (4235564347099/10000000000000 : ℝ)^6241 := by
    have hnat : (2618556641 : ℕ)^8289*10000000000000^6241 ≤ 4235564347099^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618556641 5000000000 4235564347099 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896734571/5000000000 : ℝ)^8289 ≤ (159445290279/1562500000000 : ℝ)^6241 := by
    have hnat : (896734571 : ℕ)^8289*1562500000000^6241 ≤ 159445290279^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896734571 5000000000 159445290279 1562500000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2851872307/5000000000 : ℝ)^8289 ≤ (23719928974433/50000000000000 : ℝ)^6241 := by
    have hnat : (2851872307 : ℕ)^8289*50000000000000^6241 ≤ 23719928974433^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2851872307 5000000000 23719928974433 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618556641/5000000000 : ℝ), (-896734571/5000000000 : ℝ), (2851872307/5000000000 : ℝ)] ![(4235564347099/10000000000000 : ℝ), (159445290279/1562500000000 : ℝ), (23719928974433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618556641/5000000000 : ℝ)|^8289 ≤ (4235564347099/10000000000000 : ℝ)^6241
        have hw : |(2618556641/5000000000 : ℝ)|=(2618556641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-896734571/5000000000 : ℝ)|^8289 ≤ (159445290279/1562500000000 : ℝ)^6241
        have hw : |(-896734571/5000000000 : ℝ)|=(896734571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2851872307/5000000000 : ℝ)|^8289 ≤ (23719928974433/50000000000000 : ℝ)^6241
        have hw : |(2851872307/5000000000 : ℝ)|=(2851872307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2618556651/5000000000 : ℝ)*x 0 + (285187237/500000000 : ℝ)*x 1 + (-3502869/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618556651/5000000000 : ℝ)^8289 ≤ (42355643685821/100000000000000 : ℝ)^6241 := by
    have hnat : (2618556651 : ℕ)^8289*100000000000000^6241 ≤ 42355643685821^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618556651 5000000000 42355643685821 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285187237/500000000 : ℝ)^8289 ≤ (23719929670373/50000000000000 : ℝ)^6241 := by
    have hnat : (285187237 : ℕ)^8289*50000000000000^6241 ≤ 23719929670373^6241*500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285187237 500000000 23719929670373 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3502869/19531250 : ℝ)^8289 ≤ (318890530021/3125000000000 : ℝ)^6241 := by
    have hnat : (3502869 : ℕ)^8289*3125000000000^6241 ≤ 318890530021^6241*19531250^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3502869 19531250 318890530021 3125000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618556651/5000000000 : ℝ), (285187237/500000000 : ℝ), (-3502869/19531250 : ℝ)] ![(42355643685821/100000000000000 : ℝ), (23719929670373/50000000000000 : ℝ), (318890530021/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618556651/5000000000 : ℝ)|^8289 ≤ (42355643685821/100000000000000 : ℝ)^6241
        have hw : |(2618556651/5000000000 : ℝ)|=(2618556651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285187237/500000000 : ℝ)|^8289 ≤ (23719929670373/50000000000000 : ℝ)^6241
        have hw : |(285187237/500000000 : ℝ)|=(285187237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3502869/19531250 : ℝ)|^8289 ≤ (318890530021/3125000000000 : ℝ)^6241
        have hw : |(-3502869/19531250 : ℝ)|=(3502869/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s1_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4323030669/10000000000 : ℝ)*x 0 + (1014195241/2000000000 : ℝ)*x 1 + (461062781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323030669/10000000000 : ℝ)^8289 ≤ (4103754204471/12500000000000 : ℝ)^6241 := by
    have hnat : (4323030669 : ℕ)^8289*12500000000000^6241 ≤ 4103754204471^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323030669 10000000000 4103754204471 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014195241/2000000000 : ℝ)^8289 ≤ (10145107001717/25000000000000 : ℝ)^6241 := by
    have hnat : (1014195241 : ℕ)^8289*25000000000000^6241 ≤ 10145107001717^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014195241 2000000000 10145107001717 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461062781/1250000000 : ℝ)^8289 ≤ (13294769175393/50000000000000 : ℝ)^6241 := by
    have hnat : (461062781 : ℕ)^8289*50000000000000^6241 ≤ 13294769175393^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461062781 1250000000 13294769175393 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323030669/10000000000 : ℝ), (1014195241/2000000000 : ℝ), (461062781/1250000000 : ℝ)] ![(4103754204471/12500000000000 : ℝ), (10145107001717/25000000000000 : ℝ), (13294769175393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323030669/10000000000 : ℝ)|^8289 ≤ (4103754204471/12500000000000 : ℝ)^6241
        have hw : |(4323030669/10000000000 : ℝ)|=(4323030669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014195241/2000000000 : ℝ)|^8289 ≤ (10145107001717/25000000000000 : ℝ)^6241
        have hw : |(1014195241/2000000000 : ℝ)|=(1014195241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461062781/1250000000 : ℝ)|^8289 ≤ (13294769175393/50000000000000 : ℝ)^6241
        have hw : |(461062781/1250000000 : ℝ)|=(461062781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1347/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20649/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/100000 : ℝ) ^ (259/64 : ℝ) ≤ (928733791/50000000000000000000 : ℝ) := by
    have hpowers : (223/100000 : ℝ)^259 ≤ (928733791/50000000000000000000 : ℝ)^64 := by
      have hnat : (223 : ℕ)^259*50000000000000000000^64 ≤ 928733791^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 100000 928733791 50000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/100000 : ℝ)) (X := (928733791/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/12500 : ℝ) ^ (259/64 : ℝ) ≤ (578382885171847137/100000000000000000000 : ℝ) := by
    have hpowers : (3499/12500 : ℝ)^259 ≤ (578382885171847137/100000000000000000000 : ℝ)^64 := by
      have hnat : (3499 : ℕ)^259*100000000000000000000^64 ≤ 578382885171847137^64*12500^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 12500 578382885171847137 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/12500 : ℝ)) (X := (578382885171847137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000928733791/25000000000000000000 : ℝ) ≤ (5000000000045899/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (25000000000928733791/25000000000000000000 : ℝ)^64 ≤ (5000000000045899/5000000000000000 : ℝ)^259 := by
      have hnat : (25000000000928733791 : ℕ)^64*5000000000000000^259 ≤ 5000000000045899^259*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000928733791 25000000000000000000 5000000000045899 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000045899/5000000000000000 : ℝ)) (X := (25000000000928733791/25000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100578382887029314719/100000000000000000000 : ℝ) ≤ (1001426107322587/1000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100578382887029314719/100000000000000000000 : ℝ)^64 ≤ (1001426107322587/1000000000000000 : ℝ)^259 := by
      have hnat : (100578382887029314719 : ℕ)^64*1000000000000000^259 ≤ 1001426107322587^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100578382887029314719 100000000000000000000 1001426107322587 1000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001426107322587/1000000000000000 : ℝ)) (X := (100578382887029314719/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50578382885171847137/50000000000000000000 : ℝ) ≤ (5014261073179971/5000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50578382885171847137/50000000000000000000 : ℝ)^64 ≤ (5014261073179971/5000000000000000 : ℝ)^259 := by
      have hnat : (50578382885171847137 : ℕ)^64*5000000000000000^259 ≤ 5014261073179971^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50578382885171847137 50000000000000000000 5014261073179971 5000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014261073179971/5000000000000000 : ℝ)) (X := (50578382885171847137/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(928733791/50000000000000000000 : ℝ) ≤ ((5553672791278626851/5553800000000000000 : ℝ)+2*(1782634141759/347112500000000 : ℝ)*(223/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (5553672791278626851/5553800000000000000 : ℝ)+2*(1782634141759/347112500000000 : ℝ)*(223/100000 : ℝ)=(5000000000045899/5000000000000000 : ℝ) by norm_num, show 1+2*(928733791/50000000000000000000 : ℝ)=(25000000000928733791/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(578382885171847137/100000000000000000000 : ℝ)+(928733791/50000000000000000000 : ℝ) ≤ ((5553672791278626851/5553800000000000000 : ℝ)+(1782634141759/347112500000000 : ℝ)*((3499/12500 : ℝ)+(223/100000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (5553672791278626851/5553800000000000000 : ℝ)+(1782634141759/347112500000000 : ℝ)*((3499/12500 : ℝ)+(223/100000 : ℝ))=(1001426107322587/1000000000000000 : ℝ) by norm_num, show 1+(578382885171847137/100000000000000000000 : ℝ)+(928733791/50000000000000000000 : ℝ)=(100578382887029314719/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(578382885171847137/100000000000000000000 : ℝ) ≤ ((5553672791278626851/5553800000000000000 : ℝ)+2*(1782634141759/347112500000000 : ℝ)*(3499/12500 : ℝ))^(259/64 : ℝ) := by
    rw [show (5553672791278626851/5553800000000000000 : ℝ)+2*(1782634141759/347112500000000 : ℝ)*(3499/12500 : ℝ)=(5014261073179971/5000000000000000 : ℝ) by norm_num, show 1+2*(578382885171847137/100000000000000000000 : ℝ)=(50578382885171847137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5553672791278626851/5553800000000000000 : ℝ)*(X 1 0+X 2 0)+(1782634141759/347112500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (223/100000 : ℝ)) (hi := (3499/12500 : ℝ)) (c := (5553672791278626851/5553800000000000000 : ℝ)) (alpha := (1782634141759/347112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5553672791278626851/5553800000000000000 : ℝ)*(X 0 1+X 2 1)+(1782634141759/347112500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (223/100000 : ℝ)) (hi := (3499/12500 : ℝ)) (c := (5553672791278626851/5553800000000000000 : ℝ)) (alpha := (1782634141759/347112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5553672791278626851/5553800000000000000 : ℝ)*(X 0 2+X 1 2)+(1782634141759/347112500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (223/100000 : ℝ)) (hi := (3499/12500 : ℝ)) (c := (5553672791278626851/5553800000000000000 : ℝ)) (alpha := (1782634141759/347112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132152539/625000000 : ℝ)*X 0 0+(5713971367/10000000000 : ℝ)*X 0 1+(1248126083/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((84713319/156250000 : ℝ)*X 1 0+(-626177427/2500000000 : ℝ)*X 1 1+(998500899/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710826709/5000000000 : ℝ)*X 2 0+(4992503493/10000000000 : ℝ)*X 2 1+(-2504709673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080327869/2500000000 : ℝ)*X 0 0+(917085219/2500000000 : ℝ)*X 0 1+(1018148063/2000000000 : ℝ)*X 0 2+(1080327869/2500000000 : ℝ)*X 1 0+(917085219/2500000000 : ℝ)*X 1 1+(1018148063/2000000000 : ℝ)*X 1 2+(1080327869/2500000000 : ℝ)*X 2 0+(917085219/2500000000 : ℝ)*X 2 1+(1018148063/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115313133/10000000000 : ℝ)*X 0 0+(312658089/625000000 : ℝ)*X 0 1+(5703744779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2618556641/5000000000 : ℝ)*X 1 0+(-896734571/5000000000 : ℝ)*X 1 1+(2851872307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618556651/5000000000 : ℝ)*X 2 0+(285187237/500000000 : ℝ)*X 2 1+(-3502869/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323030669/10000000000 : ℝ)*X 0 0+(1014195241/2000000000 : ℝ)*X 0 1+(461062781/1250000000 : ℝ)*X 0 2+(4323030669/10000000000 : ℝ)*X 1 0+(1014195241/2000000000 : ℝ)*X 1 1+(461062781/1250000000 : ℝ)*X 1 2+(4323030669/10000000000 : ℝ)*X 2 0+(1014195241/2000000000 : ℝ)*X 2 1+(461062781/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26252327338740977112296943/3471125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49241911/25000000000000 : ℝ)*(base1) + (755007419/50000000000000 : ℝ)*(base19) + (220772749/12500000000000 : ℝ)*(base23) + (7278457/6250000000000 : ℝ)*(upper3) + (7902539/4000000000000 : ℝ)*(upper5) + (6528509690249/625000000000 : ℝ)*(major0) + (6528509690249/625000000000 : ℝ)*(major1) + (6528509690249/625000000000 : ℝ)*(major2) + (1386071149799237/100000000000000 : ℝ)*(sp0) + (1386077371792759/100000000000000 : ℝ)*(sp1) + (277215423125121/20000000000000 : ℝ)*(sp2) + (703040581587811/100000000000000 : ℝ)*(sp3) + (1982244001/25000000000000 : ℝ)*(sp4) + (3188414611/100000000000000 : ℝ)*(sp7) + (351521983485033/50000000000000 : ℝ)*(f.failure) + (1386078881807597/100000000000000 : ℝ)*(f.sum) + (5280496138679/27769000000000000000000000000 : ℝ)*base66 + (2873640414564307/495875000000000000000000000000 : ℝ)*base67 + (1568737479725341/247937500000000000000000000000 : ℝ)*base69 + (978199366600733/123968750000000000000000000000 : ℝ)*base71 + (18505749750723/5553800000000000000000000000 : ℝ)*base74 + (4014244486808807/495875000000000000000000000000 : ℝ)*base75 + (1839146078002591/247937500000000000000000000000 : ℝ)*base77 + (4050674311623057/495875000000000000000000000000 : ℝ)*base79 + (14879792359759/6942250000000000000000000000 : ℝ)*base82 + (13444849/1250000000000000000000 : ℝ)*base90 + (13444849/1250000000000000000000 : ℝ)*base92 + (13444849/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2110215929555445369486954501/277690000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89258381/100000000000000 : ℝ)*(base1) + (847651137/50000000000000 : ℝ)*(base19) + (1715775579/100000000000000 : ℝ)*(base23) + (85949409/50000000000000 : ℝ)*(upper3) + (86154811/50000000000000 : ℝ)*(upper5) + (1074718338873283/100000000000000 : ℝ)*(major0) + (1074718338873283/100000000000000 : ℝ)*(major1) + (1074718338873283/100000000000000 : ℝ)*(major2) + (211780209/3125000000000 : ℝ)*(sp1) + (3601695763/50000000000000 : ℝ)*(sp2) + (285219093572267/20000000000000 : ℝ)*(sp4) + (178260863291749/12500000000000 : ℝ)*(sp5) + (1426086459435849/100000000000000 : ℝ)*(sp6) + (723340956579271/100000000000000 : ℝ)*(sp7) + (180835261459413/25000000000000 : ℝ)*(f.failure) + (713047689301477/50000000000000 : ℝ)*(f.sum) + (38820134011587/17355625000000000000000000000 : ℝ)*base65 + (63801442654860881/79340000000000000000000000000000 : ℝ)*base68 + (428166709533380881/79340000000000000000000000000000 : ℝ)*base70 + (121886317338099119/79340000000000000000000000000000 : ℝ)*base71 + (203042528283639/138845000000000000000000000000 : ℝ)*base74 + (376486742537399119/79340000000000000000000000000000 : ℝ)*base75 + (140475733765339119/79340000000000000000000000000000 : ℝ)*base77 + (141422294240219119/79340000000000000000000000000000 : ℝ)*base79 + (246691053140617/69422500000000000000000000000 : ℝ)*base82 + (1802989/625000000000000000000 : ℝ)*base90 + (1802989/625000000000000000000 : ℝ)*base92 + (1802989/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1347/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20649/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1096_s2_0 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170179511/10000000000 : ℝ)*x 0 + (1379947807/2500000000 : ℝ)*x 1 + (643911159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170179511/10000000000 : ℝ)^8289 ≤ (13145134203159/100000000000000 : ℝ)^6241 := by
    have hnat : (2170179511 : ℕ)^8289*100000000000000^6241 ≤ 13145134203159^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170179511 10000000000 13145134203159 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379947807/2500000000 : ℝ)^8289 ≤ (11354654484921/25000000000000 : ℝ)^6241 := by
    have hnat : (1379947807 : ℕ)^8289*25000000000000^6241 ≤ 11354654484921^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379947807 2500000000 11354654484921 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643911159/1250000000 : ℝ)^8289 ≤ (2589765490253/6250000000000 : ℝ)^6241 := by
    have hnat : (643911159 : ℕ)^8289*6250000000000^6241 ≤ 2589765490253^6241*1250000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643911159 1250000000 2589765490253 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170179511/10000000000 : ℝ), (1379947807/2500000000 : ℝ), (643911159/1250000000 : ℝ)] ![(13145134203159/100000000000000 : ℝ), (11354654484921/25000000000000 : ℝ), (2589765490253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170179511/10000000000 : ℝ)|^8289 ≤ (13145134203159/100000000000000 : ℝ)^6241
        have hw : |(-2170179511/10000000000 : ℝ)|=(2170179511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379947807/2500000000 : ℝ)|^8289 ≤ (11354654484921/25000000000000 : ℝ)^6241
        have hw : |(1379947807/2500000000 : ℝ)|=(1379947807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643911159/1250000000 : ℝ)|^8289 ≤ (2589765490253/6250000000000 : ℝ)^6241
        have hw : |(643911159/1250000000 : ℝ)|=(643911159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_1 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075173437/2000000000 : ℝ)*x 0 + (-236211747/1000000000 : ℝ)*x 1 + (160977823/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075173437/2000000000 : ℝ)^8289 ≤ (21926258790343/50000000000000 : ℝ)^6241 := by
    have hnat : (1075173437 : ℕ)^8289*50000000000000^6241 ≤ 21926258790343^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075173437 2000000000 21926258790343 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236211747/1000000000 : ℝ)^8289 ≤ (459725724809/3125000000000 : ℝ)^6241 := by
    have hnat : (236211747 : ℕ)^8289*3125000000000^6241 ≤ 459725724809^6241*1000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236211747 1000000000 459725724809 3125000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160977823/312500000 : ℝ)^8289 ≤ (41436259211263/100000000000000 : ℝ)^6241 := by
    have hnat : (160977823 : ℕ)^8289*100000000000000^6241 ≤ 41436259211263^6241*312500000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160977823 312500000 41436259211263 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075173437/2000000000 : ℝ), (-236211747/1000000000 : ℝ), (160977823/312500000 : ℝ)] ![(21926258790343/50000000000000 : ℝ), (459725724809/3125000000000 : ℝ), (41436259211263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075173437/2000000000 : ℝ)|^8289 ≤ (21926258790343/50000000000000 : ℝ)^6241
        have hw : |(1075173437/2000000000 : ℝ)|=(1075173437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236211747/1000000000 : ℝ)|^8289 ≤ (459725724809/3125000000000 : ℝ)^6241
        have hw : |(-236211747/1000000000 : ℝ)|=(236211747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160977823/312500000 : ℝ)|^8289 ≤ (41436259211263/100000000000000 : ℝ)^6241
        have hw : |(160977823/312500000 : ℝ)|=(160977823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_2 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687933569/5000000000 : ℝ)*x 0 + (321955649/625000000 : ℝ)*x 1 + (-2362117469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687933569/5000000000 : ℝ)^8289 ≤ (21926258535741/50000000000000 : ℝ)^6241 := by
    have hnat : (2687933569 : ℕ)^8289*50000000000000^6241 ≤ 21926258535741^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687933569 5000000000 21926258535741 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321955649/625000000 : ℝ)^8289 ≤ (4143625972407/10000000000000 : ℝ)^6241 := by
    have hnat : (321955649 : ℕ)^8289*10000000000000^6241 ≤ 4143625972407^6241*625000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321955649 625000000 4143625972407 10000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2362117469/10000000000 : ℝ)^8289 ≤ (919451449101/6250000000000 : ℝ)^6241 := by
    have hnat : (2362117469 : ℕ)^8289*6250000000000^6241 ≤ 919451449101^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362117469 10000000000 919451449101 6250000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687933569/5000000000 : ℝ), (321955649/625000000 : ℝ), (-2362117469/10000000000 : ℝ)] ![(21926258535741/50000000000000 : ℝ), (4143625972407/10000000000000 : ℝ), (919451449101/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687933569/5000000000 : ℝ)|^8289 ≤ (21926258535741/50000000000000 : ℝ)^6241
        have hw : |(2687933569/5000000000 : ℝ)|=(2687933569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321955649/625000000 : ℝ)|^8289 ≤ (4143625972407/10000000000000 : ℝ)^6241
        have hw : |(321955649/625000000 : ℝ)|=(321955649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2362117469/10000000000 : ℝ)|^8289 ≤ (919451449101/6250000000000 : ℝ)^6241
        have hw : |(-2362117469/10000000000 : ℝ)|=(2362117469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_3 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179713237/5000000000 : ℝ)*x 0 + (4011327297/10000000000 : ℝ)*x 1 + (2368920853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179713237/5000000000 : ℝ)^8289 ≤ (33197638016127/100000000000000 : ℝ)^6241 := by
    have hnat : (2179713237 : ℕ)^8289*100000000000000^6241 ≤ 33197638016127^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179713237 5000000000 33197638016127 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011327297/10000000000 : ℝ)^8289 ≤ (29723919814043/100000000000000 : ℝ)^6241 := by
    have hnat : (4011327297 : ℕ)^8289*100000000000000^6241 ≤ 29723919814043^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011327297 10000000000 29723919814043 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368920853/5000000000 : ℝ)^8289 ≤ (9269610539073/25000000000000 : ℝ)^6241 := by
    have hnat : (2368920853 : ℕ)^8289*25000000000000^6241 ≤ 9269610539073^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368920853 5000000000 9269610539073 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179713237/5000000000 : ℝ), (4011327297/10000000000 : ℝ), (2368920853/5000000000 : ℝ)] ![(33197638016127/100000000000000 : ℝ), (29723919814043/100000000000000 : ℝ), (9269610539073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179713237/5000000000 : ℝ)|^8289 ≤ (33197638016127/100000000000000 : ℝ)^6241
        have hw : |(2179713237/5000000000 : ℝ)|=(2179713237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011327297/10000000000 : ℝ)|^8289 ≤ (29723919814043/100000000000000 : ℝ)^6241
        have hw : |(4011327297/10000000000 : ℝ)|=(4011327297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2368920853/5000000000 : ℝ)|^8289 ≤ (9269610539073/25000000000000 : ℝ)^6241
        have hw : |(2368920853/5000000000 : ℝ)|=(2368920853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_4 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542573859/2500000000 : ℝ)*x 0 + (5153913911/10000000000 : ℝ)*x 1 + (5517139667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542573859/2500000000 : ℝ)^8289 ≤ (13146066809219/100000000000000 : ℝ)^6241 := by
    have hnat : (542573859 : ℕ)^8289*100000000000000^6241 ≤ 13146066809219^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542573859 2500000000 13146066809219 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153913911/10000000000 : ℝ)^8289 ≤ (20732145223379/50000000000000 : ℝ)^6241 := by
    have hnat : (5153913911 : ℕ)^8289*50000000000000^6241 ≤ 20732145223379^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153913911 10000000000 20732145223379 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517139667/10000000000 : ℝ)^8289 ≤ (22694821364339/50000000000000 : ℝ)^6241 := by
    have hnat : (5517139667 : ℕ)^8289*50000000000000^6241 ≤ 22694821364339^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517139667 10000000000 22694821364339 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542573859/2500000000 : ℝ), (5153913911/10000000000 : ℝ), (5517139667/10000000000 : ℝ)] ![(13146066809219/100000000000000 : ℝ), (20732145223379/50000000000000 : ℝ), (22694821364339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542573859/2500000000 : ℝ)|^8289 ≤ (13146066809219/100000000000000 : ℝ)^6241
        have hw : |(-542573859/2500000000 : ℝ)|=(542573859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153913911/10000000000 : ℝ)|^8289 ≤ (20732145223379/50000000000000 : ℝ)^6241
        have hw : |(5153913911/10000000000 : ℝ)|=(5153913911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517139667/10000000000 : ℝ)|^8289 ≤ (22694821364339/50000000000000 : ℝ)^6241
        have hw : |(5517139667/10000000000 : ℝ)|=(5517139667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_5 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641329739/5000000000 : ℝ)*x 0 + (-998133809/5000000000 : ℝ)*x 1 + (1379284939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641329739/5000000000 : ℝ)^8289 ≤ (21422788664559/50000000000000 : ℝ)^6241 := by
    have hnat : (2641329739 : ℕ)^8289*50000000000000^6241 ≤ 21422788664559^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641329739 5000000000 21422788664559 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998133809/5000000000 : ℝ)^8289 ≤ (11764778949889/100000000000000 : ℝ)^6241 := by
    have hnat : (998133809 : ℕ)^8289*100000000000000^6241 ≤ 11764778949889^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998133809 5000000000 11764778949889 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379284939/2500000000 : ℝ)^8289 ≤ (22694821850579/50000000000000 : ℝ)^6241 := by
    have hnat : (1379284939 : ℕ)^8289*50000000000000^6241 ≤ 22694821850579^6241*2500000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379284939 2500000000 22694821850579 50000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641329739/5000000000 : ℝ), (-998133809/5000000000 : ℝ), (1379284939/2500000000 : ℝ)] ![(21422788664559/50000000000000 : ℝ), (11764778949889/100000000000000 : ℝ), (22694821850579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641329739/5000000000 : ℝ)|^8289 ≤ (21422788664559/50000000000000 : ℝ)^6241
        have hw : |(2641329739/5000000000 : ℝ)|=(2641329739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998133809/5000000000 : ℝ)|^8289 ≤ (11764778949889/100000000000000 : ℝ)^6241
        have hw : |(-998133809/5000000000 : ℝ)|=(998133809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379284939/2500000000 : ℝ)|^8289 ≤ (22694821850579/50000000000000 : ℝ)^6241
        have hw : |(1379284939/2500000000 : ℝ)|=(1379284939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_6 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5282659651/10000000000 : ℝ)*x 0 + (2758569841/5000000000 : ℝ)*x 1 + (-399253497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282659651/10000000000 : ℝ)^8289 ≤ (5355697399087/12500000000000 : ℝ)^6241 := by
    have hnat : (5282659651 : ℕ)^8289*12500000000000^6241 ≤ 5355697399087^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282659651 10000000000 5355697399087 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758569841/5000000000 : ℝ)^8289 ≤ (45389642892579/100000000000000 : ℝ)^6241 := by
    have hnat : (2758569841 : ℕ)^8289*100000000000000^6241 ≤ 45389642892579^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758569841 5000000000 45389642892579 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399253497/2000000000 : ℝ)^8289 ≤ (1470597238607/12500000000000 : ℝ)^6241 := by
    have hnat : (399253497 : ℕ)^8289*12500000000000^6241 ≤ 1470597238607^6241*2000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399253497 2000000000 1470597238607 12500000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282659651/10000000000 : ℝ), (2758569841/5000000000 : ℝ), (-399253497/2000000000 : ℝ)] ![(5355697399087/12500000000000 : ℝ), (45389642892579/100000000000000 : ℝ), (1470597238607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282659651/10000000000 : ℝ)|^8289 ≤ (5355697399087/12500000000000 : ℝ)^6241
        have hw : |(5282659651/10000000000 : ℝ)|=(5282659651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758569841/5000000000 : ℝ)|^8289 ≤ (45389642892579/100000000000000 : ℝ)^6241
        have hw : |(2758569841/5000000000 : ℝ)|=(2758569841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399253497/2000000000 : ℝ)|^8289 ≤ (1470597238607/12500000000000 : ℝ)^6241
        have hw : |(-399253497/2000000000 : ℝ)|=(399253497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1096_s2_7 (p : ℝ) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359656353/10000000000 : ℝ)*x 0 + (2366333901/5000000000 : ℝ)*x 1 + (4016553341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359656353/10000000000 : ℝ)^8289 ≤ (33199963047629/100000000000000 : ℝ)^6241 := by
    have hnat : (4359656353 : ℕ)^8289*100000000000000^6241 ≤ 33199963047629^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359656353 10000000000 33199963047629 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366333901/5000000000 : ℝ)^8289 ≤ (9256168367863/25000000000000 : ℝ)^6241 := by
    have hnat : (2366333901 : ℕ)^8289*25000000000000^6241 ≤ 9256168367863^6241*5000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366333901 5000000000 9256168367863 25000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016553341/10000000000 : ℝ)^8289 ≤ (29775363467003/100000000000000 : ℝ)^6241 := by
    have hnat : (4016553341 : ℕ)^8289*100000000000000^6241 ≤ 29775363467003^6241*10000000000^8289 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016553341 10000000000 29775363467003 100000000000000 8289 6241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8289/2048 : ℝ)) 8289 6241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359656353/10000000000 : ℝ), (2366333901/5000000000 : ℝ), (4016553341/10000000000 : ℝ)] ![(33199963047629/100000000000000 : ℝ), (9256168367863/25000000000000 : ℝ), (29775363467003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359656353/10000000000 : ℝ)|^8289 ≤ (33199963047629/100000000000000 : ℝ)^6241
        have hw : |(4359656353/10000000000 : ℝ)|=(4359656353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366333901/5000000000 : ℝ)|^8289 ≤ (9256168367863/25000000000000 : ℝ)^6241
        have hw : |(2366333901/5000000000 : ℝ)|=(2366333901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016553341/10000000000 : ℝ)|^8289 ≤ (29775363467003/100000000000000 : ℝ)^6241
        have hw : |(4016553341/10000000000 : ℝ)|=(4016553341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1096_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8857/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4161/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1347/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1347/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1347/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1347/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1347/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1347/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1347/25000 : ℝ) ^ (259/64 : ℝ) ≤ (734930068724453/100000000000000000000 : ℝ) := by
    have hpowers : (1347/25000 : ℝ)^259 ≤ (734930068724453/100000000000000000000 : ℝ)^64 := by
      have hnat : (1347 : ℕ)^259*100000000000000000000^64 ≤ 734930068724453^64*25000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1347 25000 734930068724453 100000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1347/25000 : ℝ)) (X := (734930068724453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hpowhi : (20649/100000 : ℝ) ^ (259/64 : ℝ) ≤ (84421291765820029/50000000000000000000 : ℝ) := by
    have hpowers : (20649/100000 : ℝ)^259 ≤ (84421291765820029/50000000000000000000 : ℝ)^64 := by
      have hnat : (20649 : ℕ)^259*50000000000000000000^64 ≤ 84421291765820029^64*100000^259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20649 100000 84421291765820029 50000000000000000000 259 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20649/100000 : ℝ)) (X := (84421291765820029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000734930068724453/50000000000000000000 : ℝ) ≤ (10000036320667291/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (50000734930068724453/50000000000000000000 : ℝ)^64 ≤ (10000036320667291/10000000000000000 : ℝ)^259 := by
      have hnat : (50000734930068724453 : ℕ)^64*10000000000000000^259 ≤ 10000036320667291^259*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000734930068724453 50000000000000000000 10000036320667291 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036320667291/10000000000000000 : ℝ)) (X := (50000734930068724453/50000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100169577513600364511/100000000000000000000 : ℝ) ≤ (1250523457505417/1250000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (100169577513600364511/100000000000000000000 : ℝ)^64 ≤ (1250523457505417/1250000000000000 : ℝ)^259 := by
      have hnat : (100169577513600364511 : ℕ)^64*1250000000000000^259 ≤ 1250523457505417^259*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100169577513600364511 100000000000000000000 1250523457505417 1250000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250523457505417/1250000000000000 : ℝ)) (X := (100169577513600364511/100000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25084421291765820029/25000000000000000000 : ℝ) ≤ (10008338999419381/10000000000000000 : ℝ) ^ (259/64 : ℝ) := by
    have hpowers : (25084421291765820029/25000000000000000000 : ℝ)^64 ≤ (10008338999419381/10000000000000000 : ℝ)^259 := by
      have hnat : (25084421291765820029 : ℕ)^64*10000000000000000^259 ≤ 10008338999419381^259*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25084421291765820029 25000000000000000000 10008338999419381 10000000000000000 64 259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008338999419381/10000000000000000 : ℝ)) (X := (25084421291765820029/25000000000000000000 : ℝ)) (by norm_num) 259 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(734930068724453/100000000000000000000 : ℝ) ≤ ((50855273152195755677/50870000000000000000 : ℝ)+2*(276755958403/101740000000000 : ℝ)*(1347/25000 : ℝ))^(259/64 : ℝ) := by
    rw [show (50855273152195755677/50870000000000000000 : ℝ)+2*(276755958403/101740000000000 : ℝ)*(1347/25000 : ℝ)=(10000036320667291/10000000000000000 : ℝ) by norm_num, show 1+2*(734930068724453/100000000000000000000 : ℝ)=(50000734930068724453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(84421291765820029/50000000000000000000 : ℝ)+(734930068724453/100000000000000000000 : ℝ) ≤ ((50855273152195755677/50870000000000000000 : ℝ)+(276755958403/101740000000000 : ℝ)*((20649/100000 : ℝ)+(1347/25000 : ℝ)))^(259/64 : ℝ) := by
    rw [show (50855273152195755677/50870000000000000000 : ℝ)+(276755958403/101740000000000 : ℝ)*((20649/100000 : ℝ)+(1347/25000 : ℝ))=(1250523457505417/1250000000000000 : ℝ) by norm_num, show 1+(84421291765820029/50000000000000000000 : ℝ)+(734930068724453/100000000000000000000 : ℝ)=(100169577513600364511/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(84421291765820029/50000000000000000000 : ℝ) ≤ ((50855273152195755677/50870000000000000000 : ℝ)+2*(276755958403/101740000000000 : ℝ)*(20649/100000 : ℝ))^(259/64 : ℝ) := by
    rw [show (50855273152195755677/50870000000000000000 : ℝ)+2*(276755958403/101740000000000 : ℝ)*(20649/100000 : ℝ)=(10008338999419381/10000000000000000 : ℝ) by norm_num, show 1+2*(84421291765820029/50000000000000000000 : ℝ)=(25084421291765820029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50855273152195755677/50870000000000000000 : ℝ)*(X 1 0+X 2 0)+(276755958403/101740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (1347/25000 : ℝ)) (hi := (20649/100000 : ℝ)) (c := (50855273152195755677/50870000000000000000 : ℝ)) (alpha := (276755958403/101740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50855273152195755677/50870000000000000000 : ℝ)*(X 0 1+X 2 1)+(276755958403/101740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (1347/25000 : ℝ)) (hi := (20649/100000 : ℝ)) (c := (50855273152195755677/50870000000000000000 : ℝ)) (alpha := (276755958403/101740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50855273152195755677/50870000000000000000 : ℝ)*(X 0 2+X 1 2)+(276755958403/101740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (259/64 : ℝ)) (lo := (1347/25000 : ℝ)) (hi := (20649/100000 : ℝ)) (c := (50855273152195755677/50870000000000000000 : ℝ)) (alpha := (276755958403/101740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2170179511/10000000000 : ℝ)*X 0 0+(1379947807/2500000000 : ℝ)*X 0 1+(643911159/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075173437/2000000000 : ℝ)*X 1 0+(-236211747/1000000000 : ℝ)*X 1 1+(160977823/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687933569/5000000000 : ℝ)*X 2 0+(321955649/625000000 : ℝ)*X 2 1+(-2362117469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179713237/5000000000 : ℝ)*X 0 0+(4011327297/10000000000 : ℝ)*X 0 1+(2368920853/5000000000 : ℝ)*X 0 2+(2179713237/5000000000 : ℝ)*X 1 0+(4011327297/10000000000 : ℝ)*X 1 1+(2368920853/5000000000 : ℝ)*X 1 2+(2179713237/5000000000 : ℝ)*X 2 0+(4011327297/10000000000 : ℝ)*X 2 1+(2368920853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542573859/2500000000 : ℝ)*X 0 0+(5153913911/10000000000 : ℝ)*X 0 1+(5517139667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641329739/5000000000 : ℝ)*X 1 0+(-998133809/5000000000 : ℝ)*X 1 1+(1379284939/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282659651/10000000000 : ℝ)*X 2 0+(2758569841/5000000000 : ℝ)*X 2 1+(-399253497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359656353/10000000000 : ℝ)*X 0 0+(2366333901/5000000000 : ℝ)*X 0 1+(4016553341/10000000000 : ℝ)*X 0 2+(4359656353/10000000000 : ℝ)*X 1 0+(2366333901/5000000000 : ℝ)*X 1 1+(4016553341/10000000000 : ℝ)*X 1 2+(4359656353/10000000000 : ℝ)*X 2 0+(2366333901/5000000000 : ℝ)*X 2 1+(4016553341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1096_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6892231575709194929659396983/1271750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5362647/1250000000000 : ℝ)*(base19) + (29436563/12500000000000 : ℝ)*(base23) + (28616671/100000000000000 : ℝ)*(upper2) + (67672757/50000000000000 : ℝ)*(upper3) + (29973903/25000000000000 : ℝ)*(upper4) + (1022538389813269/50000000000000 : ℝ)*(major0) + (1022538389813269/50000000000000 : ℝ)*(major1) + (1022538389813269/50000000000000 : ℝ)*(major2) + (33921262739293/1250000000000 : ℝ)*(sp0) + (2713710468723503/100000000000000 : ℝ)*(sp1) + (2713710662242759/100000000000000 : ℝ)*(sp2) + (172054773365831/12500000000000 : ℝ)*(sp3) + (9878591823/100000000000000 : ℝ)*(sp4) + (1073485403/25000000000000 : ℝ)*(sp7) + (68822124043413/5000000000000 : ℝ)*(f.failure) + (2713710897735263/100000000000000 : ℝ)*(f.sum) + (5751191729787/2543500000000000000000000000 : ℝ)*base65 + (33603343877724678113/2543500000000000000000000000000000 : ℝ)*base67 + (31611924674236678113/2543500000000000000000000000000000 : ℝ)*base69 + (27751239009509678113/2543500000000000000000000000000000 : ℝ)*base71 + (4056635307531/1271750000000000000000000000 : ℝ)*base73 + (28092615001902178113/2543500000000000000000000000000000 : ℝ)*base75 + (10275855988125178113/2543500000000000000000000000000000 : ℝ)*base77 + (37484634881064178113/2543500000000000000000000000000000 : ℝ)*base79 + (29257093485631/5087000000000000000000000000 : ℝ)*base81 + (1304989/125000000000000000000 : ℝ)*base90 + (1304989/125000000000000000000 : ℝ)*base92 + (1304989/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1141750035343294740745580091/158968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1424091801/100000000000000 : ℝ)*(base19) + (826539083/50000000000000 : ℝ)*(base23) + (195800737/100000000000000 : ℝ)*(upper3) + (47013531/100000000000000 : ℝ)*(lower4) + (69814063/50000000000000 : ℝ)*(upper5) + (259345831491511/12500000000000 : ℝ)*(major0) + (259345831491511/12500000000000 : ℝ)*(major1) + (259345831491511/12500000000000 : ℝ)*(major2) + (3989879/31250000000 : ℝ)*(sp1) + (15591818753/100000000000000 : ℝ)*(sp2) + (1376553881716027/50000000000000 : ℝ)*(sp4) + (1376546785863727/50000000000000 : ℝ)*(sp5) + (86034078704223/3125000000000 : ℝ)*(sp6) + (349106325256117/25000000000000 : ℝ)*(sp7) + (349106325256117/25000000000000 : ℝ)*(f.failure) + (1376553881716027/50000000000000 : ℝ)*(f.sum) + (1603499271261/1271750000000000000000000000 : ℝ)*base65 + (1162434487858307947/635875000000000000000000000000000 : ℝ)*base67 + (284722315093192053/635875000000000000000000000000000 : ℝ)*base70 + (1149695834976942053/635875000000000000000000000000000 : ℝ)*base72 + (753920540749/1271750000000000000000000000 : ℝ)*base73 + (4931236445408442053/635875000000000000000000000000000 : ℝ)*base76 + (5261237792615192053/635875000000000000000000000000000 : ℝ)*base78 + (2985209445862942053/635875000000000000000000000000000 : ℝ)*base80 + (991973313487/5087000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1891101/625000000000000000000 : ℝ)*base90 + (1891101/625000000000000000000 : ℝ)*base92 + (1891101/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1096_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1096_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1096_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1096_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1096_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1096_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (259/64 : ℝ) ≤ p) (hpb : p ≤ (8289/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37144247/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8857/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4161/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1096_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

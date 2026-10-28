-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:51.474247+00:00
-- url     : https://prove2.me/submissions/da81572c-95cb-4fe8-ad56-f7278bf54c82

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
theorem support_rectangle_w1131_s3_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-271029361/1250000000 : ℝ)*x 0 + (54303193/100000000 : ℝ)*x 1 + (5231040209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271029361/1250000000 : ℝ)^2081 ≤ (3291568482159/25000000000000 : ℝ)^1569 := by
    have hnat : (271029361 : ℕ)^2081*25000000000000^1569 ≤ 3291568482159^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271029361 1250000000 3291568482159 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54303193/100000000 : ℝ)^2081 ≤ (8898625164311/20000000000000 : ℝ)^1569 := by
    have hnat : (54303193 : ℕ)^2081*20000000000000^1569 ≤ 8898625164311^1569*100000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54303193 100000000 8898625164311 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231040209/10000000000 : ℝ)^2081 ≤ (42340600231199/100000000000000 : ℝ)^1569 := by
    have hnat : (5231040209 : ℕ)^2081*100000000000000^1569 ≤ 42340600231199^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231040209 10000000000 42340600231199 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271029361/1250000000 : ℝ), (54303193/100000000 : ℝ), (5231040209/10000000000 : ℝ)] ![(3291568482159/25000000000000 : ℝ), (8898625164311/20000000000000 : ℝ), (42340600231199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271029361/1250000000 : ℝ)|^2081 ≤ (3291568482159/25000000000000 : ℝ)^1569
        have hw : |(-271029361/1250000000 : ℝ)|=(271029361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54303193/100000000 : ℝ)|^2081 ≤ (8898625164311/20000000000000 : ℝ)^1569
        have hw : |(54303193/100000000 : ℝ)|=(54303193/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231040209/10000000000 : ℝ)|^2081 ≤ (42340600231199/100000000000000 : ℝ)^1569
        have hw : |(5231040209/10000000000 : ℝ)|=(5231040209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338514693/2500000000 : ℝ)*x 0 + (-2270124311/10000000000 : ℝ)*x 1 + (5231040091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338514693/2500000000 : ℝ)^2081 ≤ (43666294216279/100000000000000 : ℝ)^1569 := by
    have hnat : (1338514693 : ℕ)^2081*100000000000000^1569 ≤ 43666294216279^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338514693 2500000000 43666294216279 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270124311/10000000000 : ℝ)^2081 ≤ (13993106811083/100000000000000 : ℝ)^1569 := by
    have hnat : (2270124311 : ℕ)^2081*100000000000000^1569 ≤ 13993106811083^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270124311 10000000000 13993106811083 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231040091/10000000000 : ℝ)^2081 ≤ (21170299482211/50000000000000 : ℝ)^1569 := by
    have hnat : (5231040091 : ℕ)^2081*50000000000000^1569 ≤ 21170299482211^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231040091 10000000000 21170299482211 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338514693/2500000000 : ℝ), (-2270124311/10000000000 : ℝ), (5231040091/10000000000 : ℝ)] ![(43666294216279/100000000000000 : ℝ), (13993106811083/100000000000000 : ℝ), (21170299482211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338514693/2500000000 : ℝ)|^2081 ≤ (43666294216279/100000000000000 : ℝ)^1569
        have hw : |(1338514693/2500000000 : ℝ)|=(1338514693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270124311/10000000000 : ℝ)|^2081 ≤ (13993106811083/100000000000000 : ℝ)^1569
        have hw : |(-2270124311/10000000000 : ℝ)|=(2270124311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231040091/10000000000 : ℝ)|^2081 ≤ (21170299482211/50000000000000 : ℝ)^1569
        have hw : |(5231040091/10000000000 : ℝ)|=(5231040091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5354058863/10000000000 : ℝ)*x 0 + (5231040189/10000000000 : ℝ)*x 1 + (-1135062031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354058863/10000000000 : ℝ)^2081 ≤ (21833147600319/50000000000000 : ℝ)^1569 := by
    have hnat : (5354058863 : ℕ)^2081*50000000000000^1569 ≤ 21833147600319^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354058863 10000000000 21833147600319 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231040189/10000000000 : ℝ)^2081 ≤ (42340600016491/100000000000000 : ℝ)^1569 := by
    have hnat : (5231040189 : ℕ)^2081*100000000000000^1569 ≤ 42340600016491^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231040189 10000000000 42340600016491 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135062031/5000000000 : ℝ)^2081 ≤ (13993104775387/100000000000000 : ℝ)^1569 := by
    have hnat : (1135062031 : ℕ)^2081*100000000000000^1569 ≤ 13993104775387^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135062031 5000000000 13993104775387 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354058863/10000000000 : ℝ), (5231040189/10000000000 : ℝ), (-1135062031/5000000000 : ℝ)] ![(21833147600319/50000000000000 : ℝ), (42340600016491/100000000000000 : ℝ), (13993104775387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354058863/10000000000 : ℝ)|^2081 ≤ (21833147600319/50000000000000 : ℝ)^1569
        have hw : |(5354058863/10000000000 : ℝ)|=(5354058863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231040189/10000000000 : ℝ)|^2081 ≤ (42340600016491/100000000000000 : ℝ)^1569
        have hw : |(5231040189/10000000000 : ℝ)|=(5231040189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135062031/5000000000 : ℝ)|^2081 ≤ (13993104775387/100000000000000 : ℝ)^1569
        have hw : |(-1135062031/5000000000 : ℝ)|=(1135062031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363896173/10000000000 : ℝ)*x 0 + (417055977/1000000000 : ℝ)*x 1 + (228308237/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363896173/10000000000 : ℝ)^2081 ≤ (33293336989547/100000000000000 : ℝ)^1569 := by
    have hnat : (4363896173 : ℕ)^2081*100000000000000^1569 ≤ 33293336989547^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363896173 10000000000 33293336989547 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417055977/1000000000 : ℝ)^2081 ≤ (31351275966421/100000000000000 : ℝ)^1569 := by
    have hnat : (417055977 : ℕ)^2081*100000000000000^1569 ≤ 31351275966421^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417055977 1000000000 31351275966421 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228308237/500000000 : ℝ)^2081 ≤ (35355387035391/100000000000000 : ℝ)^1569 := by
    have hnat : (228308237 : ℕ)^2081*100000000000000^1569 ≤ 35355387035391^1569*500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228308237 500000000 35355387035391 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363896173/10000000000 : ℝ), (417055977/1000000000 : ℝ), (228308237/500000000 : ℝ)] ![(33293336989547/100000000000000 : ℝ), (31351275966421/100000000000000 : ℝ), (35355387035391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363896173/10000000000 : ℝ)|^2081 ≤ (33293336989547/100000000000000 : ℝ)^1569
        have hw : |(4363896173/10000000000 : ℝ)|=(4363896173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417055977/1000000000 : ℝ)|^2081 ≤ (31351275966421/100000000000000 : ℝ)^1569
        have hw : |(417055977/1000000000 : ℝ)|=(417055977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228308237/500000000 : ℝ)|^2081 ≤ (35355387035391/100000000000000 : ℝ)^1569
        have hw : |(228308237/500000000 : ℝ)|=(228308237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084126757/5000000000 : ℝ)*x 0 + (5231819611/10000000000 : ℝ)*x 1 + (1357383877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084126757/5000000000 : ℝ)^2081 ≤ (6583211970301/50000000000000 : ℝ)^1569 := by
    have hnat : (1084126757 : ℕ)^2081*50000000000000^1569 ≤ 6583211970301^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084126757 5000000000 6583211970301 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231819611/10000000000 : ℝ)^2081 ≤ (21174483812047/50000000000000 : ℝ)^1569 := by
    have hnat : (5231819611 : ℕ)^2081*50000000000000^1569 ≤ 21174483812047^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231819611 10000000000 21174483812047 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357383877/2500000000 : ℝ)^2081 ≤ (8896921683359/20000000000000 : ℝ)^1569 := by
    have hnat : (1357383877 : ℕ)^2081*20000000000000^1569 ≤ 8896921683359^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357383877 2500000000 8896921683359 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084126757/5000000000 : ℝ), (5231819611/10000000000 : ℝ), (1357383877/2500000000 : ℝ)] ![(6583211970301/50000000000000 : ℝ), (21174483812047/50000000000000 : ℝ), (8896921683359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084126757/5000000000 : ℝ)|^2081 ≤ (6583211970301/50000000000000 : ℝ)^1569
        have hw : |(-1084126757/5000000000 : ℝ)|=(1084126757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231819611/10000000000 : ℝ)|^2081 ≤ (21174483812047/50000000000000 : ℝ)^1569
        have hw : |(5231819611/10000000000 : ℝ)|=(5231819611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357383877/2500000000 : ℝ)|^2081 ≤ (8896921683359/20000000000000 : ℝ)^1569
        have hw : |(1357383877/2500000000 : ℝ)|=(1357383877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41434477/78125000 : ℝ)*x 0 + (-64738397/312500000 : ℝ)*x 1 + (1357383939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41434477/78125000 : ℝ)^2081 ≤ (5390182079517/12500000000000 : ℝ)^1569 := by
    have hnat : (41434477 : ℕ)^2081*12500000000000^1569 ≤ 5390182079517^1569*78125000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41434477 78125000 5390182079517 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64738397/312500000 : ℝ)^2081 ≤ (6196966119739/50000000000000 : ℝ)^1569 := by
    have hnat : (64738397 : ℕ)^2081*50000000000000^1569 ≤ 6196966119739^1569*312500000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64738397 312500000 6196966119739 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357383939/2500000000 : ℝ)^2081 ≤ (2780288194483/6250000000000 : ℝ)^1569 := by
    have hnat : (1357383939 : ℕ)^2081*6250000000000^1569 ≤ 2780288194483^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357383939 2500000000 2780288194483 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41434477/78125000 : ℝ), (-64738397/312500000 : ℝ), (1357383939/2500000000 : ℝ)] ![(5390182079517/12500000000000 : ℝ), (6196966119739/50000000000000 : ℝ), (2780288194483/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41434477/78125000 : ℝ)|^2081 ≤ (5390182079517/12500000000000 : ℝ)^1569
        have hw : |(41434477/78125000 : ℝ)|=(41434477/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64738397/312500000 : ℝ)|^2081 ≤ (6196966119739/50000000000000 : ℝ)^1569
        have hw : |(-64738397/312500000 : ℝ)|=(64738397/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357383939/2500000000 : ℝ)|^2081 ≤ (2780288194483/6250000000000 : ℝ)^1569
        have hw : |(1357383939/2500000000 : ℝ)|=(1357383939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651806447/5000000000 : ℝ)*x 0 + (2714767979/5000000000 : ℝ)*x 1 + (-258953581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651806447/5000000000 : ℝ)^2081 ≤ (10780363722291/25000000000000 : ℝ)^1569 := by
    have hnat : (2651806447 : ℕ)^2081*25000000000000^1569 ≤ 10780363722291^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651806447 5000000000 10780363722291 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714767979/5000000000 : ℝ)^2081 ≤ (22242306653397/50000000000000 : ℝ)^1569 := by
    have hnat : (2714767979 : ℕ)^2081*50000000000000^1569 ≤ 22242306653397^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714767979 5000000000 22242306653397 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258953581/1250000000 : ℝ)^2081 ≤ (12393931795119/100000000000000 : ℝ)^1569 := by
    have hnat : (258953581 : ℕ)^2081*100000000000000^1569 ≤ 12393931795119^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258953581 1250000000 12393931795119 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651806447/5000000000 : ℝ), (2714767979/5000000000 : ℝ), (-258953581/1250000000 : ℝ)] ![(10780363722291/25000000000000 : ℝ), (22242306653397/50000000000000 : ℝ), (12393931795119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651806447/5000000000 : ℝ)|^2081 ≤ (10780363722291/25000000000000 : ℝ)^1569
        have hw : |(2651806447/5000000000 : ℝ)|=(2651806447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714767979/5000000000 : ℝ)|^2081 ≤ (22242306653397/50000000000000 : ℝ)^1569
        have hw : |(2714767979/5000000000 : ℝ)|=(2714767979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258953581/1250000000 : ℝ)|^2081 ≤ (12393931795119/100000000000000 : ℝ)^1569
        have hw : |(-258953581/1250000000 : ℝ)|=(258953581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s3_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (6982293/16000000 : ℝ)*x 0 + (4564618007/10000000000 : ℝ)*x 1 + (4172115241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6982293/16000000 : ℝ)^2081 ≤ (1664685545129/5000000000000 : ℝ)^1569 := by
    have hnat : (6982293 : ℕ)^2081*5000000000000^1569 ≤ 1664685545129^1569*16000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6982293 16000000 1664685545129 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4564618007/10000000000 : ℝ)^2081 ≤ (141358014391/400000000000 : ℝ)^1569 := by
    have hnat : (4564618007 : ℕ)^2081*400000000000^1569 ≤ 141358014391^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564618007 10000000000 141358014391 400000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172115241/10000000000 : ℝ)^2081 ≤ (31366785486227/100000000000000 : ℝ)^1569 := by
    have hnat : (4172115241 : ℕ)^2081*100000000000000^1569 ≤ 31366785486227^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172115241 10000000000 31366785486227 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6982293/16000000 : ℝ), (4564618007/10000000000 : ℝ), (4172115241/10000000000 : ℝ)] ![(1664685545129/5000000000000 : ℝ), (141358014391/400000000000 : ℝ), (31366785486227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6982293/16000000 : ℝ)|^2081 ≤ (1664685545129/5000000000000 : ℝ)^1569
        have hw : |(6982293/16000000 : ℝ)|=(6982293/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4564618007/10000000000 : ℝ)|^2081 ≤ (141358014391/400000000000 : ℝ)^1569
        have hw : |(4564618007/10000000000 : ℝ)|=(4564618007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172115241/10000000000 : ℝ)|^2081 ≤ (31366785486227/100000000000000 : ℝ)^1569
        have hw : |(4172115241/10000000000 : ℝ)|=(4172115241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5301/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14819/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3307/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (451/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3307/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (451/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3307/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (451/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3307/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (451/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3307/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (451/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3307/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (451/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (451/5000 : ℝ) ^ (8323/2048 : ℝ) ≤ (5675395082994271/100000000000000000000 : ℝ) := by
    have hpowers : (451/5000 : ℝ)^8323 ≤ (5675395082994271/100000000000000000000 : ℝ)^2048 := by
      have hnat : (451 : ℕ)^8323*100000000000000000000^2048 ≤ 5675395082994271^2048*5000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        451 5000 5675395082994271 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (451/5000 : ℝ)) (X := (5675395082994271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3307/20000 : ℝ) ^ (8323/2048 : ℝ) ≤ (33311343440607677/50000000000000000000 : ℝ) := by
    have hpowers : (3307/20000 : ℝ)^8323 ≤ (33311343440607677/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3307 : ℕ)^8323*50000000000000000000^2048 ≤ 33311343440607677^2048*20000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3307 20000 33311343440607677 50000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3307/20000 : ℝ)) (X := (33311343440607677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005675395082994271/50000000000000000000 : ℝ) ≤ (10000279291405023/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50005675395082994271/50000000000000000000 : ℝ)^2048 ≤ (10000279291405023/10000000000000000 : ℝ)^8323 := by
      have hnat : (50005675395082994271 : ℕ)^2048*10000000000000000^8323 ≤ 10000279291405023^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005675395082994271 50000000000000000000 10000279291405023 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279291405023/10000000000000000 : ℝ)) (X := (50005675395082994271/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (800578384655713677/800000000000000000 : ℝ) ≤ (10001778518981633/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (800578384655713677/800000000000000000 : ℝ)^2048 ≤ (10001778518981633/10000000000000000 : ℝ)^8323 := by
      have hnat : (800578384655713677 : ℕ)^2048*10000000000000000^8323 ≤ 10001778518981633^8323*800000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800578384655713677 800000000000000000 10001778518981633 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001778518981633/10000000000000000 : ℝ)) (X := (800578384655713677/800000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033311343440607677/25000000000000000000 : ℝ) ≤ (10003277746558243/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (25033311343440607677/25000000000000000000 : ℝ)^2048 ≤ (10003277746558243/10000000000000000 : ℝ)^8323 := by
      have hnat : (25033311343440607677 : ℕ)^2048*10000000000000000^8323 ≤ 10003277746558243^8323*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033311343440607677 25000000000000000000 10003277746558243 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003277746558243/10000000000000000 : ℝ)) (X := (25033311343440607677/25000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5675395082994271/100000000000000000000 : ℝ) ≤ ((15025010561885340689/15030000000000000000 : ℝ)+2*(149922757661/75150000000000 : ℝ)*(451/5000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (15025010561885340689/15030000000000000000 : ℝ)+2*(149922757661/75150000000000 : ℝ)*(451/5000 : ℝ)=(10000279291405023/10000000000000000 : ℝ) by norm_num, show 1+2*(5675395082994271/100000000000000000000 : ℝ)=(50005675395082994271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33311343440607677/50000000000000000000 : ℝ)+(5675395082994271/100000000000000000000 : ℝ) ≤ ((15025010561885340689/15030000000000000000 : ℝ)+(149922757661/75150000000000 : ℝ)*((3307/20000 : ℝ)+(451/5000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (15025010561885340689/15030000000000000000 : ℝ)+(149922757661/75150000000000 : ℝ)*((3307/20000 : ℝ)+(451/5000 : ℝ))=(10001778518981633/10000000000000000 : ℝ) by norm_num, show 1+(33311343440607677/50000000000000000000 : ℝ)+(5675395082994271/100000000000000000000 : ℝ)=(800578384655713677/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33311343440607677/50000000000000000000 : ℝ) ≤ ((15025010561885340689/15030000000000000000 : ℝ)+2*(149922757661/75150000000000 : ℝ)*(3307/20000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (15025010561885340689/15030000000000000000 : ℝ)+2*(149922757661/75150000000000 : ℝ)*(3307/20000 : ℝ)=(10003277746558243/10000000000000000 : ℝ) by norm_num, show 1+2*(33311343440607677/50000000000000000000 : ℝ)=(25033311343440607677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15025010561885340689/15030000000000000000 : ℝ)*(X 1 0+X 2 0)+(149922757661/75150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (451/5000 : ℝ)) (hi := (3307/20000 : ℝ)) (c := (15025010561885340689/15030000000000000000 : ℝ)) (alpha := (149922757661/75150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15025010561885340689/15030000000000000000 : ℝ)*(X 0 1+X 2 1)+(149922757661/75150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (451/5000 : ℝ)) (hi := (3307/20000 : ℝ)) (c := (15025010561885340689/15030000000000000000 : ℝ)) (alpha := (149922757661/75150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15025010561885340689/15030000000000000000 : ℝ)*(X 0 2+X 1 2)+(149922757661/75150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (451/5000 : ℝ)) (hi := (3307/20000 : ℝ)) (c := (15025010561885340689/15030000000000000000 : ℝ)) (alpha := (149922757661/75150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271029361/1250000000 : ℝ)*X 0 0+(54303193/100000000 : ℝ)*X 0 1+(5231040209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338514693/2500000000 : ℝ)*X 1 0+(-2270124311/10000000000 : ℝ)*X 1 1+(5231040091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354058863/10000000000 : ℝ)*X 2 0+(5231040189/10000000000 : ℝ)*X 2 1+(-1135062031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363896173/10000000000 : ℝ)*X 0 0+(417055977/1000000000 : ℝ)*X 0 1+(228308237/500000000 : ℝ)*X 0 2+(4363896173/10000000000 : ℝ)*X 1 0+(417055977/1000000000 : ℝ)*X 1 1+(228308237/500000000 : ℝ)*X 1 2+(4363896173/10000000000 : ℝ)*X 2 0+(417055977/1000000000 : ℝ)*X 2 1+(228308237/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084126757/5000000000 : ℝ)*X 0 0+(5231819611/10000000000 : ℝ)*X 0 1+(1357383877/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41434477/78125000 : ℝ)*X 1 0+(-64738397/312500000 : ℝ)*X 1 1+(1357383939/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651806447/5000000000 : ℝ)*X 2 0+(2714767979/5000000000 : ℝ)*X 2 1+(-258953581/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6982293/16000000 : ℝ)*X 0 0+(4564618007/10000000000 : ℝ)*X 0 1+(4172115241/10000000000 : ℝ)*X 0 2+(6982293/16000000 : ℝ)*X 1 0+(4564618007/10000000000 : ℝ)*X 1 1+(4172115241/10000000000 : ℝ)*X 1 2+(6982293/16000000 : ℝ)*X 2 0+(4564618007/10000000000 : ℝ)*X 2 1+(4172115241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1521499550773389802140853247/250500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406496171/25000000000000 : ℝ)*(base19) + (767308977/50000000000000 : ℝ)*(base23) + (18916679/20000000000000 : ℝ)*(lower2) + (18275837/25000000000000 : ℝ)*(upper3) + (21489597/10000000000000 : ℝ)*(upper5) + (3772973235563377/100000000000000 : ℝ)*(major0) + (3772973235563377/100000000000000 : ℝ)*(major1) + (3772973235563377/100000000000000 : ℝ)*(major2) + (2509056617376781/50000000000000 : ℝ)*(sp0) + (200725760317187/4000000000000 : ℝ)*(sp1) + (2509072049648203/50000000000000 : ℝ)*(sp2) + (2527787795827939/100000000000000 : ℝ)*(sp3) + (32399160797/100000000000000 : ℝ)*(sp4) + (3209730691/25000000000000 : ℝ)*(sp7) + (157987539671919/6250000000000 : ℝ)*(f.failure) + (5018145633914359/100000000000000 : ℝ)*(f.sum) + (34142039716399/7515000000000000000000000000 : ℝ)*base65 + (7137559763133582251/501000000000000000000000000000000 : ℝ)*base67 + (1588662532739417749/501000000000000000000000000000000 : ℝ)*base70 + (276749480031582251/501000000000000000000000000000000 : ℝ)*base71 + (21152939218099/7515000000000000000000000000 : ℝ)*base73 + (368971875669582251/501000000000000000000000000000000 : ℝ)*base75 + (5041609646246417749/501000000000000000000000000000000 : ℝ)*base78 + (2002347755466582251/501000000000000000000000000000000 : ℝ)*base79 + (4709037982393/3757500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (912047/62500000000000000000 : ℝ)*base89 + (912047/62500000000000000000 : ℝ)*base91 + (912047/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61872572427180088421734343/7828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291087869/20000000000000 : ℝ)*(base19) + (391499767/25000000000000 : ℝ)*(base23) + (60971/25000000000 : ℝ)*(upper3) + (797703/781250000000 : ℝ)*(lower4) + (114495107/100000000000000 : ℝ)*(upper5) + (118836084263021/3125000000000 : ℝ)*(major0) + (118836084263021/3125000000000 : ℝ)*(major1) + (118836084263021/3125000000000 : ℝ)*(major2) + (13772383593/50000000000000 : ℝ)*(sp1) + (2198116431/6250000000000 : ℝ)*(sp2) + (1264438909390751/25000000000000 : ℝ)*(sp4) + (5057726637356473/100000000000000 : ℝ)*(sp5) + (63221486271263/1250000000000 : ℝ)*(sp6) + (1273876745903809/50000000000000 : ℝ)*(sp7) + (1273876745903809/50000000000000 : ℝ)*(f.failure) + (1264438909390751/25000000000000 : ℝ)*(f.sum) + (2125463229763/3757500000000000000000000000 : ℝ)*base66 + (4218302476541323/15656250000000000000000000000000 : ℝ)*base67 + (161273924251541323/15656250000000000000000000000000 : ℝ)*base69 + (97065116709041323/15656250000000000000000000000000 : ℝ)*base71 + (2935277354621/469687500000000000000000000 : ℝ)*base74 + (100313864955228823/15656250000000000000000000000000 : ℝ)*base75 + (86561496273791323/15656250000000000000000000000000 : ℝ)*base77 + (128424778657166323/15656250000000000000000000000000 : ℝ)*base79 + (7818541563197/3757500000000000000000000000 : ℝ)*base81 + (497383/500000000000000000000 : ℝ)*base90 + (497383/500000000000000000000 : ℝ)*base92 + (497383/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1131_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5301/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14819/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s4_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085661839/5000000000 : ℝ)*x 0 + (5402425719/10000000000 : ℝ)*x 1 + (1051382767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085661839/5000000000 : ℝ)^2081 ≤ (824447280247/6250000000000 : ℝ)^1569 := by
    have hnat : (1085661839 : ℕ)^2081*6250000000000^1569 ≤ 824447280247^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085661839 5000000000 824447280247 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402425719/10000000000 : ℝ)^2081 ≤ (44190255718957/100000000000000 : ℝ)^1569 := by
    have hnat : (5402425719 : ℕ)^2081*100000000000000^1569 ≤ 44190255718957^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402425719 10000000000 44190255718957 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051382767/2000000000 : ℝ)^2081 ≤ (42618587778219/100000000000000 : ℝ)^1569 := by
    have hnat : (1051382767 : ℕ)^2081*100000000000000^1569 ≤ 42618587778219^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051382767 2000000000 42618587778219 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085661839/5000000000 : ℝ), (5402425719/10000000000 : ℝ), (1051382767/2000000000 : ℝ)] ![(824447280247/6250000000000 : ℝ), (44190255718957/100000000000000 : ℝ), (42618587778219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085661839/5000000000 : ℝ)|^2081 ≤ (824447280247/6250000000000 : ℝ)^1569
        have hw : |(-1085661839/5000000000 : ℝ)|=(1085661839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402425719/10000000000 : ℝ)|^2081 ≤ (44190255718957/100000000000000 : ℝ)^1569
        have hw : |(5402425719/10000000000 : ℝ)|=(5402425719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051382767/2000000000 : ℝ)|^2081 ≤ (42618587778219/100000000000000 : ℝ)^1569
        have hw : |(1051382767/2000000000 : ℝ)|=(1051382767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673550529/5000000000 : ℝ)*x 0 + (-2245280783/10000000000 : ℝ)*x 1 + (1051382807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673550529/5000000000 : ℝ)^2081 ≤ (43591047631869/100000000000000 : ℝ)^1569 := by
    have hnat : (2673550529 : ℕ)^2081*100000000000000^1569 ≤ 43591047631869^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673550529 5000000000 43591047631869 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245280783/10000000000 : ℝ)^2081 ≤ (13790362426359/100000000000000 : ℝ)^1569 := by
    have hnat : (2245280783 : ℕ)^2081*100000000000000^1569 ≤ 13790362426359^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245280783 10000000000 13790362426359 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051382807/2000000000 : ℝ)^2081 ≤ (21309294964379/50000000000000 : ℝ)^1569 := by
    have hnat : (1051382807 : ℕ)^2081*50000000000000^1569 ≤ 21309294964379^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051382807 2000000000 21309294964379 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673550529/5000000000 : ℝ), (-2245280783/10000000000 : ℝ), (1051382807/2000000000 : ℝ)] ![(43591047631869/100000000000000 : ℝ), (13790362426359/100000000000000 : ℝ), (21309294964379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673550529/5000000000 : ℝ)|^2081 ≤ (43591047631869/100000000000000 : ℝ)^1569
        have hw : |(2673550529/5000000000 : ℝ)|=(2673550529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245280783/10000000000 : ℝ)|^2081 ≤ (13790362426359/100000000000000 : ℝ)^1569
        have hw : |(-2245280783/10000000000 : ℝ)|=(2245280783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051382807/2000000000 : ℝ)|^2081 ≤ (21309294964379/50000000000000 : ℝ)^1569
        have hw : |(1051382807/2000000000 : ℝ)|=(1051382807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069420333/2000000000 : ℝ)*x 0 + (262845663/500000000 : ℝ)*x 1 + (-2245281/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069420333/2000000000 : ℝ)^2081 ≤ (21795527097543/50000000000000 : ℝ)^1569 := by
    have hnat : (1069420333 : ℕ)^2081*50000000000000^1569 ≤ 21795527097543^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069420333 2000000000 21795527097543 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262845663/500000000 : ℝ)^2081 ≤ (42618581595419/100000000000000 : ℝ)^1569 := by
    have hnat : (262845663 : ℕ)^2081*100000000000000^1569 ≤ 42618581595419^1569*500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262845663 500000000 42618581595419 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245281/10000000 : ℝ)^2081 ≤ (13790364194081/100000000000000 : ℝ)^1569 := by
    have hnat : (2245281 : ℕ)^2081*100000000000000^1569 ≤ 13790364194081^1569*10000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245281 10000000 13790364194081 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069420333/2000000000 : ℝ), (262845663/500000000 : ℝ), (-2245281/10000000 : ℝ)] ![(21795527097543/50000000000000 : ℝ), (42618581595419/100000000000000 : ℝ), (13790364194081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069420333/2000000000 : ℝ)|^2081 ≤ (21795527097543/50000000000000 : ℝ)^1569
        have hw : |(1069420333/2000000000 : ℝ)|=(1069420333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262845663/500000000 : ℝ)|^2081 ≤ (42618581595419/100000000000000 : ℝ)^1569
        have hw : |(262845663/500000000 : ℝ)|=(262845663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245281/10000000 : ℝ)|^2081 ≤ (13790364194081/100000000000000 : ℝ)^1569
        have hw : |(-2245281/10000000 : ℝ)|=(2245281/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4365740467/10000000000 : ℝ)*x 0 + (4223688021/10000000000 : ℝ)*x 1 + (4512557403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365740467/10000000000 : ℝ)^2081 ≤ (33312000449141/100000000000000 : ℝ)^1569 := by
    have hnat : (4365740467 : ℕ)^2081*100000000000000^1569 ≤ 33312000449141^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365740467 10000000000 33312000449141 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223688021/10000000000 : ℝ)^2081 ≤ (7970520149637/25000000000000 : ℝ)^1569 := by
    have hnat : (4223688021 : ℕ)^2081*25000000000000^1569 ≤ 7970520149637^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223688021 10000000000 7970520149637 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512557403/10000000000 : ℝ)^2081 ≤ (1740295947117/5000000000000 : ℝ)^1569 := by
    have hnat : (4512557403 : ℕ)^2081*5000000000000^1569 ≤ 1740295947117^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512557403 10000000000 1740295947117 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365740467/10000000000 : ℝ), (4223688021/10000000000 : ℝ), (4512557403/10000000000 : ℝ)] ![(33312000449141/100000000000000 : ℝ), (7970520149637/25000000000000 : ℝ), (1740295947117/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365740467/10000000000 : ℝ)|^2081 ≤ (33312000449141/100000000000000 : ℝ)^1569
        have hw : |(4365740467/10000000000 : ℝ)|=(4365740467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223688021/10000000000 : ℝ)|^2081 ≤ (7970520149637/25000000000000 : ℝ)^1569
        have hw : |(4223688021/10000000000 : ℝ)|=(4223688021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512557403/10000000000 : ℝ)|^2081 ≤ (1740295947117/5000000000000 : ℝ)^1569
        have hw : |(4512557403/10000000000 : ℝ)|=(4512557403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-21713317/100000000 : ℝ)*x 0 + (5257329381/10000000000 : ℝ)*x 1 + (1350501973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21713317/100000000 : ℝ)^2081 ≤ (3297805280579/25000000000000 : ℝ)^1569 := by
    have hnat : (21713317 : ℕ)^2081*25000000000000^1569 ≤ 3297805280579^1569*100000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21713317 100000000 3297805280579 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257329381/10000000000 : ℝ)^2081 ≤ (426230560753/1000000000000 : ℝ)^1569 := by
    have hnat : (5257329381 : ℕ)^2081*1000000000000^1569 ≤ 426230560753^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257329381 10000000000 426230560753 1000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350501973/2500000000 : ℝ)^2081 ≤ (4418572280091/10000000000000 : ℝ)^1569 := by
    have hnat : (1350501973 : ℕ)^2081*10000000000000^1569 ≤ 4418572280091^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350501973 2500000000 4418572280091 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21713317/100000000 : ℝ), (5257329381/10000000000 : ℝ), (1350501973/2500000000 : ℝ)] ![(3297805280579/25000000000000 : ℝ), (426230560753/1000000000000 : ℝ), (4418572280091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21713317/100000000 : ℝ)|^2081 ≤ (3297805280579/25000000000000 : ℝ)^1569
        have hw : |(-21713317/100000000 : ℝ)|=(21713317/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257329381/10000000000 : ℝ)|^2081 ≤ (426230560753/1000000000000 : ℝ)^1569
        have hw : |(5257329381/10000000000 : ℝ)|=(5257329381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350501973/2500000000 : ℝ)|^2081 ≤ (4418572280091/10000000000000 : ℝ)^1569
        have hw : |(1350501973/2500000000 : ℝ)|=(1350501973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310267499/10000000000 : ℝ)*x 0 + (-1050093119/5000000000 : ℝ)*x 1 + (5402008057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310267499/10000000000 : ℝ)^2081 ≤ (43193231323871/100000000000000 : ℝ)^1569 := by
    have hnat : (5310267499 : ℕ)^2081*100000000000000^1569 ≤ 43193231323871^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310267499 10000000000 43193231323871 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050093119/5000000000 : ℝ)^2081 ≤ (12621044066047/100000000000000 : ℝ)^1569 := by
    have hnat : (1050093119 : ℕ)^2081*100000000000000^1569 ≤ 12621044066047^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050093119 5000000000 12621044066047 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402008057/10000000000 : ℝ)^2081 ≤ (22092862295469/50000000000000 : ℝ)^1569 := by
    have hnat : (5402008057 : ℕ)^2081*50000000000000^1569 ≤ 22092862295469^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402008057 10000000000 22092862295469 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310267499/10000000000 : ℝ), (-1050093119/5000000000 : ℝ), (5402008057/10000000000 : ℝ)] ![(43193231323871/100000000000000 : ℝ), (12621044066047/100000000000000 : ℝ), (22092862295469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310267499/10000000000 : ℝ)|^2081 ≤ (43193231323871/100000000000000 : ℝ)^1569
        have hw : |(5310267499/10000000000 : ℝ)|=(5310267499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050093119/5000000000 : ℝ)|^2081 ≤ (12621044066047/100000000000000 : ℝ)^1569
        have hw : |(-1050093119/5000000000 : ℝ)|=(1050093119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402008057/10000000000 : ℝ)|^2081 ≤ (22092862295469/50000000000000 : ℝ)^1569
        have hw : |(5402008057/10000000000 : ℝ)|=(5402008057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655133831/5000000000 : ℝ)*x 0 + (2701003969/5000000000 : ℝ)*x 1 + (-105009309/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655133831/5000000000 : ℝ)^2081 ≤ (8638646616469/20000000000000 : ℝ)^1569 := by
    have hnat : (2655133831 : ℕ)^2081*20000000000000^1569 ≤ 8638646616469^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655133831 5000000000 8638646616469 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701003969/5000000000 : ℝ)^2081 ≤ (11046430824987/25000000000000 : ℝ)^1569 := by
    have hnat : (2701003969 : ℕ)^2081*25000000000000^1569 ≤ 11046430824987^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701003969 5000000000 11046430824987 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105009309/500000000 : ℝ)^2081 ≤ (12621043603757/100000000000000 : ℝ)^1569 := by
    have hnat : (105009309 : ℕ)^2081*100000000000000^1569 ≤ 12621043603757^1569*500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105009309 500000000 12621043603757 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655133831/5000000000 : ℝ), (2701003969/5000000000 : ℝ), (-105009309/500000000 : ℝ)] ![(8638646616469/20000000000000 : ℝ), (11046430824987/25000000000000 : ℝ), (12621043603757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655133831/5000000000 : ℝ)|^2081 ≤ (8638646616469/20000000000000 : ℝ)^1569
        have hw : |(2655133831/5000000000 : ℝ)|=(2655133831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701003969/5000000000 : ℝ)|^2081 ≤ (11046430824987/25000000000000 : ℝ)^1569
        have hw : |(2701003969/5000000000 : ℝ)|=(2701003969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105009309/500000000 : ℝ)|^2081 ≤ (12621043603757/100000000000000 : ℝ)^1569
        have hw : |(-105009309/500000000 : ℝ)|=(105009309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s4_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4365754891/10000000000 : ℝ)*x 0 + (4511730791/10000000000 : ℝ)*x 1 + (4224518039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365754891/10000000000 : ℝ)^2081 ≤ (1665607321197/5000000000000 : ℝ)^1569 := by
    have hnat : (4365754891 : ℕ)^2081*5000000000000^1569 ≤ 1665607321197^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365754891 10000000000 1665607321197 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511730791/10000000000 : ℝ)^2081 ≤ (34797462879019/100000000000000 : ℝ)^1569 := by
    have hnat : (4511730791 : ℕ)^2081*100000000000000^1569 ≤ 34797462879019^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511730791 10000000000 34797462879019 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224518039/10000000000 : ℝ)^2081 ≤ (7972597670547/25000000000000 : ℝ)^1569 := by
    have hnat : (4224518039 : ℕ)^2081*25000000000000^1569 ≤ 7972597670547^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224518039 10000000000 7972597670547 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365754891/10000000000 : ℝ), (4511730791/10000000000 : ℝ), (4224518039/10000000000 : ℝ)] ![(1665607321197/5000000000000 : ℝ), (34797462879019/100000000000000 : ℝ), (7972597670547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365754891/10000000000 : ℝ)|^2081 ≤ (1665607321197/5000000000000 : ℝ)^1569
        have hw : |(4365754891/10000000000 : ℝ)|=(4365754891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511730791/10000000000 : ℝ)|^2081 ≤ (34797462879019/100000000000000 : ℝ)^1569
        have hw : |(4511730791/10000000000 : ℝ)|=(4511730791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224518039/10000000000 : ℝ)|^2081 ≤ (7972597670547/25000000000000 : ℝ)^1569
        have hw : |(4224518039/10000000000 : ℝ)|=(4224518039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14819/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14819/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14819/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14819/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14819/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14819/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14819/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5301/50000 : ℝ) ^ (8323/2048 : ℝ) ≤ (10944861808368813/100000000000000000000 : ℝ) := by
    have hpowers : (5301/50000 : ℝ)^8323 ≤ (10944861808368813/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5301 : ℕ)^8323*100000000000000000000^2048 ≤ 10944861808368813^2048*50000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5301 50000 10944861808368813 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5301/50000 : ℝ)) (X := (10944861808368813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14819/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (8536250441155907/20000000000000000000 : ℝ) := by
    have hpowers : (14819/100000 : ℝ)^8323 ≤ (8536250441155907/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14819 : ℕ)^8323*20000000000000000000^2048 ≤ 8536250441155907^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14819 100000 8536250441155907 20000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14819/100000 : ℝ)) (X := (8536250441155907/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010944861808368813/50000000000000000000 : ℝ) ≤ (10000538585307999/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50010944861808368813/50000000000000000000 : ℝ)^2048 ≤ (10000538585307999/10000000000000000 : ℝ)^8323 := by
      have hnat : (50010944861808368813 : ℕ)^2048*10000000000000000^8323 ≤ 10000538585307999^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010944861808368813 50000000000000000000 10000538585307999 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538585307999/10000000000000000 : ℝ)) (X := (50010944861808368813/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013406528503537087/25000000000000000000 : ℝ) ≤ (10001319284954321/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (25013406528503537087/25000000000000000000 : ℝ)^2048 ≤ (10001319284954321/10000000000000000 : ℝ)^8323 := by
      have hnat : (25013406528503537087 : ℕ)^2048*10000000000000000^8323 ≤ 10001319284954321^8323*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013406528503537087 25000000000000000000 10001319284954321 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001319284954321/10000000000000000 : ℝ)) (X := (25013406528503537087/25000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008536250441155907/10000000000000000000 : ℝ) ≤ (10002099984600643/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (10008536250441155907/10000000000000000000 : ℝ)^2048 ≤ (10002099984600643/10000000000000000 : ℝ)^8323 := by
      have hnat : (10008536250441155907 : ℕ)^2048*10000000000000000^8323 ≤ 10002099984600643^8323*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008536250441155907 10000000000000000000 10002099984600643 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002099984600643/10000000000000000 : ℝ)) (X := (10008536250441155907/10000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10944861808368813/100000000000000000000 : ℝ) ≤ ((8431143451788644019/8434000000000000000 : ℝ)+2*(390349823161/210850000000000 : ℝ)*(5301/50000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (8431143451788644019/8434000000000000000 : ℝ)+2*(390349823161/210850000000000 : ℝ)*(5301/50000 : ℝ)=(10000538585307999/10000000000000000 : ℝ) by norm_num, show 1+2*(10944861808368813/100000000000000000000 : ℝ)=(50010944861808368813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8536250441155907/20000000000000000000 : ℝ)+(10944861808368813/100000000000000000000 : ℝ) ≤ ((8431143451788644019/8434000000000000000 : ℝ)+(390349823161/210850000000000 : ℝ)*((14819/100000 : ℝ)+(5301/50000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (8431143451788644019/8434000000000000000 : ℝ)+(390349823161/210850000000000 : ℝ)*((14819/100000 : ℝ)+(5301/50000 : ℝ))=(10001319284954321/10000000000000000 : ℝ) by norm_num, show 1+(8536250441155907/20000000000000000000 : ℝ)+(10944861808368813/100000000000000000000 : ℝ)=(25013406528503537087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8536250441155907/20000000000000000000 : ℝ) ≤ ((8431143451788644019/8434000000000000000 : ℝ)+2*(390349823161/210850000000000 : ℝ)*(14819/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (8431143451788644019/8434000000000000000 : ℝ)+2*(390349823161/210850000000000 : ℝ)*(14819/100000 : ℝ)=(10002099984600643/10000000000000000 : ℝ) by norm_num, show 1+2*(8536250441155907/20000000000000000000 : ℝ)=(10008536250441155907/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8431143451788644019/8434000000000000000 : ℝ)*(X 1 0+X 2 0)+(390349823161/210850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5301/50000 : ℝ)) (hi := (14819/100000 : ℝ)) (c := (8431143451788644019/8434000000000000000 : ℝ)) (alpha := (390349823161/210850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8431143451788644019/8434000000000000000 : ℝ)*(X 0 1+X 2 1)+(390349823161/210850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5301/50000 : ℝ)) (hi := (14819/100000 : ℝ)) (c := (8431143451788644019/8434000000000000000 : ℝ)) (alpha := (390349823161/210850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8431143451788644019/8434000000000000000 : ℝ)*(X 0 2+X 1 2)+(390349823161/210850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5301/50000 : ℝ)) (hi := (14819/100000 : ℝ)) (c := (8431143451788644019/8434000000000000000 : ℝ)) (alpha := (390349823161/210850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085661839/5000000000 : ℝ)*X 0 0+(5402425719/10000000000 : ℝ)*X 0 1+(1051382767/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673550529/5000000000 : ℝ)*X 1 0+(-2245280783/10000000000 : ℝ)*X 1 1+(1051382807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069420333/2000000000 : ℝ)*X 2 0+(262845663/500000000 : ℝ)*X 2 1+(-2245281/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365740467/10000000000 : ℝ)*X 0 0+(4223688021/10000000000 : ℝ)*X 0 1+(4512557403/10000000000 : ℝ)*X 0 2+(4365740467/10000000000 : ℝ)*X 1 0+(4223688021/10000000000 : ℝ)*X 1 1+(4512557403/10000000000 : ℝ)*X 1 2+(4365740467/10000000000 : ℝ)*X 2 0+(4223688021/10000000000 : ℝ)*X 2 1+(4512557403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21713317/100000000 : ℝ)*X 0 0+(5257329381/10000000000 : ℝ)*X 0 1+(1350501973/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310267499/10000000000 : ℝ)*X 1 0+(-1050093119/5000000000 : ℝ)*X 1 1+(5402008057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655133831/5000000000 : ℝ)*X 2 0+(2701003969/5000000000 : ℝ)*X 2 1+(-105009309/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365754891/10000000000 : ℝ)*X 0 0+(4511730791/10000000000 : ℝ)*X 0 1+(4224518039/10000000000 : ℝ)*X 0 2+(4365754891/10000000000 : ℝ)*X 1 0+(4511730791/10000000000 : ℝ)*X 1 1+(4224518039/10000000000 : ℝ)*X 1 2+(4365754891/10000000000 : ℝ)*X 2 0+(4511730791/10000000000 : ℝ)*X 2 1+(4224518039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2778336058463209362839412327/210850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168257361/50000000000000 : ℝ)*(base19) + (995636897/100000000000000 : ℝ)*(base23) + (312228169/100000000000000 : ℝ)*(lower2) + (148528843/50000000000000 : ℝ)*(upper3) + (123759661/50000000000000 : ℝ)*(lower4) + (45531877/100000000000000 : ℝ)*(upper5) + (2583521923552111/50000000000000 : ℝ)*(major0) + (2583521923552111/50000000000000 : ℝ)*(major1) + (2583521923552111/50000000000000 : ℝ)*(major2) + (6872293093977301/100000000000000 : ℝ)*(sp0) + (6872292757462579/100000000000000 : ℝ)*(sp1) + (1718073024585101/25000000000000 : ℝ)*(sp2) + (346177880939841/10000000000000 : ℝ)*(sp3) + (15351604821/100000000000000 : ℝ)*(sp7) + (108181067531351/3125000000000 : ℝ)*(f.failure) + (6872293093977301/100000000000000 : ℝ)*(f.sum) + (344003216073271/21085000000000000000000000000 : ℝ)*base66 + (889190057058185891/421700000000000000000000000000000 : ℝ)*base68 + (4644121130217014109/421700000000000000000000000000000 : ℝ)*base69 + (5313034380627285891/421700000000000000000000000000000 : ℝ)*base72 + (5474798755261/5271250000000000000000000000 : ℝ)*base73 + (1145624593163985891/421700000000000000000000000000000 : ℝ)*base76 + (13916964637680114109/421700000000000000000000000000000 : ℝ)*base77 + (17275082637333885891/421700000000000000000000000000000 : ℝ)*base80 + (63904116313681/21085000000000000000000000000 : ℝ)*base82 + (423463/31250000000000000000 : ℝ)*base89 + (423463/31250000000000000000 : ℝ)*base91 + (423463/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1872711548739625081104998079/210850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1952343533/100000000000000 : ℝ)*(base19) + (1087639253/50000000000000 : ℝ)*(base23) + (269009597/100000000000000 : ℝ)*(upper3) + (8658051/100000000000000 : ℝ)*(lower4) + (10523021/2500000000000 : ℝ)*(upper5) + (5196811395759753/100000000000000 : ℝ)*(major0) + (5196811395759753/100000000000000 : ℝ)*(major1) + (5196811395759753/100000000000000 : ℝ)*(major2) + (25594523927/50000000000000 : ℝ)*(sp1) + (50390987499/100000000000000 : ℝ)*(sp2) + (6911884798237237/100000000000000 : ℝ)*(sp4) + (6911831656845851/100000000000000 : ℝ)*(sp5) + (215994757249101/3125000000000 : ℝ)*(sp6) + (870434424306197/25000000000000 : ℝ)*(sp7) + (870434424306197/25000000000000 : ℝ)*(f.failure) + (6911884798237237/100000000000000 : ℝ)*(f.sum) + (44308022033893/10542500000000000000000000000 : ℝ)*base65 + (108334661676687307/843400000000000000000000000000000 : ℝ)*base67 + (9032925656031287307/843400000000000000000000000000000 : ℝ)*base69 + (4890702214391087307/843400000000000000000000000000000 : ℝ)*base71 + (30202854103993/10542500000000000000000000000 : ℝ)*base73 + (13170404183264912693/843400000000000000000000000000000 : ℝ)*base76 + (3923609813061887307/843400000000000000000000000000000 : ℝ)*base77 + (2174145077516087307/843400000000000000000000000000000 : ℝ)*base79 + (41368427619423/10542500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (717139/250000000000000000000 : ℝ)*base90 + (717139/250000000000000000000 : ℝ)*base92 + (717139/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1131_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14819/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s5_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085992769/5000000000 : ℝ)*x 0 + (1079041443/2000000000 : ℝ)*x 1 + (5263697931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085992769/5000000000 : ℝ)^2081 ≤ (13196489773629/100000000000000 : ℝ)^1569 := by
    have hnat : (1085992769 : ℕ)^2081*100000000000000^1569 ≤ 13196489773629^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085992769 5000000000 13196489773629 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079041443/2000000000 : ℝ)^2081 ≤ (44111959763271/100000000000000 : ℝ)^1569 := by
    have hnat : (1079041443 : ℕ)^2081*100000000000000^1569 ≤ 44111959763271^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079041443 2000000000 44111959763271 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263697931/10000000000 : ℝ)^2081 ≤ (21345775224847/50000000000000 : ℝ)^1569 := by
    have hnat : (5263697931 : ℕ)^2081*50000000000000^1569 ≤ 21345775224847^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263697931 10000000000 21345775224847 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085992769/5000000000 : ℝ), (1079041443/2000000000 : ℝ), (5263697931/10000000000 : ℝ)] ![(13196489773629/100000000000000 : ℝ), (44111959763271/100000000000000 : ℝ), (21345775224847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085992769/5000000000 : ℝ)|^2081 ≤ (13196489773629/100000000000000 : ℝ)^1569
        have hw : |(-1085992769/5000000000 : ℝ)|=(1085992769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079041443/2000000000 : ℝ)|^2081 ≤ (44111959763271/100000000000000 : ℝ)^1569
        have hw : |(1079041443/2000000000 : ℝ)|=(1079041443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263697931/10000000000 : ℝ)|^2081 ≤ (21345775224847/50000000000000 : ℝ)^1569
        have hw : |(5263697931/10000000000 : ℝ)|=(5263697931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345292803/10000000000 : ℝ)*x 0 + (-447744243/2000000000 : ℝ)*x 1 + (1315924487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345292803/10000000000 : ℝ)^2081 ≤ (43571496866661/100000000000000 : ℝ)^1569 := by
    have hnat : (5345292803 : ℕ)^2081*100000000000000^1569 ≤ 43571496866661^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345292803 10000000000 43571496866661 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447744243/2000000000 : ℝ)^2081 ≤ (13736952473631/100000000000000 : ℝ)^1569 := by
    have hnat : (447744243 : ℕ)^2081*100000000000000^1569 ≤ 13736952473631^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447744243 2000000000 13736952473631 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315924487/2500000000 : ℝ)^2081 ≤ (42691550632567/100000000000000 : ℝ)^1569 := by
    have hnat : (1315924487 : ℕ)^2081*100000000000000^1569 ≤ 42691550632567^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315924487 2500000000 42691550632567 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345292803/10000000000 : ℝ), (-447744243/2000000000 : ℝ), (1315924487/2500000000 : ℝ)] ![(43571496866661/100000000000000 : ℝ), (13736952473631/100000000000000 : ℝ), (42691550632567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345292803/10000000000 : ℝ)|^2081 ≤ (43571496866661/100000000000000 : ℝ)^1569
        have hw : |(5345292803/10000000000 : ℝ)|=(5345292803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447744243/2000000000 : ℝ)|^2081 ≤ (13736952473631/100000000000000 : ℝ)^1569
        have hw : |(-447744243/2000000000 : ℝ)|=(447744243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315924487/2500000000 : ℝ)|^2081 ≤ (42691550632567/100000000000000 : ℝ)^1569
        have hw : |(1315924487/2500000000 : ℝ)|=(1315924487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672646659/5000000000 : ℝ)*x 0 + (1315924381/2500000000 : ℝ)*x 1 + (-2238721093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672646659/5000000000 : ℝ)^2081 ≤ (43571502434509/100000000000000 : ℝ)^1569 := by
    have hnat : (2672646659 : ℕ)^2081*100000000000000^1569 ≤ 43571502434509^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672646659 5000000000 43571502434509 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315924381/2500000000 : ℝ)^2081 ≤ (8538309214301/20000000000000 : ℝ)^1569 := by
    have hnat : (1315924381 : ℕ)^2081*20000000000000^1569 ≤ 8538309214301^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315924381 2500000000 8538309214301 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238721093/10000000000 : ℝ)^2081 ≤ (2747390296149/20000000000000 : ℝ)^1569 := by
    have hnat : (2238721093 : ℕ)^2081*20000000000000^1569 ≤ 2747390296149^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238721093 10000000000 2747390296149 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672646659/5000000000 : ℝ), (1315924381/2500000000 : ℝ), (-2238721093/10000000000 : ℝ)] ![(43571502434509/100000000000000 : ℝ), (8538309214301/20000000000000 : ℝ), (2747390296149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672646659/5000000000 : ℝ)|^2081 ≤ (43571502434509/100000000000000 : ℝ)^1569
        have hw : |(2672646659/5000000000 : ℝ)|=(2672646659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315924381/2500000000 : ℝ)|^2081 ≤ (8538309214301/20000000000000 : ℝ)^1569
        have hw : |(1315924381/2500000000 : ℝ)|=(1315924381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238721093/10000000000 : ℝ)|^2081 ≤ (2747390296149/20000000000000 : ℝ)^1569
        have hw : |(-2238721093/10000000000 : ℝ)|=(2238721093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4366126209/10000000000 : ℝ)*x 0 + (4237537423/10000000000 : ℝ)*x 1 + (4498607883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366126209/10000000000 : ℝ)^2081 ≤ (16657952158571/50000000000000 : ℝ)^1569 := by
    have hnat : (4366126209 : ℕ)^2081*50000000000000^1569 ≤ 16657952158571^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366126209 10000000000 16657952158571 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237537423/10000000000 : ℝ)^2081 ≤ (8005202386999/25000000000000 : ℝ)^1569 := by
    have hnat : (4237537423 : ℕ)^2081*25000000000000^1569 ≤ 8005202386999^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237537423 10000000000 8005202386999 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498607883/10000000000 : ℝ)^2081 ≤ (34663286108593/100000000000000 : ℝ)^1569 := by
    have hnat : (4498607883 : ℕ)^2081*100000000000000^1569 ≤ 34663286108593^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498607883 10000000000 34663286108593 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366126209/10000000000 : ℝ), (4237537423/10000000000 : ℝ), (4498607883/10000000000 : ℝ)] ![(16657952158571/50000000000000 : ℝ), (8005202386999/25000000000000 : ℝ), (34663286108593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366126209/10000000000 : ℝ)|^2081 ≤ (16657952158571/50000000000000 : ℝ)^1569
        have hw : |(4366126209/10000000000 : ℝ)|=(4366126209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237537423/10000000000 : ℝ)|^2081 ≤ (8005202386999/25000000000000 : ℝ)^1569
        have hw : |(4237537423/10000000000 : ℝ)|=(4237537423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498607883/10000000000 : ℝ)|^2081 ≤ (34663286108593/100000000000000 : ℝ)^1569
        have hw : |(4498607883/10000000000 : ℝ)|=(4498607883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085995349/5000000000 : ℝ)*x 0 + (210561527/400000000 : ℝ)*x 1 + (5394865859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085995349/5000000000 : ℝ)^2081 ≤ (13196531355163/100000000000000 : ℝ)^1569 := by
    have hnat : (1085995349 : ℕ)^2081*100000000000000^1569 ≤ 13196531355163^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085995349 5000000000 13196531355163 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210561527/400000000 : ℝ)^2081 ≤ (42695210568323/100000000000000 : ℝ)^1569 := by
    have hnat : (210561527 : ℕ)^2081*100000000000000^1569 ≤ 42695210568323^1569*400000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210561527 400000000 42695210568323 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394865859/10000000000 : ℝ)^2081 ≤ (5513532258763/12500000000000 : ℝ)^1569 := by
    have hnat : (5394865859 : ℕ)^2081*12500000000000^1569 ≤ 5513532258763^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394865859 10000000000 5513532258763 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085995349/5000000000 : ℝ), (210561527/400000000 : ℝ), (5394865859/10000000000 : ℝ)] ![(13196531355163/100000000000000 : ℝ), (42695210568323/100000000000000 : ℝ), (5513532258763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085995349/5000000000 : ℝ)|^2081 ≤ (13196531355163/100000000000000 : ℝ)^1569
        have hw : |(-1085995349/5000000000 : ℝ)|=(1085995349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210561527/400000000 : ℝ)|^2081 ≤ (42695210568323/100000000000000 : ℝ)^1569
        have hw : |(210561527/400000000 : ℝ)|=(210561527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394865859/10000000000 : ℝ)|^2081 ≤ (5513532258763/12500000000000 : ℝ)^1569
        have hw : |(5394865859/10000000000 : ℝ)|=(5394865859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531200231/1000000000 : ℝ)*x 0 + (-2107553011/10000000000 : ℝ)*x 1 + (5394865811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531200231/1000000000 : ℝ)^2081 ≤ (43211947785459/100000000000000 : ℝ)^1569 := by
    have hnat : (531200231 : ℕ)^2081*100000000000000^1569 ≤ 43211947785459^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531200231 1000000000 43211947785459 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107553011/10000000000 : ℝ)^2081 ≤ (633989732493/5000000000000 : ℝ)^1569 := by
    have hnat : (2107553011 : ℕ)^2081*5000000000000^1569 ≤ 633989732493^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107553011 10000000000 633989732493 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394865811/10000000000 : ℝ)^2081 ≤ (44108257549593/100000000000000 : ℝ)^1569 := by
    have hnat : (5394865811 : ℕ)^2081*100000000000000^1569 ≤ 44108257549593^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394865811 10000000000 44108257549593 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531200231/1000000000 : ℝ), (-2107553011/10000000000 : ℝ), (5394865811/10000000000 : ℝ)] ![(43211947785459/100000000000000 : ℝ), (633989732493/5000000000000 : ℝ), (44108257549593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531200231/1000000000 : ℝ)|^2081 ≤ (43211947785459/100000000000000 : ℝ)^1569
        have hw : |(531200231/1000000000 : ℝ)|=(531200231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107553011/10000000000 : ℝ)|^2081 ≤ (633989732493/5000000000000 : ℝ)^1569
        have hw : |(-2107553011/10000000000 : ℝ)|=(2107553011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394865811/10000000000 : ℝ)|^2081 ≤ (44108257549593/100000000000000 : ℝ)^1569
        have hw : |(5394865811/10000000000 : ℝ)|=(5394865811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312001933/10000000000 : ℝ)*x 0 + (5394866081/10000000000 : ℝ)*x 1 + (-2107553153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312001933/10000000000 : ℝ)^2081 ≤ (43211943717879/100000000000000 : ℝ)^1569 := by
    have hnat : (5312001933 : ℕ)^2081*100000000000000^1569 ≤ 43211943717879^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312001933 10000000000 43211943717879 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394866081/10000000000 : ℝ)^2081 ≤ (22054130238733/50000000000000 : ℝ)^1569 := by
    have hnat : (5394866081 : ℕ)^2081*50000000000000^1569 ≤ 22054130238733^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394866081 10000000000 22054130238733 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107553153/10000000000 : ℝ)^2081 ≤ (1584974472871/12500000000000 : ℝ)^1569 := by
    have hnat : (2107553153 : ℕ)^2081*12500000000000^1569 ≤ 1584974472871^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107553153 10000000000 1584974472871 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312001933/10000000000 : ℝ), (5394866081/10000000000 : ℝ), (-2107553153/10000000000 : ℝ)] ![(43211943717879/100000000000000 : ℝ), (22054130238733/50000000000000 : ℝ), (1584974472871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312001933/10000000000 : ℝ)|^2081 ≤ (43211943717879/100000000000000 : ℝ)^1569
        have hw : |(5312001933/10000000000 : ℝ)|=(5312001933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394866081/10000000000 : ℝ)|^2081 ≤ (22054130238733/50000000000000 : ℝ)^1569
        have hw : |(5394866081/10000000000 : ℝ)|=(5394866081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107553153/10000000000 : ℝ)|^2081 ≤ (1584974472871/12500000000000 : ℝ)^1569
        have hw : |(-2107553153/10000000000 : ℝ)|=(2107553153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s5_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (873227213/2000000000 : ℝ)*x 0 + (2248966453/5000000000 : ℝ)*x 1 + (4238215711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873227213/2000000000 : ℝ)^2081 ≤ (16658002032699/50000000000000 : ℝ)^1569 := by
    have hnat : (873227213 : ℕ)^2081*50000000000000^1569 ≤ 16658002032699^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873227213 2000000000 16658002032699 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248966453/5000000000 : ℝ)^2081 ≤ (1386255526961/4000000000000 : ℝ)^1569 := by
    have hnat : (2248966453 : ℕ)^2081*4000000000000^1569 ≤ 1386255526961^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248966453 5000000000 1386255526961 4000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238215711/10000000000 : ℝ)^2081 ≤ (16013803869583/50000000000000 : ℝ)^1569 := by
    have hnat : (4238215711 : ℕ)^2081*50000000000000^1569 ≤ 16013803869583^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238215711 10000000000 16013803869583 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873227213/2000000000 : ℝ), (2248966453/5000000000 : ℝ), (4238215711/10000000000 : ℝ)] ![(16658002032699/50000000000000 : ℝ), (1386255526961/4000000000000 : ℝ), (16013803869583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873227213/2000000000 : ℝ)|^2081 ≤ (16658002032699/50000000000000 : ℝ)^1569
        have hw : |(873227213/2000000000 : ℝ)|=(873227213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248966453/5000000000 : ℝ)|^2081 ≤ (1386255526961/4000000000000 : ℝ)^1569
        have hw : |(2248966453/5000000000 : ℝ)|=(2248966453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238215711/10000000000 : ℝ)|^2081 ≤ (16013803869583/50000000000000 : ℝ)^1569
        have hw : |(4238215711/10000000000 : ℝ)|=(4238215711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5577/50000 : ℝ) ^ (8323/2048 : ℝ) ≤ (13452147182239449/100000000000000000000 : ℝ) := by
    have hpowers : (5577/50000 : ℝ)^8323 ≤ (13452147182239449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5577 : ℕ)^8323*100000000000000000000^2048 ≤ 13452147182239449^2048*50000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5577 50000 13452147182239449 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5577/50000 : ℝ)) (X := (13452147182239449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8323/2048 : ℝ) ≤ (290060438177849/800000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8323 ≤ (290060438177849/800000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8323*800000000000000000^2048 ≤ 290060438177849^2048*25000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 290060438177849 800000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (290060438177849/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013452147182239449/50000000000000000000 : ℝ) ≤ (10000661953712269/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50013452147182239449/50000000000000000000 : ℝ)^2048 ≤ (10000661953712269/10000000000000000 : ℝ)^8323 := by
      have hnat : (50013452147182239449 : ℕ)^2048*10000000000000000^8323 ≤ 10000661953712269^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013452147182239449 50000000000000000000 10000661953712269 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000661953712269/10000000000000000 : ℝ)) (X := (50013452147182239449/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024854850977235287/50000000000000000000 : ℝ) ≤ (10001222953236577/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50024854850977235287/50000000000000000000 : ℝ)^2048 ≤ (10001222953236577/10000000000000000 : ℝ)^8323 := by
      have hnat : (50024854850977235287 : ℕ)^2048*10000000000000000^8323 ≤ 10001222953236577^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024854850977235287 50000000000000000000 10001222953236577 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222953236577/10000000000000000 : ℝ)) (X := (50024854850977235287/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (400290060438177849/400000000000000000 : ℝ) ≤ (2000356790552177/2000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (400290060438177849/400000000000000000 : ℝ)^2048 ≤ (2000356790552177/2000000000000000 : ℝ)^8323 := by
      have hnat : (400290060438177849 : ℕ)^2048*2000000000000000^8323 ≤ 2000356790552177^8323*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400290060438177849 400000000000000000 2000356790552177 2000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000356790552177/2000000000000000 : ℝ)) (X := (400290060438177849/400000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13452147182239449/100000000000000000000 : ℝ) ≤ ((15404762681976475097/15410000000000000000 : ℝ)+2*(140249881077/77050000000000 : ℝ)*(5577/50000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (15404762681976475097/15410000000000000000 : ℝ)+2*(140249881077/77050000000000 : ℝ)*(5577/50000 : ℝ)=(10000661953712269/10000000000000000 : ℝ) by norm_num, show 1+2*(13452147182239449/100000000000000000000 : ℝ)=(50013452147182239449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(290060438177849/800000000000000000 : ℝ)+(13452147182239449/100000000000000000000 : ℝ) ≤ ((15404762681976475097/15410000000000000000 : ℝ)+(140249881077/77050000000000 : ℝ)*((3559/25000 : ℝ)+(5577/50000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (15404762681976475097/15410000000000000000 : ℝ)+(140249881077/77050000000000 : ℝ)*((3559/25000 : ℝ)+(5577/50000 : ℝ))=(10001222953236577/10000000000000000 : ℝ) by norm_num, show 1+(290060438177849/800000000000000000 : ℝ)+(13452147182239449/100000000000000000000 : ℝ)=(50024854850977235287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(290060438177849/800000000000000000 : ℝ) ≤ ((15404762681976475097/15410000000000000000 : ℝ)+2*(140249881077/77050000000000 : ℝ)*(3559/25000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (15404762681976475097/15410000000000000000 : ℝ)+2*(140249881077/77050000000000 : ℝ)*(3559/25000 : ℝ)=(2000356790552177/2000000000000000 : ℝ) by norm_num, show 1+2*(290060438177849/800000000000000000 : ℝ)=(400290060438177849/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15404762681976475097/15410000000000000000 : ℝ)*(X 1 0+X 2 0)+(140249881077/77050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15404762681976475097/15410000000000000000 : ℝ)) (alpha := (140249881077/77050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15404762681976475097/15410000000000000000 : ℝ)*(X 0 1+X 2 1)+(140249881077/77050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15404762681976475097/15410000000000000000 : ℝ)) (alpha := (140249881077/77050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15404762681976475097/15410000000000000000 : ℝ)*(X 0 2+X 1 2)+(140249881077/77050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15404762681976475097/15410000000000000000 : ℝ)) (alpha := (140249881077/77050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085992769/5000000000 : ℝ)*X 0 0+(1079041443/2000000000 : ℝ)*X 0 1+(5263697931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345292803/10000000000 : ℝ)*X 1 0+(-447744243/2000000000 : ℝ)*X 1 1+(1315924487/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672646659/5000000000 : ℝ)*X 2 0+(1315924381/2500000000 : ℝ)*X 2 1+(-2238721093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366126209/10000000000 : ℝ)*X 0 0+(4237537423/10000000000 : ℝ)*X 0 1+(4498607883/10000000000 : ℝ)*X 0 2+(4366126209/10000000000 : ℝ)*X 1 0+(4237537423/10000000000 : ℝ)*X 1 1+(4498607883/10000000000 : ℝ)*X 1 2+(4366126209/10000000000 : ℝ)*X 2 0+(4237537423/10000000000 : ℝ)*X 2 1+(4498607883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085995349/5000000000 : ℝ)*X 0 0+(210561527/400000000 : ℝ)*X 0 1+(5394865859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531200231/1000000000 : ℝ)*X 1 0+(-2107553011/10000000000 : ℝ)*X 1 1+(5394865811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312001933/10000000000 : ℝ)*X 2 0+(5394866081/10000000000 : ℝ)*X 2 1+(-2107553153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873227213/2000000000 : ℝ)*X 0 0+(2248966453/5000000000 : ℝ)*X 0 1+(4238215711/10000000000 : ℝ)*X 0 2+(873227213/2000000000 : ℝ)*X 1 0+(2248966453/5000000000 : ℝ)*X 1 1+(4238215711/10000000000 : ℝ)*X 1 2+(873227213/2000000000 : ℝ)*X 2 0+(2248966453/5000000000 : ℝ)*X 2 1+(4238215711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (508263248745271956690438657/77050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67477241/10000000000000 : ℝ)*(base19) + (417882029/50000000000000 : ℝ)*(base23) + (152776883/50000000000000 : ℝ)*(lower2) + (50713703/50000000000000 : ℝ)*(upper3) + (4336833/100000000000000 : ℝ)*(upper5) + (1143445318403827/20000000000000 : ℝ)*(major0) + (1143445318403827/20000000000000 : ℝ)*(major1) + (1143445318403827/20000000000000 : ℝ)*(major2) + (190100801974637/2500000000000 : ℝ)*(sp0) + (1901012255561253/25000000000000 : ℝ)*(sp1) + (1901012215313341/25000000000000 : ℝ)*(sp2) + (3830389054142141/100000000000000 : ℝ)*(sp3) + (17618031941/100000000000000 : ℝ)*(sp4) + (1776624263/12500000000000 : ℝ)*(sp7) + (766080653427249/20000000000000 : ℝ)*(f.failure) + (3802024848508711/50000000000000 : ℝ)*(f.sum) + (800260201153/1541000000000000000000000000 : ℝ)*base66 + (3436129607293603781/308200000000000000000000000000000 : ℝ)*base68 + (1925362456706403781/308200000000000000000000000000000 : ℝ)*base70 + (10692522802203781/308200000000000000000000000000000 : ℝ)*base72 + (3535131637909/1541000000000000000000000000 : ℝ)*base74 + (412159377457803781/308200000000000000000000000000000 : ℝ)*base76 + (1905497837153403781/308200000000000000000000000000000 : ℝ)*base78 + (1416823078546196219/308200000000000000000000000000000 : ℝ)*base79 + (5541759131537/1541000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (403337/200000000000000000000 : ℝ)*base89 + (403337/200000000000000000000 : ℝ)*base91 + (403337/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80871788727544145245502883/24078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7344063/2000000000000 : ℝ)*(base8) + (38846231/50000000000000 : ℝ)*(base15) + (29219299/12500000000000 : ℝ)*(upper2) + (40268821/50000000000000 : ℝ)*(lower4) + (359186441807613/6250000000000 : ℝ)*(major0) + (359186441807613/6250000000000 : ℝ)*(major1) + (359186441807613/6250000000000 : ℝ)*(major2) + (9110289821/100000000000000 : ℝ)*(sp1) + (2440481469/20000000000000 : ℝ)*(sp2) + (239957147/12500000000000 : ℝ)*(sp3) + (3821813136565639/50000000000000 : ℝ)*(sp4) + (477726090772009/6250000000000 : ℝ)*(sp5) + (7643614437927083/100000000000000 : ℝ)*(sp6) + (3850337465894521/100000000000000 : ℝ)*(sp7) + (3850339385551697/100000000000000 : ℝ)*(f.failure) + (1910906660083607/25000000000000 : ℝ)*(f.sum) + (46529581472093/7705000000000000000000000000 : ℝ)*base66 + (395090928780536539/96312500000000000000000000000000 : ℝ)*base68 + (750227141824099039/96312500000000000000000000000000 : ℝ)*base70 + (735560666685213461/96312500000000000000000000000000 : ℝ)*base71 + (5347615130057/7705000000000000000000000000 : ℝ)*base73 + (651400720879724039/96312500000000000000000000000000 : ℝ)*base76 + (1273013525820161539/96312500000000000000000000000000 : ℝ)*base78 + (834790993872599039/96312500000000000000000000000000 : ℝ)*base80 + (978341504343/7705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6424361/1000000000000000000000 : ℝ)*base89 + (6424361/1000000000000000000000 : ℝ)*base91 + (6424361/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1131_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1131_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1131_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1131_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1131_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3307/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:58.396991+00:00
-- url     : https://prove2.me/submissions/914213a9-cbc4-4ed0-ae10-8d4d3019ffe4

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
theorem support_rectangle_w1298_box_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911769817/10000000000 : ℝ)*x 0 + (1347940993/2500000000 : ℝ)*x 1 + (1078352741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911769817/10000000000 : ℝ)^2129 ≤ (2264344086479/20000000000000 : ℝ)^1617 := by
    have hnat : (1911769817 : ℕ)^2129*20000000000000^1617 ≤ 2264344086479^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911769817 10000000000 2264344086479 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347940993/2500000000 : ℝ)^2129 ≤ (44339141223739/100000000000000 : ℝ)^1617 := by
    have hnat : (1347940993 : ℕ)^2129*100000000000000^1617 ≤ 44339141223739^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347940993 2500000000 44339141223739 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078352741/2000000000 : ℝ)^2129 ≤ (44339138332837/100000000000000 : ℝ)^1617 := by
    have hnat : (1078352741 : ℕ)^2129*100000000000000^1617 ≤ 44339138332837^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078352741 2000000000 44339138332837 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911769817/10000000000 : ℝ), (1347940993/2500000000 : ℝ), (1078352741/2000000000 : ℝ)] ![(2264344086479/20000000000000 : ℝ), (44339141223739/100000000000000 : ℝ), (44339138332837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911769817/10000000000 : ℝ)|^2129 ≤ (2264344086479/20000000000000 : ℝ)^1617
        have hw : |(-1911769817/10000000000 : ℝ)|=(1911769817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347940993/2500000000 : ℝ)|^2129 ≤ (44339141223739/100000000000000 : ℝ)^1617
        have hw : |(1347940993/2500000000 : ℝ)|=(1347940993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078352741/2000000000 : ℝ)|^2129 ≤ (44339138332837/100000000000000 : ℝ)^1617
        have hw : |(1078352741/2000000000 : ℝ)|=(1078352741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330279781/625000000 : ℝ)*x 0 + (-257315621/1250000000 : ℝ)*x 1 + (5391763907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330279781/625000000 : ℝ)^2129 ≤ (43181178722329/100000000000000 : ℝ)^1617 := by
    have hnat : (330279781 : ℕ)^2129*100000000000000^1617 ≤ 43181178722329^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330279781 625000000 43181178722329 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257315621/1250000000 : ℝ)^2129 ≤ (12479680747769/100000000000000 : ℝ)^1617 := by
    have hnat : (257315621 : ℕ)^2129*100000000000000^1617 ≤ 12479680747769^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257315621 1250000000 12479680747769 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391763907/10000000000 : ℝ)^2129 ≤ (44339140519961/100000000000000 : ℝ)^1617 := by
    have hnat : (5391763907 : ℕ)^2129*100000000000000^1617 ≤ 44339140519961^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391763907 10000000000 44339140519961 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330279781/625000000 : ℝ), (-257315621/1250000000 : ℝ), (5391763907/10000000000 : ℝ)] ![(43181178722329/100000000000000 : ℝ), (12479680747769/100000000000000 : ℝ), (44339140519961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330279781/625000000 : ℝ)|^2129 ≤ (43181178722329/100000000000000 : ℝ)^1617
        have hw : |(330279781/625000000 : ℝ)|=(330279781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257315621/1250000000 : ℝ)|^2129 ≤ (12479680747769/100000000000000 : ℝ)^1617
        have hw : |(-257315621/1250000000 : ℝ)|=(257315621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391763907/10000000000 : ℝ)|^2129 ≤ (44339140519961/100000000000000 : ℝ)^1617
        have hw : |(5391763907/10000000000 : ℝ)|=(5391763907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642238429/5000000000 : ℝ)*x 0 + (2695881879/5000000000 : ℝ)*x 1 + (-2058524681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642238429/5000000000 : ℝ)^2129 ≤ (10795295654241/25000000000000 : ℝ)^1617 := by
    have hnat : (2642238429 : ℕ)^2129*25000000000000^1617 ≤ 10795295654241^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642238429 5000000000 10795295654241 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695881879/5000000000 : ℝ)^2129 ≤ (44339138906687/100000000000000 : ℝ)^1617 := by
    have hnat : (2695881879 : ℕ)^2129*100000000000000^1617 ≤ 44339138906687^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695881879 5000000000 44339138906687 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058524681/10000000000 : ℝ)^2129 ≤ (12479678456929/100000000000000 : ℝ)^1617 := by
    have hnat : (2058524681 : ℕ)^2129*100000000000000^1617 ≤ 12479678456929^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058524681 10000000000 12479678456929 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642238429/5000000000 : ℝ), (2695881879/5000000000 : ℝ), (-2058524681/10000000000 : ℝ)] ![(10795295654241/25000000000000 : ℝ), (44339138906687/100000000000000 : ℝ), (12479678456929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642238429/5000000000 : ℝ)|^2129 ≤ (10795295654241/25000000000000 : ℝ)^1617
        have hw : |(2642238429/5000000000 : ℝ)|=(2642238429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695881879/5000000000 : ℝ)|^2129 ≤ (44339138906687/100000000000000 : ℝ)^1617
        have hw : |(2695881879/5000000000 : ℝ)|=(2695881879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058524681/10000000000 : ℝ)|^2129 ≤ (12479678456929/100000000000000 : ℝ)^1617
        have hw : |(-2058524681/10000000000 : ℝ)|=(2058524681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4487527047/10000000000 : ℝ)*x 0 + (533452189/1250000000 : ℝ)*x 1 + (4267617587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487527047/10000000000 : ℝ)^2129 ≤ (6963860728469/20000000000000 : ℝ)^1617 := by
    have hnat : (4487527047 : ℕ)^2129*20000000000000^1617 ≤ 6963860728469^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487527047 10000000000 6963860728469 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533452189/1250000000 : ℝ)^2129 ≤ (16295173897417/50000000000000 : ℝ)^1617 := by
    have hnat : (533452189 : ℕ)^2129*50000000000000^1617 ≤ 16295173897417^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533452189 1250000000 16295173897417 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4267617587/10000000000 : ℝ)^2129 ≤ (32590348548937/100000000000000 : ℝ)^1617 := by
    have hnat : (4267617587 : ℕ)^2129*100000000000000^1617 ≤ 32590348548937^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267617587 10000000000 32590348548937 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487527047/10000000000 : ℝ), (533452189/1250000000 : ℝ), (4267617587/10000000000 : ℝ)] ![(6963860728469/20000000000000 : ℝ), (16295173897417/50000000000000 : ℝ), (32590348548937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487527047/10000000000 : ℝ)|^2129 ≤ (6963860728469/20000000000000 : ℝ)^1617
        have hw : |(4487527047/10000000000 : ℝ)|=(4487527047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(533452189/1250000000 : ℝ)|^2129 ≤ (16295173897417/50000000000000 : ℝ)^1617
        have hw : |(533452189/1250000000 : ℝ)|=(533452189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4267617587/10000000000 : ℝ)|^2129 ≤ (32590348548937/100000000000000 : ℝ)^1617
        have hw : |(4267617587/10000000000 : ℝ)|=(4267617587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1128102521/5000000000 : ℝ)*x 0 + (328991029/625000000 : ℝ)*x 1 + (1315964207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128102521/5000000000 : ℝ)^2129 ≤ (7040526053699/50000000000000 : ℝ)^1617 := by
    have hnat : (1128102521 : ℕ)^2129*50000000000000^1617 ≤ 7040526053699^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128102521 5000000000 7040526053699 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328991029/625000000 : ℝ)^2129 ≤ (42959471986019/100000000000000 : ℝ)^1617 := by
    have hnat : (328991029 : ℕ)^2129*100000000000000^1617 ≤ 42959471986019^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328991029 625000000 42959471986019 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315964207/2500000000 : ℝ)^2129 ≤ (21479737948663/50000000000000 : ℝ)^1617 := by
    have hnat : (1315964207 : ℕ)^2129*50000000000000^1617 ≤ 21479737948663^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315964207 2500000000 21479737948663 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1128102521/5000000000 : ℝ), (328991029/625000000 : ℝ), (1315964207/2500000000 : ℝ)] ![(7040526053699/50000000000000 : ℝ), (42959471986019/100000000000000 : ℝ), (21479737948663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1128102521/5000000000 : ℝ)|^2129 ≤ (7040526053699/50000000000000 : ℝ)^1617
        have hw : |(-1128102521/5000000000 : ℝ)|=(1128102521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328991029/625000000 : ℝ)|^2129 ≤ (42959471986019/100000000000000 : ℝ)^1617
        have hw : |(328991029/625000000 : ℝ)|=(328991029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315964207/2500000000 : ℝ)|^2129 ≤ (21479737948663/50000000000000 : ℝ)^1617
        have hw : |(1315964207/2500000000 : ℝ)|=(1315964207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2687242673/5000000000 : ℝ)*x 0 + (-210952759/1000000000 : ℝ)*x 1 + (210554261/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687242673/5000000000 : ℝ)^2129 ≤ (8830430906733/20000000000000 : ℝ)^1617 := by
    have hnat : (2687242673 : ℕ)^2129*20000000000000^1617 ≤ 8830430906733^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687242673 5000000000 8830430906733 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210952759/1000000000 : ℝ)^2129 ≤ (6444186405593/50000000000000 : ℝ)^1617 := by
    have hnat : (210952759 : ℕ)^2129*50000000000000^1617 ≤ 6444186405593^1617*1000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210952759 1000000000 6444186405593 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210554261/400000000 : ℝ)^2129 ≤ (8591894528297/20000000000000 : ℝ)^1617 := by
    have hnat : (210554261 : ℕ)^2129*20000000000000^1617 ≤ 8591894528297^1617*400000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210554261 400000000 8591894528297 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687242673/5000000000 : ℝ), (-210952759/1000000000 : ℝ), (210554261/400000000 : ℝ)] ![(8830430906733/20000000000000 : ℝ), (6444186405593/50000000000000 : ℝ), (8591894528297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687242673/5000000000 : ℝ)|^2129 ≤ (8830430906733/20000000000000 : ℝ)^1617
        have hw : |(2687242673/5000000000 : ℝ)|=(2687242673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210952759/1000000000 : ℝ)|^2129 ≤ (6444186405593/50000000000000 : ℝ)^1617
        have hw : |(-210952759/1000000000 : ℝ)|=(210952759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210554261/400000000 : ℝ)|^2129 ≤ (8591894528297/20000000000000 : ℝ)^1617
        have hw : |(210554261/400000000 : ℝ)|=(210554261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5374485897/10000000000 : ℝ)*x 0 + (5263855497/10000000000 : ℝ)*x 1 + (-2109528223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374485897/10000000000 : ℝ)^2129 ≤ (44152160493473/100000000000000 : ℝ)^1617 := by
    have hnat : (5374485897 : ℕ)^2129*100000000000000^1617 ≤ 44152160493473^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374485897 10000000000 44152160493473 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263855497/10000000000 : ℝ)^2129 ≤ (21479730797633/50000000000000 : ℝ)^1617 := by
    have hnat : (5263855497 : ℕ)^2129*50000000000000^1617 ≤ 21479730797633^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263855497 10000000000 21479730797633 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109528223/10000000000 : ℝ)^2129 ≤ (6444188951557/50000000000000 : ℝ)^1617 := by
    have hnat : (2109528223 : ℕ)^2129*50000000000000^1617 ≤ 6444188951557^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109528223 10000000000 6444188951557 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374485897/10000000000 : ℝ), (5263855497/10000000000 : ℝ), (-2109528223/10000000000 : ℝ)] ![(44152160493473/100000000000000 : ℝ), (21479730797633/50000000000000 : ℝ), (6444188951557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374485897/10000000000 : ℝ)|^2129 ≤ (44152160493473/100000000000000 : ℝ)^1617
        have hw : |(5374485897/10000000000 : ℝ)|=(5374485897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263855497/10000000000 : ℝ)|^2129 ≤ (21479730797633/50000000000000 : ℝ)^1617
        have hw : |(5263855497/10000000000 : ℝ)|=(5263855497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109528223/10000000000 : ℝ)|^2129 ≤ (6444188951557/50000000000000 : ℝ)^1617
        have hw : |(-2109528223/10000000000 : ℝ)|=(2109528223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4188133279/10000000000 : ℝ)*x 0 + (2208629447/5000000000 : ℝ)*x 1 + (4417259681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4188133279/10000000000 : ℝ)^2129 ≤ (15896762120697/50000000000000 : ℝ)^1617 := by
    have hnat : (4188133279 : ℕ)^2129*50000000000000^1617 ≤ 15896762120697^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188133279 10000000000 15896762120697 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208629447/5000000000 : ℝ)^2129 ≤ (17051616934399/50000000000000 : ℝ)^1617 := by
    have hnat : (2208629447 : ℕ)^2129*50000000000000^1617 ≤ 17051616934399^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208629447 5000000000 17051616934399 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417259681/10000000000 : ℝ)^2129 ≤ (34103241868671/100000000000000 : ℝ)^1617 := by
    have hnat : (4417259681 : ℕ)^2129*100000000000000^1617 ≤ 34103241868671^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417259681 10000000000 34103241868671 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4188133279/10000000000 : ℝ), (2208629447/5000000000 : ℝ), (4417259681/10000000000 : ℝ)] ![(15896762120697/50000000000000 : ℝ), (17051616934399/50000000000000 : ℝ), (34103241868671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4188133279/10000000000 : ℝ)|^2129 ≤ (15896762120697/50000000000000 : ℝ)^1617
        have hw : |(4188133279/10000000000 : ℝ)|=(4188133279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2208629447/5000000000 : ℝ)|^2129 ≤ (17051616934399/50000000000000 : ℝ)^1617
        have hw : |(2208629447/5000000000 : ℝ)|=(2208629447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417259681/10000000000 : ℝ)|^2129 ≤ (34103241868671/100000000000000 : ℝ)^1617
        have hw : |(4417259681/10000000000 : ℝ)|=(4417259681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_8 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-109199957/500000000 : ℝ)*x 0 + (2588007251/5000000000 : ℝ)*x 1 + (1081159779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109199957/500000000 : ℝ)^2129 ≤ (1686344060233/12500000000000 : ℝ)^1617 := by
    have hnat : (109199957 : ℕ)^2129*12500000000000^1617 ≤ 1686344060233^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109199957 500000000 1686344060233 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588007251/5000000000 : ℝ)^2129 ≤ (10504520675783/25000000000000 : ℝ)^1617 := by
    have hnat : (2588007251 : ℕ)^2129*25000000000000^1617 ≤ 10504520675783^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588007251 5000000000 10504520675783 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081159779/2000000000 : ℝ)^2129 ≤ (22245582394483/50000000000000 : ℝ)^1617 := by
    have hnat : (1081159779 : ℕ)^2129*50000000000000^1617 ≤ 22245582394483^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081159779 2000000000 22245582394483 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109199957/500000000 : ℝ), (2588007251/5000000000 : ℝ), (1081159779/2000000000 : ℝ)] ![(1686344060233/12500000000000 : ℝ), (10504520675783/25000000000000 : ℝ), (22245582394483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109199957/500000000 : ℝ)|^2129 ≤ (1686344060233/12500000000000 : ℝ)^1617
        have hw : |(-109199957/500000000 : ℝ)|=(109199957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588007251/5000000000 : ℝ)|^2129 ≤ (10504520675783/25000000000000 : ℝ)^1617
        have hw : |(2588007251/5000000000 : ℝ)|=(2588007251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081159779/2000000000 : ℝ)|^2129 ≤ (22245582394483/50000000000000 : ℝ)^1617
        have hw : |(1081159779/2000000000 : ℝ)|=(1081159779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_9 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (527459357/1000000000 : ℝ)*x 0 + (-128299547/625000000 : ℝ)*x 1 + (5405799427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527459357/1000000000 : ℝ)^2129 ≤ (43074883181367/100000000000000 : ℝ)^1617 := by
    have hnat : (527459357 : ℕ)^2129*100000000000000^1617 ≤ 43074883181367^1617*1000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527459357 1000000000 43074883181367 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128299547/625000000 : ℝ)^2129 ≤ (12433946251497/100000000000000 : ℝ)^1617 := by
    have hnat : (128299547 : ℕ)^2129*100000000000000^1617 ≤ 12433946251497^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128299547 625000000 12433946251497 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405799427/10000000000 : ℝ)^2129 ≤ (22245585276929/50000000000000 : ℝ)^1617 := by
    have hnat : (5405799427 : ℕ)^2129*50000000000000^1617 ≤ 22245585276929^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405799427 10000000000 22245585276929 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527459357/1000000000 : ℝ), (-128299547/625000000 : ℝ), (5405799427/10000000000 : ℝ)] ![(43074883181367/100000000000000 : ℝ), (12433946251497/100000000000000 : ℝ), (22245585276929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527459357/1000000000 : ℝ)|^2129 ≤ (43074883181367/100000000000000 : ℝ)^1617
        have hw : |(527459357/1000000000 : ℝ)|=(527459357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128299547/625000000 : ℝ)|^2129 ≤ (12433946251497/100000000000000 : ℝ)^1617
        have hw : |(-128299547/625000000 : ℝ)|=(128299547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405799427/10000000000 : ℝ)|^2129 ≤ (22245585276929/50000000000000 : ℝ)^1617
        have hw : |(5405799427/10000000000 : ℝ)|=(5405799427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_10 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274593311/10000000000 : ℝ)*x 0 + (5405798617/10000000000 : ℝ)*x 1 + (-2052794203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274593311/10000000000 : ℝ)^2129 ≤ (1722995215861/4000000000000 : ℝ)^1617 := by
    have hnat : (5274593311 : ℕ)^2129*4000000000000^1617 ≤ 1722995215861^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274593311 10000000000 1722995215861 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405798617/10000000000 : ℝ)^2129 ≤ (8898232355297/20000000000000 : ℝ)^1617 := by
    have hnat : (5405798617 : ℕ)^2129*20000000000000^1617 ≤ 8898232355297^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405798617 10000000000 8898232355297 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052794203/10000000000 : ℝ)^2129 ≤ (1554244727899/12500000000000 : ℝ)^1617 := by
    have hnat : (2052794203 : ℕ)^2129*12500000000000^1617 ≤ 1554244727899^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052794203 10000000000 1554244727899 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274593311/10000000000 : ℝ), (5405798617/10000000000 : ℝ), (-2052794203/10000000000 : ℝ)] ![(1722995215861/4000000000000 : ℝ), (8898232355297/20000000000000 : ℝ), (1554244727899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274593311/10000000000 : ℝ)|^2129 ≤ (1722995215861/4000000000000 : ℝ)^1617
        have hw : |(5274593311/10000000000 : ℝ)|=(5274593311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405798617/10000000000 : ℝ)|^2129 ≤ (8898232355297/20000000000000 : ℝ)^1617
        have hw : |(5405798617/10000000000 : ℝ)|=(5405798617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052794203/10000000000 : ℝ)|^2129 ≤ (1554244727899/12500000000000 : ℝ)^1617
        have hw : |(-2052794203/10000000000 : ℝ)|=(2052794203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_11 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2259910441/5000000000 : ℝ)*x 0 + (4251184079/10000000000 : ℝ)*x 1 + (531397739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2259910441/5000000000 : ℝ)^2129 ≤ (35149591017057/100000000000000 : ℝ)^1617 := by
    have hnat : (2259910441 : ℕ)^2129*100000000000000^1617 ≤ 35149591017057^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259910441 5000000000 35149591017057 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251184079/10000000000 : ℝ)^2129 ≤ (16212607682707/50000000000000 : ℝ)^1617 := by
    have hnat : (4251184079 : ℕ)^2129*50000000000000^1617 ≤ 16212607682707^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251184079 10000000000 16212607682707 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531397739/1250000000 : ℝ)^2129 ≤ (810629840087/2500000000000 : ℝ)^1617 := by
    have hnat : (531397739 : ℕ)^2129*2500000000000^1617 ≤ 810629840087^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531397739 1250000000 810629840087 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2259910441/5000000000 : ℝ), (4251184079/10000000000 : ℝ), (531397739/1250000000 : ℝ)] ![(35149591017057/100000000000000 : ℝ), (16212607682707/50000000000000 : ℝ), (810629840087/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2259910441/5000000000 : ℝ)|^2129 ≤ (35149591017057/100000000000000 : ℝ)^1617
        have hw : |(2259910441/5000000000 : ℝ)|=(2259910441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251184079/10000000000 : ℝ)|^2129 ≤ (16212607682707/50000000000000 : ℝ)^1617
        have hw : |(4251184079/10000000000 : ℝ)|=(4251184079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531397739/1250000000 : ℝ)|^2129 ≤ (810629840087/2500000000000 : ℝ)^1617
        have hw : |(531397739/1250000000 : ℝ)|=(531397739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_12 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-24805047/125000000 : ℝ)*x 0 + (219091869/400000000 : ℝ)*x 1 + (1313206943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24805047/125000000 : ℝ)^2129 ≤ (5945722149989/50000000000000 : ℝ)^1617 := by
    have hnat : (24805047 : ℕ)^2129*50000000000000^1617 ≤ 5945722149989^1617*125000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24805047 125000000 5945722149989 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219091869/400000000 : ℝ)^2129 ≤ (22633775762557/50000000000000 : ℝ)^1617 := by
    have hnat : (219091869 : ℕ)^2129*50000000000000^1617 ≤ 22633775762557^1617*400000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219091869 400000000 22633775762557 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313206943/2500000000 : ℝ)^2129 ≤ (42841004166071/100000000000000 : ℝ)^1617 := by
    have hnat : (1313206943 : ℕ)^2129*100000000000000^1617 ≤ 42841004166071^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313206943 2500000000 42841004166071 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24805047/125000000 : ℝ), (219091869/400000000 : ℝ), (1313206943/2500000000 : ℝ)] ![(5945722149989/50000000000000 : ℝ), (22633775762557/50000000000000 : ℝ), (42841004166071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24805047/125000000 : ℝ)|^2129 ≤ (5945722149989/50000000000000 : ℝ)^1617
        have hw : |(-24805047/125000000 : ℝ)|=(24805047/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219091869/400000000 : ℝ)|^2129 ≤ (22633775762557/50000000000000 : ℝ)^1617
        have hw : |(219091869/400000000 : ℝ)|=(219091869/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313206943/2500000000 : ℝ)|^2129 ≤ (42841004166071/100000000000000 : ℝ)^1617
        have hw : |(1313206943/2500000000 : ℝ)|=(1313206943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_13 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076448709/2000000000 : ℝ)*x 0 + (-52845497/250000000 : ℝ)*x 1 + (1313206829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076448709/2000000000 : ℝ)^2129 ≤ (44236089086793/100000000000000 : ℝ)^1617 := by
    have hnat : (1076448709 : ℕ)^2129*100000000000000^1617 ≤ 44236089086793^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076448709 2000000000 44236089086793 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52845497/250000000 : ℝ)^2129 ≤ (2584582324569/20000000000000 : ℝ)^1617 := by
    have hnat : (52845497 : ℕ)^2129*20000000000000^1617 ≤ 2584582324569^1617*250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52845497 250000000 2584582324569 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313206829/2500000000 : ℝ)^2129 ≤ (10710249817361/25000000000000 : ℝ)^1617 := by
    have hnat : (1313206829 : ℕ)^2129*25000000000000^1617 ≤ 10710249817361^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313206829 2500000000 10710249817361 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076448709/2000000000 : ℝ), (-52845497/250000000 : ℝ), (1313206829/2500000000 : ℝ)] ![(44236089086793/100000000000000 : ℝ), (2584582324569/20000000000000 : ℝ), (10710249817361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076448709/2000000000 : ℝ)|^2129 ≤ (44236089086793/100000000000000 : ℝ)^1617
        have hw : |(1076448709/2000000000 : ℝ)|=(1076448709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52845497/250000000 : ℝ)|^2129 ≤ (2584582324569/20000000000000 : ℝ)^1617
        have hw : |(-52845497/250000000 : ℝ)|=(52845497/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313206829/2500000000 : ℝ)|^2129 ≤ (10710249817361/25000000000000 : ℝ)^1617
        have hw : |(1313206829/2500000000 : ℝ)|=(1313206829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_14 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2691121811/5000000000 : ℝ)*x 0 + (5252827723/10000000000 : ℝ)*x 1 + (-422763847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691121811/5000000000 : ℝ)^2129 ≤ (1382377810001/3125000000000 : ℝ)^1617 := by
    have hnat : (2691121811 : ℕ)^2129*3125000000000^1617 ≤ 1382377810001^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691121811 5000000000 1382377810001 3125000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252827723/10000000000 : ℝ)^2129 ≤ (21420501819949/50000000000000 : ℝ)^1617 := by
    have hnat : (5252827723 : ℕ)^2129*50000000000000^1617 ≤ 21420501819949^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252827723 10000000000 21420501819949 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422763847/2000000000 : ℝ)^2129 ≤ (1615363303881/12500000000000 : ℝ)^1617 := by
    have hnat : (422763847 : ℕ)^2129*12500000000000^1617 ≤ 1615363303881^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422763847 2000000000 1615363303881 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691121811/5000000000 : ℝ), (5252827723/10000000000 : ℝ), (-422763847/2000000000 : ℝ)] ![(1382377810001/3125000000000 : ℝ), (21420501819949/50000000000000 : ℝ), (1615363303881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691121811/5000000000 : ℝ)|^2129 ≤ (1382377810001/3125000000000 : ℝ)^1617
        have hw : |(2691121811/5000000000 : ℝ)|=(2691121811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252827723/10000000000 : ℝ)|^2129 ≤ (21420501819949/50000000000000 : ℝ)^1617
        have hw : |(5252827723/10000000000 : ℝ)|=(5252827723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422763847/2000000000 : ℝ)|^2129 ≤ (1615363303881/12500000000000 : ℝ)^1617
        have hw : |(-422763847/2000000000 : ℝ)|=(422763847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_box_15 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2080935681/5000000000 : ℝ)*x 0 + (4430151919/10000000000 : ℝ)*x 1 + (4430151791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080935681/5000000000 : ℝ)^2129 ≤ (31531296720431/100000000000000 : ℝ)^1617 := by
    have hnat : (2080935681 : ℕ)^2129*100000000000000^1617 ≤ 31531296720431^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080935681 5000000000 31531296720431 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4430151919/10000000000 : ℝ)^2129 ≤ (3423435228111/10000000000000 : ℝ)^1617 := by
    have hnat : (4430151919 : ℕ)^2129*10000000000000^1617 ≤ 3423435228111^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430151919 10000000000 3423435228111 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4430151791/10000000000 : ℝ)^2129 ≤ (17117175489393/50000000000000 : ℝ)^1617 := by
    have hnat : (4430151791 : ℕ)^2129*50000000000000^1617 ≤ 17117175489393^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430151791 10000000000 17117175489393 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2080935681/5000000000 : ℝ), (4430151919/10000000000 : ℝ), (4430151791/10000000000 : ℝ)] ![(31531296720431/100000000000000 : ℝ), (3423435228111/10000000000000 : ℝ), (17117175489393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2080935681/5000000000 : ℝ)|^2129 ≤ (31531296720431/100000000000000 : ℝ)^1617
        have hw : |(2080935681/5000000000 : ℝ)|=(2080935681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4430151919/10000000000 : ℝ)|^2129 ≤ (3423435228111/10000000000000 : ℝ)^1617
        have hw : |(4430151919/10000000000 : ℝ)|=(4430151919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4430151791/10000000000 : ℝ)|^2129 ≤ (17117175489393/50000000000000 : ℝ)^1617
        have hw : |(4430151791/10000000000 : ℝ)|=(4430151791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62841/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58857/100000 : ℝ) ∧ (79693/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84179/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11043/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (10517103754979943/100000000000000000000 : ℝ) := by
    have hpowers : (11043/100000 : ℝ)^4257 ≤ (10517103754979943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11043 : ℕ)^4257*100000000000000000000^1024 ≤ 10517103754979943^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11043 100000 10517103754979943 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11043/100000 : ℝ)) (X := (10517103754979943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3669/25000 : ℝ) ^ (4257/1024 : ℝ) ≤ (3430831637468461/10000000000000000000 : ℝ) := by
    have hpowers : (3669/25000 : ℝ)^4257 ≤ (3430831637468461/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3669 : ℕ)^4257*10000000000000000000^1024 ≤ 3430831637468461^1024*25000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3669 25000 3430831637468461 10000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3669/25000 : ℝ)) (X := (3430831637468461/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010517103754979943/50000000000000000000 : ℝ) ≤ (2000101185380891/2000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50010517103754979943/50000000000000000000 : ℝ)^1024 ≤ (2000101185380891/2000000000000000 : ℝ)^4257 := by
      have hnat : (50010517103754979943 : ℕ)^1024*2000000000000000^4257 ≤ 2000101185380891^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010517103754979943 50000000000000000000 2000101185380891 2000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101185380891/2000000000000000 : ℝ)) (X := (50010517103754979943/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044825420129664553/100000000000000000000 : ℝ) ≤ (10001078069514059/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (100044825420129664553/100000000000000000000 : ℝ)^1024 ≤ (10001078069514059/10000000000000000 : ℝ)^4257 := by
      have hnat : (100044825420129664553 : ℕ)^1024*10000000000000000^4257 ≤ 10001078069514059^4257*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044825420129664553 100000000000000000000 10001078069514059 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001078069514059/10000000000000000 : ℝ)) (X := (100044825420129664553/100000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003430831637468461/5000000000000000000 : ℝ) ≤ (10001650212123663/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (5003430831637468461/5000000000000000000 : ℝ)^1024 ≤ (10001650212123663/10000000000000000 : ℝ)^4257 := by
      have hnat : (5003430831637468461 : ℕ)^1024*10000000000000000^4257 ≤ 10001650212123663^4257*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003430831637468461 5000000000000000000 10001650212123663 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001650212123663/10000000000000000 : ℝ)) (X := (5003430831637468461/5000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10517103754979943/100000000000000000000 : ℝ) ≤ ((12106400563589390357/12110000000000000000 : ℝ)+2*(143035652401/90825000000000 : ℝ)*(11043/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (12106400563589390357/12110000000000000000 : ℝ)+2*(143035652401/90825000000000 : ℝ)*(11043/100000 : ℝ)=(2000101185380891/2000000000000000 : ℝ) by norm_num, show 1+2*(10517103754979943/100000000000000000000 : ℝ)=(50010517103754979943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3430831637468461/10000000000000000000 : ℝ)+(10517103754979943/100000000000000000000 : ℝ) ≤ ((12106400563589390357/12110000000000000000 : ℝ)+(143035652401/90825000000000 : ℝ)*((3669/25000 : ℝ)+(11043/100000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (12106400563589390357/12110000000000000000 : ℝ)+(143035652401/90825000000000 : ℝ)*((3669/25000 : ℝ)+(11043/100000 : ℝ))=(10001078069514059/10000000000000000 : ℝ) by norm_num, show 1+(3430831637468461/10000000000000000000 : ℝ)+(10517103754979943/100000000000000000000 : ℝ)=(100044825420129664553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3430831637468461/10000000000000000000 : ℝ) ≤ ((12106400563589390357/12110000000000000000 : ℝ)+2*(143035652401/90825000000000 : ℝ)*(3669/25000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (12106400563589390357/12110000000000000000 : ℝ)+2*(143035652401/90825000000000 : ℝ)*(3669/25000 : ℝ)=(10001650212123663/10000000000000000 : ℝ) by norm_num, show 1+2*(3430831637468461/10000000000000000000 : ℝ)=(5003430831637468461/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12106400563589390357/12110000000000000000 : ℝ)*(X 1 0+X 2 0)+(143035652401/90825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12106400563589390357/12110000000000000000 : ℝ)) (alpha := (143035652401/90825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12106400563589390357/12110000000000000000 : ℝ)*(X 0 1+X 2 1)+(143035652401/90825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12106400563589390357/12110000000000000000 : ℝ)) (alpha := (143035652401/90825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12106400563589390357/12110000000000000000 : ℝ)*(X 0 2+X 1 2)+(143035652401/90825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12106400563589390357/12110000000000000000 : ℝ)) (alpha := (143035652401/90825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1911769817/10000000000 : ℝ)*X 0 0+(1347940993/2500000000 : ℝ)*X 0 1+(1078352741/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330279781/625000000 : ℝ)*X 1 0+(-257315621/1250000000 : ℝ)*X 1 1+(5391763907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642238429/5000000000 : ℝ)*X 2 0+(2695881879/5000000000 : ℝ)*X 2 1+(-2058524681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487527047/10000000000 : ℝ)*X 0 0+(533452189/1250000000 : ℝ)*X 0 1+(4267617587/10000000000 : ℝ)*X 0 2+(4487527047/10000000000 : ℝ)*X 1 0+(533452189/1250000000 : ℝ)*X 1 1+(4267617587/10000000000 : ℝ)*X 1 2+(4487527047/10000000000 : ℝ)*X 2 0+(533452189/1250000000 : ℝ)*X 2 1+(4267617587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1128102521/5000000000 : ℝ)*X 0 0+(328991029/625000000 : ℝ)*X 0 1+(1315964207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687242673/5000000000 : ℝ)*X 1 0+(-210952759/1000000000 : ℝ)*X 1 1+(210554261/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374485897/10000000000 : ℝ)*X 2 0+(5263855497/10000000000 : ℝ)*X 2 1+(-2109528223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4188133279/10000000000 : ℝ)*X 0 0+(2208629447/5000000000 : ℝ)*X 0 1+(4417259681/10000000000 : ℝ)*X 0 2+(4188133279/10000000000 : ℝ)*X 1 0+(2208629447/5000000000 : ℝ)*X 1 1+(4417259681/10000000000 : ℝ)*X 1 2+(4188133279/10000000000 : ℝ)*X 2 0+(2208629447/5000000000 : ℝ)*X 2 1+(4417259681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-109199957/500000000 : ℝ)*X 0 0+(2588007251/5000000000 : ℝ)*X 0 1+(1081159779/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527459357/1000000000 : ℝ)*X 1 0+(-128299547/625000000 : ℝ)*X 1 1+(5405799427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274593311/10000000000 : ℝ)*X 2 0+(5405798617/10000000000 : ℝ)*X 2 1+(-2052794203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2259910441/5000000000 : ℝ)*X 0 0+(4251184079/10000000000 : ℝ)*X 0 1+(531397739/1250000000 : ℝ)*X 0 2+(2259910441/5000000000 : ℝ)*X 1 0+(4251184079/10000000000 : ℝ)*X 1 1+(531397739/1250000000 : ℝ)*X 1 2+(2259910441/5000000000 : ℝ)*X 2 0+(4251184079/10000000000 : ℝ)*X 2 1+(531397739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-24805047/125000000 : ℝ)*X 0 0+(219091869/400000000 : ℝ)*X 0 1+(1313206943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1076448709/2000000000 : ℝ)*X 1 0+(-52845497/250000000 : ℝ)*X 1 1+(1313206829/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691121811/5000000000 : ℝ)*X 2 0+(5252827723/10000000000 : ℝ)*X 2 1+(-422763847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2080935681/5000000000 : ℝ)*X 0 0+(4430151919/10000000000 : ℝ)*X 0 1+(4430151791/10000000000 : ℝ)*X 0 2+(2080935681/5000000000 : ℝ)*X 1 0+(4430151919/10000000000 : ℝ)*X 1 1+(4430151791/10000000000 : ℝ)*X 1 2+(2080935681/5000000000 : ℝ)*X 2 0+(4430151919/10000000000 : ℝ)*X 2 1+(4430151791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62841/100000 : ℝ) ≤ (-190242807796025457786568427546057/302750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4437557/20000000000000 : ℝ)*(lower3) + (86212173/50000000000000 : ℝ)*(lower4) + (49264237/50000000000000 : ℝ)*(upper5) + (1435495794282211/50000000000000 : ℝ)*(major0) + (1435495794282211/50000000000000 : ℝ)*(major1) + (1435495794282211/50000000000000 : ℝ)*(major2) + (3408360231/50000000000000 : ℝ)*(sp1) + (4976426343/10000000000000 : ℝ)*(sp2) + (7119283561/50000000000000 : ℝ)*(sp3) + (388642598409037/10000000000000 : ℝ)*(sp4) + (388642676572261/10000000000000 : ℝ)*(sp5) + (1943191909089821/50000000000000 : ℝ)*(sp6) + (187648144010389/10000000000000 : ℝ)*(sp7) + (3799176351/50000000000000 : ℝ)*(sp12) + (469123919667753/25000000000000 : ℝ)*(f.failure) + (60725524725673/1562500000000 : ℝ)*(f.sum) + (4843975491533/1135312500000000000000000000 : ℝ)*base65 + (27966842557496482019/1816500000000000000000000000000000 : ℝ)*base68 + (27586157297387482019/1816500000000000000000000000000000 : ℝ)*base70 + (15020006744879482019/1816500000000000000000000000000000 : ℝ)*base72 + (8118594585179/2270625000000000000000000000 : ℝ)*base74 + (27764372259557482019/1816500000000000000000000000000000 : ℝ)*base76 + (25201630208912482019/1816500000000000000000000000000000 : ℝ)*base78 + (22825801303532482019/1816500000000000000000000000000000 : ℝ)*base80 + (414787079233/4541250000000000000000000000 : ℝ)*base82 + (3812009/1250000000000000000000 : ℝ)*base89 + (3812009/1250000000000000000000 : ℝ)*base91 + (3812009/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58857/100000 : ℝ) ≤ (89097859419535660871316157897317/151375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32811857/100000000000000 : ℝ)*(upper0) + (71407529/100000000000000 : ℝ)*(lower1) + (45840849/25000000000000 : ℝ)*(upper4) + (1469100615774573/50000000000000 : ℝ)*(major0) + (1469100615774573/50000000000000 : ℝ)*(major1) + (1469100615774573/50000000000000 : ℝ)*(major2) + (1968176700838893/50000000000000 : ℝ)*(sp0) + (157454337906399/4000000000000 : ℝ)*(sp1) + (3936353907314133/100000000000000 : ℝ)*(sp2) + (960211451319413/50000000000000 : ℝ)*(sp3) + (72196983/100000000000000 : ℝ)*(sp5) + (576567853/12500000000000 : ℝ)*(sp6) + (272665743/20000000000000 : ℝ)*(sp7) + (1279544793/25000000000000 : ℝ)*(sp8) + (960212132983771/50000000000000 : ℝ)*(f.failure) + (1968179259928479/50000000000000 : ℝ)*(f.sum) + (38508069159153/6055000000000000000000000000 : ℝ)*base65 + (1972623573729392561/605500000000000000000000000000000 : ℝ)*base67 + (2098337233810107439/605500000000000000000000000000000 : ℝ)*base70 + (2335286849910892561/605500000000000000000000000000000 : ℝ)*base71 + (9348107278949/189218750000000000000000000 : ℝ)*base73 + (5897765989374892561/605500000000000000000000000000000 : ℝ)*base75 + (3288932078628892561/605500000000000000000000000000000 : ℝ)*base77 + (30021189776596392561/605500000000000000000000000000000 : ℝ)*base79 + (11694953606467/1513750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (737563/2500000000000000000000 : ℝ)*base89 + (737563/2500000000000000000000 : ℝ)*base91 + (737563/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79693/100000 : ℝ) ≤ (120638788260794205057168539855949/151375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610034709/100000000000000 : ℝ)*(upper1) + (721922303/100000000000000 : ℝ)*(upper2) + (230416823/100000000000000 : ℝ)*(upper3) + (175466683/100000000000000 : ℝ)*(upper4) + (1626001528978619/50000000000000 : ℝ)*(major0) + (1626001528978619/50000000000000 : ℝ)*(major1) + (1626001528978619/50000000000000 : ℝ)*(major2) + (215976001/6250000000000 : ℝ)*(sp0) + (219439590177/50000000000000 : ℝ)*(sp1) + (168840453671/100000000000000 : ℝ)*(sp3) + (2175955355968917/50000000000000 : ℝ)*(sp8) + (4351475288373497/100000000000000 : ℝ)*(sp9) + (87038283351077/2000000000000 : ℝ)*(sp10) + (132834875110399/6250000000000 : ℝ)*(sp11) + (425105368444011/20000000000000 : ℝ)*(f.failure) + (87038283351077/2000000000000 : ℝ)*(f.sum) + (163192904495093/18165000000000000000000000000 : ℝ)*base66 + (5290193198701069051/1816500000000000000000000000000000 : ℝ)*base68 + (25168188460136569051/1816500000000000000000000000000000 : ℝ)*base70 + (70992295196852569051/1816500000000000000000000000000000 : ℝ)*base72 + (431550391883/1135312500000000000000000000 : ℝ)*base74 + (126593344719577930949/1816500000000000000000000000000000 : ℝ)*base75 + (3690467891006569051/1816500000000000000000000000000000 : ℝ)*base78 + (3767205502996069051/1816500000000000000000000000000000 : ℝ)*base80 + (32503942105477/18165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11818283/1000000000000000000000 : ℝ)*base89 + (11818283/1000000000000000000000 : ℝ)*base91 + (11818283/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84179/100000 : ℝ) ≤ (-254843536842974935935571766362821/302750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85091749/100000000000000 : ℝ)*(lower1) + (66630761/25000000000000 : ℝ)*(lower2) + (23138151/50000000000000 : ℝ)*(upper5) + (3287966157844251/100000000000000 : ℝ)*(major0) + (3287966157844251/100000000000000 : ℝ)*(major1) + (3287966157844251/100000000000000 : ℝ)*(major2) + (4361539339/100000000000000 : ℝ)*(sp0) + (63256632963/20000000000000 : ℝ)*(sp5) + (8481166091/50000000000000 : ℝ)*(sp6) + (55690735257/50000000000000 : ℝ)*(sp7) + (4454954178117763/100000000000000 : ℝ)*(sp12) + (17400946314423/390625000000 : ℝ)*(sp13) + (4454941577324921/100000000000000 : ℝ)*(sp14) + (53723028448781/2500000000000 : ℝ)*(sp15) + (429806503884351/20000000000000 : ℝ)*(f.failure) + (2227479269828551/50000000000000 : ℝ)*(f.sum) + (26090427526503/6055000000000000000000000000 : ℝ)*base65 + (13533657217185087607/1211000000000000000000000000000000 : ℝ)*base67 + (14801792020379087607/1211000000000000000000000000000000 : ℝ)*base69 + (2241197504461912393/1211000000000000000000000000000000 : ℝ)*base72 + (16048053737319/3027500000000000000000000000 : ℝ)*base73 + (614803677607087607/1211000000000000000000000000000000 : ℝ)*base75 + (7311704345512087607/1211000000000000000000000000000000 : ℝ)*base77 + (281479977191087607/1211000000000000000000000000000000 : ℝ)*base79 + (1363718423953/6055000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2285697/1000000000000000000000 : ℝ)*base90 + (2285697/1000000000000000000000 : ℝ)*base92 + (2285697/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1298_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58857/100000 : ℝ) else (79693/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84179/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1298_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1298_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58857/100000 : ℝ) else (79693/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84179/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1298_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58857/100000 : ℝ) else (79693/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84179/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

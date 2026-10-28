-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:18.519368+00:00
-- url     : https://prove2.me/submissions/e59baedb-4377-45a1-8e2a-260db7f0156e

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
theorem support_rectangle_w1099_s6_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-273447603/1250000000 : ℝ)*x 0 + (2697120859/5000000000 : ℝ)*x 1 + (5264605279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273447603/1250000000 : ℝ)^2073 ≤ (13288492564591/100000000000000 : ℝ)^1561 := by
    have hnat : (273447603 : ℕ)^2073*100000000000000^1561 ≤ 13288492564591^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273447603 1250000000 13288492564591 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697120859/5000000000 : ℝ)^2073 ≤ (44055988450367/100000000000000 : ℝ)^1561 := by
    have hnat : (2697120859 : ℕ)^2073*100000000000000^1561 ≤ 44055988450367^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697120859 5000000000 44055988450367 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264605279/10000000000 : ℝ)^2073 ≤ (10663879742599/25000000000000 : ℝ)^1561 := by
    have hnat : (5264605279 : ℕ)^2073*25000000000000^1561 ≤ 10663879742599^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264605279 10000000000 10663879742599 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273447603/1250000000 : ℝ), (2697120859/5000000000 : ℝ), (5264605279/10000000000 : ℝ)] ![(13288492564591/100000000000000 : ℝ), (44055988450367/100000000000000 : ℝ), (10663879742599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273447603/1250000000 : ℝ)|^2073 ≤ (13288492564591/100000000000000 : ℝ)^1561
        have hw : |(-273447603/1250000000 : ℝ)|=(273447603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697120859/5000000000 : ℝ)|^2073 ≤ (44055988450367/100000000000000 : ℝ)^1561
        have hw : |(2697120859/5000000000 : ℝ)|=(2697120859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264605279/10000000000 : ℝ)|^2073 ≤ (10663879742599/25000000000000 : ℝ)^1561
        have hw : |(5264605279/10000000000 : ℝ)|=(5264605279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33406311/62500000 : ℝ)*x 0 + (-1126676061/5000000000 : ℝ)*x 1 + (263230263/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33406311/62500000 : ℝ)^2073 ≤ (2176140892519/5000000000000 : ℝ)^1561 := by
    have hnat : (33406311 : ℕ)^2073*5000000000000^1561 ≤ 2176140892519^1561*62500000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33406311 62500000 2176140892519 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126676061/5000000000 : ℝ)^2073 ≤ (6910831687993/50000000000000 : ℝ)^1561 := by
    have hnat : (1126676061 : ℕ)^2073*50000000000000^1561 ≤ 6910831687993^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126676061 5000000000 6910831687993 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263230263/500000000 : ℝ)^2073 ≤ (1066387969149/2500000000000 : ℝ)^1561 := by
    have hnat : (263230263 : ℕ)^2073*2500000000000^1561 ≤ 1066387969149^1561*500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263230263 500000000 1066387969149 2500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33406311/62500000 : ℝ), (-1126676061/5000000000 : ℝ), (263230263/500000000 : ℝ)] ![(2176140892519/5000000000000 : ℝ), (6910831687993/50000000000000 : ℝ), (1066387969149/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33406311/62500000 : ℝ)|^2073 ≤ (2176140892519/5000000000000 : ℝ)^1561
        have hw : |(33406311/62500000 : ℝ)|=(33406311/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126676061/5000000000 : ℝ)|^2073 ≤ (6910831687993/50000000000000 : ℝ)^1561
        have hw : |(-1126676061/5000000000 : ℝ)|=(1126676061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263230263/500000000 : ℝ)|^2073 ≤ (1066387969149/2500000000000 : ℝ)^1561
        have hw : |(263230263/500000000 : ℝ)|=(263230263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213800391/400000000 : ℝ)*x 0 + (5264605259/10000000000 : ℝ)*x 1 + (-1126676051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213800391/400000000 : ℝ)^2073 ≤ (21761409006291/50000000000000 : ℝ)^1561 := by
    have hnat : (213800391 : ℕ)^2073*50000000000000^1561 ≤ 21761409006291^1561*400000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213800391 400000000 21761409006291 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264605259/10000000000 : ℝ)^2073 ≤ (13329849611/31250000000 : ℝ)^1561 := by
    have hnat : (5264605259 : ℕ)^2073*31250000000^1561 ≤ 13329849611^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264605259 10000000000 13329849611 31250000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126676051/5000000000 : ℝ)^2073 ≤ (13821663213073/100000000000000 : ℝ)^1561 := by
    have hnat : (1126676051 : ℕ)^2073*100000000000000^1561 ≤ 13821663213073^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126676051 5000000000 13821663213073 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213800391/400000000 : ℝ), (5264605259/10000000000 : ℝ), (-1126676051/5000000000 : ℝ)] ![(21761409006291/50000000000000 : ℝ), (13329849611/31250000000 : ℝ), (13821663213073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213800391/400000000 : ℝ)|^2073 ≤ (21761409006291/50000000000000 : ℝ)^1561
        have hw : |(213800391/400000000 : ℝ)|=(213800391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264605259/10000000000 : ℝ)|^2073 ≤ (13329849611/31250000000 : ℝ)^1561
        have hw : |(5264605259/10000000000 : ℝ)|=(5264605259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126676051/5000000000 : ℝ)|^2073 ≤ (13821663213073/100000000000000 : ℝ)^1561
        have hw : |(-1126676051/5000000000 : ℝ)|=(1126676051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (109268613/250000000 : ℝ)*x 0 + (424475711/1000000000 : ℝ)*x 1 + (2250246041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109268613/250000000 : ℝ)^2073 ≤ (33316505447313/100000000000000 : ℝ)^1561 := by
    have hnat : (109268613 : ℕ)^2073*100000000000000^1561 ≤ 33316505447313^1561*250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109268613 250000000 33316505447313 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424475711/1000000000 : ℝ)^2073 ≤ (6409445813869/20000000000000 : ℝ)^1561 := by
    have hnat : (424475711 : ℕ)^2073*20000000000000^1561 ≤ 6409445813869^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424475711 1000000000 6409445813869 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250246041/5000000000 : ℝ)^2073 ≤ (1385450618717/4000000000000 : ℝ)^1561 := by
    have hnat : (2250246041 : ℕ)^2073*4000000000000^1561 ≤ 1385450618717^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250246041 5000000000 1385450618717 4000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109268613/250000000 : ℝ), (424475711/1000000000 : ℝ), (2250246041/5000000000 : ℝ)] ![(33316505447313/100000000000000 : ℝ), (6409445813869/20000000000000 : ℝ), (1385450618717/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109268613/250000000 : ℝ)|^2073 ≤ (33316505447313/100000000000000 : ℝ)^1561
        have hw : |(109268613/250000000 : ℝ)|=(109268613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424475711/1000000000 : ℝ)|^2073 ≤ (6409445813869/20000000000000 : ℝ)^1561
        have hw : |(424475711/1000000000 : ℝ)|=(424475711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250246041/5000000000 : ℝ)|^2073 ≤ (1385450618717/4000000000000 : ℝ)^1561
        have hw : |(2250246041/5000000000 : ℝ)|=(2250246041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187585903/10000000000 : ℝ)*x 0 + (5264932613/10000000000 : ℝ)*x 1 + (13484783/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187585903/10000000000 : ℝ)^2073 ≤ (6644266768259/50000000000000 : ℝ)^1561 := by
    have hnat : (2187585903 : ℕ)^2073*50000000000000^1561 ≤ 6644266768259^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187585903 10000000000 6644266768259 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264932613/10000000000 : ℝ)^2073 ≤ (5332380133473/12500000000000 : ℝ)^1561 := by
    have hnat : (5264932613 : ℕ)^2073*12500000000000^1561 ≤ 5332380133473^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264932613 10000000000 5332380133473 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13484783/25000000 : ℝ)^2073 ≤ (44052425368691/100000000000000 : ℝ)^1561 := by
    have hnat : (13484783 : ℕ)^2073*100000000000000^1561 ≤ 44052425368691^1561*25000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13484783 25000000 44052425368691 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187585903/10000000000 : ℝ), (5264932613/10000000000 : ℝ), (13484783/25000000 : ℝ)] ![(6644266768259/50000000000000 : ℝ), (5332380133473/12500000000000 : ℝ), (44052425368691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187585903/10000000000 : ℝ)|^2073 ≤ (6644266768259/50000000000000 : ℝ)^1561
        have hw : |(-2187585903/10000000000 : ℝ)|=(2187585903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264932613/10000000000 : ℝ)|^2073 ≤ (5332380133473/12500000000000 : ℝ)^1561
        have hw : |(5264932613/10000000000 : ℝ)|=(5264932613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13484783/25000000 : ℝ)|^2073 ≤ (44052425368691/100000000000000 : ℝ)^1561
        have hw : |(13484783/25000000 : ℝ)|=(13484783/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531227243/1000000000 : ℝ)*x 0 + (-1062022091/5000000000 : ℝ)*x 1 + (5393913201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531227243/1000000000 : ℝ)^2073 ≤ (21584584965289/50000000000000 : ℝ)^1561 := by
    have hnat : (531227243 : ℕ)^2073*50000000000000^1561 ≤ 21584584965289^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531227243 1000000000 21584584965289 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062022091/5000000000 : ℝ)^2073 ≤ (12778404676893/100000000000000 : ℝ)^1561 := by
    have hnat : (1062022091 : ℕ)^2073*100000000000000^1561 ≤ 12778404676893^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062022091 5000000000 12778404676893 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393913201/10000000000 : ℝ)^2073 ≤ (44052425379537/100000000000000 : ℝ)^1561 := by
    have hnat : (5393913201 : ℕ)^2073*100000000000000^1561 ≤ 44052425379537^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393913201 10000000000 44052425379537 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531227243/1000000000 : ℝ), (-1062022091/5000000000 : ℝ), (5393913201/10000000000 : ℝ)] ![(21584584965289/50000000000000 : ℝ), (12778404676893/100000000000000 : ℝ), (44052425379537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531227243/1000000000 : ℝ)|^2073 ≤ (21584584965289/50000000000000 : ℝ)^1561
        have hw : |(531227243/1000000000 : ℝ)|=(531227243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062022091/5000000000 : ℝ)|^2073 ≤ (12778404676893/100000000000000 : ℝ)^1561
        have hw : |(-1062022091/5000000000 : ℝ)|=(1062022091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393913201/10000000000 : ℝ)|^2073 ≤ (44052425379537/100000000000000 : ℝ)^1561
        have hw : |(5393913201/10000000000 : ℝ)|=(5393913201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531227243/1000000000 : ℝ)*x 0 + (5393913201/10000000000 : ℝ)*x 1 + (-1062022091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531227243/1000000000 : ℝ)^2073 ≤ (21584584965289/50000000000000 : ℝ)^1561 := by
    have hnat : (531227243 : ℕ)^2073*50000000000000^1561 ≤ 21584584965289^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531227243 1000000000 21584584965289 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393913201/10000000000 : ℝ)^2073 ≤ (44052425379537/100000000000000 : ℝ)^1561 := by
    have hnat : (5393913201 : ℕ)^2073*100000000000000^1561 ≤ 44052425379537^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393913201 10000000000 44052425379537 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062022091/5000000000 : ℝ)^2073 ≤ (12778404676893/100000000000000 : ℝ)^1561 := by
    have hnat : (1062022091 : ℕ)^2073*100000000000000^1561 ≤ 12778404676893^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062022091 5000000000 12778404676893 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531227243/1000000000 : ℝ), (5393913201/10000000000 : ℝ), (-1062022091/5000000000 : ℝ)] ![(21584584965289/50000000000000 : ℝ), (44052425379537/100000000000000 : ℝ), (12778404676893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531227243/1000000000 : ℝ)|^2073 ≤ (21584584965289/50000000000000 : ℝ)^1561
        have hw : |(531227243/1000000000 : ℝ)|=(531227243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393913201/10000000000 : ℝ)|^2073 ≤ (44052425379537/100000000000000 : ℝ)^1561
        have hw : |(5393913201/10000000000 : ℝ)|=(5393913201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1062022091/5000000000 : ℝ)|^2073 ≤ (12778404676893/100000000000000 : ℝ)^1561
        have hw : |(-1062022091/5000000000 : ℝ)|=(1062022091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s6_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4370754527/10000000000 : ℝ)*x 0 + (4499846329/10000000000 : ℝ)*x 1 + (2122702619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370754527/10000000000 : ℝ)^2073 ≤ (6663321349231/20000000000000 : ℝ)^1561 := by
    have hnat : (4370754527 : ℕ)^2073*20000000000000^1561 ≤ 6663321349231^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370754527 10000000000 6663321349231 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499846329/10000000000 : ℝ)^2073 ≤ (17314832887953/50000000000000 : ℝ)^1561 := by
    have hnat : (4499846329 : ℕ)^2073*50000000000000^1561 ≤ 17314832887953^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499846329 10000000000 17314832887953 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122702619/5000000000 : ℝ)^2073 ≤ (6410745491647/20000000000000 : ℝ)^1561 := by
    have hnat : (2122702619 : ℕ)^2073*20000000000000^1561 ≤ 6410745491647^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122702619 5000000000 6410745491647 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370754527/10000000000 : ℝ), (4499846329/10000000000 : ℝ), (2122702619/5000000000 : ℝ)] ![(6663321349231/20000000000000 : ℝ), (17314832887953/50000000000000 : ℝ), (6410745491647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370754527/10000000000 : ℝ)|^2073 ≤ (6663321349231/20000000000000 : ℝ)^1561
        have hw : |(4370754527/10000000000 : ℝ)|=(4370754527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499846329/10000000000 : ℝ)|^2073 ≤ (17314832887953/50000000000000 : ℝ)^1561
        have hw : |(4499846329/10000000000 : ℝ)|=(4499846329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122702619/5000000000 : ℝ)|^2073 ≤ (6410745491647/20000000000000 : ℝ)^1561
        have hw : |(2122702619/5000000000 : ℝ)|=(2122702619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (8291/2048 : ℝ) ≤ (14417807607475403/100000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^8291 ≤ (14417807607475403/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11251 : ℕ)^8291*100000000000000000000^2048 ≤ 14417807607475403^2048*100000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 14417807607475403 100000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (14417807607475403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (8291/2048 : ℝ) ≤ (17827892976146139/50000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^8291 ≤ (17827892976146139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14071 : ℕ)^8291*50000000000000000000^2048 ≤ 17827892976146139^2048*100000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 17827892976146139 50000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (17827892976146139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014417807607475403/50000000000000000000 : ℝ) ≤ (250017805128983/250000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (50014417807607475403/50000000000000000000 : ℝ)^2048 ≤ (250017805128983/250000000000000 : ℝ)^8291 := by
      have hnat : (50014417807607475403 : ℕ)^2048*250000000000000^8291 ≤ 250017805128983^8291*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014417807607475403 50000000000000000000 250017805128983 250000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017805128983/250000000000000 : ℝ)) (X := (50014417807607475403/50000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050073593559767681/100000000000000000000 : ℝ) ≤ (10001236658932077/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (100050073593559767681/100000000000000000000 : ℝ)^2048 ≤ (10001236658932077/10000000000000000 : ℝ)^8291 := by
      have hnat : (100050073593559767681 : ℕ)^2048*10000000000000000^8291 ≤ 10001236658932077^8291*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050073593559767681 100000000000000000000 10001236658932077 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001236658932077/10000000000000000 : ℝ)) (X := (100050073593559767681/100000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017827892976146139/25000000000000000000 : ℝ) ≤ (5000880556352417/5000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (25017827892976146139/25000000000000000000 : ℝ)^2048 ≤ (5000880556352417/5000000000000000 : ℝ)^8291 := by
      have hnat : (25017827892976146139 : ℕ)^2048*5000000000000000^8291 ≤ 5000880556352417^8291*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017827892976146139 25000000000000000000 5000880556352417 5000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000880556352417/5000000000000000 : ℝ)) (X := (25017827892976146139/25000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14417807607475403/100000000000000000000 : ℝ) ≤ ((14095103579877352193/14100000000000000000 : ℝ)+2*(524453772757/282000000000000 : ℝ)*(11251/100000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (14095103579877352193/14100000000000000000 : ℝ)+2*(524453772757/282000000000000 : ℝ)*(11251/100000 : ℝ)=(250017805128983/250000000000000 : ℝ) by norm_num, show 1+2*(14417807607475403/100000000000000000000 : ℝ)=(50014417807607475403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17827892976146139/50000000000000000000 : ℝ)+(14417807607475403/100000000000000000000 : ℝ) ≤ ((14095103579877352193/14100000000000000000 : ℝ)+(524453772757/282000000000000 : ℝ)*((14071/100000 : ℝ)+(11251/100000 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (14095103579877352193/14100000000000000000 : ℝ)+(524453772757/282000000000000 : ℝ)*((14071/100000 : ℝ)+(11251/100000 : ℝ))=(10001236658932077/10000000000000000 : ℝ) by norm_num, show 1+(17827892976146139/50000000000000000000 : ℝ)+(14417807607475403/100000000000000000000 : ℝ)=(100050073593559767681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17827892976146139/50000000000000000000 : ℝ) ≤ ((14095103579877352193/14100000000000000000 : ℝ)+2*(524453772757/282000000000000 : ℝ)*(14071/100000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (14095103579877352193/14100000000000000000 : ℝ)+2*(524453772757/282000000000000 : ℝ)*(14071/100000 : ℝ)=(5000880556352417/5000000000000000 : ℝ) by norm_num, show 1+2*(17827892976146139/50000000000000000000 : ℝ)=(25017827892976146139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14095103579877352193/14100000000000000000 : ℝ)*(X 1 0+X 2 0)+(524453772757/282000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (14095103579877352193/14100000000000000000 : ℝ)) (alpha := (524453772757/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14095103579877352193/14100000000000000000 : ℝ)*(X 0 1+X 2 1)+(524453772757/282000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (14095103579877352193/14100000000000000000 : ℝ)) (alpha := (524453772757/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14095103579877352193/14100000000000000000 : ℝ)*(X 0 2+X 1 2)+(524453772757/282000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (14095103579877352193/14100000000000000000 : ℝ)) (alpha := (524453772757/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-273447603/1250000000 : ℝ)*X 0 0+(2697120859/5000000000 : ℝ)*X 0 1+(5264605279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33406311/62500000 : ℝ)*X 1 0+(-1126676061/5000000000 : ℝ)*X 1 1+(263230263/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213800391/400000000 : ℝ)*X 2 0+(5264605259/10000000000 : ℝ)*X 2 1+(-1126676051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109268613/250000000 : ℝ)*X 0 0+(424475711/1000000000 : ℝ)*X 0 1+(2250246041/5000000000 : ℝ)*X 0 2+(109268613/250000000 : ℝ)*X 1 0+(424475711/1000000000 : ℝ)*X 1 1+(2250246041/5000000000 : ℝ)*X 1 2+(109268613/250000000 : ℝ)*X 2 0+(424475711/1000000000 : ℝ)*X 2 1+(2250246041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2187585903/10000000000 : ℝ)*X 0 0+(5264932613/10000000000 : ℝ)*X 0 1+(13484783/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531227243/1000000000 : ℝ)*X 1 0+(-1062022091/5000000000 : ℝ)*X 1 1+(5393913201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531227243/1000000000 : ℝ)*X 2 0+(5393913201/10000000000 : ℝ)*X 2 1+(-1062022091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370754527/10000000000 : ℝ)*X 0 0+(4499846329/10000000000 : ℝ)*X 0 1+(2122702619/5000000000 : ℝ)*X 0 2+(4370754527/10000000000 : ℝ)*X 1 0+(4499846329/10000000000 : ℝ)*X 1 1+(2122702619/5000000000 : ℝ)*X 1 2+(4370754527/10000000000 : ℝ)*X 2 0+(4499846329/10000000000 : ℝ)*X 2 1+(2122702619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (917992865472261980378439747/117500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1628522669/100000000000000 : ℝ)*(base19) + (191684923/12500000000000 : ℝ)*(base23) + (62371677/100000000000000 : ℝ)*(lower2) + (12084449/6250000000000 : ℝ)*(upper3) + (141274039/100000000000000 : ℝ)*(upper5) + (2906077984540579/50000000000000 : ℝ)*(major0) + (2906077984540579/50000000000000 : ℝ)*(major1) + (2906077984540579/50000000000000 : ℝ)*(major2) + (154278486522513/2000000000000 : ℝ)*(sp0) + (1928491562404317/25000000000000 : ℝ)*(sp1) + (964245793082569/12500000000000 : ℝ)*(sp2) + (1955160018621089/50000000000000 : ℝ)*(sp3) + (2722000893/6250000000000 : ℝ)*(sp4) + (594058917/2500000000000 : ℝ)*(sp7) + (3910343799598857/100000000000000 : ℝ)*(f.failure) + (7713967878139937/100000000000000 : ℝ)*(f.sum) + (22864593551503/7050000000000000000000000000 : ℝ)*base65 + (8031071455121710253/705000000000000000000000000000000 : ℝ)*base68 + (7932778833731710253/705000000000000000000000000000000 : ℝ)*base70 + (7742432125398289747/705000000000000000000000000000000 : ℝ)*base71 + (691101551897/7050000000000000000000000000 : ℝ)*base74 + (24049446653381710253/705000000000000000000000000000000 : ℝ)*base76 + (3672918240798289747/705000000000000000000000000000000 : ℝ)*base77 + (3347052670541710253/705000000000000000000000000000000 : ℝ)*base80 + (1873199924297/7050000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (58686203/10000000000000000000000 : ℝ)*base90 + (58686203/10000000000000000000000 : ℝ)*base92 + (58686203/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (680119491316335508532706543/117500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070720991/100000000000000 : ℝ)*(base19) + (1164827509/100000000000000 : ℝ)*(base23) + (116958353/100000000000000 : ℝ)*(upper3) + (10691843/25000000000000 : ℝ)*(lower4) + (118647477/100000000000000 : ℝ)*(upper5) + (5841643156027049/100000000000000 : ℝ)*(major0) + (5841643156027049/100000000000000 : ℝ)*(major1) + (5841643156027049/100000000000000 : ℝ)*(major2) + (7288808771/25000000000000 : ℝ)*(sp1) + (31362051353/100000000000000 : ℝ)*(sp2) + (3876551859650671/50000000000000 : ℝ)*(sp4) + (3876536746672633/50000000000000 : ℝ)*(sp5) + (7753071192422479/100000000000000 : ℝ)*(sp6) + (982545599952761/25000000000000 : ℝ)*(sp7) + (982545599952761/25000000000000 : ℝ)*(f.failure) + (3876551859650671/50000000000000 : ℝ)*(f.sum) + (26074551200107/14100000000000000000000000000 : ℝ)*base66 + (18833205696792118457/1410000000000000000000000000000000 : ℝ)*base67 + (834374940707881543/1410000000000000000000000000000000 : ℝ)*base70 + (8365918013532118457/1410000000000000000000000000000000 : ℝ)*base71 + (44526229198493/14100000000000000000000000000 : ℝ)*base73 + (38223070751832118457/1410000000000000000000000000000000 : ℝ)*base75 + (5794510425282118457/1410000000000000000000000000000000 : ℝ)*base77 + (27845017572192118457/1410000000000000000000000000000000 : ℝ)*base79 + (2780969456707/14100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13652619/2500000000000000000000 : ℝ)*base90 + (13652619/2500000000000000000000 : ℝ)*base92 + (13652619/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1099_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1099_s7_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-27345197/125000000 : ℝ)*x 0 + (2696925153/5000000000 : ℝ)*x 1 + (42119789/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27345197/125000000 : ℝ)^2073 ≤ (2657754878283/20000000000000 : ℝ)^1561 := by
    have hnat : (27345197 : ℕ)^2073*20000000000000^1561 ≤ 2657754878283^1561*125000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27345197 125000000 2657754878283 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696925153/5000000000 : ℝ)^2073 ≤ (8810348646637/20000000000000 : ℝ)^1561 := by
    have hnat : (2696925153 : ℕ)^2073*20000000000000^1561 ≤ 8810348646637^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696925153 5000000000 8810348646637 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42119789/80000000 : ℝ)^2073 ≤ (21329741179953/50000000000000 : ℝ)^1561 := by
    have hnat : (42119789 : ℕ)^2073*50000000000000^1561 ≤ 21329741179953^1561*80000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42119789 80000000 21329741179953 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27345197/125000000 : ℝ), (2696925153/5000000000 : ℝ), (42119789/80000000 : ℝ)] ![(2657754878283/20000000000000 : ℝ), (8810348646637/20000000000000 : ℝ), (21329741179953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27345197/125000000 : ℝ)|^2073 ≤ (2657754878283/20000000000000 : ℝ)^1561
        have hw : |(-27345197/125000000 : ℝ)|=(27345197/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696925153/5000000000 : ℝ)|^2073 ≤ (8810348646637/20000000000000 : ℝ)^1561
        have hw : |(2696925153/5000000000 : ℝ)|=(2696925153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42119789/80000000 : ℝ)|^2073 ≤ (21329741179953/50000000000000 : ℝ)^1561
        have hw : |(42119789/80000000 : ℝ)|=(42119789/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344911351/10000000000 : ℝ)*x 0 + (-1126498017/5000000000 : ℝ)*x 1 + (2632486861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344911351/10000000000 : ℝ)^2073 ≤ (43521753711259/100000000000000 : ℝ)^1561 := by
    have hnat : (5344911351 : ℕ)^2073*100000000000000^1561 ≤ 43521753711259^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344911351 10000000000 43521753711259 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126498017/5000000000 : ℝ)^2073 ≤ (2763752574047/20000000000000 : ℝ)^1561 := by
    have hnat : (1126498017 : ℕ)^2073*20000000000000^1561 ≤ 2763752574047^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126498017 5000000000 2763752574047 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632486861/5000000000 : ℝ)^2073 ≤ (21329741701817/50000000000000 : ℝ)^1561 := by
    have hnat : (2632486861 : ℕ)^2073*50000000000000^1561 ≤ 21329741701817^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632486861 5000000000 21329741701817 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344911351/10000000000 : ℝ), (-1126498017/5000000000 : ℝ), (2632486861/5000000000 : ℝ)] ![(43521753711259/100000000000000 : ℝ), (2763752574047/20000000000000 : ℝ), (21329741701817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344911351/10000000000 : ℝ)|^2073 ≤ (43521753711259/100000000000000 : ℝ)^1561
        have hw : |(5344911351/10000000000 : ℝ)|=(5344911351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126498017/5000000000 : ℝ)|^2073 ≤ (2763752574047/20000000000000 : ℝ)^1561
        have hw : |(-1126498017/5000000000 : ℝ)|=(1126498017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632486861/5000000000 : ℝ)|^2073 ≤ (21329741701817/50000000000000 : ℝ)^1561
        have hw : |(2632486861/5000000000 : ℝ)|=(2632486861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672455797/5000000000 : ℝ)*x 0 + (2632486779/5000000000 : ℝ)*x 1 + (-281624491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672455797/5000000000 : ℝ)^2073 ≤ (10880439084729/25000000000000 : ℝ)^1561 := by
    have hnat : (2672455797 : ℕ)^2073*25000000000000^1561 ≤ 10880439084729^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672455797 5000000000 10880439084729 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632486779/5000000000 : ℝ)^2073 ≤ (2132974081949/5000000000000 : ℝ)^1561 := by
    have hnat : (2632486779 : ℕ)^2073*5000000000000^1561 ≤ 2132974081949^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632486779 5000000000 2132974081949 5000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281624491/1250000000 : ℝ)^2073 ≤ (13818762006837/100000000000000 : ℝ)^1561 := by
    have hnat : (281624491 : ℕ)^2073*100000000000000^1561 ≤ 13818762006837^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281624491 1250000000 13818762006837 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672455797/5000000000 : ℝ), (2632486779/5000000000 : ℝ), (-281624491/1250000000 : ℝ)] ![(10880439084729/25000000000000 : ℝ), (2132974081949/5000000000000 : ℝ), (13818762006837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672455797/5000000000 : ℝ)|^2073 ≤ (10880439084729/25000000000000 : ℝ)^1561
        have hw : |(2672455797/5000000000 : ℝ)|=(2672455797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632486779/5000000000 : ℝ)|^2073 ≤ (2132974081949/5000000000000 : ℝ)^1561
        have hw : |(2632486779/5000000000 : ℝ)|=(2632486779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281624491/1250000000 : ℝ)|^2073 ≤ (13818762006837/100000000000000 : ℝ)^1561
        have hw : |(-281624491/1250000000 : ℝ)|=(281624491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (437076399/1000000000 : ℝ)*x 0 + (1061376041/2500000000 : ℝ)*x 1 + (44997399/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437076399/1000000000 : ℝ)^2073 ≤ (6663340507653/20000000000000 : ℝ)^1561 := by
    have hnat : (437076399 : ℕ)^2073*20000000000000^1561 ≤ 6663340507653^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437076399 1000000000 6663340507653 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061376041/2500000000 : ℝ)^2073 ≤ (4006839919781/12500000000000 : ℝ)^1561 := by
    have hnat : (1061376041 : ℕ)^2073*12500000000000^1561 ≤ 4006839919781^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061376041 2500000000 4006839919781 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44997399/100000000 : ℝ)^2073 ≤ (34628578085461/100000000000000 : ℝ)^1561 := by
    have hnat : (44997399 : ℕ)^2073*100000000000000^1561 ≤ 34628578085461^1561*100000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44997399 100000000 34628578085461 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437076399/1000000000 : ℝ), (1061376041/2500000000 : ℝ), (44997399/100000000 : ℝ)] ![(6663340507653/20000000000000 : ℝ), (4006839919781/12500000000000 : ℝ), (34628578085461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437076399/1000000000 : ℝ)|^2073 ≤ (6663340507653/20000000000000 : ℝ)^1561
        have hw : |(437076399/1000000000 : ℝ)|=(437076399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061376041/2500000000 : ℝ)|^2073 ≤ (4006839919781/12500000000000 : ℝ)^1561
        have hw : |(1061376041/2500000000 : ℝ)|=(1061376041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44997399/100000000 : ℝ)|^2073 ≤ (34628578085461/100000000000000 : ℝ)^1561
        have hw : |(44997399/100000000 : ℝ)|=(44997399/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093810431/5000000000 : ℝ)*x 0 + (1316324301/2500000000 : ℝ)*x 1 + (5393525483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093810431/5000000000 : ℝ)^2073 ≤ (1661101943637/12500000000000 : ℝ)^1561 := by
    have hnat : (1093810431 : ℕ)^2073*12500000000000^1561 ≤ 1661101943637^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093810431 5000000000 1661101943637 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316324301/2500000000 : ℝ)^2073 ≤ (4266296413317/10000000000000 : ℝ)^1561 := by
    have hnat : (1316324301 : ℕ)^2073*10000000000000^1561 ≤ 4266296413317^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316324301 2500000000 4266296413317 10000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393525483/10000000000 : ℝ)^2073 ≤ (44048220310659/100000000000000 : ℝ)^1561 := by
    have hnat : (5393525483 : ℕ)^2073*100000000000000^1561 ≤ 44048220310659^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393525483 10000000000 44048220310659 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093810431/5000000000 : ℝ), (1316324301/2500000000 : ℝ), (5393525483/10000000000 : ℝ)] ![(1661101943637/12500000000000 : ℝ), (4266296413317/10000000000000 : ℝ), (44048220310659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093810431/5000000000 : ℝ)|^2073 ≤ (1661101943637/12500000000000 : ℝ)^1561
        have hw : |(-1093810431/5000000000 : ℝ)|=(1093810431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316324301/2500000000 : ℝ)|^2073 ≤ (4266296413317/10000000000000 : ℝ)^1561
        have hw : |(1316324301/2500000000 : ℝ)|=(1316324301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393525483/10000000000 : ℝ)|^2073 ≤ (44048220310659/100000000000000 : ℝ)^1561
        have hw : |(5393525483/10000000000 : ℝ)|=(5393525483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656182953/5000000000 : ℝ)*x 0 + (-424888849/2000000000 : ℝ)*x 1 + (5393525481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656182953/5000000000 : ℝ)^2073 ≤ (43170178698193/100000000000000 : ℝ)^1561 := by
    have hnat : (2656182953 : ℕ)^2073*100000000000000^1561 ≤ 43170178698193^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656182953 5000000000 43170178698193 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424888849/2000000000 : ℝ)^2073 ≤ (12482032231/97656250000 : ℝ)^1561 := by
    have hnat : (424888849 : ℕ)^2073*97656250000^1561 ≤ 12482032231^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424888849 2000000000 12482032231 97656250000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393525481/10000000000 : ℝ)^2073 ≤ (44048220288967/100000000000000 : ℝ)^1561 := by
    have hnat : (5393525481 : ℕ)^2073*100000000000000^1561 ≤ 44048220288967^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393525481 10000000000 44048220288967 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656182953/5000000000 : ℝ), (-424888849/2000000000 : ℝ), (5393525481/10000000000 : ℝ)] ![(43170178698193/100000000000000 : ℝ), (12482032231/97656250000 : ℝ), (44048220288967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656182953/5000000000 : ℝ)|^2073 ≤ (43170178698193/100000000000000 : ℝ)^1561
        have hw : |(2656182953/5000000000 : ℝ)|=(2656182953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424888849/2000000000 : ℝ)|^2073 ≤ (12482032231/97656250000 : ℝ)^1561
        have hw : |(-424888849/2000000000 : ℝ)|=(424888849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393525481/10000000000 : ℝ)|^2073 ≤ (44048220288967/100000000000000 : ℝ)^1561
        have hw : |(5393525481/10000000000 : ℝ)|=(5393525481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312365907/10000000000 : ℝ)*x 0 + (134838137/250000000 : ℝ)*x 1 + (-531111061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312365907/10000000000 : ℝ)^2073 ≤ (5396272338623/12500000000000 : ℝ)^1561 := by
    have hnat : (5312365907 : ℕ)^2073*12500000000000^1561 ≤ 5396272338623^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312365907 10000000000 5396272338623 12500000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134838137/250000000 : ℝ)^2073 ≤ (22024110139061/50000000000000 : ℝ)^1561 := by
    have hnat : (134838137 : ℕ)^2073*50000000000000^1561 ≤ 22024110139061^1561*250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134838137 250000000 22024110139061 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531111061/2500000000 : ℝ)^2073 ≤ (6390800498277/50000000000000 : ℝ)^1561 := by
    have hnat : (531111061 : ℕ)^2073*50000000000000^1561 ≤ 6390800498277^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531111061 2500000000 6390800498277 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312365907/10000000000 : ℝ), (134838137/250000000 : ℝ), (-531111061/2500000000 : ℝ)] ![(5396272338623/12500000000000 : ℝ), (22024110139061/50000000000000 : ℝ), (6390800498277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312365907/10000000000 : ℝ)|^2073 ≤ (5396272338623/12500000000000 : ℝ)^1561
        have hw : |(5312365907/10000000000 : ℝ)|=(5312365907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134838137/250000000 : ℝ)|^2073 ≤ (22024110139061/50000000000000 : ℝ)^1561
        have hw : |(134838137/250000000 : ℝ)|=(134838137/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531111061/2500000000 : ℝ)|^2073 ≤ (6390800498277/50000000000000 : ℝ)^1561
        have hw : |(-531111061/2500000000 : ℝ)|=(531111061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s7_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4370773771/10000000000 : ℝ)*x 0 + (4499101727/10000000000 : ℝ)*x 1 + (2123072361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370773771/10000000000 : ℝ)^2073 ≤ (33316801549499/100000000000000 : ℝ)^1561 := by
    have hnat : (4370773771 : ℕ)^2073*100000000000000^1561 ≤ 33316801549499^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370773771 10000000000 33316801549499 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499101727/10000000000 : ℝ)^2073 ≤ (34622056217957/100000000000000 : ℝ)^1561 := by
    have hnat : (4499101727 : ℕ)^2073*100000000000000^1561 ≤ 34622056217957^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499101727 10000000000 34622056217957 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123072361/5000000000 : ℝ)^2073 ≤ (32061142216121/100000000000000 : ℝ)^1561 := by
    have hnat : (2123072361 : ℕ)^2073*100000000000000^1561 ≤ 32061142216121^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123072361 5000000000 32061142216121 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370773771/10000000000 : ℝ), (4499101727/10000000000 : ℝ), (2123072361/5000000000 : ℝ)] ![(33316801549499/100000000000000 : ℝ), (34622056217957/100000000000000 : ℝ), (32061142216121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370773771/10000000000 : ℝ)|^2073 ≤ (33316801549499/100000000000000 : ℝ)^1561
        have hw : |(4370773771/10000000000 : ℝ)|=(4370773771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499101727/10000000000 : ℝ)|^2073 ≤ (34622056217957/100000000000000 : ℝ)^1561
        have hw : |(4499101727/10000000000 : ℝ)|=(4499101727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123072361/5000000000 : ℝ)|^2073 ≤ (32061142216121/100000000000000 : ℝ)^1561
        have hw : |(2123072361/5000000000 : ℝ)|=(2123072361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (561/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11287/100000 : ℝ) ^ (8291/2048 : ℝ) ≤ (7302741004744687/50000000000000000000 : ℝ) := by
    have hpowers : (11287/100000 : ℝ)^8291 ≤ (7302741004744687/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11287 : ℕ)^8291*50000000000000000000^2048 ≤ 7302741004744687^2048*100000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11287 100000 7302741004744687 50000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11287/100000 : ℝ)) (X := (7302741004744687/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/100000 : ℝ) ^ (8291/2048 : ℝ) ≤ (7053513244315989/20000000000000000000 : ℝ) := by
    have hpowers : (14033/100000 : ℝ)^8291 ≤ (7053513244315989/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14033 : ℕ)^8291*20000000000000000000^2048 ≤ 7053513244315989^2048*100000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 100000 7053513244315989 20000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/100000 : ℝ)) (X := (7053513244315989/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007302741004744687/25000000000000000000 : ℝ) ≤ (10000721474805897/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (25007302741004744687/25000000000000000000 : ℝ)^2048 ≤ (10000721474805897/10000000000000000 : ℝ)^8291 := by
      have hnat : (25007302741004744687 : ℕ)^2048*10000000000000000^8291 ≤ 10000721474805897^8291*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007302741004744687 25000000000000000000 10000721474805897 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000721474805897/10000000000000000 : ℝ)) (X := (25007302741004744687/25000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049873048231069319/100000000000000000000 : ℝ) ≤ (10001231707028187/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (100049873048231069319/100000000000000000000 : ℝ)^2048 ≤ (10001231707028187/10000000000000000 : ℝ)^8291 := by
      have hnat : (100049873048231069319 : ℕ)^2048*10000000000000000^8291 ≤ 10001231707028187^8291*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049873048231069319 100000000000000000000 10001231707028187 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001231707028187/10000000000000000 : ℝ)) (X := (100049873048231069319/100000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007053513244315989/10000000000000000000 : ℝ) ≤ (10001741939250477/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (10007053513244315989/10000000000000000000 : ℝ)^2048 ≤ (10001741939250477/10000000000000000 : ℝ)^8291 := by
      have hnat : (10007053513244315989 : ℕ)^2048*10000000000000000^8291 ≤ 10001741939250477^8291*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007053513244315989 10000000000000000000 10001741939250477 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001741939250477/10000000000000000 : ℝ)) (X := (10007053513244315989/10000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7302741004744687/50000000000000000000 : ℝ) ≤ ((13725231593815509351/13730000000000000000 : ℝ)+2*(51023222229/27460000000000 : ℝ)*(11287/100000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (13725231593815509351/13730000000000000000 : ℝ)+2*(51023222229/27460000000000 : ℝ)*(11287/100000 : ℝ)=(10000721474805897/10000000000000000 : ℝ) by norm_num, show 1+2*(7302741004744687/50000000000000000000 : ℝ)=(25007302741004744687/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7053513244315989/20000000000000000000 : ℝ)+(7302741004744687/50000000000000000000 : ℝ) ≤ ((13725231593815509351/13730000000000000000 : ℝ)+(51023222229/27460000000000 : ℝ)*((14033/100000 : ℝ)+(11287/100000 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (13725231593815509351/13730000000000000000 : ℝ)+(51023222229/27460000000000 : ℝ)*((14033/100000 : ℝ)+(11287/100000 : ℝ))=(10001231707028187/10000000000000000 : ℝ) by norm_num, show 1+(7053513244315989/20000000000000000000 : ℝ)+(7302741004744687/50000000000000000000 : ℝ)=(100049873048231069319/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7053513244315989/20000000000000000000 : ℝ) ≤ ((13725231593815509351/13730000000000000000 : ℝ)+2*(51023222229/27460000000000 : ℝ)*(14033/100000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (13725231593815509351/13730000000000000000 : ℝ)+2*(51023222229/27460000000000 : ℝ)*(14033/100000 : ℝ)=(10001741939250477/10000000000000000 : ℝ) by norm_num, show 1+2*(7053513244315989/20000000000000000000 : ℝ)=(10007053513244315989/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13725231593815509351/13730000000000000000 : ℝ)*(X 1 0+X 2 0)+(51023222229/27460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (13725231593815509351/13730000000000000000 : ℝ)) (alpha := (51023222229/27460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13725231593815509351/13730000000000000000 : ℝ)*(X 0 1+X 2 1)+(51023222229/27460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (13725231593815509351/13730000000000000000 : ℝ)) (alpha := (51023222229/27460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13725231593815509351/13730000000000000000 : ℝ)*(X 0 2+X 1 2)+(51023222229/27460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (13725231593815509351/13730000000000000000 : ℝ)) (alpha := (51023222229/27460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27345197/125000000 : ℝ)*X 0 0+(2696925153/5000000000 : ℝ)*X 0 1+(42119789/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344911351/10000000000 : ℝ)*X 1 0+(-1126498017/5000000000 : ℝ)*X 1 1+(2632486861/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672455797/5000000000 : ℝ)*X 2 0+(2632486779/5000000000 : ℝ)*X 2 1+(-281624491/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437076399/1000000000 : ℝ)*X 0 0+(1061376041/2500000000 : ℝ)*X 0 1+(44997399/100000000 : ℝ)*X 0 2+(437076399/1000000000 : ℝ)*X 1 0+(1061376041/2500000000 : ℝ)*X 1 1+(44997399/100000000 : ℝ)*X 1 2+(437076399/1000000000 : ℝ)*X 2 0+(1061376041/2500000000 : ℝ)*X 2 1+(44997399/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093810431/5000000000 : ℝ)*X 0 0+(1316324301/2500000000 : ℝ)*X 0 1+(5393525483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656182953/5000000000 : ℝ)*X 1 0+(-424888849/2000000000 : ℝ)*X 1 1+(5393525481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312365907/10000000000 : ℝ)*X 2 0+(134838137/250000000 : ℝ)*X 2 1+(-531111061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370773771/10000000000 : ℝ)*X 0 0+(4499101727/10000000000 : ℝ)*X 0 1+(2123072361/5000000000 : ℝ)*X 0 2+(4370773771/10000000000 : ℝ)*X 1 0+(4499101727/10000000000 : ℝ)*X 1 1+(2123072361/5000000000 : ℝ)*X 1 2+(4370773771/10000000000 : ℝ)*X 2 0+(4499101727/10000000000 : ℝ)*X 2 1+(2123072361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132891330260710721856577053/21453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169072073/12500000000000 : ℝ)*(base19) + (44075021/3125000000000 : ℝ)*(base23) + (78823987/50000000000000 : ℝ)*(lower2) + (9342683/10000000000000 : ℝ)*(upper3) + (21755513/20000000000000 : ℝ)*(upper5) + (365401234179499/6250000000000 : ℝ)*(major0) + (365401234179499/6250000000000 : ℝ)*(major1) + (365401234179499/6250000000000 : ℝ)*(major2) + (155187897019547/2000000000000 : ℝ)*(sp0) + (7759441905973051/100000000000000 : ℝ)*(sp1) + (7759441848148963/100000000000000 : ℝ)*(sp2) + (983343765773021/25000000000000 : ℝ)*(sp3) + (9681514457/20000000000000 : ℝ)*(sp4) + (5241404747/25000000000000 : ℝ)*(sp7) + (122918625897221/3125000000000 : ℝ)*(f.failure) + (1551888651709927/20000000000000 : ℝ)*(f.sum) + (826304361719/686500000000000000000000000 : ℝ)*base66 + (584597878950245149/85812500000000000000000000000000 : ℝ)*base67 + (176467188807932649/85812500000000000000000000000000 : ℝ)*base69 + (464526410210182649/85812500000000000000000000000000 : ℝ)*base71 + (2998065572861/686500000000000000000000000 : ℝ)*base73 + (323024497538379851/85812500000000000000000000000000 : ℝ)*base76 + (53675457639370149/85812500000000000000000000000000 : ℝ)*base77 + (318136326667620149/85812500000000000000000000000000 : ℝ)*base79 + (39367599111/17162500000000000000000000 : ℝ)*base81 + (3934959/312500000000000000000 : ℝ)*base90 + (3934959/312500000000000000000 : ℝ)*base92 + (3934959/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2673782471503196825181189993/343250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (715032453/50000000000000 : ℝ)*(base19) + (155853763/10000000000000 : ℝ)*(base23) + (30981961/20000000000000 : ℝ)*(upper3) + (3604681/6250000000000 : ℝ)*(lower4) + (9870587/6250000000000 : ℝ)*(upper5) + (5875915582609019/100000000000000 : ℝ)*(major0) + (5875915582609019/100000000000000 : ℝ)*(major1) + (5875915582609019/100000000000000 : ℝ)*(major2) + (19536342233/50000000000000 : ℝ)*(sp1) + (42081903469/100000000000000 : ℝ)*(sp2) + (7798590457845749/100000000000000 : ℝ)*(sp4) + (7798549955096377/100000000000000 : ℝ)*(sp5) + (155970936348093/2000000000000 : ℝ)*(sp6) + (395324044771873/10000000000000 : ℝ)*(sp7) + (395324044771873/10000000000000 : ℝ)*(f.failure) + (7798590457845749/100000000000000 : ℝ)*(f.sum) + (844506235053/274600000000000000000000000 : ℝ)*base66 + (5213127145908936669/1373000000000000000000000000000000 : ℝ)*base67 + (16064450969175936669/1373000000000000000000000000000000 : ℝ)*base69 + (19889973436687063331/1373000000000000000000000000000000 : ℝ)*base72 + (1043323210739/686500000000000000000000000 : ℝ)*base73 + (13135618139969936669/1373000000000000000000000000000000 : ℝ)*base75 + (91994409328936669/1373000000000000000000000000000000 : ℝ)*base77 + (5534451837970936669/1373000000000000000000000000000000 : ℝ)*base79 + (317129888307/1373000000000000000000000000 : ℝ)*base81 + (2313533/1000000000000000000000 : ℝ)*base89 + (2313533/1000000000000000000000 : ℝ)*base91 + (2313533/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1099_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1099_s8_0 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187621883/10000000000 : ℝ)*x 0 + (1348441827/2500000000 : ℝ)*x 1 + (1316263173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187621883/10000000000 : ℝ)^2073 ≤ (13288823785477/100000000000000 : ℝ)^1561 := by
    have hnat : (2187621883 : ℕ)^2073*100000000000000^1561 ≤ 13288823785477^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187621883 10000000000 13288823785477 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348441827/2500000000 : ℝ)^2073 ≤ (22025421528893/50000000000000 : ℝ)^1561 := by
    have hnat : (1348441827 : ℕ)^2073*50000000000000^1561 ≤ 22025421528893^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348441827 2500000000 22025421528893 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316263173/2500000000 : ℝ)^2073 ≤ (8532066625959/20000000000000 : ℝ)^1561 := by
    have hnat : (1316263173 : ℕ)^2073*20000000000000^1561 ≤ 8532066625959^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316263173 2500000000 8532066625959 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187621883/10000000000 : ℝ), (1348441827/2500000000 : ℝ), (1316263173/2500000000 : ℝ)] ![(13288823785477/100000000000000 : ℝ), (22025421528893/50000000000000 : ℝ), (8532066625959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187621883/10000000000 : ℝ)|^2073 ≤ (13288823785477/100000000000000 : ℝ)^1561
        have hw : |(-2187621883/10000000000 : ℝ)|=(2187621883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348441827/2500000000 : ℝ)|^2073 ≤ (22025421528893/50000000000000 : ℝ)^1561
        have hw : |(1348441827/2500000000 : ℝ)|=(1348441827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316263173/2500000000 : ℝ)|^2073 ≤ (8532066625959/20000000000000 : ℝ)^1561
        have hw : |(1316263173/2500000000 : ℝ)|=(1316263173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_1 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668111369/1250000000 : ℝ)*x 0 + (-563229707/2500000000 : ℝ)*x 1 + (1053010533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668111369/1250000000 : ℝ)^2073 ≤ (8704306625769/20000000000000 : ℝ)^1561 := by
    have hnat : (668111369 : ℕ)^2073*20000000000000^1561 ≤ 8704306625769^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668111369 1250000000 8704306625769 20000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563229707/2500000000 : ℝ)^2073 ≤ (6909067005279/50000000000000 : ℝ)^1561 := by
    have hnat : (563229707 : ℕ)^2073*50000000000000^1561 ≤ 6909067005279^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563229707 2500000000 6909067005279 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053010533/2000000000 : ℝ)^2073 ≤ (42660332839271/100000000000000 : ℝ)^1561 := by
    have hnat : (1053010533 : ℕ)^2073*100000000000000^1561 ≤ 42660332839271^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053010533 2000000000 42660332839271 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668111369/1250000000 : ℝ), (-563229707/2500000000 : ℝ), (1053010533/2000000000 : ℝ)] ![(8704306625769/20000000000000 : ℝ), (6909067005279/50000000000000 : ℝ), (42660332839271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668111369/1250000000 : ℝ)|^2073 ≤ (8704306625769/20000000000000 : ℝ)^1561
        have hw : |(668111369/1250000000 : ℝ)|=(668111369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563229707/2500000000 : ℝ)|^2073 ≤ (6909067005279/50000000000000 : ℝ)^1561
        have hw : |(-563229707/2500000000 : ℝ)|=(563229707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053010533/2000000000 : ℝ)|^2073 ≤ (42660332839271/100000000000000 : ℝ)^1561
        have hw : |(1053010533/2000000000 : ℝ)|=(1053010533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_2 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344891/10000000 : ℝ)*x 0 + (5265052661/10000000000 : ℝ)*x 1 + (-225291877/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344891/10000000 : ℝ)^2073 ≤ (2720095852993/6250000000000 : ℝ)^1561 := by
    have hnat : (5344891 : ℕ)^2073*6250000000000^1561 ≤ 2720095852993^1561*10000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344891 10000000 2720095852993 6250000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265052661/10000000000 : ℝ)^2073 ≤ (42660332796231/100000000000000 : ℝ)^1561 := by
    have hnat : (5265052661 : ℕ)^2073*100000000000000^1561 ≤ 42660332796231^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265052661 10000000000 42660332796231 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225291877/1000000000 : ℝ)^2073 ≤ (6909066769069/50000000000000 : ℝ)^1561 := by
    have hnat : (225291877 : ℕ)^2073*50000000000000^1561 ≤ 6909066769069^1561*1000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225291877 1000000000 6909066769069 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344891/10000000 : ℝ), (5265052661/10000000000 : ℝ), (-225291877/1000000000 : ℝ)] ![(2720095852993/6250000000000 : ℝ), (42660332796231/100000000000000 : ℝ), (6909066769069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344891/10000000 : ℝ)|^2073 ≤ (2720095852993/6250000000000 : ℝ)^1561
        have hw : |(5344891/10000000 : ℝ)|=(5344891/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265052661/10000000000 : ℝ)|^2073 ≤ (42660332796231/100000000000000 : ℝ)^1561
        have hw : |(5265052661/10000000000 : ℝ)|=(5265052661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225291877/1000000000 : ℝ)|^2073 ≤ (6909066769069/50000000000000 : ℝ)^1561
        have hw : |(-225291877/1000000000 : ℝ)|=(225291877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_3 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (546346009/1250000000 : ℝ)*x 0 + (849132659/2000000000 : ℝ)*x 1 + (4499579731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546346009/1250000000 : ℝ)^2073 ≤ (33316743859579/100000000000000 : ℝ)^1561 := by
    have hnat : (546346009 : ℕ)^2073*100000000000000^1561 ≤ 33316743859579^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546346009 1250000000 33316743859579 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849132659/2000000000 : ℝ)^2073 ≤ (32056314930843/100000000000000 : ℝ)^1561 := by
    have hnat : (849132659 : ℕ)^2073*100000000000000^1561 ≤ 32056314930843^1561*2000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849132659 2000000000 32056314930843 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499579731/10000000000 : ℝ)^2073 ≤ (34626941195157/100000000000000 : ℝ)^1561 := by
    have hnat : (4499579731 : ℕ)^2073*100000000000000^1561 ≤ 34626941195157^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499579731 10000000000 34626941195157 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546346009/1250000000 : ℝ), (849132659/2000000000 : ℝ), (4499579731/10000000000 : ℝ)] ![(33316743859579/100000000000000 : ℝ), (32056314930843/100000000000000 : ℝ), (34626941195157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546346009/1250000000 : ℝ)|^2073 ≤ (33316743859579/100000000000000 : ℝ)^1561
        have hw : |(546346009/1250000000 : ℝ)|=(546346009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849132659/2000000000 : ℝ)|^2073 ≤ (32056314930843/100000000000000 : ℝ)^1561
        have hw : |(849132659/2000000000 : ℝ)|=(849132659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499579731/10000000000 : ℝ)|^2073 ≤ (34626941195157/100000000000000 : ℝ)^1561
        have hw : |(4499579731/10000000000 : ℝ)|=(4499579731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_4 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187626839/10000000000 : ℝ)*x 0 + (1316343833/2500000000 : ℝ)*x 1 + (2696721761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187626839/10000000000 : ℝ)^2073 ≤ (13288863765417/100000000000000 : ℝ)^1561 := by
    have hnat : (2187626839 : ℕ)^2073*100000000000000^1561 ≤ 13288863765417^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187626839 10000000000 13288863765417 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316343833/2500000000 : ℝ)^2073 ≤ (21331902408117/50000000000000 : ℝ)^1561 := by
    have hnat : (1316343833 : ℕ)^2073*50000000000000^1561 ≤ 21331902408117^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316343833 2500000000 21331902408117 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696721761/5000000000 : ℝ)^2073 ≤ (44047331399831/100000000000000 : ℝ)^1561 := by
    have hnat : (2696721761 : ℕ)^2073*100000000000000^1561 ≤ 44047331399831^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696721761 5000000000 44047331399831 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187626839/10000000000 : ℝ), (1316343833/2500000000 : ℝ), (2696721761/5000000000 : ℝ)] ![(13288863765417/100000000000000 : ℝ), (21331902408117/50000000000000 : ℝ), (44047331399831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187626839/10000000000 : ℝ)|^2073 ≤ (13288863765417/100000000000000 : ℝ)^1561
        have hw : |(-2187626839/10000000000 : ℝ)|=(2187626839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316343833/2500000000 : ℝ)|^2073 ≤ (21331902408117/50000000000000 : ℝ)^1561
        have hw : |(1316343833/2500000000 : ℝ)|=(1316343833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696721761/5000000000 : ℝ)|^2073 ≤ (44047331399831/100000000000000 : ℝ)^1561
        have hw : |(2696721761/5000000000 : ℝ)|=(2696721761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_5 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106247729/200000000 : ℝ)*x 0 + (-2124527733/10000000000 : ℝ)*x 1 + (5393443533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106247729/200000000 : ℝ)^2073 ≤ (10792600101061/25000000000000 : ℝ)^1561 := by
    have hnat : (106247729 : ℕ)^2073*25000000000000^1561 ≤ 10792600101061^1561*200000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106247729 200000000 10792600101061 25000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124527733/10000000000 : ℝ)^2073 ≤ (6391134030947/50000000000000 : ℝ)^1561 := by
    have hnat : (2124527733 : ℕ)^2073*50000000000000^1561 ≤ 6391134030947^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124527733 10000000000 6391134030947 50000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393443533/10000000000 : ℝ)^2073 ≤ (44047331519131/100000000000000 : ℝ)^1561 := by
    have hnat : (5393443533 : ℕ)^2073*100000000000000^1561 ≤ 44047331519131^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393443533 10000000000 44047331519131 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106247729/200000000 : ℝ), (-2124527733/10000000000 : ℝ), (5393443533/10000000000 : ℝ)] ![(10792600101061/25000000000000 : ℝ), (6391134030947/50000000000000 : ℝ), (44047331519131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106247729/200000000 : ℝ)|^2073 ≤ (10792600101061/25000000000000 : ℝ)^1561
        have hw : |(106247729/200000000 : ℝ)|=(106247729/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124527733/10000000000 : ℝ)|^2073 ≤ (6391134030947/50000000000000 : ℝ)^1561
        have hw : |(-2124527733/10000000000 : ℝ)|=(2124527733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393443533/10000000000 : ℝ)|^2073 ≤ (44047331519131/100000000000000 : ℝ)^1561
        have hw : |(5393443533/10000000000 : ℝ)|=(5393443533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_6 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656193033/5000000000 : ℝ)*x 0 + (5393443477/10000000000 : ℝ)*x 1 + (-265566041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656193033/5000000000 : ℝ)^2073 ≤ (43170396260203/100000000000000 : ℝ)^1561 := by
    have hnat : (2656193033 : ℕ)^2073*100000000000000^1561 ≤ 43170396260203^1561*5000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656193033 5000000000 43170396260203 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393443477/10000000000 : ℝ)^2073 ≤ (44047330911783/100000000000000 : ℝ)^1561 := by
    have hnat : (5393443477 : ℕ)^2073*100000000000000^1561 ≤ 44047330911783^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393443477 10000000000 44047330911783 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265566041/1250000000 : ℝ)^2073 ≤ (12782272815891/100000000000000 : ℝ)^1561 := by
    have hnat : (265566041 : ℕ)^2073*100000000000000^1561 ≤ 12782272815891^1561*1250000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265566041 1250000000 12782272815891 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656193033/5000000000 : ℝ), (5393443477/10000000000 : ℝ), (-265566041/1250000000 : ℝ)] ![(43170396260203/100000000000000 : ℝ), (44047330911783/100000000000000 : ℝ), (12782272815891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656193033/5000000000 : ℝ)|^2073 ≤ (43170396260203/100000000000000 : ℝ)^1561
        have hw : |(2656193033/5000000000 : ℝ)|=(2656193033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393443477/10000000000 : ℝ)|^2073 ≤ (44047330911783/100000000000000 : ℝ)^1561
        have hw : |(5393443477/10000000000 : ℝ)|=(5393443477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265566041/1250000000 : ℝ)|^2073 ≤ (12782272815891/100000000000000 : ℝ)^1561
        have hw : |(-265566041/1250000000 : ℝ)|=(265566041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1099_s8_7 (p : ℝ) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092694377/2500000000 : ℝ)*x 0 + (4498943169/10000000000 : ℝ)*x 1 + (4246302543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092694377/2500000000 : ℝ)^2073 ≤ (3331683937847/10000000000000 : ℝ)^1561 := by
    have hnat : (1092694377 : ℕ)^2073*10000000000000^1561 ≤ 3331683937847^1561*2500000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092694377 2500000000 3331683937847 10000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498943169/10000000000 : ℝ)^2073 ≤ (34620435866991/100000000000000 : ℝ)^1561 := by
    have hnat : (4498943169 : ℕ)^2073*100000000000000^1561 ≤ 34620435866991^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498943169 10000000000 34620435866991 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246302543/10000000000 : ℝ)^2073 ≤ (32062724731851/100000000000000 : ℝ)^1561 := by
    have hnat : (4246302543 : ℕ)^2073*100000000000000^1561 ≤ 32062724731851^1561*10000000000^2073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246302543 10000000000 32062724731851 100000000000000 2073 1561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2073/512 : ℝ)) 2073 1561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092694377/2500000000 : ℝ), (4498943169/10000000000 : ℝ), (4246302543/10000000000 : ℝ)] ![(3331683937847/10000000000000 : ℝ), (34620435866991/100000000000000 : ℝ), (32062724731851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092694377/2500000000 : ℝ)|^2073 ≤ (3331683937847/10000000000000 : ℝ)^1561
        have hw : |(1092694377/2500000000 : ℝ)|=(1092694377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498943169/10000000000 : ℝ)|^2073 ≤ (34620435866991/100000000000000 : ℝ)^1561
        have hw : |(4498943169/10000000000 : ℝ)|=(4498943169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246302543/10000000000 : ℝ)|^2073 ≤ (32062724731851/100000000000000 : ℝ)^1561
        have hw : |(4246302543/10000000000 : ℝ)|=(4246302543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1099_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2259/20000 : ℝ) ^ (8291/2048 : ℝ) ≤ (14647436017940299/100000000000000000000 : ℝ) := by
    have hpowers : (2259/20000 : ℝ)^8291 ≤ (14647436017940299/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2259 : ℕ)^8291*100000000000000000000^2048 ≤ 14647436017940299^2048*20000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 20000 14647436017940299 100000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/20000 : ℝ)) (X := (14647436017940299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (561/4000 : ℝ) ^ (8291/2048 : ℝ) ≤ (35186243007066751/100000000000000000000 : ℝ) := by
    have hpowers : (561/4000 : ℝ)^8291 ≤ (35186243007066751/100000000000000000000 : ℝ)^2048 := by
      have hnat : (561 : ℕ)^8291*100000000000000000000^2048 ≤ 35186243007066751^2048*4000^8291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 4000 35186243007066751 100000000000000000000 8291 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/4000 : ℝ)) (X := (35186243007066751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014647436017940299/50000000000000000000 : ℝ) ≤ (10000723547001969/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (50014647436017940299/50000000000000000000 : ℝ)^2048 ≤ (10000723547001969/10000000000000000 : ℝ)^8291 := by
      have hnat : (50014647436017940299 : ℕ)^2048*10000000000000000^8291 ≤ 10000723547001969^8291*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014647436017940299 50000000000000000000 10000723547001969 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000723547001969/10000000000000000 : ℝ)) (X := (50014647436017940299/50000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000996673580500141/2000000000000000000 : ℝ) ≤ (10001230734915289/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (2000996673580500141/2000000000000000000 : ℝ)^2048 ≤ (10001230734915289/10000000000000000 : ℝ)^8291 := by
      have hnat : (2000996673580500141 : ℕ)^2048*10000000000000000^8291 ≤ 10001230734915289^8291*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000996673580500141 2000000000000000000 10001230734915289 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001230734915289/10000000000000000 : ℝ)) (X := (2000996673580500141/2000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035186243007066751/50000000000000000000 : ℝ) ≤ (10001737922828609/10000000000000000 : ℝ) ^ (8291/2048 : ℝ) := by
    have hpowers : (50035186243007066751/50000000000000000000 : ℝ)^2048 ≤ (10001737922828609/10000000000000000 : ℝ)^8291 := by
      have hnat : (50035186243007066751 : ℕ)^2048*10000000000000000^8291 ≤ 10001737922828609^8291*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035186243007066751 50000000000000000000 10001737922828609 10000000000000000 2048 8291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001737922828609/10000000000000000 : ℝ)) (X := (50035186243007066751/50000000000000000000 : ℝ)) (by norm_num) 8291 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14647436017940299/100000000000000000000 : ℝ) ≤ ((909683930278449219/910000000000000000 : ℝ)+2*(12679697833/6825000000000 : ℝ)*(2259/20000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (909683930278449219/910000000000000000 : ℝ)+2*(12679697833/6825000000000 : ℝ)*(2259/20000 : ℝ)=(10000723547001969/10000000000000000 : ℝ) by norm_num, show 1+2*(14647436017940299/100000000000000000000 : ℝ)=(50014647436017940299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35186243007066751/100000000000000000000 : ℝ)+(14647436017940299/100000000000000000000 : ℝ) ≤ ((909683930278449219/910000000000000000 : ℝ)+(12679697833/6825000000000 : ℝ)*((561/4000 : ℝ)+(2259/20000 : ℝ)))^(8291/2048 : ℝ) := by
    rw [show (909683930278449219/910000000000000000 : ℝ)+(12679697833/6825000000000 : ℝ)*((561/4000 : ℝ)+(2259/20000 : ℝ))=(10001230734915289/10000000000000000 : ℝ) by norm_num, show 1+(35186243007066751/100000000000000000000 : ℝ)+(14647436017940299/100000000000000000000 : ℝ)=(2000996673580500141/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35186243007066751/100000000000000000000 : ℝ) ≤ ((909683930278449219/910000000000000000 : ℝ)+2*(12679697833/6825000000000 : ℝ)*(561/4000 : ℝ))^(8291/2048 : ℝ) := by
    rw [show (909683930278449219/910000000000000000 : ℝ)+2*(12679697833/6825000000000 : ℝ)*(561/4000 : ℝ)=(10001737922828609/10000000000000000 : ℝ) by norm_num, show 1+2*(35186243007066751/100000000000000000000 : ℝ)=(50035186243007066751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (909683930278449219/910000000000000000 : ℝ)*(X 1 0+X 2 0)+(12679697833/6825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (909683930278449219/910000000000000000 : ℝ)) (alpha := (12679697833/6825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (909683930278449219/910000000000000000 : ℝ)*(X 0 1+X 2 1)+(12679697833/6825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (909683930278449219/910000000000000000 : ℝ)) (alpha := (12679697833/6825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (909683930278449219/910000000000000000 : ℝ)*(X 0 2+X 1 2)+(12679697833/6825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8291/2048 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (909683930278449219/910000000000000000 : ℝ)) (alpha := (12679697833/6825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2187621883/10000000000 : ℝ)*X 0 0+(1348441827/2500000000 : ℝ)*X 0 1+(1316263173/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668111369/1250000000 : ℝ)*X 1 0+(-563229707/2500000000 : ℝ)*X 1 1+(1053010533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344891/10000000 : ℝ)*X 2 0+(5265052661/10000000000 : ℝ)*X 2 1+(-225291877/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546346009/1250000000 : ℝ)*X 0 0+(849132659/2000000000 : ℝ)*X 0 1+(4499579731/10000000000 : ℝ)*X 0 2+(546346009/1250000000 : ℝ)*X 1 0+(849132659/2000000000 : ℝ)*X 1 1+(4499579731/10000000000 : ℝ)*X 1 2+(546346009/1250000000 : ℝ)*X 2 0+(849132659/2000000000 : ℝ)*X 2 1+(4499579731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2187626839/10000000000 : ℝ)*X 0 0+(1316343833/2500000000 : ℝ)*X 0 1+(2696721761/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106247729/200000000 : ℝ)*X 1 0+(-2124527733/10000000000 : ℝ)*X 1 1+(5393443533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656193033/5000000000 : ℝ)*X 2 0+(5393443477/10000000000 : ℝ)*X 2 1+(-265566041/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092694377/2500000000 : ℝ)*X 0 0+(4498943169/10000000000 : ℝ)*X 0 1+(4246302543/10000000000 : ℝ)*X 0 2+(1092694377/2500000000 : ℝ)*X 1 0+(4498943169/10000000000 : ℝ)*X 1 1+(4246302543/10000000000 : ℝ)*X 1 2+(1092694377/2500000000 : ℝ)*X 2 0+(4498943169/10000000000 : ℝ)*X 2 1+(4246302543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1099_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20704452831139767008705157/5687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (725811799/100000000000000 : ℝ)*(base19) + (70201569/10000000000000 : ℝ)*(base23) + (50010737/100000000000000 : ℝ)*(lower2) + (7528037/12500000000000 : ℝ)*(upper3) + (48125399/50000000000000 : ℝ)*(upper5) + (1463435649402499/25000000000000 : ℝ)*(major0) + (1463435649402499/25000000000000 : ℝ)*(major1) + (1463435649402499/25000000000000 : ℝ)*(major2) + (3884570941266059/50000000000000 : ℝ)*(sp0) + (1942290399884419/25000000000000 : ℝ)*(sp1) + (1553832324666757/20000000000000 : ℝ)*(sp2) + (30768070703089/781250000000 : ℝ)*(sp3) + (20442817357/100000000000000 : ℝ)*(sp4) + (4849265171/50000000000000 : ℝ)*(sp7) + (1969161374262867/50000000000000 : ℝ)*(f.failure) + (310766493013979/4000000000000 : ℝ)*(f.sum) + (2549963537977/1365000000000000000000000000 : ℝ)*base65 + (678403864471894843/68250000000000000000000000000000 : ℝ)*base67 + (329699192565394843/68250000000000000000000000000000 : ℝ)*base69 + (102880743162394843/68250000000000000000000000000000 : ℝ)*base71 + (1471000652239/682500000000000000000000000 : ℝ)*base74 + (530150720857105157/68250000000000000000000000000000 : ℝ)*base76 + (402707944836394843/68250000000000000000000000000000 : ℝ)*base77 + (545465421311644843/68250000000000000000000000000000 : ℝ)*base79 + (481227267719/170625000000000000000000000 : ℝ)*base81 + (1212007/5000000000000000000000 : ℝ)*base89 + (1212007/5000000000000000000000 : ℝ)*base91 + (1212007/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21515279128659054731107137/3250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1035828653/100000000000000 : ℝ)*(base19) + (166756889/50000000000000 : ℝ)*(base23) + (6029993/100000000000000 : ℝ)*(lower1) + (63011403/100000000000000 : ℝ)*(upper2) + (393493/390625000000 : ℝ)*(upper5) + (5883264000863487/100000000000000 : ℝ)*(major0) + (5883264000863487/100000000000000 : ℝ)*(major1) + (5883264000863487/100000000000000 : ℝ)*(major2) + (4558768711/100000000000000 : ℝ)*(sp0) + (20961378379/50000000000000 : ℝ)*(sp1) + (7808338853259023/100000000000000 : ℝ)*(sp4) + (1952075113360581/25000000000000 : ℝ)*(sp5) + (7808343078513957/100000000000000 : ℝ)*(sp6) + (3958184369029699/100000000000000 : ℝ)*(sp7) + (3958184369029699/100000000000000 : ℝ)*(f.failure) + (1561668682405547/20000000000000 : ℝ)*(f.sum) + (240378879387/32500000000000000000000000 : ℝ)*base65 + (34177701657347621/13000000000000000000000000000000 : ℝ)*base68 + (65730610317347621/13000000000000000000000000000000 : ℝ)*base70 + (53280899446347621/13000000000000000000000000000000 : ℝ)*base72 + (35184683371/65000000000000000000000000 : ℝ)*base74 + (99239822989347621/13000000000000000000000000000000 : ℝ)*base76 + (173593023855652379/13000000000000000000000000000000 : ℝ)*base77 + (483969743902347621/13000000000000000000000000000000 : ℝ)*base80 + (195007249639/65000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27631721/10000000000000000000000 : ℝ)*base90 + (27631721/10000000000000000000000 : ℝ)*base92 + (27631721/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1099_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1099_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1099_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1099_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1099_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1099_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8291/2048 : ℝ) ≤ p) (hpb : p ≤ (2073/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148635421/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1099_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

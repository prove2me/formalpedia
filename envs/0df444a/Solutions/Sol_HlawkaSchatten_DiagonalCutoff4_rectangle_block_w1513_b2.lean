-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1513_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:45.472977+00:00
-- url     : https://prove2.me/submissions/add0888c-50a3-47f4-ac45-07244d5f75ca

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
theorem support_rectangle_w1513_s6_0 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1866540523/10000000000 : ℝ)*x 0 + (2716551123/5000000000 : ℝ)*x 1 + (1304422091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866540523/10000000000 : ℝ)^4523 ≤ (2284193247739/20000000000000 : ℝ)^3499 := by
    have hnat : (1866540523 : ℕ)^4523*20000000000000^3499 ≤ 2284193247739^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866540523 10000000000 2284193247739 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716551123/5000000000 : ℝ)^4523 ≤ (11361830652297/25000000000000 : ℝ)^3499 := by
    have hnat : (2716551123 : ℕ)^4523*25000000000000^3499 ≤ 11361830652297^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716551123 5000000000 11361830652297 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304422091/2500000000 : ℝ)^4523 ≤ (1347865973191/3125000000000 : ℝ)^3499 := by
    have hnat : (1304422091 : ℕ)^4523*3125000000000^3499 ≤ 1347865973191^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304422091 2500000000 1347865973191 3125000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1866540523/10000000000 : ℝ), (2716551123/5000000000 : ℝ), (1304422091/2500000000 : ℝ)] ![(2284193247739/20000000000000 : ℝ), (11361830652297/25000000000000 : ℝ), (1347865973191/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1866540523/10000000000 : ℝ)|^4523 ≤ (2284193247739/20000000000000 : ℝ)^3499
        have hw : |(-1866540523/10000000000 : ℝ)|=(1866540523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716551123/5000000000 : ℝ)|^4523 ≤ (11361830652297/25000000000000 : ℝ)^3499
        have hw : |(2716551123/5000000000 : ℝ)|=(2716551123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304422091/2500000000 : ℝ)|^4523 ≤ (1347865973191/3125000000000 : ℝ)^3499
        have hw : |(1304422091/2500000000 : ℝ)|=(1304422091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_1 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351535421/10000000000 : ℝ)*x 0 + (-98843189/500000000 : ℝ)*x 1 + (2608843577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351535421/10000000000 : ℝ)^4523 ≤ (22283645662333/50000000000000 : ℝ)^3499 := by
    have hnat : (5351535421 : ℕ)^4523*50000000000000^3499 ≤ 22283645662333^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351535421 10000000000 22283645662333 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98843189/500000000 : ℝ)^4523 ≤ (6150505222903/50000000000000 : ℝ)^3499 := by
    have hnat : (98843189 : ℕ)^4523*50000000000000^3499 ≤ 6150505222903^3499*500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98843189 500000000 6150505222903 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608843577/5000000000 : ℝ)^4523 ≤ (43131698212469/100000000000000 : ℝ)^3499 := by
    have hnat : (2608843577 : ℕ)^4523*100000000000000^3499 ≤ 43131698212469^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608843577 5000000000 43131698212469 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351535421/10000000000 : ℝ), (-98843189/500000000 : ℝ), (2608843577/5000000000 : ℝ)] ![(22283645662333/50000000000000 : ℝ), (6150505222903/50000000000000 : ℝ), (43131698212469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351535421/10000000000 : ℝ)|^4523 ≤ (22283645662333/50000000000000 : ℝ)^3499
        have hw : |(5351535421/10000000000 : ℝ)|=(5351535421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98843189/500000000 : ℝ)|^4523 ≤ (6150505222903/50000000000000 : ℝ)^3499
        have hw : |(-98843189/500000000 : ℝ)|=(98843189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608843577/5000000000 : ℝ)|^4523 ≤ (43131698212469/100000000000000 : ℝ)^3499
        have hw : |(2608843577/5000000000 : ℝ)|=(2608843577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_2 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351536871/10000000000 : ℝ)*x 0 + (2608842717/5000000000 : ℝ)*x 1 + (-15814913/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351536871/10000000000 : ℝ)^4523 ≤ (11141826733537/25000000000000 : ℝ)^3499 := by
    have hnat : (5351536871 : ℕ)^4523*25000000000000^3499 ≤ 11141826733537^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351536871 10000000000 11141826733537 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608842717/5000000000 : ℝ)^4523 ≤ (21565839916571/50000000000000 : ℝ)^3499 := by
    have hnat : (2608842717 : ℕ)^4523*50000000000000^3499 ≤ 21565839916571^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608842717 5000000000 21565839916571 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15814913/80000000 : ℝ)^4523 ≤ (1537626652603/12500000000000 : ℝ)^3499 := by
    have hnat : (15814913 : ℕ)^4523*12500000000000^3499 ≤ 1537626652603^3499*80000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15814913 80000000 1537626652603 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351536871/10000000000 : ℝ), (2608842717/5000000000 : ℝ), (-15814913/80000000 : ℝ)] ![(11141826733537/25000000000000 : ℝ), (21565839916571/50000000000000 : ℝ), (1537626652603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351536871/10000000000 : ℝ)|^4523 ≤ (11141826733537/25000000000000 : ℝ)^3499
        have hw : |(5351536871/10000000000 : ℝ)|=(5351536871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608842717/5000000000 : ℝ)|^4523 ≤ (21565839916571/50000000000000 : ℝ)^3499
        have hw : |(2608842717/5000000000 : ℝ)|=(2608842717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15814913/80000000 : ℝ)|^4523 ≤ (1537626652603/12500000000000 : ℝ)^3499
        have hw : |(-15814913/80000000 : ℝ)|=(15814913/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_3 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133415827/312500000 : ℝ)*x 0 + (2015415991/5000000000 : ℝ)*x 1 + (451965129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133415827/312500000 : ℝ)^4523 ≤ (3327971046307/10000000000000 : ℝ)^3499 := by
    have hnat : (133415827 : ℕ)^4523*10000000000000^3499 ≤ 3327971046307^3499*312500000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133415827 312500000 3327971046307 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015415991/5000000000 : ℝ)^4523 ≤ (3089665496431/10000000000000 : ℝ)^3499 := by
    have hnat : (2015415991 : ℕ)^4523*10000000000000^3499 ≤ 3089665496431^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015415991 5000000000 3089665496431 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451965129/1000000000 : ℝ)^4523 ≤ (17911817282019/50000000000000 : ℝ)^3499 := by
    have hnat : (451965129 : ℕ)^4523*50000000000000^3499 ≤ 17911817282019^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451965129 1000000000 17911817282019 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133415827/312500000 : ℝ), (2015415991/5000000000 : ℝ), (451965129/1000000000 : ℝ)] ![(3327971046307/10000000000000 : ℝ), (3089665496431/10000000000000 : ℝ), (17911817282019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133415827/312500000 : ℝ)|^4523 ≤ (3327971046307/10000000000000 : ℝ)^3499
        have hw : |(133415827/312500000 : ℝ)|=(133415827/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015415991/5000000000 : ℝ)|^4523 ≤ (3089665496431/10000000000000 : ℝ)^3499
        have hw : |(2015415991/5000000000 : ℝ)|=(2015415991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451965129/1000000000 : ℝ)|^4523 ≤ (17911817282019/50000000000000 : ℝ)^3499
        have hw : |(451965129/1000000000 : ℝ)|=(451965129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_4 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-466642489/2500000000 : ℝ)*x 0 + (5218796207/10000000000 : ℝ)*x 1 + (1357996461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466642489/2500000000 : ℝ)^4523 ≤ (1142119903903/10000000000000 : ℝ)^3499 := by
    have hnat : (466642489 : ℕ)^4523*10000000000000^3499 ≤ 1142119903903^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466642489 2500000000 1142119903903 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218796207/10000000000 : ℝ)^4523 ≤ (21571774769651/50000000000000 : ℝ)^3499 := by
    have hnat : (5218796207 : ℕ)^4523*50000000000000^3499 ≤ 21571774769651^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218796207 10000000000 21571774769651 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357996461/2500000000 : ℝ)^4523 ≤ (45435251404419/100000000000000 : ℝ)^3499 := by
    have hnat : (1357996461 : ℕ)^4523*100000000000000^3499 ≤ 45435251404419^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357996461 2500000000 45435251404419 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466642489/2500000000 : ℝ), (5218796207/10000000000 : ℝ), (1357996461/2500000000 : ℝ)] ![(1142119903903/10000000000000 : ℝ), (21571774769651/50000000000000 : ℝ), (45435251404419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466642489/2500000000 : ℝ)|^4523 ≤ (1142119903903/10000000000000 : ℝ)^3499
        have hw : |(-466642489/2500000000 : ℝ)|=(466642489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218796207/10000000000 : ℝ)|^4523 ≤ (21571774769651/50000000000000 : ℝ)^3499
        have hw : |(5218796207/10000000000 : ℝ)|=(5218796207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357996461/2500000000 : ℝ)|^4523 ≤ (45435251404419/100000000000000 : ℝ)^3499
        have hw : |(1357996461/2500000000 : ℝ)|=(1357996461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_5 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529497707/1000000000 : ℝ)*x 0 + (-881282853/5000000000 : ℝ)*x 1 + (5431985861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529497707/1000000000 : ℝ)^4523 ≤ (43959375584963/100000000000000 : ℝ)^3499 := by
    have hnat : (529497707 : ℕ)^4523*100000000000000^3499 ≤ 43959375584963^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529497707 1000000000 43959375584963 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881282853/5000000000 : ℝ)^4523 ≤ (5302686405379/50000000000000 : ℝ)^3499 := by
    have hnat : (881282853 : ℕ)^4523*50000000000000^3499 ≤ 5302686405379^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881282853 5000000000 5302686405379 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431985861/10000000000 : ℝ)^4523 ≤ (45435251588227/100000000000000 : ℝ)^3499 := by
    have hnat : (5431985861 : ℕ)^4523*100000000000000^3499 ≤ 45435251588227^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431985861 10000000000 45435251588227 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529497707/1000000000 : ℝ), (-881282853/5000000000 : ℝ), (5431985861/10000000000 : ℝ)] ![(43959375584963/100000000000000 : ℝ), (5302686405379/50000000000000 : ℝ), (45435251588227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529497707/1000000000 : ℝ)|^4523 ≤ (43959375584963/100000000000000 : ℝ)^3499
        have hw : |(529497707/1000000000 : ℝ)|=(529497707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881282853/5000000000 : ℝ)|^4523 ≤ (5302686405379/50000000000000 : ℝ)^3499
        have hw : |(-881282853/5000000000 : ℝ)|=(881282853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431985861/10000000000 : ℝ)|^4523 ≤ (45435251588227/100000000000000 : ℝ)^3499
        have hw : |(5431985861/10000000000 : ℝ)|=(5431985861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_6 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647488537/5000000000 : ℝ)*x 0 + (5431985849/10000000000 : ℝ)*x 1 + (-881282859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647488537/5000000000 : ℝ)^4523 ≤ (4395937562789/10000000000000 : ℝ)^3499 := by
    have hnat : (2647488537 : ℕ)^4523*10000000000000^3499 ≤ 4395937562789^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647488537 5000000000 4395937562789 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431985849/10000000000 : ℝ)^4523 ≤ (567940643231/1250000000000 : ℝ)^3499 := by
    have hnat : (5431985849 : ℕ)^4523*1250000000000^3499 ≤ 567940643231^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431985849 10000000000 567940643231 1250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881282859/5000000000 : ℝ)^4523 ≤ (10605372904093/100000000000000 : ℝ)^3499 := by
    have hnat : (881282859 : ℕ)^4523*100000000000000^3499 ≤ 10605372904093^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881282859 5000000000 10605372904093 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647488537/5000000000 : ℝ), (5431985849/10000000000 : ℝ), (-881282859/5000000000 : ℝ)] ![(4395937562789/10000000000000 : ℝ), (567940643231/1250000000000 : ℝ), (10605372904093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647488537/5000000000 : ℝ)|^4523 ≤ (4395937562789/10000000000000 : ℝ)^3499
        have hw : |(2647488537/5000000000 : ℝ)|=(2647488537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431985849/10000000000 : ℝ)|^4523 ≤ (567940643231/1250000000000 : ℝ)^3499
        have hw : |(5431985849/10000000000 : ℝ)|=(5431985849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-881282859/5000000000 : ℝ)|^4523 ≤ (10605372904093/100000000000000 : ℝ)^3499
        have hw : |(-881282859/5000000000 : ℝ)|=(881282859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_s6_7 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269372281/10000000000 : ℝ)*x 0 + (4517134021/10000000000 : ℝ)*x 1 + (4033367623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269372281/10000000000 : ℝ)^4523 ≤ (33280373662151/100000000000000 : ℝ)^3499 := by
    have hnat : (4269372281 : ℕ)^4523*100000000000000^3499 ≤ 33280373662151^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269372281 10000000000 33280373662151 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517134021/10000000000 : ℝ)^4523 ≤ (894946128579/2500000000000 : ℝ)^3499 := by
    have hnat : (4517134021 : ℕ)^4523*2500000000000^3499 ≤ 894946128579^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517134021 10000000000 894946128579 2500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033367623/10000000000 : ℝ)^4523 ≤ (6184356236729/20000000000000 : ℝ)^3499 := by
    have hnat : (4033367623 : ℕ)^4523*20000000000000^3499 ≤ 6184356236729^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033367623 10000000000 6184356236729 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269372281/10000000000 : ℝ), (4517134021/10000000000 : ℝ), (4033367623/10000000000 : ℝ)] ![(33280373662151/100000000000000 : ℝ), (894946128579/2500000000000 : ℝ), (6184356236729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269372281/10000000000 : ℝ)|^4523 ≤ (33280373662151/100000000000000 : ℝ)^3499
        have hw : |(4269372281/10000000000 : ℝ)|=(4269372281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517134021/10000000000 : ℝ)|^4523 ≤ (894946128579/2500000000000 : ℝ)^3499
        have hw : |(4517134021/10000000000 : ℝ)|=(4517134021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033367623/10000000000 : ℝ)|^4523 ≤ (6184356236729/20000000000000 : ℝ)^3499
        have hw : |(4033367623/10000000000 : ℝ)|=(4033367623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1513_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (273/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10919/100000 : ℝ) ^ (4521/1024 : ℝ) ≤ (5669435024650301/100000000000000000000 : ℝ) := by
    have hpowers : (10919/100000 : ℝ)^4521 ≤ (5669435024650301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10919 : ℕ)^4521*100000000000000000000^1024 ≤ 5669435024650301^1024*100000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10919 100000 5669435024650301 100000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10919/100000 : ℝ)) (X := (5669435024650301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4521/1024 : ℝ) ≤ (6623975077624097/25000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4521 ≤ (6623975077624097/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4521*25000000000000000000^1024 ≤ 6623975077624097^1024*100000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 6623975077624097 25000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (6623975077624097/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005669435024650301/50000000000000000000 : ℝ) ≤ (625016050782163/625000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (50005669435024650301/50000000000000000000 : ℝ)^1024 ≤ (625016050782163/625000000000000 : ℝ)^4521 := by
      have hnat : (50005669435024650301 : ℕ)^1024*625000000000000^4521 ≤ 625016050782163^4521*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005669435024650301 50000000000000000000 625016050782163 625000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016050782163/625000000000000 : ℝ)) (X := (50005669435024650301/50000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032165335335146689/100000000000000000000 : ℝ) ≤ (625045528100493/625000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (100032165335335146689/100000000000000000000 : ℝ)^1024 ≤ (625045528100493/625000000000000 : ℝ)^4521 := by
      have hnat : (100032165335335146689 : ℕ)^1024*625000000000000^4521 ≤ 625045528100493^4521*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032165335335146689 100000000000000000000 625045528100493 625000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625045528100493/625000000000000 : ℝ)) (X := (100032165335335146689/100000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506623975077624097/12500000000000000000 : ℝ) ≤ (625075005418823/625000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (12506623975077624097/12500000000000000000 : ℝ)^1024 ≤ (625075005418823/625000000000000 : ℝ)^4521 := by
      have hnat : (12506623975077624097 : ℕ)^1024*625000000000000^4521 ≤ 625075005418823^4521*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506623975077624097 12500000000000000000 625075005418823 625000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625075005418823/625000000000000 : ℝ)) (X := (12506623975077624097/12500000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5669435024650301/100000000000000000000 : ℝ) ≤ ((178245595630756337/178281250000000000 : ℝ)+2*(2947731833/2852500000000 : ℝ)*(10919/100000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (178245595630756337/178281250000000000 : ℝ)+2*(2947731833/2852500000000 : ℝ)*(10919/100000 : ℝ)=(625016050782163/625000000000000 : ℝ) by norm_num, show 1+2*(5669435024650301/100000000000000000000 : ℝ)=(50005669435024650301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6623975077624097/25000000000000000000 : ℝ)+(5669435024650301/100000000000000000000 : ℝ) ≤ ((178245595630756337/178281250000000000 : ℝ)+(2947731833/2852500000000 : ℝ)*((15483/100000 : ℝ)+(10919/100000 : ℝ)))^(4521/1024 : ℝ) := by
    rw [show (178245595630756337/178281250000000000 : ℝ)+(2947731833/2852500000000 : ℝ)*((15483/100000 : ℝ)+(10919/100000 : ℝ))=(625045528100493/625000000000000 : ℝ) by norm_num, show 1+(6623975077624097/25000000000000000000 : ℝ)+(5669435024650301/100000000000000000000 : ℝ)=(100032165335335146689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6623975077624097/25000000000000000000 : ℝ) ≤ ((178245595630756337/178281250000000000 : ℝ)+2*(2947731833/2852500000000 : ℝ)*(15483/100000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (178245595630756337/178281250000000000 : ℝ)+2*(2947731833/2852500000000 : ℝ)*(15483/100000 : ℝ)=(625075005418823/625000000000000 : ℝ) by norm_num, show 1+2*(6623975077624097/25000000000000000000 : ℝ)=(12506623975077624097/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (178245595630756337/178281250000000000 : ℝ)*(X 1 0+X 2 0)+(2947731833/2852500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (178245595630756337/178281250000000000 : ℝ)) (alpha := (2947731833/2852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (178245595630756337/178281250000000000 : ℝ)*(X 0 1+X 2 1)+(2947731833/2852500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (178245595630756337/178281250000000000 : ℝ)) (alpha := (2947731833/2852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (178245595630756337/178281250000000000 : ℝ)*(X 0 2+X 1 2)+(2947731833/2852500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (178245595630756337/178281250000000000 : ℝ)) (alpha := (2947731833/2852500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1866540523/10000000000 : ℝ)*X 0 0+(2716551123/5000000000 : ℝ)*X 0 1+(1304422091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351535421/10000000000 : ℝ)*X 1 0+(-98843189/500000000 : ℝ)*X 1 1+(2608843577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351536871/10000000000 : ℝ)*X 2 0+(2608842717/5000000000 : ℝ)*X 2 1+(-15814913/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((133415827/312500000 : ℝ)*X 0 0+(2015415991/5000000000 : ℝ)*X 0 1+(451965129/1000000000 : ℝ)*X 0 2+(133415827/312500000 : ℝ)*X 1 0+(2015415991/5000000000 : ℝ)*X 1 1+(451965129/1000000000 : ℝ)*X 1 2+(133415827/312500000 : ℝ)*X 2 0+(2015415991/5000000000 : ℝ)*X 2 1+(451965129/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-466642489/2500000000 : ℝ)*X 0 0+(5218796207/10000000000 : ℝ)*X 0 1+(1357996461/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529497707/1000000000 : ℝ)*X 1 0+(-881282853/5000000000 : ℝ)*X 1 1+(5431985861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647488537/5000000000 : ℝ)*X 2 0+(5431985849/10000000000 : ℝ)*X 2 1+(-881282859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269372281/10000000000 : ℝ)*X 0 0+(4517134021/10000000000 : ℝ)*X 0 1+(4033367623/10000000000 : ℝ)*X 0 2+(4269372281/10000000000 : ℝ)*X 1 0+(4517134021/10000000000 : ℝ)*X 1 1+(4033367623/10000000000 : ℝ)*X 1 2+(4269372281/10000000000 : ℝ)*X 2 0+(4517134021/10000000000 : ℝ)*X 2 1+(4033367623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11325445287540852808755171/8914062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12431633/1000000000000 : ℝ)*(base19) + (469875363/20000000000000 : ℝ)*(base23) + (142310303/100000000000000 : ℝ)*(lower2) + (61181749/100000000000000 : ℝ)*(lower4) + (11340903/5000000000000 : ℝ)*(lower5) + (417999861128121/12500000000000 : ℝ)*(major0) + (417999861128121/12500000000000 : ℝ)*(major1) + (417999861128121/12500000000000 : ℝ)*(major2) + (4642225890609293/100000000000000 : ℝ)*(sp0) + (1160556544624551/25000000000000 : ℝ)*(sp1) + (290139067017793/6250000000000 : ℝ)*(sp2) + (255719376482267/12500000000000 : ℝ)*(sp3) + (1531052211/100000000000000 : ℝ)*(sp4) + (7651089903/50000000000000 : ℝ)*(sp7) + (2045770314037941/100000000000000 : ℝ)*(f.failure) + (72534803463461/1562500000000 : ℝ)*(f.sum) + (3503419068783/1141000000000000000000000000 : ℝ)*base66 + (20045074841907987/2546875000000000000000000000000 : ℝ)*base68 + (11396402125664931/1273437500000000000000000000000 : ℝ)*base70 + (15326800954414931/1273437500000000000000000000000 : ℝ)*base72 + (490618624137/570500000000000000000000000 : ℝ)*base73 + (22207381811914931/1273437500000000000000000000000 : ℝ)*base76 + (16281684707008681/1273437500000000000000000000000 : ℝ)*base78 + (55066403803819/1273437500000000000000000000000 : ℝ)*base79 + (836001663373/570500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3040551/2500000000000000000000 : ℝ)*base90 + (3040551/2500000000000000000000 : ℝ)*base92 + (3040551/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4258019503095119114151/570500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1179347041/100000000000000 : ℝ)*(base19) + (639392953/50000000000000 : ℝ)*(base23) + (98008831/25000000000000 : ℝ)*(lower1) + (77333081/50000000000000 : ℝ)*(upper3) + (10768191/25000000000000 : ℝ)*(lower4) + (70596801/50000000000000 : ℝ)*(upper5) + (1689436364513587/50000000000000 : ℝ)*(major0) + (1689436364513587/50000000000000 : ℝ)*(major1) + (1689436364513587/50000000000000 : ℝ)*(major2) + (681015849/50000000000000 : ℝ)*(sp2) + (938127999959669/20000000000000 : ℝ)*(sp4) + (586329852556413/12500000000000 : ℝ)*(sp5) + (2345318679490371/50000000000000 : ℝ)*(sp6) + (413421041893447/20000000000000 : ℝ)*(sp7) + (413421041893447/20000000000000 : ℝ)*(f.failure) + (938127999959669/20000000000000 : ℝ)*(f.sum) + (4877966604221/1141000000000000000000000000 : ℝ)*base65 + (459512215927937/79589843750000000000000000000 : ℝ)*base67 + (1643044951803359/2546875000000000000000000000000 : ℝ)*base69 + (189973519610540391/2546875000000000000000000000000 : ℝ)*base72 + (158926884737/228200000000000000000000000 : ℝ)*base73 + (57489940515365859/2546875000000000000000000000000 : ℝ)*base75 + (2736557009259141/2546875000000000000000000000000 : ℝ)*base78 + (64904629471946641/2546875000000000000000000000000 : ℝ)*base80 + (3698594010723/1141000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2137683/500000000000000000000 : ℝ)*base89 + (2137683/500000000000000000000 : ℝ)*base91 + (2137683/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1513_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1513_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1513_box_0 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1653093443/10000000000 : ℝ)*x 0 + (1350681099/2500000000 : ℝ)*x 1 + (108054491/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1653093443/10000000000 : ℝ)^4523 ≤ (1220220194361/12500000000000 : ℝ)^3499 := by
    have hnat : (1653093443 : ℕ)^4523*12500000000000^3499 ≤ 1220220194361^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653093443 10000000000 1220220194361 12500000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350681099/2500000000 : ℝ)^4523 ≤ (45119118383487/100000000000000 : ℝ)^3499 := by
    have hnat : (1350681099 : ℕ)^4523*100000000000000^3499 ≤ 45119118383487^3499*2500000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350681099 2500000000 45119118383487 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108054491/200000000 : ℝ)^4523 ≤ (22559560022973/50000000000000 : ℝ)^3499 := by
    have hnat : (108054491 : ℕ)^4523*50000000000000^3499 ≤ 22559560022973^3499*200000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108054491 200000000 22559560022973 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1653093443/10000000000 : ℝ), (1350681099/2500000000 : ℝ), (108054491/200000000 : ℝ)] ![(1220220194361/12500000000000 : ℝ), (45119118383487/100000000000000 : ℝ), (22559560022973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1653093443/10000000000 : ℝ)|^4523 ≤ (1220220194361/12500000000000 : ℝ)^3499
        have hw : |(-1653093443/10000000000 : ℝ)|=(1653093443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350681099/2500000000 : ℝ)|^4523 ≤ (45119118383487/100000000000000 : ℝ)^3499
        have hw : |(1350681099/2500000000 : ℝ)|=(1350681099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108054491/200000000 : ℝ)|^4523 ≤ (22559560022973/50000000000000 : ℝ)^3499
        have hw : |(108054491/200000000 : ℝ)|=(108054491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_1 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270790569/10000000000 : ℝ)*x 0 + (-183611567/1000000000 : ℝ)*x 1 + (2701362103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270790569/10000000000 : ℝ)^4523 ≤ (8739997212561/20000000000000 : ℝ)^3499 := by
    have hnat : (5270790569 : ℕ)^4523*20000000000000^3499 ≤ 8739997212561^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270790569 10000000000 8739997212561 20000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183611567/1000000000 : ℝ)^4523 ≤ (11180897593359/100000000000000 : ℝ)^3499 := by
    have hnat : (183611567 : ℕ)^4523*100000000000000^3499 ≤ 11180897593359^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183611567 1000000000 11180897593359 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701362103/5000000000 : ℝ)^4523 ≤ (112797790831/250000000000 : ℝ)^3499 := by
    have hnat : (2701362103 : ℕ)^4523*250000000000^3499 ≤ 112797790831^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701362103 5000000000 112797790831 250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270790569/10000000000 : ℝ), (-183611567/1000000000 : ℝ), (2701362103/5000000000 : ℝ)] ![(8739997212561/20000000000000 : ℝ), (11180897593359/100000000000000 : ℝ), (112797790831/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270790569/10000000000 : ℝ)|^4523 ≤ (8739997212561/20000000000000 : ℝ)^3499
        have hw : |(5270790569/10000000000 : ℝ)|=(5270790569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183611567/1000000000 : ℝ)|^4523 ≤ (11180897593359/100000000000000 : ℝ)^3499
        have hw : |(-183611567/1000000000 : ℝ)|=(183611567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701362103/5000000000 : ℝ)|^4523 ≤ (112797790831/250000000000 : ℝ)^3499
        have hw : |(2701362103/5000000000 : ℝ)|=(2701362103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_2 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42166327/80000000 : ℝ)*x 0 + (5402724033/10000000000 : ℝ)*x 1 + (-183611549/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42166327/80000000 : ℝ)^4523 ≤ (546249866779/1250000000000 : ℝ)^3499 := by
    have hnat : (42166327 : ℕ)^4523*1250000000000^3499 ≤ 546249866779^3499*80000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42166327 80000000 546249866779 1250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402724033/10000000000 : ℝ)^4523 ≤ (45119114464831/100000000000000 : ℝ)^3499 := by
    have hnat : (5402724033 : ℕ)^4523*100000000000000^3499 ≤ 45119114464831^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402724033 10000000000 45119114464831 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183611549/1000000000 : ℝ)^4523 ≤ (11180896176483/100000000000000 : ℝ)^3499 := by
    have hnat : (183611549 : ℕ)^4523*100000000000000^3499 ≤ 11180896176483^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183611549 1000000000 11180896176483 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42166327/80000000 : ℝ), (5402724033/10000000000 : ℝ), (-183611549/1000000000 : ℝ)] ![(546249866779/1250000000000 : ℝ), (45119114464831/100000000000000 : ℝ), (11180896176483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42166327/80000000 : ℝ)|^4523 ≤ (546249866779/1250000000000 : ℝ)^3499
        have hw : |(42166327/80000000 : ℝ)|=(42166327/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402724033/10000000000 : ℝ)|^4523 ≤ (45119114464831/100000000000000 : ℝ)^3499
        have hw : |(5402724033/10000000000 : ℝ)|=(5402724033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183611549/1000000000 : ℝ)|^4523 ≤ (11180896176483/100000000000000 : ℝ)^3499
        have hw : |(-183611549/1000000000 : ℝ)|=(183611549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_3 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (559040507/1250000000 : ℝ)*x 0 + (2087386757/5000000000 : ℝ)*x 1 + (417477379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559040507/1250000000 : ℝ)^4523 ≤ (35339472373641/100000000000000 : ℝ)^3499 := by
    have hnat : (559040507 : ℕ)^4523*100000000000000^3499 ≤ 35339472373641^3499*1250000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559040507 1250000000 35339472373641 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087386757/5000000000 : ℝ)^4523 ≤ (32330262422589/100000000000000 : ℝ)^3499 := by
    have hnat : (2087386757 : ℕ)^4523*100000000000000^3499 ≤ 32330262422589^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087386757 5000000000 32330262422589 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417477379/1000000000 : ℝ)^4523 ≤ (32330265185507/100000000000000 : ℝ)^3499 := by
    have hnat : (417477379 : ℕ)^4523*100000000000000^3499 ≤ 32330265185507^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417477379 1000000000 32330265185507 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559040507/1250000000 : ℝ), (2087386757/5000000000 : ℝ), (417477379/1000000000 : ℝ)] ![(35339472373641/100000000000000 : ℝ), (32330262422589/100000000000000 : ℝ), (32330265185507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559040507/1250000000 : ℝ)|^4523 ≤ (35339472373641/100000000000000 : ℝ)^3499
        have hw : |(559040507/1250000000 : ℝ)|=(559040507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2087386757/5000000000 : ℝ)|^4523 ≤ (32330262422589/100000000000000 : ℝ)^3499
        have hw : |(2087386757/5000000000 : ℝ)|=(2087386757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417477379/1000000000 : ℝ)|^4523 ≤ (32330265185507/100000000000000 : ℝ)^3499
        have hw : |(417477379/1000000000 : ℝ)|=(417477379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_4 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2085427043/10000000000 : ℝ)*x 0 + (209746357/400000000 : ℝ)*x 1 + (1048731379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085427043/10000000000 : ℝ)^4523 ≤ (1318117068647/10000000000000 : ℝ)^3499 := by
    have hnat : (2085427043 : ℕ)^4523*10000000000000^3499 ≤ 1318117068647^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085427043 10000000000 1318117068647 10000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209746357/400000000 : ℝ)^4523 ≤ (43409425512521/100000000000000 : ℝ)^3499 := by
    have hnat : (209746357 : ℕ)^4523*100000000000000^3499 ≤ 43409425512521^3499*400000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209746357 400000000 43409425512521 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048731379/2000000000 : ℝ)^4523 ≤ (21704701894549/50000000000000 : ℝ)^3499 := by
    have hnat : (1048731379 : ℕ)^4523*50000000000000^3499 ≤ 21704701894549^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048731379 2000000000 21704701894549 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2085427043/10000000000 : ℝ), (209746357/400000000 : ℝ), (1048731379/2000000000 : ℝ)] ![(1318117068647/10000000000000 : ℝ), (43409425512521/100000000000000 : ℝ), (21704701894549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2085427043/10000000000 : ℝ)|^4523 ≤ (1318117068647/10000000000000 : ℝ)^3499
        have hw : |(-2085427043/10000000000 : ℝ)|=(2085427043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209746357/400000000 : ℝ)|^4523 ≤ (43409425512521/100000000000000 : ℝ)^3499
        have hw : |(209746357/400000000 : ℝ)|=(209746357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048731379/2000000000 : ℝ)|^4523 ≤ (21704701894549/50000000000000 : ℝ)^3499
        have hw : |(1048731379/2000000000 : ℝ)|=(1048731379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_5 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381526517/10000000000 : ℝ)*x 0 + (-190174311/1000000000 : ℝ)*x 1 + (5243658393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381526517/10000000000 : ℝ)^4523 ≤ (11222603669171/25000000000000 : ℝ)^3499 := by
    have hnat : (5381526517 : ℕ)^4523*25000000000000^3499 ≤ 11222603669171^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381526517 10000000000 11222603669171 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190174311/1000000000 : ℝ)^4523 ≤ (11700165492463/100000000000000 : ℝ)^3499 := by
    have hnat : (190174311 : ℕ)^4523*100000000000000^3499 ≤ 11700165492463^3499*1000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190174311 1000000000 11700165492463 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243658393/10000000000 : ℝ)^4523 ≤ (21704709909743/50000000000000 : ℝ)^3499 := by
    have hnat : (5243658393 : ℕ)^4523*50000000000000^3499 ≤ 21704709909743^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243658393 10000000000 21704709909743 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381526517/10000000000 : ℝ), (-190174311/1000000000 : ℝ), (5243658393/10000000000 : ℝ)] ![(11222603669171/25000000000000 : ℝ), (11700165492463/100000000000000 : ℝ), (21704709909743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381526517/10000000000 : ℝ)|^4523 ≤ (11222603669171/25000000000000 : ℝ)^3499
        have hw : |(5381526517/10000000000 : ℝ)|=(5381526517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190174311/1000000000 : ℝ)|^4523 ≤ (11700165492463/100000000000000 : ℝ)^3499
        have hw : |(-190174311/1000000000 : ℝ)|=(190174311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243658393/10000000000 : ℝ)|^4523 ≤ (21704709909743/50000000000000 : ℝ)^3499
        have hw : |(5243658393/10000000000 : ℝ)|=(5243658393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_6 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690764173/5000000000 : ℝ)*x 0 + (2621828281/5000000000 : ℝ)*x 1 + (-950871547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690764173/5000000000 : ℝ)^4523 ≤ (44890434398391/100000000000000 : ℝ)^3499 := by
    have hnat : (2690764173 : ℕ)^4523*100000000000000^3499 ≤ 44890434398391^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690764173 5000000000 44890434398391 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621828281/5000000000 : ℝ)^4523 ≤ (43409400225601/100000000000000 : ℝ)^3499 := by
    have hnat : (2621828281 : ℕ)^4523*100000000000000^3499 ≤ 43409400225601^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621828281 5000000000 43409400225601 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950871547/5000000000 : ℝ)^4523 ≤ (11700165365217/100000000000000 : ℝ)^3499 := by
    have hnat : (950871547 : ℕ)^4523*100000000000000^3499 ≤ 11700165365217^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950871547 5000000000 11700165365217 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690764173/5000000000 : ℝ), (2621828281/5000000000 : ℝ), (-950871547/5000000000 : ℝ)] ![(44890434398391/100000000000000 : ℝ), (43409400225601/100000000000000 : ℝ), (11700165365217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690764173/5000000000 : ℝ)|^4523 ≤ (44890434398391/100000000000000 : ℝ)^3499
        have hw : |(2690764173/5000000000 : ℝ)|=(2690764173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621828281/5000000000 : ℝ)|^4523 ≤ (43409400225601/100000000000000 : ℝ)^3499
        have hw : |(2621828281/5000000000 : ℝ)|=(2621828281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950871547/5000000000 : ℝ)|^4523 ≤ (11700165365217/100000000000000 : ℝ)^3499
        have hw : |(-950871547/5000000000 : ℝ)|=(950871547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_7 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2031932723/5000000000 : ℝ)*x 0 + (35030949/80000000 : ℝ)*x 1 + (2189434481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031932723/5000000000 : ℝ)^4523 ≤ (31224352378931/100000000000000 : ℝ)^3499 := by
    have hnat : (2031932723 : ℕ)^4523*100000000000000^3499 ≤ 31224352378931^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031932723 5000000000 31224352378931 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35030949/80000000 : ℝ)^4523 ≤ (34387822091361/100000000000000 : ℝ)^3499 := by
    have hnat : (35030949 : ℕ)^4523*100000000000000^3499 ≤ 34387822091361^3499*80000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35030949 80000000 34387822091361 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189434481/5000000000 : ℝ)^4523 ≤ (17193912756189/50000000000000 : ℝ)^3499 := by
    have hnat : (2189434481 : ℕ)^4523*50000000000000^3499 ≤ 17193912756189^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189434481 5000000000 17193912756189 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031932723/5000000000 : ℝ), (35030949/80000000 : ℝ), (2189434481/5000000000 : ℝ)] ![(31224352378931/100000000000000 : ℝ), (34387822091361/100000000000000 : ℝ), (17193912756189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031932723/5000000000 : ℝ)|^4523 ≤ (31224352378931/100000000000000 : ℝ)^3499
        have hw : |(2031932723/5000000000 : ℝ)|=(2031932723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35030949/80000000 : ℝ)|^4523 ≤ (34387822091361/100000000000000 : ℝ)^3499
        have hw : |(35030949/80000000 : ℝ)|=(35030949/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189434481/5000000000 : ℝ)|^4523 ≤ (17193912756189/50000000000000 : ℝ)^3499
        have hw : |(2189434481/5000000000 : ℝ)|=(2189434481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_8 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994059487/10000000000 : ℝ)*x 0 + (1026441591/2000000000 : ℝ)*x 1 + (5423174611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994059487/10000000000 : ℝ)^4523 ≤ (12439500321917/100000000000000 : ℝ)^3499 := by
    have hnat : (1994059487 : ℕ)^4523*100000000000000^3499 ≤ 12439500321917^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994059487 10000000000 12439500321917 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026441591/2000000000 : ℝ)^4523 ≤ (42220495086397/100000000000000 : ℝ)^3499 := by
    have hnat : (1026441591 : ℕ)^4523*100000000000000^3499 ≤ 42220495086397^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026441591 2000000000 42220495086397 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423174611/10000000000 : ℝ)^4523 ≤ (45340004580677/100000000000000 : ℝ)^3499 := by
    have hnat : (5423174611 : ℕ)^4523*100000000000000^3499 ≤ 45340004580677^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423174611 10000000000 45340004580677 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994059487/10000000000 : ℝ), (1026441591/2000000000 : ℝ), (5423174611/10000000000 : ℝ)] ![(12439500321917/100000000000000 : ℝ), (42220495086397/100000000000000 : ℝ), (45340004580677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994059487/10000000000 : ℝ)|^4523 ≤ (12439500321917/100000000000000 : ℝ)^3499
        have hw : |(-1994059487/10000000000 : ℝ)|=(1994059487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026441591/2000000000 : ℝ)|^4523 ≤ (42220495086397/100000000000000 : ℝ)^3499
        have hw : |(1026441591/2000000000 : ℝ)|=(1026441591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423174611/10000000000 : ℝ)|^4523 ≤ (45340004580677/100000000000000 : ℝ)^3499
        have hw : |(5423174611/10000000000 : ℝ)|=(5423174611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_9 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628273867/5000000000 : ℝ)*x 0 + (-1827432571/10000000000 : ℝ)*x 1 + (5423174519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628273867/5000000000 : ℝ)^4523 ≤ (43547400740597/100000000000000 : ℝ)^3499 := by
    have hnat : (2628273867 : ℕ)^4523*100000000000000^3499 ≤ 43547400740597^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628273867 5000000000 43547400740597 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827432571/10000000000 : ℝ)^4523 ≤ (5556297824849/50000000000000 : ℝ)^3499 := by
    have hnat : (1827432571 : ℕ)^4523*50000000000000^3499 ≤ 5556297824849^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827432571 10000000000 5556297824849 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423174519/10000000000 : ℝ)^4523 ≤ (2267000179321/5000000000000 : ℝ)^3499 := by
    have hnat : (5423174519 : ℕ)^4523*5000000000000^3499 ≤ 2267000179321^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423174519 10000000000 2267000179321 5000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628273867/5000000000 : ℝ), (-1827432571/10000000000 : ℝ), (5423174519/10000000000 : ℝ)] ![(43547400740597/100000000000000 : ℝ), (5556297824849/50000000000000 : ℝ), (2267000179321/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628273867/5000000000 : ℝ)|^4523 ≤ (43547400740597/100000000000000 : ℝ)^3499
        have hw : |(2628273867/5000000000 : ℝ)|=(2628273867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827432571/10000000000 : ℝ)|^4523 ≤ (5556297824849/50000000000000 : ℝ)^3499
        have hw : |(-1827432571/10000000000 : ℝ)|=(1827432571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423174519/10000000000 : ℝ)|^4523 ≤ (2267000179321/5000000000000 : ℝ)^3499
        have hw : |(5423174519/10000000000 : ℝ)|=(5423174519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_10 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256548007/10000000000 : ℝ)*x 0 + (2711587001/5000000000 : ℝ)*x 1 + (-1827432911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256548007/10000000000 : ℝ)^4523 ≤ (21773701832061/50000000000000 : ℝ)^3499 := by
    have hnat : (5256548007 : ℕ)^4523*50000000000000^3499 ≤ 21773701832061^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256548007 10000000000 21773701832061 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711587001/5000000000 : ℝ)^4523 ≤ (45339997999131/100000000000000 : ℝ)^3499 := by
    have hnat : (2711587001 : ℕ)^4523*100000000000000^3499 ≤ 45339997999131^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711587001 5000000000 45339997999131 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1827432911/10000000000 : ℝ)^4523 ≤ (11112598322309/100000000000000 : ℝ)^3499 := by
    have hnat : (1827432911 : ℕ)^4523*100000000000000^3499 ≤ 11112598322309^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827432911 10000000000 11112598322309 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256548007/10000000000 : ℝ), (2711587001/5000000000 : ℝ), (-1827432911/10000000000 : ℝ)] ![(21773701832061/50000000000000 : ℝ), (45339997999131/100000000000000 : ℝ), (11112598322309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256548007/10000000000 : ℝ)|^4523 ≤ (21773701832061/50000000000000 : ℝ)^3499
        have hw : |(5256548007/10000000000 : ℝ)|=(5256548007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711587001/5000000000 : ℝ)|^4523 ≤ (45339997999131/100000000000000 : ℝ)^3499
        have hw : |(2711587001/5000000000 : ℝ)|=(2711587001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1827432911/10000000000 : ℝ)|^4523 ≤ (11112598322309/100000000000000 : ℝ)^3499
        have hw : |(-1827432911/10000000000 : ℝ)|=(1827432911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_11 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (90473709/200000000 : ℝ)*x 0 + (829700371/2000000000 : ℝ)*x 1 + (4148502407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90473709/200000000 : ℝ)^4523 ≤ (8966243324909/25000000000000 : ℝ)^3499 := by
    have hnat : (90473709 : ℕ)^4523*25000000000000^3499 ≤ 8966243324909^3499*200000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90473709 200000000 8966243324909 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829700371/2000000000 : ℝ)^4523 ≤ (501054852893/1562500000000 : ℝ)^3499 := by
    have hnat : (829700371 : ℕ)^4523*1562500000000^3499 ≤ 501054852893^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829700371 2000000000 501054852893 1562500000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148502407/10000000000 : ℝ)^4523 ≤ (32067516100789/100000000000000 : ℝ)^3499 := by
    have hnat : (4148502407 : ℕ)^4523*100000000000000^3499 ≤ 32067516100789^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148502407 10000000000 32067516100789 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90473709/200000000 : ℝ), (829700371/2000000000 : ℝ), (4148502407/10000000000 : ℝ)] ![(8966243324909/25000000000000 : ℝ), (501054852893/1562500000000 : ℝ), (32067516100789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90473709/200000000 : ℝ)|^4523 ≤ (8966243324909/25000000000000 : ℝ)^3499
        have hw : |(90473709/200000000 : ℝ)|=(90473709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829700371/2000000000 : ℝ)|^4523 ≤ (501054852893/1562500000000 : ℝ)^3499
        have hw : |(829700371/2000000000 : ℝ)|=(829700371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148502407/10000000000 : ℝ)|^4523 ≤ (32067516100789/100000000000000 : ℝ)^3499
        have hw : |(4148502407/10000000000 : ℝ)|=(4148502407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_12 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34888107/200000000 : ℝ)*x 0 + (5510595299/10000000000 : ℝ)*x 1 + (1045726111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34888107/200000000 : ℝ)^4523 ≤ (2616084139381/25000000000000 : ℝ)^3499 := by
    have hnat : (34888107 : ℕ)^4523*25000000000000^3499 ≤ 2616084139381^3499*200000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34888107 200000000 2616084139381 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510595299/10000000000 : ℝ)^4523 ≤ (578587399099/1250000000000 : ℝ)^3499 := by
    have hnat : (5510595299 : ℕ)^4523*1250000000000^3499 ≤ 578587399099^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510595299 10000000000 578587399099 1250000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045726111/2000000000 : ℝ)^4523 ≤ (10812167873959/25000000000000 : ℝ)^3499 := by
    have hnat : (1045726111 : ℕ)^4523*25000000000000^3499 ≤ 10812167873959^3499*2000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045726111 2000000000 10812167873959 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34888107/200000000 : ℝ), (5510595299/10000000000 : ℝ), (1045726111/2000000000 : ℝ)] ![(2616084139381/25000000000000 : ℝ), (578587399099/1250000000000 : ℝ), (10812167873959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34888107/200000000 : ℝ)|^4523 ≤ (2616084139381/25000000000000 : ℝ)^3499
        have hw : |(-34888107/200000000 : ℝ)|=(34888107/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510595299/10000000000 : ℝ)|^4523 ≤ (578587399099/1250000000000 : ℝ)^3499
        have hw : |(5510595299/10000000000 : ℝ)|=(5510595299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045726111/2000000000 : ℝ)|^4523 ≤ (10812167873959/25000000000000 : ℝ)^3499
        have hw : |(1045726111/2000000000 : ℝ)|=(1045726111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_13 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695994339/5000000000 : ℝ)*x 0 + (-119235253/625000000 : ℝ)*x 1 + (5228630487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695994339/5000000000 : ℝ)^4523 ≤ (45003257942877/100000000000000 : ℝ)^3499 := by
    have hnat : (2695994339 : ℕ)^4523*100000000000000^3499 ≤ 45003257942877^3499*5000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695994339 5000000000 45003257942877 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119235253/625000000 : ℝ)^4523 ≤ (11748071276747/100000000000000 : ℝ)^3499 := by
    have hnat : (119235253 : ℕ)^4523*100000000000000^3499 ≤ 11748071276747^3499*625000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119235253 625000000 11748071276747 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228630487/10000000000 : ℝ)^4523 ≤ (21624335384383/50000000000000 : ℝ)^3499 := by
    have hnat : (5228630487 : ℕ)^4523*50000000000000^3499 ≤ 21624335384383^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228630487 10000000000 21624335384383 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695994339/5000000000 : ℝ), (-119235253/625000000 : ℝ), (5228630487/10000000000 : ℝ)] ![(45003257942877/100000000000000 : ℝ), (11748071276747/100000000000000 : ℝ), (21624335384383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695994339/5000000000 : ℝ)|^4523 ≤ (45003257942877/100000000000000 : ℝ)^3499
        have hw : |(2695994339/5000000000 : ℝ)|=(2695994339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119235253/625000000 : ℝ)|^4523 ≤ (11748071276747/100000000000000 : ℝ)^3499
        have hw : |(-119235253/625000000 : ℝ)|=(119235253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228630487/10000000000 : ℝ)|^4523 ≤ (21624335384383/50000000000000 : ℝ)^3499
        have hw : |(5228630487/10000000000 : ℝ)|=(5228630487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_14 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391988673/10000000000 : ℝ)*x 0 + (5228630563/10000000000 : ℝ)*x 1 + (-1907763953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391988673/10000000000 : ℝ)^4523 ≤ (11250814472233/25000000000000 : ℝ)^3499 := by
    have hnat : (5391988673 : ℕ)^4523*25000000000000^3499 ≤ 11250814472233^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391988673 10000000000 11250814472233 25000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228630563/10000000000 : ℝ)^4523 ≤ (21624335790687/50000000000000 : ℝ)^3499 := by
    have hnat : (5228630563 : ℕ)^4523*50000000000000^3499 ≤ 21624335790687^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228630563 10000000000 21624335790687 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907763953/10000000000 : ℝ)^4523 ≤ (11748070520527/100000000000000 : ℝ)^3499 := by
    have hnat : (1907763953 : ℕ)^4523*100000000000000^3499 ≤ 11748070520527^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907763953 10000000000 11748070520527 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391988673/10000000000 : ℝ), (5228630563/10000000000 : ℝ), (-1907763953/10000000000 : ℝ)] ![(11250814472233/25000000000000 : ℝ), (21624335790687/50000000000000 : ℝ), (11748070520527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391988673/10000000000 : ℝ)|^4523 ≤ (11250814472233/25000000000000 : ℝ)^3499
        have hw : |(5391988673/10000000000 : ℝ)|=(5391988673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228630563/10000000000 : ℝ)|^4523 ≤ (21624335790687/50000000000000 : ℝ)^3499
        have hw : |(5228630563/10000000000 : ℝ)|=(5228630563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1907763953/10000000000 : ℝ)|^4523 ≤ (11748070520527/100000000000000 : ℝ)^3499
        have hw : |(-1907763953/10000000000 : ℝ)|=(1907763953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1513_box_15 (p : ℝ) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4024417183/10000000000 : ℝ)*x 0 + (4398126643/10000000000 : ℝ)*x 1 + (4398126963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024417183/10000000000 : ℝ)^4523 ≤ (30833109979359/100000000000000 : ℝ)^3499 := by
    have hnat : (4024417183 : ℕ)^4523*100000000000000^3499 ≤ 30833109979359^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024417183 10000000000 30833109979359 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4398126643/10000000000 : ℝ)^4523 ≤ (17291721685637/50000000000000 : ℝ)^3499 := by
    have hnat : (4398126643 : ℕ)^4523*50000000000000^3499 ≤ 17291721685637^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398126643 10000000000 17291721685637 50000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4398126963/10000000000 : ℝ)^4523 ≤ (34583446623893/100000000000000 : ℝ)^3499 := by
    have hnat : (4398126963 : ℕ)^4523*100000000000000^3499 ≤ 34583446623893^3499*10000000000^4523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398126963 10000000000 34583446623893 100000000000000 4523 3499 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4523/1024 : ℝ)) 4523 3499 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024417183/10000000000 : ℝ), (4398126643/10000000000 : ℝ), (4398126963/10000000000 : ℝ)] ![(30833109979359/100000000000000 : ℝ), (17291721685637/50000000000000 : ℝ), (34583446623893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024417183/10000000000 : ℝ)|^4523 ≤ (30833109979359/100000000000000 : ℝ)^3499
        have hw : |(4024417183/10000000000 : ℝ)|=(4024417183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4398126643/10000000000 : ℝ)|^4523 ≤ (17291721685637/50000000000000 : ℝ)^3499
        have hw : |(4398126643/10000000000 : ℝ)|=(4398126643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4398126963/10000000000 : ℝ)|^4523 ≤ (34583446623893/100000000000000 : ℝ)^3499
        have hw : |(4398126963/10000000000 : ℝ)|=(4398126963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1513_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(63741/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7329/12500 : ℝ) ∧ (8033/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10751/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (273/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (273/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (273/2500 : ℝ) ^ (4521/1024 : ℝ) ≤ (5671727788796479/100000000000000000000 : ℝ) := by
    have hpowers : (273/2500 : ℝ)^4521 ≤ (5671727788796479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (273 : ℕ)^4521*100000000000000000000^1024 ≤ 5671727788796479^1024*2500^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        273 2500 5671727788796479 100000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (273/2500 : ℝ)) (X := (5671727788796479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4521/1024 : ℝ) ≤ (26488345732279947/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4521 ≤ (26488345732279947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4521*100000000000000000000^1024 ≤ 26488345732279947^1024*50000^4521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26488345732279947 100000000000000000000 4521 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26488345732279947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005671727788796479/50000000000000000000 : ℝ) ≤ (2000051383273411/2000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (50005671727788796479/50000000000000000000 : ℝ)^1024 ≤ (2000051383273411/2000000000000000 : ℝ)^4521 := by
      have hnat : (50005671727788796479 : ℕ)^1024*2000000000000000^4521 ≤ 2000051383273411^4521*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005671727788796479 50000000000000000000 2000051383273411 2000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051383273411/2000000000000000 : ℝ)) (X := (50005671727788796479/50000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016080036760538213/50000000000000000000 : ℝ) ≤ (10000728330458197/10000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (50016080036760538213/50000000000000000000 : ℝ)^1024 ≤ (10000728330458197/10000000000000000 : ℝ)^4521 := by
      have hnat : (50016080036760538213 : ℕ)^1024*10000000000000000^4521 ≤ 10000728330458197^4521*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016080036760538213 50000000000000000000 10000728330458197 10000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000728330458197/10000000000000000 : ℝ)) (X := (50016080036760538213/50000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026488345732279947/50000000000000000000 : ℝ) ≤ (10001199744549339/10000000000000000 : ℝ) ^ (4521/1024 : ℝ) := by
    have hpowers : (50026488345732279947/50000000000000000000 : ℝ)^1024 ≤ (10001199744549339/10000000000000000 : ℝ)^4521 := by
      have hnat : (50026488345732279947 : ℕ)^1024*10000000000000000^4521 ≤ 10001199744549339^4521*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026488345732279947 50000000000000000000 10001199744549339 10000000000000000 1024 4521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001199744549339/10000000000000000 : ℝ)) (X := (50026488345732279947/50000000000000000000 : ℝ)) (by norm_num) 4521 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5671727788796479/100000000000000000000 : ℝ) ≤ ((4561087636871596363/4562000000000000000 : ℝ)+2*(235707045571/228100000000000 : ℝ)*(273/2500 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (4561087636871596363/4562000000000000000 : ℝ)+2*(235707045571/228100000000000 : ℝ)*(273/2500 : ℝ)=(2000051383273411/2000000000000000 : ℝ) by norm_num, show 1+2*(5671727788796479/100000000000000000000 : ℝ)=(50005671727788796479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26488345732279947/100000000000000000000 : ℝ)+(5671727788796479/100000000000000000000 : ℝ) ≤ ((4561087636871596363/4562000000000000000 : ℝ)+(235707045571/228100000000000 : ℝ)*((7741/50000 : ℝ)+(273/2500 : ℝ)))^(4521/1024 : ℝ) := by
    rw [show (4561087636871596363/4562000000000000000 : ℝ)+(235707045571/228100000000000 : ℝ)*((7741/50000 : ℝ)+(273/2500 : ℝ))=(10000728330458197/10000000000000000 : ℝ) by norm_num, show 1+(26488345732279947/100000000000000000000 : ℝ)+(5671727788796479/100000000000000000000 : ℝ)=(50016080036760538213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26488345732279947/100000000000000000000 : ℝ) ≤ ((4561087636871596363/4562000000000000000 : ℝ)+2*(235707045571/228100000000000 : ℝ)*(7741/50000 : ℝ))^(4521/1024 : ℝ) := by
    rw [show (4561087636871596363/4562000000000000000 : ℝ)+2*(235707045571/228100000000000 : ℝ)*(7741/50000 : ℝ)=(10001199744549339/10000000000000000 : ℝ) by norm_num, show 1+2*(26488345732279947/100000000000000000000 : ℝ)=(50026488345732279947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4561087636871596363/4562000000000000000 : ℝ)*(X 1 0+X 2 0)+(235707045571/228100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (4561087636871596363/4562000000000000000 : ℝ)) (alpha := (235707045571/228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4561087636871596363/4562000000000000000 : ℝ)*(X 0 1+X 2 1)+(235707045571/228100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (4561087636871596363/4562000000000000000 : ℝ)) (alpha := (235707045571/228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4561087636871596363/4562000000000000000 : ℝ)*(X 0 2+X 1 2)+(235707045571/228100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4521/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (4561087636871596363/4562000000000000000 : ℝ)) (alpha := (235707045571/228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1653093443/10000000000 : ℝ)*X 0 0+(1350681099/2500000000 : ℝ)*X 0 1+(108054491/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270790569/10000000000 : ℝ)*X 1 0+(-183611567/1000000000 : ℝ)*X 1 1+(2701362103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42166327/80000000 : ℝ)*X 2 0+(5402724033/10000000000 : ℝ)*X 2 1+(-183611549/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((559040507/1250000000 : ℝ)*X 0 0+(2087386757/5000000000 : ℝ)*X 0 1+(417477379/1000000000 : ℝ)*X 0 2+(559040507/1250000000 : ℝ)*X 1 0+(2087386757/5000000000 : ℝ)*X 1 1+(417477379/1000000000 : ℝ)*X 1 2+(559040507/1250000000 : ℝ)*X 2 0+(2087386757/5000000000 : ℝ)*X 2 1+(417477379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2085427043/10000000000 : ℝ)*X 0 0+(209746357/400000000 : ℝ)*X 0 1+(1048731379/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5381526517/10000000000 : ℝ)*X 1 0+(-190174311/1000000000 : ℝ)*X 1 1+(5243658393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2690764173/5000000000 : ℝ)*X 2 0+(2621828281/5000000000 : ℝ)*X 2 1+(-950871547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2031932723/5000000000 : ℝ)*X 0 0+(35030949/80000000 : ℝ)*X 0 1+(2189434481/5000000000 : ℝ)*X 0 2+(2031932723/5000000000 : ℝ)*X 1 0+(35030949/80000000 : ℝ)*X 1 1+(2189434481/5000000000 : ℝ)*X 1 2+(2031932723/5000000000 : ℝ)*X 2 0+(35030949/80000000 : ℝ)*X 2 1+(2189434481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1994059487/10000000000 : ℝ)*X 0 0+(1026441591/2000000000 : ℝ)*X 0 1+(5423174611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628273867/5000000000 : ℝ)*X 1 0+(-1827432571/10000000000 : ℝ)*X 1 1+(5423174519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256548007/10000000000 : ℝ)*X 2 0+(2711587001/5000000000 : ℝ)*X 2 1+(-1827432911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((90473709/200000000 : ℝ)*X 0 0+(829700371/2000000000 : ℝ)*X 0 1+(4148502407/10000000000 : ℝ)*X 0 2+(90473709/200000000 : ℝ)*X 1 0+(829700371/2000000000 : ℝ)*X 1 1+(4148502407/10000000000 : ℝ)*X 1 2+(90473709/200000000 : ℝ)*X 2 0+(829700371/2000000000 : ℝ)*X 2 1+(4148502407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-34888107/200000000 : ℝ)*X 0 0+(5510595299/10000000000 : ℝ)*X 0 1+(1045726111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695994339/5000000000 : ℝ)*X 1 0+(-119235253/625000000 : ℝ)*X 1 1+(5228630487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391988673/10000000000 : ℝ)*X 2 0+(5228630563/10000000000 : ℝ)*X 2 1+(-1907763953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4024417183/10000000000 : ℝ)*X 0 0+(4398126643/10000000000 : ℝ)*X 0 1+(4398126963/10000000000 : ℝ)*X 0 2+(4024417183/10000000000 : ℝ)*X 1 0+(4398126643/10000000000 : ℝ)*X 1 1+(4398126963/10000000000 : ℝ)*X 1 2+(4024417183/10000000000 : ℝ)*X 2 0+(4398126643/10000000000 : ℝ)*X 2 1+(4398126963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1513_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63741/100000 : ℝ) ≤ (-14538661399284110660163315413229/22810000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119262977/100000000000000 : ℝ)*(upper0) + (7163939/25000000000000 : ℝ)*(lower2) + (234425293/100000000000000 : ℝ)*(upper4) + (28191759/25000000000000 : ℝ)*(upper5) + (222490363473087/10000000000000 : ℝ)*(major0) + (222490363473087/10000000000000 : ℝ)*(major1) + (222490363473087/10000000000000 : ℝ)*(major2) + (27607870597/100000000000000 : ℝ)*(sp2) + (424124831/12500000000000 : ℝ)*(sp3) + (777472499157577/25000000000000 : ℝ)*(sp4) + (777478986893433/25000000000000 : ℝ)*(sp5) + (97184010615723/3125000000000 : ℝ)*(sp6) + (42535436355503/3125000000000 : ℝ)*(sp7) + (1038037737/4000000000000 : ℝ)*(sp8) + (170142169546843/12500000000000 : ℝ)*(f.failure) + (777478986893433/25000000000000 : ℝ)*(f.sum) + (25560528204669/2281000000000000000000000000 : ℝ)*base65 + (405245030570982581/45620000000000000000000000000000 : ℝ)*base67 + (36932747059782581/45620000000000000000000000000000 : ℝ)*base69 + (819353066911362581/45620000000000000000000000000000 : ℝ)*base71 + (8851130213121/1140500000000000000000000000 : ℝ)*base73 + (378144054383362581/45620000000000000000000000000000 : ℝ)*base75 + (185835244224422581/45620000000000000000000000000000 : ℝ)*base77 + (470267610819022581/45620000000000000000000000000000 : ℝ)*base79 + (2025971693289/570250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3938873/312500000000000000000 : ℝ)*base90 + (3938873/312500000000000000000 : ℝ)*base92 + (3938873/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7329/12500 : ℝ) ≤ (66873046081068894498745277662647/114050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8093047/20000000000000 : ℝ)*(lower1) + (48546733/100000000000000 : ℝ)*(lower2) + (15949341/20000000000000 : ℝ)*(lower3) + (360329/1562500000000 : ℝ)*(upper4) + (8632553/100000000000000 : ℝ)*(lower5) + (1150601862812423/50000000000000 : ℝ)*(major0) + (1150601862812423/50000000000000 : ℝ)*(major1) + (1150601862812423/50000000000000 : ℝ)*(major2) + (198440422623171/6250000000000 : ℝ)*(sp0) + (3175012561937683/100000000000000 : ℝ)*(sp1) + (158749731208403/5000000000000 : ℝ)*(sp2) + (1407815739379473/100000000000000 : ℝ)*(sp3) + (34200033053/100000000000000 : ℝ)*(sp9) + (13034450669/25000000000000 : ℝ)*(sp10) + (1407815739379473/100000000000000 : ℝ)*(f.failure) + (198440422623171/6250000000000 : ℝ)*(f.sum) + (6466946725567/5702500000000000000000000000 : ℝ)*base66 + (530910968266877549/228100000000000000000000000000000 : ℝ)*base67 + (2227508693898322451/228100000000000000000000000000000 : ℝ)*base70 + (478924140930977549/228100000000000000000000000000000 : ℝ)*base71 + (22922311037221/11405000000000000000000000000 : ℝ)*base73 + (956139148478822451/228100000000000000000000000000000 : ℝ)*base76 + (800068074923322451/228100000000000000000000000000000 : ℝ)*base78 + (348857017448722451/228100000000000000000000000000000 : ℝ)*base80 + (10024894719713/1425625000000000000000000000 : ℝ)*base82 + (5076197/2500000000000000000000 : ℝ)*base89 + (5076197/2500000000000000000000 : ℝ)*base91 + (5076197/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8033/10000 : ℝ) ≤ (91619247810140381647915067512869/114050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100775123/100000000000000 : ℝ)*(upper0) + (25797493/100000000000000 : ℝ)*(upper2) + (30222393/50000000000000 : ℝ)*(lower5) + (1247494812066007/50000000000000 : ℝ)*(major0) + (1247494812066007/50000000000000 : ℝ)*(major1) + (1247494812066007/50000000000000 : ℝ)*(major2) + (5249263537/6250000000000 : ℝ)*(sp1) + (12762936079/50000000000000 : ℝ)*(sp3) + (2779835751/100000000000000 : ℝ)*(sp4) + (3436822229773279/100000000000000 : ℝ)*(sp8) + (1718374455160543/50000000000000 : ℝ)*(sp9) + (1718416449268839/50000000000000 : ℝ)*(sp10) + (1526343314630123/100000000000000 : ℝ)*(sp11) + (986116081/12500000000000 : ℝ)*(sp12) + (1526368840502281/100000000000000 : ℝ)*(f.failure) + (1718416449268839/50000000000000 : ℝ)*(f.sum) + (16965383902983/5702500000000000000000000000 : ℝ)*base66 + (486075105379827459/228100000000000000000000000000000 : ℝ)*base68 + (1554898760176427459/228100000000000000000000000000000 : ℝ)*base70 + (638900718759927459/228100000000000000000000000000000 : ℝ)*base72 + (17899881546561/11405000000000000000000000000 : ℝ)*base74 + (931620376005627459/228100000000000000000000000000000 : ℝ)*base76 + (738504638009327459/228100000000000000000000000000000 : ℝ)*base78 + (768088703680227459/228100000000000000000000000000000 : ℝ)*base80 + (4390791253321/11405000000000000000000000000 : ℝ)*base82 + (17083709/2500000000000000000000 : ℝ)*base89 + (17083709/2500000000000000000000 : ℝ)*base91 + (17083709/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10751/12500 : ℝ) ≤ (-98089580515886025097188181416297/114050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30381619/100000000000000 : ℝ)*(lower2) + (39179243/100000000000000 : ℝ)*(lower4) + (87347847/100000000000000 : ℝ)*(upper5) + (1267040748884909/50000000000000 : ℝ)*(major0) + (1267040748884909/50000000000000 : ℝ)*(major1) + (1267040748884909/50000000000000 : ℝ)*(major2) + (2082982627/50000000000000 : ℝ)*(sp4) + (6975636341/20000000000000 : ℝ)*(sp5) + (649992613/1562500000000 : ℝ)*(sp6) + (283202699/25000000000000 : ℝ)*(sp8) + (177327103453271/5000000000000 : ℝ)*(sp12) + (886628122414941/25000000000000 : ℝ)*(sp13) + (1773252884157119/50000000000000 : ℝ)*(sp14) + (1550284217648731/100000000000000 : ℝ)*(sp15) + (1550284217648731/100000000000000 : ℝ)*(f.failure) + (354654736784147/10000000000000 : ℝ)*(f.sum) + (28989521496483/11405000000000000000000000000 : ℝ)*base65 + (3150351468127534033/228100000000000000000000000000000 : ℝ)*base68 + (2955096498615134033/228100000000000000000000000000000 : ℝ)*base70 + (1140492457074234033/228100000000000000000000000000000 : ℝ)*base72 + (52970351033377/11405000000000000000000000000 : ℝ)*base74 + (1267747356765834033/228100000000000000000000000000000 : ℝ)*base76 + (1835198600103134033/228100000000000000000000000000000 : ℝ)*base78 + (2483345478198334033/228100000000000000000000000000000 : ℝ)*base80 + (7541527573977/11405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (18432759/2500000000000000000000 : ℝ)*base89 + (18432759/2500000000000000000000 : ℝ)*base91 + (18432759/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1513_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63741/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7329/12500 : ℝ) else (8033/10000 : ℝ) ≤ X j i ∧ X j i ≤ (10751/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1513_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1513_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63741/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7329/12500 : ℝ) else (8033/10000 : ℝ) ≤ X j i ∧ X j i ≤ (10751/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1513_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1513_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4521/1024 : ℝ) ≤ p) (hpb : p ≤ (4523/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40864789/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63741/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7329/12500 : ℝ) else (8033/10000 : ℝ) ≤ X j i ∧ X j i ≤ (10751/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1513_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

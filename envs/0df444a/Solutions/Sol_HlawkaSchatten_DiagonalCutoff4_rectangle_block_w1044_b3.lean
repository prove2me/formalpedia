-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:59.133802+00:00
-- url     : https://prove2.me/submissions/f273328a-b887-4c28-849b-e1fefc8152e4

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
theorem support_rectangle_w1044_box_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084412133/10000000000 : ℝ)*x 0 + (5377666703/10000000000 : ℝ)*x 1 + (5377666941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084412133/10000000000 : ℝ)^8237 ≤ (12405911308363/100000000000000 : ℝ)^6189 := by
    have hnat : (2084412133 : ℕ)^8237*100000000000000^6189 ≤ 12405911308363^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084412133 10000000000 12405911308363 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377666703/10000000000 : ℝ)^8237 ≤ (21898521523431/50000000000000 : ℝ)^6189 := by
    have hnat : (5377666703 : ℕ)^8237*50000000000000^6189 ≤ 21898521523431^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377666703 10000000000 21898521523431 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377666941/10000000000 : ℝ)^8237 ≤ (8759409125321/20000000000000 : ℝ)^6189 := by
    have hnat : (5377666941 : ℕ)^8237*20000000000000^6189 ≤ 8759409125321^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377666941 10000000000 8759409125321 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084412133/10000000000 : ℝ), (5377666703/10000000000 : ℝ), (5377666941/10000000000 : ℝ)] ![(12405911308363/100000000000000 : ℝ), (21898521523431/50000000000000 : ℝ), (8759409125321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084412133/10000000000 : ℝ)|^8237 ≤ (12405911308363/100000000000000 : ℝ)^6189
        have hw : |(-2084412133/10000000000 : ℝ)|=(2084412133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377666703/10000000000 : ℝ)|^8237 ≤ (21898521523431/50000000000000 : ℝ)^6189
        have hw : |(5377666703/10000000000 : ℝ)|=(5377666703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377666941/10000000000 : ℝ)|^8237 ≤ (8759409125321/20000000000000 : ℝ)^6189
        have hw : |(5377666941/10000000000 : ℝ)|=(5377666941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647473339/5000000000 : ℝ)*x 0 + (-2196333261/10000000000 : ℝ)*x 1 + (672208307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647473339/5000000000 : ℝ)^8237 ≤ (42902709313349/100000000000000 : ℝ)^6189 := by
    have hnat : (2647473339 : ℕ)^8237*100000000000000^6189 ≤ 42902709313349^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647473339 5000000000 42902709313349 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196333261/10000000000 : ℝ)^8237 ≤ (13300250305759/100000000000000 : ℝ)^6189 := by
    have hnat : (2196333261 : ℕ)^8237*100000000000000^6189 ≤ 13300250305759^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196333261 10000000000 13300250305759 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672208307/1250000000 : ℝ)^8237 ≤ (8759408073913/20000000000000 : ℝ)^6189 := by
    have hnat : (672208307 : ℕ)^8237*20000000000000^6189 ≤ 8759408073913^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672208307 1250000000 8759408073913 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647473339/5000000000 : ℝ), (-2196333261/10000000000 : ℝ), (672208307/1250000000 : ℝ)] ![(42902709313349/100000000000000 : ℝ), (13300250305759/100000000000000 : ℝ), (8759408073913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647473339/5000000000 : ℝ)|^8237 ≤ (42902709313349/100000000000000 : ℝ)^6189
        have hw : |(2647473339/5000000000 : ℝ)|=(2647473339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196333261/10000000000 : ℝ)|^8237 ≤ (13300250305759/100000000000000 : ℝ)^6189
        have hw : |(-2196333261/10000000000 : ℝ)|=(2196333261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672208307/1250000000 : ℝ)|^8237 ≤ (8759408073913/20000000000000 : ℝ)^6189
        have hw : |(672208307/1250000000 : ℝ)|=(672208307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294946721/10000000000 : ℝ)*x 0 + (5377666707/10000000000 : ℝ)*x 1 + (-1098166433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294946721/10000000000 : ℝ)^8237 ≤ (10725677444263/25000000000000 : ℝ)^6189 := by
    have hnat : (5294946721 : ℕ)^8237*25000000000000^6189 ≤ 10725677444263^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294946721 10000000000 10725677444263 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377666707/10000000000 : ℝ)^8237 ≤ (43797043090219/100000000000000 : ℝ)^6189 := by
    have hnat : (5377666707 : ℕ)^8237*100000000000000^6189 ≤ 43797043090219^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377666707 10000000000 43797043090219 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098166433/5000000000 : ℝ)^8237 ≤ (13300247122241/100000000000000 : ℝ)^6189 := by
    have hnat : (1098166433 : ℕ)^8237*100000000000000^6189 ≤ 13300247122241^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098166433 5000000000 13300247122241 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294946721/10000000000 : ℝ), (5377666707/10000000000 : ℝ), (-1098166433/5000000000 : ℝ)] ![(10725677444263/25000000000000 : ℝ), (43797043090219/100000000000000 : ℝ), (13300247122241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294946721/10000000000 : ℝ)|^8237 ≤ (10725677444263/25000000000000 : ℝ)^6189
        have hw : |(5294946721/10000000000 : ℝ)|=(5294946721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377666707/10000000000 : ℝ)|^8237 ≤ (43797043090219/100000000000000 : ℝ)^6189
        have hw : |(5377666707/10000000000 : ℝ)|=(5377666707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098166433/5000000000 : ℝ)|^8237 ≤ (13300247122241/100000000000000 : ℝ)^6189
        have hw : |(-1098166433/5000000000 : ℝ)|=(1098166433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4487315459/10000000000 : ℝ)*x 0 + (4326521517/10000000000 : ℝ)*x 1 + (43265213/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487315459/10000000000 : ℝ)^8237 ≤ (2151322984249/6250000000000 : ℝ)^6189 := by
    have hnat : (4487315459 : ℕ)^8237*6250000000000^6189 ≤ 2151322984249^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487315459 10000000000 2151322984249 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4326521517/10000000000 : ℝ)^8237 ≤ (32789417209687/100000000000000 : ℝ)^6189 := by
    have hnat : (4326521517 : ℕ)^8237*100000000000000^6189 ≤ 32789417209687^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326521517 10000000000 32789417209687 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43265213/100000000 : ℝ)^8237 ≤ (16394707510451/50000000000000 : ℝ)^6189 := by
    have hnat : (43265213 : ℕ)^8237*50000000000000^6189 ≤ 16394707510451^6189*100000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43265213 100000000 16394707510451 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487315459/10000000000 : ℝ), (4326521517/10000000000 : ℝ), (43265213/100000000 : ℝ)] ![(2151322984249/6250000000000 : ℝ), (32789417209687/100000000000000 : ℝ), (16394707510451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487315459/10000000000 : ℝ)|^8237 ≤ (2151322984249/6250000000000 : ℝ)^6189
        have hw : |(4487315459/10000000000 : ℝ)|=(4487315459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4326521517/10000000000 : ℝ)|^8237 ≤ (32789417209687/100000000000000 : ℝ)^6189
        have hw : |(4326521517/10000000000 : ℝ)|=(4326521517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43265213/100000000 : ℝ)|^8237 ≤ (16394707510451/50000000000000 : ℝ)^6189
        have hw : |(43265213/100000000 : ℝ)|=(43265213/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-469254379/2000000000 : ℝ)*x 0 + (5279752463/10000000000 : ℝ)*x 1 + (5279751947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469254379/2000000000 : ℝ)^8237 ≤ (1815266737529/12500000000000 : ℝ)^6189 := by
    have hnat : (469254379 : ℕ)^8237*12500000000000^6189 ≤ 1815266737529^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469254379 2000000000 1815266737529 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279752463/10000000000 : ℝ)^8237 ≤ (10684733956081/25000000000000 : ℝ)^6189 := by
    have hnat : (5279752463 : ℕ)^8237*25000000000000^6189 ≤ 10684733956081^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279752463 10000000000 10684733956081 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279751947/10000000000 : ℝ)^8237 ≤ (21369465132587/50000000000000 : ℝ)^6189 := by
    have hnat : (5279751947 : ℕ)^8237*50000000000000^6189 ≤ 21369465132587^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279751947 10000000000 21369465132587 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469254379/2000000000 : ℝ), (5279752463/10000000000 : ℝ), (5279751947/10000000000 : ℝ)] ![(1815266737529/12500000000000 : ℝ), (10684733956081/25000000000000 : ℝ), (21369465132587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469254379/2000000000 : ℝ)|^8237 ≤ (1815266737529/12500000000000 : ℝ)^6189
        have hw : |(-469254379/2000000000 : ℝ)|=(469254379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279752463/10000000000 : ℝ)|^8237 ≤ (10684733956081/25000000000000 : ℝ)^6189
        have hw : |(5279752463/10000000000 : ℝ)|=(5279752463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279751947/10000000000 : ℝ)|^8237 ≤ (21369465132587/50000000000000 : ℝ)^6189
        have hw : |(5279751947/10000000000 : ℝ)|=(5279751947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42914221/80000000 : ℝ)*x 0 + (-2234544001/10000000000 : ℝ)*x 1 + (164992249/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42914221/80000000 : ℝ)^8237 ≤ (21825987607133/50000000000000 : ℝ)^6189 := by
    have hnat : (42914221 : ℕ)^8237*50000000000000^6189 ≤ 21825987607133^6189*80000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42914221 80000000 21825987607133 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234544001/10000000000 : ℝ)^8237 ≤ (13609094276677/100000000000000 : ℝ)^6189 := by
    have hnat : (2234544001 : ℕ)^8237*100000000000000^6189 ≤ 13609094276677^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234544001 10000000000 13609094276677 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164992249/312500000 : ℝ)^8237 ≤ (21369465245709/50000000000000 : ℝ)^6189 := by
    have hnat : (164992249 : ℕ)^8237*50000000000000^6189 ≤ 21369465245709^6189*312500000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164992249 312500000 21369465245709 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42914221/80000000 : ℝ), (-2234544001/10000000000 : ℝ), (164992249/312500000 : ℝ)] ![(21825987607133/50000000000000 : ℝ), (13609094276677/100000000000000 : ℝ), (21369465245709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42914221/80000000 : ℝ)|^8237 ≤ (21825987607133/50000000000000 : ℝ)^6189
        have hw : |(42914221/80000000 : ℝ)|=(42914221/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234544001/10000000000 : ℝ)|^8237 ≤ (13609094276677/100000000000000 : ℝ)^6189
        have hw : |(-2234544001/10000000000 : ℝ)|=(2234544001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164992249/312500000 : ℝ)|^8237 ≤ (21369465245709/50000000000000 : ℝ)^6189
        have hw : |(164992249/312500000 : ℝ)|=(164992249/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072855407/2000000000 : ℝ)*x 0 + (263987623/500000000 : ℝ)*x 1 + (-279318017/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072855407/2000000000 : ℝ)^8237 ≤ (43651968824379/100000000000000 : ℝ)^6189 := by
    have hnat : (1072855407 : ℕ)^8237*100000000000000^6189 ≤ 43651968824379^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072855407 2000000000 43651968824379 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263987623/500000000 : ℝ)^8237 ≤ (42738935792003/100000000000000 : ℝ)^6189 := by
    have hnat : (263987623 : ℕ)^8237*100000000000000^6189 ≤ 42738935792003^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263987623 500000000 42738935792003 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279318017/1250000000 : ℝ)^8237 ≤ (6804547685471/50000000000000 : ℝ)^6189 := by
    have hnat : (279318017 : ℕ)^8237*50000000000000^6189 ≤ 6804547685471^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279318017 1250000000 6804547685471 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072855407/2000000000 : ℝ), (263987623/500000000 : ℝ), (-279318017/1250000000 : ℝ)] ![(43651968824379/100000000000000 : ℝ), (42738935792003/100000000000000 : ℝ), (6804547685471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072855407/2000000000 : ℝ)|^8237 ≤ (43651968824379/100000000000000 : ℝ)^6189
        have hw : |(1072855407/2000000000 : ℝ)|=(1072855407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263987623/500000000 : ℝ)|^8237 ≤ (42738935792003/100000000000000 : ℝ)^6189
        have hw : |(263987623/500000000 : ℝ)|=(263987623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279318017/1250000000 : ℝ)|^8237 ≤ (6804547685471/50000000000000 : ℝ)^6189
        have hw : |(-279318017/1250000000 : ℝ)|=(279318017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4269698087/10000000000 : ℝ)*x 0 + (554413581/1250000000 : ℝ)*x 1 + (4435308229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269698087/10000000000 : ℝ)^8237 ≤ (32217512983711/100000000000000 : ℝ)^6189 := by
    have hnat : (4269698087 : ℕ)^8237*100000000000000^6189 ≤ 32217512983711^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269698087 10000000000 32217512983711 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554413581/1250000000 : ℝ)^8237 ≤ (16945622815819/50000000000000 : ℝ)^6189 := by
    have hnat : (554413581 : ℕ)^8237*50000000000000^6189 ≤ 16945622815819^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554413581 1250000000 16945622815819 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435308229/10000000000 : ℝ)^8237 ≤ (16945620685247/50000000000000 : ℝ)^6189 := by
    have hnat : (4435308229 : ℕ)^8237*50000000000000^6189 ≤ 16945620685247^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435308229 10000000000 16945620685247 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269698087/10000000000 : ℝ), (554413581/1250000000 : ℝ), (4435308229/10000000000 : ℝ)] ![(32217512983711/100000000000000 : ℝ), (16945622815819/50000000000000 : ℝ), (16945620685247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269698087/10000000000 : ℝ)|^8237 ≤ (32217512983711/100000000000000 : ℝ)^6189
        have hw : |(4269698087/10000000000 : ℝ)|=(4269698087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554413581/1250000000 : ℝ)|^8237 ≤ (16945622815819/50000000000000 : ℝ)^6189
        have hw : |(554413581/1250000000 : ℝ)|=(554413581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435308229/10000000000 : ℝ)|^8237 ≤ (16945620685247/50000000000000 : ℝ)^6189
        have hw : |(4435308229/10000000000 : ℝ)|=(4435308229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_8 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-458326929/2000000000 : ℝ)*x 0 + (2606677393/5000000000 : ℝ)*x 1 + (1346816263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458326929/2000000000 : ℝ)^8237 ≤ (7036898662361/50000000000000 : ℝ)^6189 := by
    have hnat : (458326929 : ℕ)^8237*50000000000000^6189 ≤ 7036898662361^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458326929 2000000000 7036898662361 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606677393/5000000000 : ℝ)^8237 ≤ (42025089938647/100000000000000 : ℝ)^6189 := by
    have hnat : (2606677393 : ℕ)^8237*100000000000000^6189 ≤ 42025089938647^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606677393 5000000000 42025089938647 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346816263/2500000000 : ℝ)^8237 ≤ (8780222544989/20000000000000 : ℝ)^6189 := by
    have hnat : (1346816263 : ℕ)^8237*20000000000000^6189 ≤ 8780222544989^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346816263 2500000000 8780222544989 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458326929/2000000000 : ℝ), (2606677393/5000000000 : ℝ), (1346816263/2500000000 : ℝ)] ![(7036898662361/50000000000000 : ℝ), (42025089938647/100000000000000 : ℝ), (8780222544989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458326929/2000000000 : ℝ)|^8237 ≤ (7036898662361/50000000000000 : ℝ)^6189
        have hw : |(-458326929/2000000000 : ℝ)|=(458326929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606677393/5000000000 : ℝ)|^8237 ≤ (42025089938647/100000000000000 : ℝ)^6189
        have hw : |(2606677393/5000000000 : ℝ)|=(2606677393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346816263/2500000000 : ℝ)|^8237 ≤ (8780222544989/20000000000000 : ℝ)^6189
        have hw : |(1346816263/2500000000 : ℝ)|=(1346816263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_9 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211525851/400000000 : ℝ)*x 0 + (-2192516569/10000000000 : ℝ)*x 1 + (5387264881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211525851/400000000 : ℝ)^8237 ≤ (21414695367199/50000000000000 : ℝ)^6189 := by
    have hnat : (211525851 : ℕ)^8237*50000000000000^6189 ≤ 21414695367199^6189*400000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211525851 400000000 21414695367199 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192516569/10000000000 : ℝ)^8237 ≤ (1326949837849/10000000000000 : ℝ)^6189 := by
    have hnat : (2192516569 : ℕ)^8237*10000000000000^6189 ≤ 1326949837849^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192516569 10000000000 1326949837849 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387264881/10000000000 : ℝ)^8237 ≤ (21950555435169/50000000000000 : ℝ)^6189 := by
    have hnat : (5387264881 : ℕ)^8237*50000000000000^6189 ≤ 21950555435169^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387264881 10000000000 21950555435169 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211525851/400000000 : ℝ), (-2192516569/10000000000 : ℝ), (5387264881/10000000000 : ℝ)] ![(21414695367199/50000000000000 : ℝ), (1326949837849/10000000000000 : ℝ), (21950555435169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211525851/400000000 : ℝ)|^8237 ≤ (21414695367199/50000000000000 : ℝ)^6189
        have hw : |(211525851/400000000 : ℝ)|=(211525851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192516569/10000000000 : ℝ)|^8237 ≤ (1326949837849/10000000000000 : ℝ)^6189
        have hw : |(-2192516569/10000000000 : ℝ)|=(2192516569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387264881/10000000000 : ℝ)|^8237 ≤ (21950555435169/50000000000000 : ℝ)^6189
        have hw : |(5387264881/10000000000 : ℝ)|=(5387264881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_10 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322036639/2500000000 : ℝ)*x 0 + (1346816249/2500000000 : ℝ)*x 1 + (-2192516039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322036639/2500000000 : ℝ)^8237 ≤ (42829393763357/100000000000000 : ℝ)^6189 := by
    have hnat : (1322036639 : ℕ)^8237*100000000000000^6189 ≤ 42829393763357^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322036639 2500000000 42829393763357 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346816249/2500000000 : ℝ)^8237 ≤ (10975278029397/25000000000000 : ℝ)^6189 := by
    have hnat : (1346816249 : ℕ)^8237*25000000000000^6189 ≤ 10975278029397^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346816249 2500000000 10975278029397 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192516039/10000000000 : ℝ)^8237 ≤ (13269494109393/100000000000000 : ℝ)^6189 := by
    have hnat : (2192516039 : ℕ)^8237*100000000000000^6189 ≤ 13269494109393^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192516039 10000000000 13269494109393 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322036639/2500000000 : ℝ), (1346816249/2500000000 : ℝ), (-2192516039/10000000000 : ℝ)] ![(42829393763357/100000000000000 : ℝ), (10975278029397/25000000000000 : ℝ), (13269494109393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322036639/2500000000 : ℝ)|^8237 ≤ (42829393763357/100000000000000 : ℝ)^6189
        have hw : |(1322036639/2500000000 : ℝ)|=(1322036639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346816249/2500000000 : ℝ)|^8237 ≤ (10975278029397/25000000000000 : ℝ)^6189
        have hw : |(1346816249/2500000000 : ℝ)|=(1346816249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192516039/10000000000 : ℝ)|^8237 ≤ (13269494109393/100000000000000 : ℝ)^6189
        have hw : |(-2192516039/10000000000 : ℝ)|=(2192516039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_11 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (56354679/125000000 : ℝ)*x 0 + (4315851319/10000000000 : ℝ)*x 1 + (4315851563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56354679/125000000 : ℝ)^8237 ≤ (34636326588743/100000000000000 : ℝ)^6189 := by
    have hnat : (56354679 : ℕ)^8237*100000000000000^6189 ≤ 34636326588743^6189*125000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56354679 125000000 34636326588743 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315851319/10000000000 : ℝ)^8237 ≤ (8170458868673/25000000000000 : ℝ)^6189 := by
    have hnat : (4315851319 : ℕ)^8237*25000000000000^6189 ≤ 8170458868673^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315851319 10000000000 8170458868673 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4315851563/10000000000 : ℝ)^8237 ≤ (8170459483451/25000000000000 : ℝ)^6189 := by
    have hnat : (4315851563 : ℕ)^8237*25000000000000^6189 ≤ 8170459483451^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315851563 10000000000 8170459483451 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56354679/125000000 : ℝ), (4315851319/10000000000 : ℝ), (4315851563/10000000000 : ℝ)] ![(34636326588743/100000000000000 : ℝ), (8170458868673/25000000000000 : ℝ), (8170459483451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56354679/125000000 : ℝ)|^8237 ≤ (34636326588743/100000000000000 : ℝ)^6189
        have hw : |(56354679/125000000 : ℝ)|=(56354679/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315851319/10000000000 : ℝ)|^8237 ≤ (8170458868673/25000000000000 : ℝ)^6189
        have hw : |(4315851319/10000000000 : ℝ)|=(4315851319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4315851563/10000000000 : ℝ)|^8237 ≤ (8170459483451/25000000000000 : ℝ)^6189
        have hw : |(4315851563/10000000000 : ℝ)|=(4315851563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_12 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139433307/10000000000 : ℝ)*x 0 + (5442710907/10000000000 : ℝ)*x 1 + (263588133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139433307/10000000000 : ℝ)^8237 ≤ (2568728025001/20000000000000 : ℝ)^6189 := by
    have hnat : (2139433307 : ℕ)^8237*20000000000000^6189 ≤ 2568728025001^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139433307 10000000000 2568728025001 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442710907/10000000000 : ℝ)^8237 ≤ (44503480987053/100000000000000 : ℝ)^6189 := by
    have hnat : (5442710907 : ℕ)^8237*100000000000000^6189 ≤ 44503480987053^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442710907 10000000000 44503480987053 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263588133/500000000 : ℝ)^8237 ≤ (853057577257/2000000000000 : ℝ)^6189 := by
    have hnat : (263588133 : ℕ)^8237*2000000000000^6189 ≤ 853057577257^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263588133 500000000 853057577257 2000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139433307/10000000000 : ℝ), (5442710907/10000000000 : ℝ), (263588133/500000000 : ℝ)] ![(2568728025001/20000000000000 : ℝ), (44503480987053/100000000000000 : ℝ), (853057577257/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139433307/10000000000 : ℝ)|^8237 ≤ (2568728025001/20000000000000 : ℝ)^6189
        have hw : |(-2139433307/10000000000 : ℝ)|=(2139433307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442710907/10000000000 : ℝ)|^8237 ≤ (44503480987053/100000000000000 : ℝ)^6189
        have hw : |(5442710907/10000000000 : ℝ)|=(5442710907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263588133/500000000 : ℝ)|^8237 ≤ (853057577257/2000000000000 : ℝ)^6189
        have hw : |(263588133/500000000 : ℝ)|=(263588133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_13 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684966181/5000000000 : ℝ)*x 0 + (-2237602461/10000000000 : ℝ)*x 1 + (2635881417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684966181/5000000000 : ℝ)^8237 ≤ (8742645699441/20000000000000 : ℝ)^6189 := by
    have hnat : (2684966181 : ℕ)^8237*20000000000000^6189 ≤ 8742645699441^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684966181 5000000000 8742645699441 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237602461/10000000000 : ℝ)^8237 ≤ (852118172203/6250000000000 : ℝ)^6189 := by
    have hnat : (2237602461 : ℕ)^8237*6250000000000^6189 ≤ 852118172203^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237602461 10000000000 852118172203 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635881417/5000000000 : ℝ)^8237 ≤ (42652880736509/100000000000000 : ℝ)^6189 := by
    have hnat : (2635881417 : ℕ)^8237*100000000000000^6189 ≤ 42652880736509^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635881417 5000000000 42652880736509 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684966181/5000000000 : ℝ), (-2237602461/10000000000 : ℝ), (2635881417/5000000000 : ℝ)] ![(8742645699441/20000000000000 : ℝ), (852118172203/6250000000000 : ℝ), (42652880736509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684966181/5000000000 : ℝ)|^8237 ≤ (8742645699441/20000000000000 : ℝ)^6189
        have hw : |(2684966181/5000000000 : ℝ)|=(2684966181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237602461/10000000000 : ℝ)|^8237 ≤ (852118172203/6250000000000 : ℝ)^6189
        have hw : |(-2237602461/10000000000 : ℝ)|=(2237602461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635881417/5000000000 : ℝ)|^8237 ≤ (42652880736509/100000000000000 : ℝ)^6189
        have hw : |(2635881417/5000000000 : ℝ)|=(2635881417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_14 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369932317/10000000000 : ℝ)*x 0 + (263588143/500000000 : ℝ)*x 1 + (-447520497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369932317/10000000000 : ℝ)^8237 ≤ (43713228009671/100000000000000 : ℝ)^6189 := by
    have hnat : (5369932317 : ℕ)^8237*100000000000000^6189 ≤ 43713228009671^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369932317 10000000000 43713228009671 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263588143/500000000 : ℝ)^8237 ≤ (266580506353/625000000000 : ℝ)^6189 := by
    have hnat : (263588143 : ℕ)^8237*625000000000^6189 ≤ 266580506353^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263588143 500000000 266580506353 625000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447520497/2000000000 : ℝ)^8237 ≤ (852118184367/6250000000000 : ℝ)^6189 := by
    have hnat : (447520497 : ℕ)^8237*6250000000000^6189 ≤ 852118184367^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447520497 2000000000 852118184367 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369932317/10000000000 : ℝ), (263588143/500000000 : ℝ), (-447520497/2000000000 : ℝ)] ![(43713228009671/100000000000000 : ℝ), (266580506353/625000000000 : ℝ), (852118184367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369932317/10000000000 : ℝ)|^8237 ≤ (43713228009671/100000000000000 : ℝ)^6189
        have hw : |(5369932317/10000000000 : ℝ)|=(5369932317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263588143/500000000 : ℝ)|^8237 ≤ (266580506353/625000000000 : ℝ)^6189
        have hw : |(263588143/500000000 : ℝ)|=(263588143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447520497/2000000000 : ℝ)|^8237 ≤ (852118184367/6250000000000 : ℝ)^6189
        have hw : |(-447520497/2000000000 : ℝ)|=(447520497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_box_15 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4251711919/10000000000 : ℝ)*x 0 + (4444180017/10000000000 : ℝ)*x 1 + (2222089849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251711919/10000000000 : ℝ)^8237 ≤ (8009253060731/25000000000000 : ℝ)^6189 := by
    have hnat : (4251711919 : ℕ)^8237*25000000000000^6189 ≤ 8009253060731^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251711919 10000000000 8009253060731 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4444180017/10000000000 : ℝ)^8237 ≤ (33981495493867/100000000000000 : ℝ)^6189 := by
    have hnat : (4444180017 : ℕ)^8237*100000000000000^6189 ≤ 33981495493867^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444180017 10000000000 33981495493867 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222089849/5000000000 : ℝ)^8237 ≤ (8495373061889/25000000000000 : ℝ)^6189 := by
    have hnat : (2222089849 : ℕ)^8237*25000000000000^6189 ≤ 8495373061889^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222089849 5000000000 8495373061889 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251711919/10000000000 : ℝ), (4444180017/10000000000 : ℝ), (2222089849/5000000000 : ℝ)] ![(8009253060731/25000000000000 : ℝ), (33981495493867/100000000000000 : ℝ), (8495373061889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251711919/10000000000 : ℝ)|^8237 ≤ (8009253060731/25000000000000 : ℝ)^6189
        have hw : |(4251711919/10000000000 : ℝ)|=(4251711919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4444180017/10000000000 : ℝ)|^8237 ≤ (33981495493867/100000000000000 : ℝ)^6189
        have hw : |(4444180017/10000000000 : ℝ)|=(4444180017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2222089849/5000000000 : ℝ)|^8237 ≤ (8495373061889/25000000000000 : ℝ)^6189
        have hw : |(2222089849/5000000000 : ℝ)|=(2222089849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7403/12500 : ℝ) ∧ (79503/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41451/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (7562872444771637/50000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^2059 ≤ (7562872444771637/50000000000000000000 : ℝ)^512 := by
      have hnat : (11221 : ℕ)^2059*50000000000000000000^512 ≤ 7562872444771637^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 7562872444771637 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (7562872444771637/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13989/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (36710850080264691/100000000000000000000 : ℝ) := by
    have hpowers : (13989/100000 : ℝ)^2059 ≤ (36710850080264691/100000000000000000000 : ℝ)^512 := by
      have hnat : (13989 : ℕ)^2059*100000000000000000000^512 ≤ 36710850080264691^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13989 100000 36710850080264691 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13989/100000 : ℝ)) (X := (36710850080264691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007562872444771637/25000000000000000000 : ℝ) ≤ (10000752161382011/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25007562872444771637/25000000000000000000 : ℝ)^512 ≤ (10000752161382011/10000000000000000 : ℝ)^2059 := by
      have hnat : (25007562872444771637 : ℕ)^512*10000000000000000^2059 ≤ 10000752161382011^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007562872444771637 25000000000000000000 10000752161382011 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000752161382011/10000000000000000 : ℝ)) (X := (25007562872444771637/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010367318993961593/20000000000000000000 : ℝ) ≤ (2500322185161463/2500000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (20010367318993961593/20000000000000000000 : ℝ)^512 ≤ (2500322185161463/2500000000000000 : ℝ)^2059 := by
      have hnat : (20010367318993961593 : ℕ)^512*2500000000000000^2059 ≤ 2500322185161463^2059*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010367318993961593 20000000000000000000 2500322185161463 2500000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500322185161463/2500000000000000 : ℝ)) (X := (20010367318993961593/20000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036710850080264691/50000000000000000000 : ℝ) ≤ (10001825319909693/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50036710850080264691/50000000000000000000 : ℝ)^512 ≤ (10001825319909693/10000000000000000 : ℝ)^2059 := by
      have hnat : (50036710850080264691 : ℕ)^512*10000000000000000^2059 ≤ 10001825319909693^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036710850080264691 50000000000000000000 10001825319909693 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001825319909693/10000000000000000 : ℝ)) (X := (50036710850080264691/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7562872444771637/50000000000000000000 : ℝ) ≤ ((13835020035433143363/13840000000000000000 : ℝ)+2*(536579263841/276800000000000 : ℝ)*(11221/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (13835020035433143363/13840000000000000000 : ℝ)+2*(536579263841/276800000000000 : ℝ)*(11221/100000 : ℝ)=(10000752161382011/10000000000000000 : ℝ) by norm_num, show 1+2*(7562872444771637/50000000000000000000 : ℝ)=(25007562872444771637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36710850080264691/100000000000000000000 : ℝ)+(7562872444771637/50000000000000000000 : ℝ) ≤ ((13835020035433143363/13840000000000000000 : ℝ)+(536579263841/276800000000000 : ℝ)*((13989/100000 : ℝ)+(11221/100000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (13835020035433143363/13840000000000000000 : ℝ)+(536579263841/276800000000000 : ℝ)*((13989/100000 : ℝ)+(11221/100000 : ℝ))=(2500322185161463/2500000000000000 : ℝ) by norm_num, show 1+(36710850080264691/100000000000000000000 : ℝ)+(7562872444771637/50000000000000000000 : ℝ)=(20010367318993961593/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36710850080264691/100000000000000000000 : ℝ) ≤ ((13835020035433143363/13840000000000000000 : ℝ)+2*(536579263841/276800000000000 : ℝ)*(13989/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (13835020035433143363/13840000000000000000 : ℝ)+2*(536579263841/276800000000000 : ℝ)*(13989/100000 : ℝ)=(10001825319909693/10000000000000000 : ℝ) by norm_num, show 1+2*(36710850080264691/100000000000000000000 : ℝ)=(50036710850080264691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13835020035433143363/13840000000000000000 : ℝ)*(X 1 0+X 2 0)+(536579263841/276800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13835020035433143363/13840000000000000000 : ℝ)) (alpha := (536579263841/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13835020035433143363/13840000000000000000 : ℝ)*(X 0 1+X 2 1)+(536579263841/276800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13835020035433143363/13840000000000000000 : ℝ)) (alpha := (536579263841/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13835020035433143363/13840000000000000000 : ℝ)*(X 0 2+X 1 2)+(536579263841/276800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13835020035433143363/13840000000000000000 : ℝ)) (alpha := (536579263841/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2084412133/10000000000 : ℝ)*X 0 0+(5377666703/10000000000 : ℝ)*X 0 1+(5377666941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647473339/5000000000 : ℝ)*X 1 0+(-2196333261/10000000000 : ℝ)*X 1 1+(672208307/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294946721/10000000000 : ℝ)*X 2 0+(5377666707/10000000000 : ℝ)*X 2 1+(-1098166433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487315459/10000000000 : ℝ)*X 0 0+(4326521517/10000000000 : ℝ)*X 0 1+(43265213/100000000 : ℝ)*X 0 2+(4487315459/10000000000 : ℝ)*X 1 0+(4326521517/10000000000 : ℝ)*X 1 1+(43265213/100000000 : ℝ)*X 1 2+(4487315459/10000000000 : ℝ)*X 2 0+(4326521517/10000000000 : ℝ)*X 2 1+(43265213/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-469254379/2000000000 : ℝ)*X 0 0+(5279752463/10000000000 : ℝ)*X 0 1+(5279751947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42914221/80000000 : ℝ)*X 1 0+(-2234544001/10000000000 : ℝ)*X 1 1+(164992249/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072855407/2000000000 : ℝ)*X 2 0+(263987623/500000000 : ℝ)*X 2 1+(-279318017/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269698087/10000000000 : ℝ)*X 0 0+(554413581/1250000000 : ℝ)*X 0 1+(4435308229/10000000000 : ℝ)*X 0 2+(4269698087/10000000000 : ℝ)*X 1 0+(554413581/1250000000 : ℝ)*X 1 1+(4435308229/10000000000 : ℝ)*X 1 2+(4269698087/10000000000 : ℝ)*X 2 0+(554413581/1250000000 : ℝ)*X 2 1+(4435308229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-458326929/2000000000 : ℝ)*X 0 0+(2606677393/5000000000 : ℝ)*X 0 1+(1346816263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((211525851/400000000 : ℝ)*X 1 0+(-2192516569/10000000000 : ℝ)*X 1 1+(5387264881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322036639/2500000000 : ℝ)*X 2 0+(1346816249/2500000000 : ℝ)*X 2 1+(-2192516039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((56354679/125000000 : ℝ)*X 0 0+(4315851319/10000000000 : ℝ)*X 0 1+(4315851563/10000000000 : ℝ)*X 0 2+(56354679/125000000 : ℝ)*X 1 0+(4315851319/10000000000 : ℝ)*X 1 1+(4315851563/10000000000 : ℝ)*X 1 2+(56354679/125000000 : ℝ)*X 2 0+(4315851319/10000000000 : ℝ)*X 2 1+(4315851563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2139433307/10000000000 : ℝ)*X 0 0+(5442710907/10000000000 : ℝ)*X 0 1+(263588133/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684966181/5000000000 : ℝ)*X 1 0+(-2237602461/10000000000 : ℝ)*X 1 1+(2635881417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369932317/10000000000 : ℝ)*X 2 0+(263588143/500000000 : ℝ)*X 2 1+(-447520497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4251711919/10000000000 : ℝ)*X 0 0+(4444180017/10000000000 : ℝ)*X 0 1+(2222089849/5000000000 : ℝ)*X 0 2+(4251711919/10000000000 : ℝ)*X 1 0+(4444180017/10000000000 : ℝ)*X 1 1+(2222089849/5000000000 : ℝ)*X 1 2+(4251711919/10000000000 : ℝ)*X 2 0+(4444180017/10000000000 : ℝ)*X 2 1+(2222089849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-53821293941414449499716519971561/86500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67006777/50000000000000 : ℝ)*(upper0) + (14826311/12500000000000 : ℝ)*(upper1) + (36909559/50000000000000 : ℝ)*(upper2) + (158597467/50000000000000 : ℝ)*(upper3) + (959425135509849/25000000000000 : ℝ)*(major0) + (959425135509849/25000000000000 : ℝ)*(major1) + (959425135509849/25000000000000 : ℝ)*(major2) + (19188577907/100000000000000 : ℝ)*(sp1) + (10126101979/50000000000000 : ℝ)*(sp3) + (5095461044002133/100000000000000 : ℝ)*(sp4) + (203817674216969/4000000000000 : ℝ)*(sp5) + (1019059044457811/20000000000000 : ℝ)*(sp6) + (1300330085447217/50000000000000 : ℝ)*(sp7) + (165821713077/100000000000000 : ℝ)*(sp14) + (325085052887299/12500000000000 : ℝ)*(f.failure) + (5095461044002133/100000000000000 : ℝ)*(f.sum) + (1343306189691/3460000000000000000000000000 : ℝ)*base66 + (1142950016346067813/346000000000000000000000000000000 : ℝ)*base68 + (1519633250213932187/346000000000000000000000000000000 : ℝ)*base69 + (6596939569932187/346000000000000000000000000000000 : ℝ)*base71 + (6434918711649/3460000000000000000000000000 : ℝ)*base73 + (2261350183627932187/346000000000000000000000000000000 : ℝ)*base75 + (3090199883571932187/346000000000000000000000000000000 : ℝ)*base77 + (1352318272067932187/346000000000000000000000000000000 : ℝ)*base79 + (3026007704949/3460000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4127549/1250000000000000000000 : ℝ)*base90 + (4127549/1250000000000000000000 : ℝ)*base92 + (4127549/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7403/12500 : ℝ) ≤ (204924879404341847050242882441939/346000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2220347/12500000000000 : ℝ)*(lower1) + (9986857/25000000000000 : ℝ)*(lower3) + (94036041/50000000000000 : ℝ)*(upper4) + (26151/500000000000 : ℝ)*(lower5) + (1950112247113349/50000000000000 : ℝ)*(major0) + (1950112247113349/50000000000000 : ℝ)*(major1) + (1950112247113349/50000000000000 : ℝ)*(major2) + (2568827953596823/50000000000000 : ℝ)*(sp0) + (5137419418749693/100000000000000 : ℝ)*(sp1) + (2568827581574219/50000000000000 : ℝ)*(sp2) + (660761375250891/25000000000000 : ℝ)*(sp3) + (744045209/100000000000000 : ℝ)*(sp6) + (118244221977/50000000000000 : ℝ)*(sp9) + (662375419/12500000000000 : ℝ)*(sp11) + (660762700001729/25000000000000 : ℝ)*(f.failure) + (2568827953596823/50000000000000 : ℝ)*(f.sum) + (4593865695349/6920000000000000000000000000 : ℝ)*base65 + (3670384490015502687/692000000000000000000000000000000 : ℝ)*base67 + (1936567825600497313/692000000000000000000000000000000 : ℝ)*base70 + (1506929041463502687/692000000000000000000000000000000 : ℝ)*base71 + (17652697488669/6920000000000000000000000000 : ℝ)*base73 + (4045728878032497313/692000000000000000000000000000000 : ℝ)*base76 + (4475881752435502687/692000000000000000000000000000000 : ℝ)*base77 + (1848176411759502687/692000000000000000000000000000000 : ℝ)*base79 + (30969895177029/6920000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9684479/2500000000000000000000 : ℝ)*base90 + (9684479/2500000000000000000000 : ℝ)*base92 + (9684479/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79503/100000 : ℝ) ≤ (137543777150914248444225790379697/173000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10302903/6250000000000 : ℝ)*(upper0) + (125853869/100000000000000 : ℝ)*(lower3) + (78824277/25000000000000 : ℝ)*(upper4) + (2184247437016127/50000000000000 : ℝ)*(major0) + (2184247437016127/50000000000000 : ℝ)*(major1) + (2184247437016127/50000000000000 : ℝ)*(major2) + (58728509741/50000000000000 : ℝ)*(sp1) + (21469573843/6250000000000 : ℝ)*(sp2) + (115310293367/100000000000000 : ℝ)*(sp3) + (3962920851/50000000000000 : ℝ)*(sp4) + (5750098263621277/100000000000000 : ℝ)*(sp8) + (5749988732443497/100000000000000 : ℝ)*(sp9) + (5749762676281491/100000000000000 : ℝ)*(sp10) + (1480133278571137/50000000000000 : ℝ)*(sp11) + (2960381867435641/100000000000000 : ℝ)*(f.failure) + (5750106189462979/100000000000000 : ℝ)*(f.sum) + (15718673292047/6920000000000000000000000000 : ℝ)*base65 + (3164118011168365101/692000000000000000000000000000000 : ℝ)*base67 + (2129601769604365101/692000000000000000000000000000000 : ℝ)*base69 + (8421631115156365101/692000000000000000000000000000000 : ℝ)*base71 + (31962076677807/6920000000000000000000000000 : ℝ)*base73 + (8703034709512365101/692000000000000000000000000000000 : ℝ)*base75 + (4701445085040365101/692000000000000000000000000000000 : ℝ)*base77 + (9258192179199634899/692000000000000000000000000000000 : ℝ)*base80 + (28006145462793/6920000000000000000000000000 : ℝ)*base82 + (44360391/10000000000000000000000 : ℝ)*base90 + (44360391/10000000000000000000000 : ℝ)*base92 + (44360391/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41451/50000 : ℝ) ≤ (-1434164550103253302931784453621/1730000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163090659/100000000000000 : ℝ)*(lower0) + (54392203/100000000000000 : ℝ)*(lower1) + (3412231/12500000000000 : ℝ)*(lower4) + (22014488243611/500000000000 : ℝ)*(major0) + (22014488243611/500000000000 : ℝ)*(major1) + (22014488243611/500000000000 : ℝ)*(major2) + (14814919057/100000000000000 : ℝ)*(sp0) + (34266287071/25000000000000 : ℝ)*(sp5) + (69387155879/50000000000000 : ℝ)*(sp6) + (5086390161/12500000000000 : ℝ)*(sp7) + (1462429560379631/25000000000000 : ℝ)*(sp12) + (365599749455581/6250000000000 : ℝ)*(sp13) + (5849594282125823/100000000000000 : ℝ)*(sp14) + (2983654778211197/100000000000000 : ℝ)*(sp15) + (745923867333121/25000000000000 : ℝ)*(f.failure) + (292486652821879/5000000000000 : ℝ)*(f.sum) + (254708822871/69200000000000000000000000 : ℝ)*base65 + (949100114686207/6920000000000000000000000000000 : ℝ)*base68 + (22169395145846207/6920000000000000000000000000000 : ℝ)*base70 + (76191135072566207/6920000000000000000000000000000 : ℝ)*base72 + (15113470906637/346000000000000000000000000 : ℝ)*base73 + (36800623094926207/6920000000000000000000000000000 : ℝ)*base76 + (47783543914046207/6920000000000000000000000000000 : ℝ)*base78 + (529404141687993793/6920000000000000000000000000000 : ℝ)*base79 + (73922016227/69200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (33687871/2500000000000000000000 : ℝ)*base90 + (33687871/2500000000000000000000 : ℝ)*base92 + (33687871/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1044_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (79503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41451/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1044_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1044_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (79503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41451/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1044_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (79503/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41451/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

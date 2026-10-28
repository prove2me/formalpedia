-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:16.25292+00:00
-- url     : https://prove2.me/submissions/d1976cd3-8570-485e-9082-0ec684bb8e2b

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
theorem support_rectangle_w1171_s6_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076533913/5000000000 : ℝ)*x 0 + (2696401631/5000000000 : ℝ)*x 1 + (42127343/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076533913/5000000000 : ℝ)^2091 ≤ (13085724330083/100000000000000 : ℝ)^1579 := by
    have hnat : (1076533913 : ℕ)^2091*100000000000000^1579 ≤ 13085724330083^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076533913 5000000000 13085724330083 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696401631/5000000000 : ℝ)^2091 ≤ (5517773833143/12500000000000 : ℝ)^1579 := by
    have hnat : (2696401631 : ℕ)^2091*12500000000000^1579 ≤ 5517773833143^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696401631 5000000000 5517773833143 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42127343/80000000 : ℝ)^2091 ≤ (42772084990247/100000000000000 : ℝ)^1579 := by
    have hnat : (42127343 : ℕ)^2091*100000000000000^1579 ≤ 42772084990247^1579*80000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42127343 80000000 42772084990247 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076533913/5000000000 : ℝ), (2696401631/5000000000 : ℝ), (42127343/80000000 : ℝ)] ![(13085724330083/100000000000000 : ℝ), (5517773833143/12500000000000 : ℝ), (42772084990247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076533913/5000000000 : ℝ)|^2091 ≤ (13085724330083/100000000000000 : ℝ)^1579
        have hw : |(-1076533913/5000000000 : ℝ)|=(1076533913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696401631/5000000000 : ℝ)|^2091 ≤ (5517773833143/12500000000000 : ℝ)^1579
        have hw : |(2696401631/5000000000 : ℝ)|=(2696401631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42127343/80000000 : ℝ)|^2091 ≤ (42772084990247/100000000000000 : ℝ)^1579
        have hw : |(42127343/80000000 : ℝ)|=(42127343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167022477/312500000 : ℝ)*x 0 + (-2217423177/10000000000 : ℝ)*x 1 + (5265917879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167022477/312500000 : ℝ)^2091 ≤ (1744869471569/4000000000000 : ℝ)^1579 := by
    have hnat : (167022477 : ℕ)^2091*4000000000000^1579 ≤ 1744869471569^1579*312500000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167022477 312500000 1744869471569 4000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217423177/10000000000 : ℝ)^2091 ≤ (3401544540063/25000000000000 : ℝ)^1579 := by
    have hnat : (2217423177 : ℕ)^2091*25000000000000^1579 ≤ 3401544540063^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217423177 10000000000 3401544540063 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265917879/10000000000 : ℝ)^2091 ≤ (42772085033271/100000000000000 : ℝ)^1579 := by
    have hnat : (5265917879 : ℕ)^2091*100000000000000^1579 ≤ 42772085033271^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265917879 10000000000 42772085033271 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167022477/312500000 : ℝ), (-2217423177/10000000000 : ℝ), (5265917879/10000000000 : ℝ)] ![(1744869471569/4000000000000 : ℝ), (3401544540063/25000000000000 : ℝ), (42772085033271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167022477/312500000 : ℝ)|^2091 ≤ (1744869471569/4000000000000 : ℝ)^1579
        have hw : |(167022477/312500000 : ℝ)|=(167022477/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217423177/10000000000 : ℝ)|^2091 ≤ (3401544540063/25000000000000 : ℝ)^1579
        have hw : |(-2217423177/10000000000 : ℝ)|=(2217423177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265917879/10000000000 : ℝ)|^2091 ≤ (42772085033271/100000000000000 : ℝ)^1579
        have hw : |(5265917879/10000000000 : ℝ)|=(5265917879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344719269/10000000000 : ℝ)*x 0 + (42127343/80000000 : ℝ)*x 1 + (-88696927/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344719269/10000000000 : ℝ)^2091 ≤ (21810868421633/50000000000000 : ℝ)^1579 := by
    have hnat : (5344719269 : ℕ)^2091*50000000000000^1579 ≤ 21810868421633^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344719269 10000000000 21810868421633 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42127343/80000000 : ℝ)^2091 ≤ (42772084990247/100000000000000 : ℝ)^1579 := by
    have hnat : (42127343 : ℕ)^2091*100000000000000^1579 ≤ 42772084990247^1579*80000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42127343 80000000 42772084990247 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88696927/400000000 : ℝ)^2091 ≤ (13606178144001/100000000000000 : ℝ)^1579 := by
    have hnat : (88696927 : ℕ)^2091*100000000000000^1579 ≤ 13606178144001^1579*400000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88696927 400000000 13606178144001 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344719269/10000000000 : ℝ), (42127343/80000000 : ℝ), (-88696927/400000000 : ℝ)] ![(21810868421633/50000000000000 : ℝ), (42772084990247/100000000000000 : ℝ), (13606178144001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344719269/10000000000 : ℝ)|^2091 ≤ (21810868421633/50000000000000 : ℝ)^1579
        have hw : |(5344719269/10000000000 : ℝ)|=(5344719269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42127343/80000000 : ℝ)|^2091 ≤ (42772084990247/100000000000000 : ℝ)^1579
        have hw : |(42127343/80000000 : ℝ)|=(42127343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88696927/400000000 : ℝ)|^2091 ≤ (13606178144001/100000000000000 : ℝ)^1579
        have hw : |(-88696927/400000000 : ℝ)|=(88696927/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (545073631/1250000000 : ℝ)*x 0 + (847095827/2000000000 : ℝ)*x 1 + (179574041/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545073631/1250000000 : ℝ)^2091 ≤ (8329243810787/25000000000000 : ℝ)^1579 := by
    have hnat : (545073631 : ℕ)^2091*25000000000000^1579 ≤ 8329243810787^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545073631 1250000000 8329243810787 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847095827/2000000000 : ℝ)^2091 ≤ (6411409367409/20000000000000 : ℝ)^1579 := by
    have hnat : (847095827 : ℕ)^2091*20000000000000^1579 ≤ 6411409367409^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847095827 2000000000 6411409367409 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179574041/400000000 : ℝ)^2091 ≤ (34625977915079/100000000000000 : ℝ)^1579 := by
    have hnat : (179574041 : ℕ)^2091*100000000000000^1579 ≤ 34625977915079^1579*400000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179574041 400000000 34625977915079 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545073631/1250000000 : ℝ), (847095827/2000000000 : ℝ), (179574041/400000000 : ℝ)] ![(8329243810787/25000000000000 : ℝ), (6411409367409/20000000000000 : ℝ), (34625977915079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545073631/1250000000 : ℝ)|^2091 ≤ (8329243810787/25000000000000 : ℝ)^1579
        have hw : |(545073631/1250000000 : ℝ)|=(545073631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847095827/2000000000 : ℝ)|^2091 ≤ (6411409367409/20000000000000 : ℝ)^1579
        have hw : |(847095827/2000000000 : ℝ)|=(847095827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179574041/400000000 : ℝ)|^2091 ≤ (34625977915079/100000000000000 : ℝ)^1579
        have hw : |(179574041/400000000 : ℝ)|=(179574041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430614543/2000000000 : ℝ)*x 0 + (1316559603/2500000000 : ℝ)*x 1 + (5392481553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430614543/2000000000 : ℝ)^2091 ≤ (13085763678943/100000000000000 : ℝ)^1579 := by
    have hnat : (430614543 : ℕ)^2091*100000000000000^1579 ≤ 13085763678943^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430614543 2000000000 13085763678943 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316559603/2500000000 : ℝ)^2091 ≤ (68440852447/160000000000 : ℝ)^1579 := by
    have hnat : (1316559603 : ℕ)^2091*160000000000^1579 ≤ 68440852447^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316559603 2500000000 68440852447 160000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392481553/10000000000 : ℝ)^2091 ≤ (1103467587961/2500000000000 : ℝ)^1579 := by
    have hnat : (5392481553 : ℕ)^2091*2500000000000^1579 ≤ 1103467587961^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392481553 10000000000 1103467587961 2500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430614543/2000000000 : ℝ), (1316559603/2500000000 : ℝ), (5392481553/10000000000 : ℝ)] ![(13085763678943/100000000000000 : ℝ), (68440852447/160000000000 : ℝ), (1103467587961/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430614543/2000000000 : ℝ)|^2091 ≤ (13085763678943/100000000000000 : ℝ)^1579
        have hw : |(-430614543/2000000000 : ℝ)|=(430614543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316559603/2500000000 : ℝ)|^2091 ≤ (68440852447/160000000000 : ℝ)^1579
        have hw : |(1316559603/2500000000 : ℝ)|=(1316559603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392481553/10000000000 : ℝ)|^2091 ≤ (1103467587961/2500000000000 : ℝ)^1579
        have hw : |(5392481553/10000000000 : ℝ)|=(5392481553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656252009/5000000000 : ℝ)*x 0 + (-209085953/1000000000 : ℝ)*x 1 + (2696240773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656252009/5000000000 : ℝ)^2091 ≤ (43273891424613/100000000000000 : ℝ)^1579 := by
    have hnat : (2656252009 : ℕ)^2091*100000000000000^1579 ≤ 43273891424613^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656252009 5000000000 43273891424613 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209085953/1000000000 : ℝ)^2091 ≤ (2517481022693/20000000000000 : ℝ)^1579 := by
    have hnat : (209085953 : ℕ)^2091*20000000000000^1579 ≤ 2517481022693^1579*1000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209085953 1000000000 2517481022693 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696240773/5000000000 : ℝ)^2091 ≤ (8827740688513/20000000000000 : ℝ)^1579 := by
    have hnat : (2696240773 : ℕ)^2091*20000000000000^1579 ≤ 8827740688513^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696240773 5000000000 8827740688513 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656252009/5000000000 : ℝ), (-209085953/1000000000 : ℝ), (2696240773/5000000000 : ℝ)] ![(43273891424613/100000000000000 : ℝ), (2517481022693/20000000000000 : ℝ), (8827740688513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656252009/5000000000 : ℝ)|^2091 ≤ (43273891424613/100000000000000 : ℝ)^1579
        have hw : |(2656252009/5000000000 : ℝ)|=(2656252009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209085953/1000000000 : ℝ)|^2091 ≤ (2517481022693/20000000000000 : ℝ)^1579
        have hw : |(-209085953/1000000000 : ℝ)|=(209085953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696240773/5000000000 : ℝ)|^2091 ≤ (8827740688513/20000000000000 : ℝ)^1579
        have hw : |(2696240773/5000000000 : ℝ)|=(2696240773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656252009/5000000000 : ℝ)*x 0 + (5392481517/10000000000 : ℝ)*x 1 + (-209085957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656252009/5000000000 : ℝ)^2091 ≤ (43273891424613/100000000000000 : ℝ)^1579 := by
    have hnat : (2656252009 : ℕ)^2091*100000000000000^1579 ≤ 43273891424613^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656252009 5000000000 43273891424613 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392481517/10000000000 : ℝ)^2091 ≤ (1379334472757/3125000000000 : ℝ)^1579 := by
    have hnat : (5392481517 : ℕ)^2091*3125000000000^1579 ≤ 1379334472757^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392481517 10000000000 1379334472757 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209085957/1000000000 : ℝ)^2091 ≤ (12587405432357/100000000000000 : ℝ)^1579 := by
    have hnat : (209085957 : ℕ)^2091*100000000000000^1579 ≤ 12587405432357^1579*1000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209085957 1000000000 12587405432357 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656252009/5000000000 : ℝ), (5392481517/10000000000 : ℝ), (-209085957/1000000000 : ℝ)] ![(43273891424613/100000000000000 : ℝ), (1379334472757/3125000000000 : ℝ), (12587405432357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656252009/5000000000 : ℝ)|^2091 ≤ (43273891424613/100000000000000 : ℝ)^1579
        have hw : |(2656252009/5000000000 : ℝ)|=(2656252009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392481517/10000000000 : ℝ)|^2091 ≤ (1379334472757/3125000000000 : ℝ)^1579
        have hw : |(5392481517/10000000000 : ℝ)|=(5392481517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209085957/1000000000 : ℝ)|^2091 ≤ (12587405432357/100000000000000 : ℝ)^1579
        have hw : |(-209085957/1000000000 : ℝ)|=(209085957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s6_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (136268711/312500000 : ℝ)*x 0 + (1122177419/2500000000 : ℝ)*x 1 + (4236122877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136268711/312500000 : ℝ)^2091 ≤ (832926835693/2500000000000 : ℝ)^1579 := by
    have hnat : (136268711 : ℕ)^2091*2500000000000^1579 ≤ 832926835693^1579*312500000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136268711 312500000 832926835693 2500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122177419/2500000000 : ℝ)^2091 ≤ (34619427410591/100000000000000 : ℝ)^1579 := by
    have hnat : (1122177419 : ℕ)^2091*100000000000000^1579 ≤ 34619427410591^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122177419 2500000000 34619427410591 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236122877/10000000000 : ℝ)^2091 ≤ (1001984348433/3125000000000 : ℝ)^1579 := by
    have hnat : (4236122877 : ℕ)^2091*3125000000000^1579 ≤ 1001984348433^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236122877 10000000000 1001984348433 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136268711/312500000 : ℝ), (1122177419/2500000000 : ℝ), (4236122877/10000000000 : ℝ)] ![(832926835693/2500000000000 : ℝ), (34619427410591/100000000000000 : ℝ), (1001984348433/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136268711/312500000 : ℝ)|^2091 ≤ (832926835693/2500000000000 : ℝ)^1579
        have hw : |(136268711/312500000 : ℝ)|=(136268711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122177419/2500000000 : ℝ)|^2091 ≤ (34619427410591/100000000000000 : ℝ)^1579
        have hw : |(1122177419/2500000000 : ℝ)|=(1122177419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236122877/10000000000 : ℝ)|^2091 ≤ (1001984348433/3125000000000 : ℝ)^1579
        have hw : |(4236122877/10000000000 : ℝ)|=(4236122877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1423/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (1387307410941127/10000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^8363 ≤ (1387307410941127/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11357 : ℕ)^8363*10000000000000000000^2048 ≤ 1387307410941127^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 1387307410941127 10000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (1387307410941127/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (16785541095392797/50000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^8363 ≤ (16785541095392797/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14101 : ℕ)^8363*50000000000000000000^2048 ≤ 16785541095392797^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 16785541095392797 50000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (16785541095392797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001387307410941127/5000000000000000000 : ℝ) ≤ (10000679399256037/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (5001387307410941127/5000000000000000000 : ℝ)^2048 ≤ (10000679399256037/10000000000000000 : ℝ)^8363 := by
      have hnat : (5001387307410941127 : ℕ)^2048*10000000000000000^8363 ≤ 10000679399256037^8363*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001387307410941127 5000000000000000000 10000679399256037 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679399256037/10000000000000000 : ℝ)) (X := (5001387307410941127/5000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (97702582183886911/97656250000000000 : ℝ) ≤ (1250145205416457/1250000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (97702582183886911/97656250000000000 : ℝ)^2048 ≤ (1250145205416457/1250000000000000 : ℝ)^8363 := by
      have hnat : (97702582183886911 : ℕ)^2048*1250000000000000^8363 ≤ 1250145205416457^8363*97656250000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97702582183886911 97656250000000000 1250145205416457 1250000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250145205416457/1250000000000000 : ℝ)) (X := (97702582183886911/97656250000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016785541095392797/25000000000000000000 : ℝ) ≤ (400065755496291/400000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (25016785541095392797/25000000000000000000 : ℝ)^2048 ≤ (400065755496291/400000000000000 : ℝ)^8363 := by
      have hnat : (25016785541095392797 : ℕ)^2048*400000000000000^8363 ≤ 400065755496291^8363*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016785541095392797 25000000000000000000 400065755496291 400000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400065755496291/400000000000000 : ℝ)) (X := (25016785541095392797/25000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1387307410941127/10000000000000000000 : ℝ) ≤ ((13715455289812477781/13720000000000000000 : ℝ)+2*(482244075619/274400000000000 : ℝ)*(11357/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (13715455289812477781/13720000000000000000 : ℝ)+2*(482244075619/274400000000000 : ℝ)*(11357/100000 : ℝ)=(10000679399256037/10000000000000000 : ℝ) by norm_num, show 1+2*(1387307410941127/10000000000000000000 : ℝ)=(5001387307410941127/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16785541095392797/50000000000000000000 : ℝ)+(1387307410941127/10000000000000000000 : ℝ) ≤ ((13715455289812477781/13720000000000000000 : ℝ)+(482244075619/274400000000000 : ℝ)*((14101/100000 : ℝ)+(11357/100000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (13715455289812477781/13720000000000000000 : ℝ)+(482244075619/274400000000000 : ℝ)*((14101/100000 : ℝ)+(11357/100000 : ℝ))=(1250145205416457/1250000000000000 : ℝ) by norm_num, show 1+(16785541095392797/50000000000000000000 : ℝ)+(1387307410941127/10000000000000000000 : ℝ)=(97702582183886911/97656250000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16785541095392797/50000000000000000000 : ℝ) ≤ ((13715455289812477781/13720000000000000000 : ℝ)+2*(482244075619/274400000000000 : ℝ)*(14101/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (13715455289812477781/13720000000000000000 : ℝ)+2*(482244075619/274400000000000 : ℝ)*(14101/100000 : ℝ)=(400065755496291/400000000000000 : ℝ) by norm_num, show 1+2*(16785541095392797/50000000000000000000 : ℝ)=(25016785541095392797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13715455289812477781/13720000000000000000 : ℝ)*(X 1 0+X 2 0)+(482244075619/274400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (13715455289812477781/13720000000000000000 : ℝ)) (alpha := (482244075619/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13715455289812477781/13720000000000000000 : ℝ)*(X 0 1+X 2 1)+(482244075619/274400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (13715455289812477781/13720000000000000000 : ℝ)) (alpha := (482244075619/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13715455289812477781/13720000000000000000 : ℝ)*(X 0 2+X 1 2)+(482244075619/274400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (13715455289812477781/13720000000000000000 : ℝ)) (alpha := (482244075619/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076533913/5000000000 : ℝ)*X 0 0+(2696401631/5000000000 : ℝ)*X 0 1+(42127343/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167022477/312500000 : ℝ)*X 1 0+(-2217423177/10000000000 : ℝ)*X 1 1+(5265917879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344719269/10000000000 : ℝ)*X 2 0+(42127343/80000000 : ℝ)*X 2 1+(-88696927/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545073631/1250000000 : ℝ)*X 0 0+(847095827/2000000000 : ℝ)*X 0 1+(179574041/400000000 : ℝ)*X 0 2+(545073631/1250000000 : ℝ)*X 1 0+(847095827/2000000000 : ℝ)*X 1 1+(179574041/400000000 : ℝ)*X 1 2+(545073631/1250000000 : ℝ)*X 2 0+(847095827/2000000000 : ℝ)*X 2 1+(179574041/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430614543/2000000000 : ℝ)*X 0 0+(1316559603/2500000000 : ℝ)*X 0 1+(5392481553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656252009/5000000000 : ℝ)*X 1 0+(-209085953/1000000000 : ℝ)*X 1 1+(2696240773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656252009/5000000000 : ℝ)*X 2 0+(5392481517/10000000000 : ℝ)*X 2 1+(-209085957/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136268711/312500000 : ℝ)*X 0 0+(1122177419/2500000000 : ℝ)*X 0 1+(4236122877/10000000000 : ℝ)*X 0 2+(136268711/312500000 : ℝ)*X 1 0+(1122177419/2500000000 : ℝ)*X 1 1+(4236122877/10000000000 : ℝ)*X 1 2+(136268711/312500000 : ℝ)*X 2 0+(1122177419/2500000000 : ℝ)*X 2 1+(4236122877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1007830025041197053604170601/98000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50938901/2500000000000 : ℝ)*(base19) + (1904442333/100000000000000 : ℝ)*(base23) + (75086159/100000000000000 : ℝ)*(lower2) + (10508297/4000000000000 : ℝ)*(upper3) + (81537779/50000000000000 : ℝ)*(upper5) + (118202938134943/2000000000000 : ℝ)*(major0) + (118202938134943/2000000000000 : ℝ)*(major1) + (5910146906747151/100000000000000 : ℝ)*(major2) + (3940593124308581/50000000000000 : ℝ)*(sp0) + (788123991747279/10000000000000 : ℝ)*(sp1) + (7881240050586497/100000000000000 : ℝ)*(sp2) + (1969510781289481/50000000000000 : ℝ)*(sp3) + (13926602917/25000000000000 : ℝ)*(sp4) + (29953087163/100000000000000 : ℝ)*(sp7) + (984762878916531/25000000000000 : ℝ)*(f.failure) + (788124195502883/10000000000000 : ℝ)*(f.sum) + (154292217633481/27440000000000000000000000000 : ℝ)*base66 + (239216690076750483/27440000000000000000000000000000 : ℝ)*base67 + (27628441462305051931/1372000000000000000000000000000000 : ℝ)*base69 + (37450803182609517/27440000000000000000000000000000 : ℝ)*base72 + (9470288629001/27440000000000000000000000000 : ℝ)*base74 + (43494961179073051931/1372000000000000000000000000000000 : ℝ)*base75 + (157524363867748517/27440000000000000000000000000000 : ℝ)*base78 + (407310433701531483/27440000000000000000000000000000 : ℝ)*base79 + (1272249525913/1372000000000000000000000000 : ℝ)*base81 + (4259089/312500000000000000000 : ℝ)*base90 + (4259089/312500000000000000000 : ℝ)*base92 + (7384089/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3326654935145983192698988641/686000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (165100361/20000000000000 : ℝ)*(base19) + (813839711/100000000000000 : ℝ)*(base23) + (19609393/25000000000000 : ℝ)*(upper3) + (5247711/100000000000000 : ℝ)*(lower4) + (10969479/10000000000000 : ℝ)*(upper5) + (5940129015074687/100000000000000 : ℝ)*(major0) + (5940129015074687/100000000000000 : ℝ)*(major1) + (5940129015074687/100000000000000 : ℝ)*(major2) + (11708298953/50000000000000 : ℝ)*(sp1) + (19864486781/100000000000000 : ℝ)*(sp2) + (7921223589107633/100000000000000 : ℝ)*(sp4) + (3960599673503961/50000000000000 : ℝ)*(sp5) + (3960601455390571/50000000000000 : ℝ)*(sp6) + (247439642462293/6250000000000 : ℝ)*(sp7) + (247439642462293/6250000000000 : ℝ)*(f.failure) + (7921223589107633/100000000000000 : ℝ)*(f.sum) + (61849580239067/13720000000000000000000000000 : ℝ)*base66 + (6699896406792320453/1372000000000000000000000000000000 : ℝ)*base68 + (9697405705044320453/1372000000000000000000000000000000 : ℝ)*base70 + (4068831064023679547/1372000000000000000000000000000000 : ℝ)*base71 + (3120973229267/13720000000000000000000000000 : ℝ)*base74 + (31067917444208320453/1372000000000000000000000000000000 : ℝ)*base76 + (1109399809243679547/1372000000000000000000000000000000 : ℝ)*base77 + (26359646605188320453/1372000000000000000000000000000000 : ℝ)*base80 + (20431276875333/13720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (787317/78125000000000000000 : ℝ)*base90 + (787317/78125000000000000000 : ℝ)*base92 + (787317/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1171_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1171_s7_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076547071/5000000000 : ℝ)*x 0 + (5392523137/10000000000 : ℝ)*x 1 + (210647219/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076547071/5000000000 : ℝ)^2091 ≤ (1308593613337/10000000000000 : ℝ)^1579 := by
    have hnat : (1076547071 : ℕ)^2091*10000000000000^1579 ≤ 1308593613337^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076547071 5000000000 1308593613337 10000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392523137/10000000000 : ℝ)^2091 ≤ (8827830852417/20000000000000 : ℝ)^1579 := by
    have hnat : (5392523137 : ℕ)^2091*20000000000000^1579 ≤ 8827830852417^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392523137 10000000000 8827830852417 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210647219/400000000 : ℝ)^2091 ≤ (42774909587127/100000000000000 : ℝ)^1579 := by
    have hnat : (210647219 : ℕ)^2091*100000000000000^1579 ≤ 42774909587127^1579*400000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210647219 400000000 42774909587127 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076547071/5000000000 : ℝ), (5392523137/10000000000 : ℝ), (210647219/400000000 : ℝ)] ![(1308593613337/10000000000000 : ℝ), (8827830852417/20000000000000 : ℝ), (42774909587127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076547071/5000000000 : ℝ)|^2091 ≤ (1308593613337/10000000000000 : ℝ)^1579
        have hw : |(-1076547071/5000000000 : ℝ)|=(1076547071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392523137/10000000000 : ℝ)|^2091 ≤ (8827830852417/20000000000000 : ℝ)^1579
        have hw : |(5392523137/10000000000 : ℝ)|=(5392523137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210647219/400000000 : ℝ)|^2091 ≤ (42774909587127/100000000000000 : ℝ)^1579
        have hw : |(210647219/400000000 : ℝ)|=(210647219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672324001/5000000000 : ℝ)*x 0 + (-2217170353/10000000000 : ℝ)*x 1 + (5266180473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672324001/5000000000 : ℝ)^2091 ≤ (21810483291499/50000000000000 : ℝ)^1579 := by
    have hnat : (2672324001 : ℕ)^2091*50000000000000^1579 ≤ 21810483291499^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672324001 5000000000 21810483291499 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217170353/10000000000 : ℝ)^2091 ≤ (13604123832451/100000000000000 : ℝ)^1579 := by
    have hnat : (2217170353 : ℕ)^2091*100000000000000^1579 ≤ 13604123832451^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217170353 10000000000 13604123832451 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266180473/10000000000 : ℝ)^2091 ≤ (21387454782807/50000000000000 : ℝ)^1579 := by
    have hnat : (5266180473 : ℕ)^2091*50000000000000^1579 ≤ 21387454782807^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266180473 10000000000 21387454782807 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672324001/5000000000 : ℝ), (-2217170353/10000000000 : ℝ), (5266180473/10000000000 : ℝ)] ![(21810483291499/50000000000000 : ℝ), (13604123832451/100000000000000 : ℝ), (21387454782807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672324001/5000000000 : ℝ)|^2091 ≤ (21810483291499/50000000000000 : ℝ)^1579
        have hw : |(2672324001/5000000000 : ℝ)|=(2672324001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217170353/10000000000 : ℝ)|^2091 ≤ (13604123832451/100000000000000 : ℝ)^1579
        have hw : |(-2217170353/10000000000 : ℝ)|=(2217170353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266180473/10000000000 : ℝ)|^2091 ≤ (21387454782807/50000000000000 : ℝ)^1579
        have hw : |(5266180473/10000000000 : ℝ)|=(5266180473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344648001/10000000000 : ℝ)*x 0 + (5266180473/10000000000 : ℝ)*x 1 + (-443434071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344648001/10000000000 : ℝ)^2091 ≤ (4362096657219/10000000000000 : ℝ)^1579 := by
    have hnat : (5344648001 : ℕ)^2091*10000000000000^1579 ≤ 4362096657219^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344648001 10000000000 4362096657219 10000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266180473/10000000000 : ℝ)^2091 ≤ (21387454782807/50000000000000 : ℝ)^1579 := by
    have hnat : (5266180473 : ℕ)^2091*50000000000000^1579 ≤ 21387454782807^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266180473 10000000000 21387454782807 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443434071/2000000000 : ℝ)^2091 ≤ (6802061924351/50000000000000 : ℝ)^1579 := by
    have hnat : (443434071 : ℕ)^2091*50000000000000^1579 ≤ 6802061924351^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443434071 2000000000 6802061924351 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344648001/10000000000 : ℝ), (5266180473/10000000000 : ℝ), (-443434071/2000000000 : ℝ)] ![(4362096657219/10000000000000 : ℝ), (21387454782807/50000000000000 : ℝ), (6802061924351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344648001/10000000000 : ℝ)|^2091 ≤ (4362096657219/10000000000000 : ℝ)^1579
        have hw : |(5344648001/10000000000 : ℝ)|=(5344648001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266180473/10000000000 : ℝ)|^2091 ≤ (21387454782807/50000000000000 : ℝ)^1579
        have hw : |(5266180473/10000000000 : ℝ)|=(5266180473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443434071/2000000000 : ℝ)|^2091 ≤ (6802061924351/50000000000000 : ℝ)^1579
        have hw : |(-443434071/2000000000 : ℝ)|=(443434071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180301413/5000000000 : ℝ)*x 0 + (4236020291/10000000000 : ℝ)*x 1 + (1122201579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180301413/5000000000 : ℝ)^2091 ≤ (4164639331033/12500000000000 : ℝ)^1579 := by
    have hnat : (2180301413 : ℕ)^2091*12500000000000^1579 ≤ 4164639331033^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180301413 5000000000 4164639331033 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236020291/10000000000 : ℝ)^2091 ≤ (32062470895257/100000000000000 : ℝ)^1579 := by
    have hnat : (4236020291 : ℕ)^2091*100000000000000^1579 ≤ 32062470895257^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236020291 10000000000 32062470895257 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122201579/2500000000 : ℝ)^2091 ≤ (34620414436843/100000000000000 : ℝ)^1579 := by
    have hnat : (1122201579 : ℕ)^2091*100000000000000^1579 ≤ 34620414436843^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122201579 2500000000 34620414436843 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180301413/5000000000 : ℝ), (4236020291/10000000000 : ℝ), (1122201579/2500000000 : ℝ)] ![(4164639331033/12500000000000 : ℝ), (32062470895257/100000000000000 : ℝ), (34620414436843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180301413/5000000000 : ℝ)|^2091 ≤ (4164639331033/12500000000000 : ℝ)^1579
        have hw : |(2180301413/5000000000 : ℝ)|=(2180301413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236020291/10000000000 : ℝ)|^2091 ≤ (32062470895257/100000000000000 : ℝ)^1579
        have hw : |(4236020291/10000000000 : ℝ)|=(4236020291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122201579/2500000000 : ℝ)|^2091 ≤ (34620414436843/100000000000000 : ℝ)^1579
        have hw : |(1122201579/2500000000 : ℝ)|=(1122201579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430619797/2000000000 : ℝ)*x 0 + (2633249141/5000000000 : ℝ)*x 1 + (5392204161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430619797/2000000000 : ℝ)^2091 ≤ (3271493778039/25000000000000 : ℝ)^1579 := by
    have hnat : (430619797 : ℕ)^2091*25000000000000^1579 ≤ 3271493778039^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430619797 2000000000 3271493778039 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633249141/5000000000 : ℝ)^2091 ≤ (5347291008321/12500000000000 : ℝ)^1579 := by
    have hnat : (2633249141 : ℕ)^2091*12500000000000^1579 ≤ 5347291008321^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633249141 5000000000 5347291008321 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392204161/10000000000 : ℝ)^2091 ≤ (1379240524923/3125000000000 : ℝ)^1579 := by
    have hnat : (5392204161 : ℕ)^2091*3125000000000^1579 ≤ 1379240524923^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392204161 10000000000 1379240524923 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430619797/2000000000 : ℝ), (2633249141/5000000000 : ℝ), (5392204161/10000000000 : ℝ)] ![(3271493778039/25000000000000 : ℝ), (5347291008321/12500000000000 : ℝ), (1379240524923/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430619797/2000000000 : ℝ)|^2091 ≤ (3271493778039/25000000000000 : ℝ)^1579
        have hw : |(-430619797/2000000000 : ℝ)|=(430619797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633249141/5000000000 : ℝ)|^2091 ≤ (5347291008321/12500000000000 : ℝ)^1579
        have hw : |(2633249141/5000000000 : ℝ)|=(2633249141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392204161/10000000000 : ℝ)|^2091 ≤ (1379240524923/3125000000000 : ℝ)^1579
        have hw : |(5392204161/10000000000 : ℝ)|=(5392204161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312570507/10000000000 : ℝ)*x 0 + (-2091146693/10000000000 : ℝ)*x 1 + (1348051041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312570507/10000000000 : ℝ)^2091 ≤ (43274608639449/100000000000000 : ℝ)^1579 := by
    have hnat : (5312570507 : ℕ)^2091*100000000000000^1579 ≤ 43274608639449^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312570507 10000000000 43274608639449 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091146693/10000000000 : ℝ)^2091 ≤ (6294847256019/50000000000000 : ℝ)^1579 := by
    have hnat : (2091146693 : ℕ)^2091*50000000000000^1579 ≤ 6294847256019^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091146693 10000000000 6294847256019 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348051041/2500000000 : ℝ)^2091 ≤ (44135696830053/100000000000000 : ℝ)^1579 := by
    have hnat : (1348051041 : ℕ)^2091*100000000000000^1579 ≤ 44135696830053^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348051041 2500000000 44135696830053 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312570507/10000000000 : ℝ), (-2091146693/10000000000 : ℝ), (1348051041/2500000000 : ℝ)] ![(43274608639449/100000000000000 : ℝ), (6294847256019/50000000000000 : ℝ), (44135696830053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312570507/10000000000 : ℝ)|^2091 ≤ (43274608639449/100000000000000 : ℝ)^1579
        have hw : |(5312570507/10000000000 : ℝ)|=(5312570507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091146693/10000000000 : ℝ)|^2091 ≤ (6294847256019/50000000000000 : ℝ)^1579
        have hw : |(-2091146693/10000000000 : ℝ)|=(2091146693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348051041/2500000000 : ℝ)|^2091 ≤ (44135696830053/100000000000000 : ℝ)^1579
        have hw : |(1348051041/2500000000 : ℝ)|=(1348051041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312570527/10000000000 : ℝ)*x 0 + (1348051037/2500000000 : ℝ)*x 1 + (-2091146687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312570527/10000000000 : ℝ)^2091 ≤ (43274608855189/100000000000000 : ℝ)^1579 := by
    have hnat : (5312570527 : ℕ)^2091*100000000000000^1579 ≤ 43274608855189^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312570527 10000000000 43274608855189 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348051037/2500000000 : ℝ)^2091 ≤ (44135696656627/100000000000000 : ℝ)^1579 := by
    have hnat : (1348051037 : ℕ)^2091*100000000000000^1579 ≤ 44135696656627^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348051037 2500000000 44135696656627 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091146687/10000000000 : ℝ)^2091 ≤ (6294847232101/50000000000000 : ℝ)^1579 := by
    have hnat : (2091146687 : ℕ)^2091*50000000000000^1579 ≤ 6294847232101^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091146687 10000000000 6294847232101 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312570527/10000000000 : ℝ), (1348051037/2500000000 : ℝ), (-2091146687/10000000000 : ℝ)] ![(43274608855189/100000000000000 : ℝ), (44135696656627/100000000000000 : ℝ), (6294847232101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312570527/10000000000 : ℝ)|^2091 ≤ (43274608855189/100000000000000 : ℝ)^1579
        have hw : |(5312570527/10000000000 : ℝ)|=(5312570527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348051037/2500000000 : ℝ)|^2091 ≤ (44135696656627/100000000000000 : ℝ)^1579
        have hw : |(1348051037/2500000000 : ℝ)|=(1348051037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091146687/10000000000 : ℝ)|^2091 ≤ (6294847232101/50000000000000 : ℝ)^1579
        have hw : |(-2091146687/10000000000 : ℝ)|=(2091146687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s7_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4360612487/10000000000 : ℝ)*x 0 + (448817037/1000000000 : ℝ)*x 1 + (105916463/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360612487/10000000000 : ℝ)^2091 ≤ (6663442479573/20000000000000 : ℝ)^1579 := by
    have hnat : (4360612487 : ℕ)^2091*20000000000000^1579 ≤ 6663442479573^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360612487 10000000000 6663442479573 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448817037/1000000000 : ℝ)^2091 ≤ (34613919370931/100000000000000 : ℝ)^1579 := by
    have hnat : (448817037 : ℕ)^2091*100000000000000^1579 ≤ 34613919370931^1579*1000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448817037 1000000000 34613919370931 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105916463/250000000 : ℝ)^2091 ≤ (3206886821417/10000000000000 : ℝ)^1579 := by
    have hnat : (105916463 : ℕ)^2091*10000000000000^1579 ≤ 3206886821417^1579*250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105916463 250000000 3206886821417 10000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360612487/10000000000 : ℝ), (448817037/1000000000 : ℝ), (105916463/250000000 : ℝ)] ![(6663442479573/20000000000000 : ℝ), (34613919370931/100000000000000 : ℝ), (3206886821417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360612487/10000000000 : ℝ)|^2091 ≤ (6663442479573/20000000000000 : ℝ)^1579
        have hw : |(4360612487/10000000000 : ℝ)|=(4360612487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448817037/1000000000 : ℝ)|^2091 ≤ (34613919370931/100000000000000 : ℝ)^1579
        have hw : |(448817037/1000000000 : ℝ)|=(448817037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105916463/250000000 : ℝ)|^2091 ≤ (3206886821417/10000000000000 : ℝ)^1579
        have hw : |(105916463/250000000 : ℝ)|=(105916463/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1423/12500 : ℝ) ^ (8363/2048 : ℝ) ≤ (14008249157755401/100000000000000000000 : ℝ) := by
    have hpowers : (1423/12500 : ℝ)^8363 ≤ (14008249157755401/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1423 : ℕ)^8363*100000000000000000000^2048 ≤ 14008249157755401^2048*12500^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1423 12500 14008249157755401 100000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1423/12500 : ℝ)) (X := (14008249157755401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (8363/2048 : ℝ) ≤ (1664502103685209/5000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^8363 ≤ (1664502103685209/5000000000000000000 : ℝ)^2048 := by
      have hnat : (1759 : ℕ)^8363*5000000000000000000^2048 ≤ 1664502103685209^2048*12500^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 1664502103685209 5000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (1664502103685209/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014008249157755401/50000000000000000000 : ℝ) ≤ (10000686018417319/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (50014008249157755401/50000000000000000000 : ℝ)^2048 ≤ (10000686018417319/10000000000000000 : ℝ)^8363 := by
      have hnat : (50014008249157755401 : ℕ)^2048*10000000000000000^8363 ≤ 10000686018417319^8363*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014008249157755401 50000000000000000000 10000686018417319 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686018417319/10000000000000000 : ℝ)) (X := (50014008249157755401/50000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047298291231459581/100000000000000000000 : ℝ) ≤ (10001158072545489/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (100047298291231459581/100000000000000000000 : ℝ)^2048 ≤ (10001158072545489/10000000000000000 : ℝ)^8363 := by
      have hnat : (100047298291231459581 : ℕ)^2048*10000000000000000^8363 ≤ 10001158072545489^8363*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047298291231459581 100000000000000000000 10001158072545489 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001158072545489/10000000000000000 : ℝ)) (X := (100047298291231459581/100000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501664502103685209/2500000000000000000 : ℝ) ≤ (10001630126673659/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (2501664502103685209/2500000000000000000 : ℝ)^2048 ≤ (10001630126673659/10000000000000000 : ℝ)^8363 := by
      have hnat : (2501664502103685209 : ℕ)^2048*10000000000000000^8363 ≤ 10001630126673659^8363*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501664502103685209 2500000000000000000 10001630126673659 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001630126673659/10000000000000000 : ℝ)) (X := (2501664502103685209/2500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14008249157755401/100000000000000000000 : ℝ) ≤ ((839721759034861841/840000000000000000 : ℝ)+2*(47205412817/26880000000000 : ℝ)*(1423/12500 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (839721759034861841/840000000000000000 : ℝ)+2*(47205412817/26880000000000 : ℝ)*(1423/12500 : ℝ)=(10000686018417319/10000000000000000 : ℝ) by norm_num, show 1+2*(14008249157755401/100000000000000000000 : ℝ)=(50014008249157755401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1664502103685209/5000000000000000000 : ℝ)+(14008249157755401/100000000000000000000 : ℝ) ≤ ((839721759034861841/840000000000000000 : ℝ)+(47205412817/26880000000000 : ℝ)*((1759/12500 : ℝ)+(1423/12500 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (839721759034861841/840000000000000000 : ℝ)+(47205412817/26880000000000 : ℝ)*((1759/12500 : ℝ)+(1423/12500 : ℝ))=(10001158072545489/10000000000000000 : ℝ) by norm_num, show 1+(1664502103685209/5000000000000000000 : ℝ)+(14008249157755401/100000000000000000000 : ℝ)=(100047298291231459581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1664502103685209/5000000000000000000 : ℝ) ≤ ((839721759034861841/840000000000000000 : ℝ)+2*(47205412817/26880000000000 : ℝ)*(1759/12500 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (839721759034861841/840000000000000000 : ℝ)+2*(47205412817/26880000000000 : ℝ)*(1759/12500 : ℝ)=(10001630126673659/10000000000000000 : ℝ) by norm_num, show 1+2*(1664502103685209/5000000000000000000 : ℝ)=(2501664502103685209/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (839721759034861841/840000000000000000 : ℝ)*(X 1 0+X 2 0)+(47205412817/26880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (839721759034861841/840000000000000000 : ℝ)) (alpha := (47205412817/26880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (839721759034861841/840000000000000000 : ℝ)*(X 0 1+X 2 1)+(47205412817/26880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (839721759034861841/840000000000000000 : ℝ)) (alpha := (47205412817/26880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (839721759034861841/840000000000000000 : ℝ)*(X 0 2+X 1 2)+(47205412817/26880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (839721759034861841/840000000000000000 : ℝ)) (alpha := (47205412817/26880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076547071/5000000000 : ℝ)*X 0 0+(5392523137/10000000000 : ℝ)*X 0 1+(210647219/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672324001/5000000000 : ℝ)*X 1 0+(-2217170353/10000000000 : ℝ)*X 1 1+(5266180473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344648001/10000000000 : ℝ)*X 2 0+(5266180473/10000000000 : ℝ)*X 2 1+(-443434071/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180301413/5000000000 : ℝ)*X 0 0+(4236020291/10000000000 : ℝ)*X 0 1+(1122201579/2500000000 : ℝ)*X 0 2+(2180301413/5000000000 : ℝ)*X 1 0+(4236020291/10000000000 : ℝ)*X 1 1+(1122201579/2500000000 : ℝ)*X 1 2+(2180301413/5000000000 : ℝ)*X 2 0+(4236020291/10000000000 : ℝ)*X 2 1+(1122201579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430619797/2000000000 : ℝ)*X 0 0+(2633249141/5000000000 : ℝ)*X 0 1+(5392204161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312570507/10000000000 : ℝ)*X 1 0+(-2091146693/10000000000 : ℝ)*X 1 1+(1348051041/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312570527/10000000000 : ℝ)*X 2 0+(1348051037/2500000000 : ℝ)*X 2 1+(-2091146687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360612487/10000000000 : ℝ)*X 0 0+(448817037/1000000000 : ℝ)*X 0 1+(105916463/250000000 : ℝ)*X 0 2+(4360612487/10000000000 : ℝ)*X 1 0+(448817037/1000000000 : ℝ)*X 1 1+(105916463/250000000 : ℝ)*X 1 2+(4360612487/10000000000 : ℝ)*X 2 0+(448817037/1000000000 : ℝ)*X 2 1+(105916463/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13152256712768677967543053/2000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1291526259/100000000000000 : ℝ)*(base19) + (1198974591/100000000000000 : ℝ)*(base23) + (48674103/100000000000000 : ℝ)*(lower2) + (167804357/100000000000000 : ℝ)*(upper3) + (48771299/50000000000000 : ℝ)*(upper5) + (5935503147085169/100000000000000 : ℝ)*(major0) + (5935503147085169/100000000000000 : ℝ)*(major1) + (5935503147085169/100000000000000 : ℝ)*(major2) + (395750990796327/5000000000000 : ℝ)*(sp0) + (1583010719400439/20000000000000 : ℝ)*(sp1) + (3957526844776931/50000000000000 : ℝ)*(sp2) + (3955932036846181/100000000000000 : ℝ)*(sp3) + (17536300957/50000000000000 : ℝ)*(sp4) + (19149591417/100000000000000 : ℝ)*(sp7) + (1977975593218799/50000000000000 : ℝ)*(f.failure) + (3957527444264227/50000000000000 : ℝ)*(f.sum) + (475308386359/192000000000000000000000000 : ℝ)*base65 + (15756445773579399/4000000000000000000000000000000 : ℝ)*base67 + (53698082230420601/4000000000000000000000000000000 : ℝ)*base70 + (4617024629579399/4000000000000000000000000000000 : ℝ)*base71 + (797426304247/192000000000000000000000000 : ℝ)*base73 + (50712047445579399/4000000000000000000000000000000 : ℝ)*base75 + (10921962741579399/4000000000000000000000000000000 : ℝ)*base77 + (19255030218420601/4000000000000000000000000000000 : ℝ)*base80 + (359449132553/192000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2162181/625000000000000000000 : ℝ)*base90 + (2162181/625000000000000000000 : ℝ)*base92 + (2162181/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47550936447961011477121351/14000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620093871/100000000000000 : ℝ)*(base19) + (169374573/25000000000000 : ℝ)*(base23) + (33137049/50000000000000 : ℝ)*(upper3) + (2877093/20000000000000 : ℝ)*(lower4) + (98025651/100000000000000 : ℝ)*(upper5) + (5965517105777111/100000000000000 : ℝ)*(major0) + (5965517105777111/100000000000000 : ℝ)*(major1) + (5965517105777111/100000000000000 : ℝ)*(major2) + (17602961851/100000000000000 : ℝ)*(sp1) + (176655973/1000000000000 : ℝ)*(sp2) + (7955078920232539/100000000000000 : ℝ)*(sp4) + (497191293573551/6250000000000 : ℝ)*(sp5) + (3977530288568473/50000000000000 : ℝ)*(sp6) + (99398879452629/2500000000000 : ℝ)*(sp7) + (99398879452629/2500000000000 : ℝ)*(f.failure) + (7955078920232539/100000000000000 : ℝ)*(f.sum) + (6830555184967/1344000000000000000000000000 : ℝ)*base65 + (492176734688886633/28000000000000000000000000000000 : ℝ)*base68 + (265030956556886633/28000000000000000000000000000000 : ℝ)*base70 + (42378102496886633/28000000000000000000000000000000 : ℝ)*base72 + (1986811032391/1344000000000000000000000000 : ℝ)*base73 + (208275371539113367/28000000000000000000000000000000 : ℝ)*base75 + (7930885519113367/28000000000000000000000000000000 : ℝ)*base77 + (146174488168886633/28000000000000000000000000000000 : ℝ)*base80 + (267520806113/53760000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (107549/31250000000000000000 : ℝ)*base89 + (107549/31250000000000000000 : ℝ)*base91 + (107549/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1171_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1171_s8_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-538274597/2500000000 : ℝ)*x 0 + (8627943/16000000 : ℝ)*x 1 + (5266236513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538274597/2500000000 : ℝ)^2091 ≤ (3271492576803/25000000000000 : ℝ)^1579 := by
    have hnat : (538274597 : ℕ)^2091*25000000000000^1579 ≤ 3271492576803^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538274597 2500000000 3271492576803 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8627943/16000000 : ℝ)^2091 ≤ (44138517320367/100000000000000 : ℝ)^1579 := by
    have hnat : (8627943 : ℕ)^2091*100000000000000^1579 ≤ 44138517320367^1579*16000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8627943 16000000 44138517320367 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266236513/10000000000 : ℝ)^2091 ≤ (42775512352979/100000000000000 : ℝ)^1579 := by
    have hnat : (5266236513 : ℕ)^2091*100000000000000^1579 ≤ 42775512352979^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266236513 10000000000 42775512352979 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538274597/2500000000 : ℝ), (8627943/16000000 : ℝ), (5266236513/10000000000 : ℝ)] ![(3271492576803/25000000000000 : ℝ), (44138517320367/100000000000000 : ℝ), (42775512352979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538274597/2500000000 : ℝ)|^2091 ≤ (3271492576803/25000000000000 : ℝ)^1579
        have hw : |(-538274597/2500000000 : ℝ)|=(538274597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8627943/16000000 : ℝ)|^2091 ≤ (44138517320367/100000000000000 : ℝ)^1579
        have hw : |(8627943/16000000 : ℝ)|=(8627943/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266236513/10000000000 : ℝ)|^2091 ≤ (42775512352979/100000000000000 : ℝ)^1579
        have hw : |(5266236513/10000000000 : ℝ)|=(5266236513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344633447/10000000000 : ℝ)*x 0 + (-2217115489/10000000000 : ℝ)*x 1 + (2633118271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344633447/10000000000 : ℝ)^2091 ≤ (21810404635817/50000000000000 : ℝ)^1579 := by
    have hnat : (5344633447 : ℕ)^2091*50000000000000^1579 ≤ 21810404635817^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344633447 10000000000 21810404635817 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217115489/10000000000 : ℝ)^2091 ≤ (13603678043663/100000000000000 : ℝ)^1579 := by
    have hnat : (2217115489 : ℕ)^2091*100000000000000^1579 ≤ 13603678043663^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217115489 10000000000 13603678043663 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633118271/5000000000 : ℝ)^2091 ≤ (8555102532983/20000000000000 : ℝ)^1579 := by
    have hnat : (2633118271 : ℕ)^2091*20000000000000^1579 ≤ 8555102532983^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633118271 5000000000 8555102532983 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344633447/10000000000 : ℝ), (-2217115489/10000000000 : ℝ), (2633118271/5000000000 : ℝ)] ![(21810404635817/50000000000000 : ℝ), (13603678043663/100000000000000 : ℝ), (8555102532983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344633447/10000000000 : ℝ)|^2091 ≤ (21810404635817/50000000000000 : ℝ)^1579
        have hw : |(5344633447/10000000000 : ℝ)|=(5344633447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217115489/10000000000 : ℝ)|^2091 ≤ (13603678043663/100000000000000 : ℝ)^1579
        have hw : |(-2217115489/10000000000 : ℝ)|=(2217115489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633118271/5000000000 : ℝ)|^2091 ≤ (8555102532983/20000000000000 : ℝ)^1579
        have hw : |(2633118271/5000000000 : ℝ)|=(2633118271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336158337/2500000000 : ℝ)*x 0 + (2633118293/5000000000 : ℝ)*x 1 + (-1108557781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336158337/2500000000 : ℝ)^2091 ≤ (10905202050409/25000000000000 : ℝ)^1579 := by
    have hnat : (1336158337 : ℕ)^2091*25000000000000^1579 ≤ 10905202050409^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336158337 2500000000 10905202050409 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633118293/5000000000 : ℝ)^2091 ≤ (10693878284549/25000000000000 : ℝ)^1579 := by
    have hnat : (2633118293 : ℕ)^2091*25000000000000^1579 ≤ 10693878284549^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633118293 5000000000 10693878284549 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108557781/5000000000 : ℝ)^2091 ≤ (1360367863681/10000000000000 : ℝ)^1579 := by
    have hnat : (1108557781 : ℕ)^2091*10000000000000^1579 ≤ 1360367863681^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108557781 5000000000 1360367863681 10000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336158337/2500000000 : ℝ), (2633118293/5000000000 : ℝ), (-1108557781/5000000000 : ℝ)] ![(10905202050409/25000000000000 : ℝ), (10693878284549/25000000000000 : ℝ), (1360367863681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336158337/2500000000 : ℝ)|^2091 ≤ (10905202050409/25000000000000 : ℝ)^1579
        have hw : |(1336158337/2500000000 : ℝ)|=(1336158337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633118293/5000000000 : ℝ)|^2091 ≤ (10693878284549/25000000000000 : ℝ)^1579
        have hw : |(2633118293/5000000000 : ℝ)|=(2633118293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1108557781/5000000000 : ℝ)|^2091 ≤ (1360367863681/10000000000000 : ℝ)^1579
        have hw : |(-1108557781/5000000000 : ℝ)|=(1108557781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (43606057/100000000 : ℝ)*x 0 + (4236134809/10000000000 : ℝ)*x 1 + (4488691083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43606057/100000000 : ℝ)^2091 ≤ (3331714372727/10000000000000 : ℝ)^1579 := by
    have hnat : (43606057 : ℕ)^2091*10000000000000^1579 ≤ 3331714372727^1579*100000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43606057 100000000 3331714372727 10000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236134809/10000000000 : ℝ)^2091 ≤ (32063618748901/100000000000000 : ℝ)^1579 := by
    have hnat : (4236134809 : ℕ)^2091*100000000000000^1579 ≤ 32063618748901^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236134809 10000000000 32063618748901 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488691083/10000000000 : ℝ)^2091 ≤ (6923847502601/20000000000000 : ℝ)^1579 := by
    have hnat : (4488691083 : ℕ)^2091*20000000000000^1579 ≤ 6923847502601^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488691083 10000000000 6923847502601 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43606057/100000000 : ℝ), (4236134809/10000000000 : ℝ), (4488691083/10000000000 : ℝ)] ![(3331714372727/10000000000000 : ℝ), (32063618748901/100000000000000 : ℝ), (6923847502601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43606057/100000000 : ℝ)|^2091 ≤ (3331714372727/10000000000000 : ℝ)^1579
        have hw : |(43606057/100000000 : ℝ)|=(43606057/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236134809/10000000000 : ℝ)|^2091 ≤ (32063618748901/100000000000000 : ℝ)^1579
        have hw : |(4236134809/10000000000 : ℝ)|=(4236134809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488691083/10000000000 : ℝ)|^2091 ≤ (6923847502601/20000000000000 : ℝ)^1579
        have hw : |(4488691083/10000000000 : ℝ)|=(4488691083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-269137899/1250000000 : ℝ)*x 0 + (210662153/400000000 : ℝ)*x 1 + (2696072959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269137899/1250000000 : ℝ)^2091 ≤ (3271502243033/25000000000000 : ℝ)^1579 := by
    have hnat : (269137899 : ℕ)^2091*25000000000000^1579 ≤ 3271502243033^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269137899 1250000000 3271502243033 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210662153/400000000 : ℝ)^2091 ≤ (8555785103939/20000000000000 : ℝ)^1579 := by
    have hnat : (210662153 : ℕ)^2091*20000000000000^1579 ≤ 8555785103939^1579*400000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210662153 400000000 8555785103939 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696072959/5000000000 : ℝ)^2091 ≤ (44135065493539/100000000000000 : ℝ)^1579 := by
    have hnat : (2696072959 : ℕ)^2091*100000000000000^1579 ≤ 44135065493539^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696072959 5000000000 44135065493539 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269137899/1250000000 : ℝ), (210662153/400000000 : ℝ), (2696072959/5000000000 : ℝ)] ![(3271502243033/25000000000000 : ℝ), (8555785103939/20000000000000 : ℝ), (44135065493539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269137899/1250000000 : ℝ)|^2091 ≤ (3271502243033/25000000000000 : ℝ)^1579
        have hw : |(-269137899/1250000000 : ℝ)|=(269137899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210662153/400000000 : ℝ)|^2091 ≤ (8555785103939/20000000000000 : ℝ)^1579
        have hw : |(210662153/400000000 : ℝ)|=(210662153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696072959/5000000000 : ℝ)|^2091 ≤ (44135065493539/100000000000000 : ℝ)^1579
        have hw : |(2696072959/5000000000 : ℝ)|=(2696072959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656292533/5000000000 : ℝ)*x 0 + (-2091206107/10000000000 : ℝ)*x 1 + (2696072987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656292533/5000000000 : ℝ)^2091 ≤ (43274765687331/100000000000000 : ℝ)^1579 := by
    have hnat : (2656292533 : ℕ)^2091*100000000000000^1579 ≤ 43274765687331^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656292533 5000000000 43274765687331 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091206107/10000000000 : ℝ)^2091 ≤ (6295084100567/50000000000000 : ℝ)^1579 := by
    have hnat : (2091206107 : ℕ)^2091*50000000000000^1579 ≤ 6295084100567^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091206107 10000000000 6295084100567 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696072987/5000000000 : ℝ)^2091 ≤ (44135066100529/100000000000000 : ℝ)^1579 := by
    have hnat : (2696072987 : ℕ)^2091*100000000000000^1579 ≤ 44135066100529^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696072987 5000000000 44135066100529 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656292533/5000000000 : ℝ), (-2091206107/10000000000 : ℝ), (2696072987/5000000000 : ℝ)] ![(43274765687331/100000000000000 : ℝ), (6295084100567/50000000000000 : ℝ), (44135066100529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656292533/5000000000 : ℝ)|^2091 ≤ (43274765687331/100000000000000 : ℝ)^1579
        have hw : |(2656292533/5000000000 : ℝ)|=(2656292533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091206107/10000000000 : ℝ)|^2091 ≤ (6295084100567/50000000000000 : ℝ)^1579
        have hw : |(-2091206107/10000000000 : ℝ)|=(2091206107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696072987/5000000000 : ℝ)|^2091 ≤ (44135066100529/100000000000000 : ℝ)^1579
        have hw : |(2696072987/5000000000 : ℝ)|=(2696072987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062517017/2000000000 : ℝ)*x 0 + (5392145959/10000000000 : ℝ)*x 1 + (-2091206101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062517017/2000000000 : ℝ)^2091 ≤ (10818691473071/25000000000000 : ℝ)^1579 := by
    have hnat : (1062517017 : ℕ)^2091*25000000000000^1579 ≤ 10818691473071^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062517017 2000000000 10818691473071 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392145959/10000000000 : ℝ)^2091 ≤ (44135065937943/100000000000000 : ℝ)^1579 := by
    have hnat : (5392145959 : ℕ)^2091*100000000000000^1579 ≤ 44135065937943^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392145959 10000000000 44135065937943 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091206101/10000000000 : ℝ)^2091 ≤ (6295084076649/50000000000000 : ℝ)^1579 := by
    have hnat : (2091206101 : ℕ)^2091*50000000000000^1579 ≤ 6295084076649^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091206101 10000000000 6295084076649 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062517017/2000000000 : ℝ), (5392145959/10000000000 : ℝ), (-2091206101/10000000000 : ℝ)] ![(10818691473071/25000000000000 : ℝ), (44135065937943/100000000000000 : ℝ), (6295084076649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062517017/2000000000 : ℝ)|^2091 ≤ (10818691473071/25000000000000 : ℝ)^1579
        have hw : |(1062517017/2000000000 : ℝ)|=(1062517017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392145959/10000000000 : ℝ)|^2091 ≤ (44135065937943/100000000000000 : ℝ)^1579
        have hw : |(5392145959/10000000000 : ℝ)|=(5392145959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091206101/10000000000 : ℝ)|^2091 ≤ (6295084076649/50000000000000 : ℝ)^1579
        have hw : |(-2091206101/10000000000 : ℝ)|=(2091206101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s8_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (87212307/200000000 : ℝ)*x 0 + (4488056281/10000000000 : ℝ)*x 1 + (132399121/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87212307/200000000 : ℝ)^2091 ≤ (16658620682797/50000000000000 : ℝ)^1579 := by
    have hnat : (87212307 : ℕ)^2091*50000000000000^1579 ≤ 16658620682797^1579*200000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87212307 200000000 16658620682797 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488056281/10000000000 : ℝ)^2091 ≤ (17306377092369/50000000000000 : ℝ)^1579 := by
    have hnat : (4488056281 : ℕ)^2091*50000000000000^1579 ≤ 17306377092369^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488056281 10000000000 17306377092369 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132399121/312500000 : ℝ)^2091 ≤ (6414000887209/20000000000000 : ℝ)^1579 := by
    have hnat : (132399121 : ℕ)^2091*20000000000000^1579 ≤ 6414000887209^1579*312500000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132399121 312500000 6414000887209 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87212307/200000000 : ℝ), (4488056281/10000000000 : ℝ), (132399121/312500000 : ℝ)] ![(16658620682797/50000000000000 : ℝ), (17306377092369/50000000000000 : ℝ), (6414000887209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87212307/200000000 : ℝ)|^2091 ≤ (16658620682797/50000000000000 : ℝ)^1579
        have hw : |(87212307/200000000 : ℝ)|=(87212307/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488056281/10000000000 : ℝ)|^2091 ≤ (17306377092369/50000000000000 : ℝ)^1579
        have hw : |(4488056281/10000000000 : ℝ)|=(4488056281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132399121/312500000 : ℝ)|^2091 ≤ (6414000887209/20000000000000 : ℝ)^1579
        have hw : |(132399121/312500000 : ℝ)|=(132399121/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2813/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/10000 : ℝ) ^ (8363/2048 : ℝ) ≤ (3509605656862789/25000000000000000000 : ℝ) := by
    have hpowers : (1139/10000 : ℝ)^8363 ≤ (3509605656862789/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1139 : ℕ)^8363*25000000000000000000^2048 ≤ 3509605656862789^2048*10000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 10000 3509605656862789 25000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/10000 : ℝ)) (X := (3509605656862789/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7033/50000 : ℝ) ^ (8363/2048 : ℝ) ≤ (1661605917910783/5000000000000000000 : ℝ) := by
    have hpowers : (7033/50000 : ℝ)^8363 ≤ (1661605917910783/5000000000000000000 : ℝ)^2048 := by
      have hnat : (7033 : ℕ)^8363*5000000000000000000^2048 ≤ 1661605917910783^2048*50000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7033 50000 1661605917910783 5000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7033/50000 : ℝ)) (X := (1661605917910783/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503509605656862789/12500000000000000000 : ℝ) ≤ (10000687495929741/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (12503509605656862789/12500000000000000000 : ℝ)^2048 ≤ (10000687495929741/10000000000000000 : ℝ)^8363 := by
      have hnat : (12503509605656862789 : ℕ)^2048*10000000000000000^8363 ≤ 10000687495929741^8363*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503509605656862789 12500000000000000000 10000687495929741 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000687495929741/10000000000000000 : ℝ)) (X := (12503509605656862789/12500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (390809650550725261/390625000000000000 : ℝ) ≤ (10001157393217261/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (390809650550725261/390625000000000000 : ℝ)^2048 ≤ (10001157393217261/10000000000000000 : ℝ)^8363 := by
      have hnat : (390809650550725261 : ℕ)^2048*10000000000000000^8363 ≤ 10001157393217261^8363*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390809650550725261 390625000000000000 10001157393217261 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001157393217261/10000000000000000 : ℝ)) (X := (390809650550725261/390625000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501661605917910783/2500000000000000000 : ℝ) ≤ (10001627290504781/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (2501661605917910783/2500000000000000000 : ℝ)^2048 ≤ (10001627290504781/10000000000000000 : ℝ)^8363 := by
      have hnat : (2501661605917910783 : ℕ)^2048*10000000000000000^8363 ≤ 10001627290504781^8363*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501661605917910783 2500000000000000000 10001627290504781 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001627290504781/10000000000000000 : ℝ)) (X := (2501661605917910783/2500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3509605656862789/25000000000000000000 : ℝ) ≤ ((6687783869724570329/6690000000000000000 : ℝ)+2*(2936858047/1672500000000 : ℝ)*(1139/10000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (6687783869724570329/6690000000000000000 : ℝ)+2*(2936858047/1672500000000 : ℝ)*(1139/10000 : ℝ)=(10000687495929741/10000000000000000 : ℝ) by norm_num, show 1+2*(3509605656862789/25000000000000000000 : ℝ)=(12503509605656862789/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1661605917910783/5000000000000000000 : ℝ)+(3509605656862789/25000000000000000000 : ℝ) ≤ ((6687783869724570329/6690000000000000000 : ℝ)+(2936858047/1672500000000 : ℝ)*((7033/50000 : ℝ)+(1139/10000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (6687783869724570329/6690000000000000000 : ℝ)+(2936858047/1672500000000 : ℝ)*((7033/50000 : ℝ)+(1139/10000 : ℝ))=(10001157393217261/10000000000000000 : ℝ) by norm_num, show 1+(1661605917910783/5000000000000000000 : ℝ)+(3509605656862789/25000000000000000000 : ℝ)=(390809650550725261/390625000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1661605917910783/5000000000000000000 : ℝ) ≤ ((6687783869724570329/6690000000000000000 : ℝ)+2*(2936858047/1672500000000 : ℝ)*(7033/50000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (6687783869724570329/6690000000000000000 : ℝ)+2*(2936858047/1672500000000 : ℝ)*(7033/50000 : ℝ)=(10001627290504781/10000000000000000 : ℝ) by norm_num, show 1+2*(1661605917910783/5000000000000000000 : ℝ)=(2501661605917910783/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6687783869724570329/6690000000000000000 : ℝ)*(X 1 0+X 2 0)+(2936858047/1672500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (6687783869724570329/6690000000000000000 : ℝ)) (alpha := (2936858047/1672500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6687783869724570329/6690000000000000000 : ℝ)*(X 0 1+X 2 1)+(2936858047/1672500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (6687783869724570329/6690000000000000000 : ℝ)) (alpha := (2936858047/1672500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6687783869724570329/6690000000000000000 : ℝ)*(X 0 2+X 1 2)+(2936858047/1672500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7033/50000 : ℝ)) (c := (6687783869724570329/6690000000000000000 : ℝ)) (alpha := (2936858047/1672500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-538274597/2500000000 : ℝ)*X 0 0+(8627943/16000000 : ℝ)*X 0 1+(5266236513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344633447/10000000000 : ℝ)*X 1 0+(-2217115489/10000000000 : ℝ)*X 1 1+(2633118271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336158337/2500000000 : ℝ)*X 2 0+(2633118293/5000000000 : ℝ)*X 2 1+(-1108557781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43606057/100000000 : ℝ)*X 0 0+(4236134809/10000000000 : ℝ)*X 0 1+(4488691083/10000000000 : ℝ)*X 0 2+(43606057/100000000 : ℝ)*X 1 0+(4236134809/10000000000 : ℝ)*X 1 1+(4488691083/10000000000 : ℝ)*X 1 2+(43606057/100000000 : ℝ)*X 2 0+(4236134809/10000000000 : ℝ)*X 2 1+(4488691083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269137899/1250000000 : ℝ)*X 0 0+(210662153/400000000 : ℝ)*X 0 1+(2696072959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656292533/5000000000 : ℝ)*X 1 0+(-2091206107/10000000000 : ℝ)*X 1 1+(2696072987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062517017/2000000000 : ℝ)*X 2 0+(5392145959/10000000000 : ℝ)*X 2 1+(-2091206101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87212307/200000000 : ℝ)*X 0 0+(4488056281/10000000000 : ℝ)*X 0 1+(132399121/312500000 : ℝ)*X 0 2+(87212307/200000000 : ℝ)*X 1 0+(4488056281/10000000000 : ℝ)*X 1 1+(132399121/312500000 : ℝ)*X 1 2+(87212307/200000000 : ℝ)*X 2 0+(4488056281/10000000000 : ℝ)*X 2 1+(132399121/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (239694196829241602278552107/27875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817726223/50000000000000 : ℝ)*(base19) + (285279849/20000000000000 : ℝ)*(base23) + (16650383/50000000000000 : ℝ)*(lower2) + (53896269/20000000000000 : ℝ)*(upper3) + (9758087/12500000000000 : ℝ)*(upper5) + (1485229377668717/25000000000000 : ℝ)*(major0) + (1485229377668717/25000000000000 : ℝ)*(major1) + (5940917510674869/100000000000000 : ℝ)*(major2) + (990279127734621/12500000000000 : ℝ)*(sp0) + (7922273295744539/100000000000000 : ℝ)*(sp1) + (7922273504797739/100000000000000 : ℝ)*(sp2) + (3959534908742139/100000000000000 : ℝ)*(sp3) + (2619332501/6250000000000 : ℝ)*(sp4) + (777961899/3125000000000 : ℝ)*(sp7) + (989889950880727/25000000000000 : ℝ)*(f.failure) + (1584454986239397/20000000000000 : ℝ)*(f.sum) + (2238998843/1045312500000000000000000 : ℝ)*base65 + (4574831948604947893/167250000000000000000000000000000 : ℝ)*base67 + (684552886182361901/669000000000000000000000000000000 : ℝ)*base69 + (1101445827396552107/167250000000000000000000000000000 : ℝ)*base72 + (1242257544821/167250000000000000000000000 : ℝ)*base73 + (4181296097171638099/669000000000000000000000000000000 : ℝ)*base76 + (303804651861232631/55750000000000000000000000000000 : ℝ)*base77 + (929391121075482631/55750000000000000000000000000000 : ℝ)*base79 + (786707250767/669000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5651187/312500000000000000000 : ℝ)*base89 + (5651187/312500000000000000000 : ℝ)*base91 + (2526187/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158204685612941817892030621/27875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201927777/20000000000000 : ℝ)*(base19) + (1113034649/100000000000000 : ℝ)*(base23) + (366615477/100000000000000 : ℝ)*(lower1) + (35800001/25000000000000 : ℝ)*(upper3) + (13681437/50000000000000 : ℝ)*(lower4) + (98102149/100000000000000 : ℝ)*(upper5) + (2985448490019451/50000000000000 : ℝ)*(major0) + (2985448490019451/50000000000000 : ℝ)*(major1) + (2985448490019451/50000000000000 : ℝ)*(major2) + (1940624711/50000000000000 : ℝ)*(sp2) + (248820405077581/3125000000000 : ℝ)*(sp4) + (7962251952843707/100000000000000 : ℝ)*(sp5) + (7962247968198521/100000000000000 : ℝ)*(sp6) + (397954080841171/10000000000000 : ℝ)*(sp7) + (397954080841171/10000000000000 : ℝ)*(f.failure) + (248820405077581/3125000000000 : ℝ)*(f.sum) + (190515782467/167250000000000000000000000 : ℝ)*base65 + (3296506464073489793/111500000000000000000000000000000 : ℝ)*base67 + (312954267314489793/111500000000000000000000000000000 : ℝ)*base69 + (5457101811475489793/111500000000000000000000000000000 : ℝ)*base71 + (803262140143/669000000000000000000000000 : ℝ)*base73 + (5112758750251489793/111500000000000000000000000000000 : ℝ)*base75 + (1479862862066989793/111500000000000000000000000000000 : ℝ)*base77 + (1682432992633010207/111500000000000000000000000000000 : ℝ)*base80 + (1006254059963/669000000000000000000000000 : ℝ)*base82 + (1377249/125000000000000000000 : ℝ)*base90 + (1377249/125000000000000000000 : ℝ)*base92 + (1377249/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1171_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1171_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1171_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1171_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1171_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

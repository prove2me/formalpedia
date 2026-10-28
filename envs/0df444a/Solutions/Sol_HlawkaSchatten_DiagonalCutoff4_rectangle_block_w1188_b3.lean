-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:20.751761+00:00
-- url     : https://prove2.me/submissions/cfe93904-d874-4bb1-b03f-3dc5326117db

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
theorem support_rectangle_w1188_s9_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429016303/2000000000 : ℝ)*x 0 + (5392147137/10000000000 : ℝ)*x 1 + (2633250627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429016303/2000000000 : ℝ)^8381 ≤ (2607789031981/20000000000000 : ℝ)^6333 := by
    have hnat : (429016303 : ℕ)^8381*20000000000000^6333 ≤ 2607789031981^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429016303 2000000000 2607789031981 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392147137/10000000000 : ℝ)^8381 ≤ (22079406172803/50000000000000 : ℝ)^6333 := by
    have hnat : (5392147137 : ℕ)^8381*50000000000000^6333 ≤ 22079406172803^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392147137 10000000000 22079406172803 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633250627/5000000000 : ℝ)^8381 ≤ (342417939881/800000000000 : ℝ)^6333 := by
    have hnat : (2633250627 : ℕ)^8381*800000000000^6333 ≤ 342417939881^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633250627 5000000000 342417939881 800000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429016303/2000000000 : ℝ), (5392147137/10000000000 : ℝ), (2633250627/5000000000 : ℝ)] ![(2607789031981/20000000000000 : ℝ), (22079406172803/50000000000000 : ℝ), (342417939881/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429016303/2000000000 : ℝ)|^8381 ≤ (2607789031981/20000000000000 : ℝ)^6333
        have hw : |(-429016303/2000000000 : ℝ)|=(429016303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392147137/10000000000 : ℝ)|^8381 ≤ (22079406172803/50000000000000 : ℝ)^6333
        have hw : |(5392147137/10000000000 : ℝ)|=(5392147137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633250627/5000000000 : ℝ)|^8381 ≤ (342417939881/800000000000 : ℝ)^6333
        have hw : |(2633250627/5000000000 : ℝ)|=(2633250627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336139883/2500000000 : ℝ)*x 0 + (-2208799387/10000000000 : ℝ)*x 1 + (5266501363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336139883/2500000000 : ℝ)^8381 ≤ (10910950950997/25000000000000 : ℝ)^6333 := by
    have hnat : (1336139883 : ℕ)^8381*25000000000000^6333 ≤ 10910950950997^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336139883 2500000000 10910950950997 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208799387/10000000000 : ℝ)^8381 ≤ (6776976261157/50000000000000 : ℝ)^6333 := by
    have hnat : (2208799387 : ℕ)^8381*50000000000000^6333 ≤ 6776976261157^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208799387 10000000000 6776976261157 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266501363/10000000000 : ℝ)^8381 ≤ (21401121828737/50000000000000 : ℝ)^6333 := by
    have hnat : (5266501363 : ℕ)^8381*50000000000000^6333 ≤ 21401121828737^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266501363 10000000000 21401121828737 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336139883/2500000000 : ℝ), (-2208799387/10000000000 : ℝ), (5266501363/10000000000 : ℝ)] ![(10910950950997/25000000000000 : ℝ), (6776976261157/50000000000000 : ℝ), (21401121828737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336139883/2500000000 : ℝ)|^8381 ≤ (10910950950997/25000000000000 : ℝ)^6333
        have hw : |(1336139883/2500000000 : ℝ)|=(1336139883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208799387/10000000000 : ℝ)|^8381 ≤ (6776976261157/50000000000000 : ℝ)^6333
        have hw : |(-2208799387/10000000000 : ℝ)|=(2208799387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266501363/10000000000 : ℝ)|^8381 ≤ (21401121828737/50000000000000 : ℝ)^6333
        have hw : |(5266501363/10000000000 : ℝ)|=(5266501363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145088077/10000000000 : ℝ)*x 0 + (5266816853/10000000000 : ℝ)*x 1 + (2695914529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145088077/10000000000 : ℝ)^8381 ≤ (13038997946233/100000000000000 : ℝ)^6333 := by
    have hnat : (2145088077 : ℕ)^8381*100000000000000^6333 ≤ 13038997946233^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145088077 10000000000 13038997946233 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266816853/10000000000 : ℝ)^8381 ≤ (21402818471839/50000000000000 : ℝ)^6333 := by
    have hnat : (5266816853 : ℕ)^8381*50000000000000^6333 ≤ 21402818471839^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266816853 10000000000 21402818471839 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695914529/5000000000 : ℝ)^8381 ≤ (2759710318437/6250000000000 : ℝ)^6333 := by
    have hnat : (2695914529 : ℕ)^8381*6250000000000^6333 ≤ 2759710318437^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695914529 5000000000 2759710318437 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145088077/10000000000 : ℝ), (5266816853/10000000000 : ℝ), (2695914529/5000000000 : ℝ)] ![(13038997946233/100000000000000 : ℝ), (21402818471839/50000000000000 : ℝ), (2759710318437/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145088077/10000000000 : ℝ)|^8381 ≤ (13038997946233/100000000000000 : ℝ)^6333
        have hw : |(-2145088077/10000000000 : ℝ)|=(2145088077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266816853/10000000000 : ℝ)|^8381 ≤ (21402818471839/50000000000000 : ℝ)^6333
        have hw : |(5266816853/10000000000 : ℝ)|=(5266816853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695914529/5000000000 : ℝ)|^8381 ≤ (2759710318437/6250000000000 : ℝ)^6333
        have hw : |(2695914529/5000000000 : ℝ)|=(2695914529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328155131/2500000000 : ℝ)*x 0 + (-520867501/2500000000 : ℝ)*x 1 + (2695915051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328155131/2500000000 : ℝ)^8381 ≤ (43298979368403/100000000000000 : ℝ)^6333 := by
    have hnat : (1328155131 : ℕ)^8381*100000000000000^6333 ≤ 43298979368403^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328155131 2500000000 43298979368403 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520867501/2500000000 : ℝ)^8381 ≤ (3136411054111/25000000000000 : ℝ)^6333 := by
    have hnat : (520867501 : ℕ)^8381*25000000000000^6333 ≤ 3136411054111^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520867501 2500000000 3136411054111 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695915051/5000000000 : ℝ)^8381 ≤ (22077688204731/50000000000000 : ℝ)^6333 := by
    have hnat : (2695915051 : ℕ)^8381*50000000000000^6333 ≤ 22077688204731^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695915051 5000000000 22077688204731 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328155131/2500000000 : ℝ), (-520867501/2500000000 : ℝ), (2695915051/5000000000 : ℝ)] ![(43298979368403/100000000000000 : ℝ), (3136411054111/25000000000000 : ℝ), (22077688204731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328155131/2500000000 : ℝ)|^8381 ≤ (43298979368403/100000000000000 : ℝ)^6333
        have hw : |(1328155131/2500000000 : ℝ)|=(1328155131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520867501/2500000000 : ℝ)|^8381 ≤ (3136411054111/25000000000000 : ℝ)^6333
        have hw : |(-520867501/2500000000 : ℝ)|=(520867501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695915051/5000000000 : ℝ)|^8381 ≤ (22077688204731/50000000000000 : ℝ)^6333
        have hw : |(2695915051/5000000000 : ℝ)|=(2695915051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312620151/10000000000 : ℝ)*x 0 + (1347957407/2500000000 : ℝ)*x 1 + (-130216947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312620151/10000000000 : ℝ)^8381 ≤ (43298975345273/100000000000000 : ℝ)^6333 := by
    have hnat : (5312620151 : ℕ)^8381*100000000000000^6333 ≤ 43298975345273^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312620151 10000000000 43298975345273 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347957407/2500000000 : ℝ)^8381 ≤ (2759710704527/6250000000000 : ℝ)^6333 := by
    have hnat : (1347957407 : ℕ)^8381*6250000000000^6333 ≤ 2759710704527^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347957407 2500000000 2759710704527 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130216947/625000000 : ℝ)^8381 ≤ (12545653364609/100000000000000 : ℝ)^6333 := by
    have hnat : (130216947 : ℕ)^8381*100000000000000^6333 ≤ 12545653364609^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130216947 625000000 12545653364609 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312620151/10000000000 : ℝ), (1347957407/2500000000 : ℝ), (-130216947/625000000 : ℝ)] ![(43298975345273/100000000000000 : ℝ), (2759710704527/6250000000000 : ℝ), (12545653364609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312620151/10000000000 : ℝ)|^8381 ≤ (43298975345273/100000000000000 : ℝ)^6333
        have hw : |(5312620151/10000000000 : ℝ)|=(5312620151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347957407/2500000000 : ℝ)|^8381 ≤ (2759710704527/6250000000000 : ℝ)^6333
        have hw : |(1347957407/2500000000 : ℝ)|=(1347957407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130216947/625000000 : ℝ)|^8381 ≤ (12545653364609/100000000000000 : ℝ)^6333
        have hw : |(-130216947/625000000 : ℝ)|=(130216947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358244057/10000000000 : ℝ)*x 0 + (4485510737/10000000000 : ℝ)*x 1 + (2117277767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358244057/10000000000 : ℝ)^8381 ≤ (33317327046591/100000000000000 : ℝ)^6333 := by
    have hnat : (4358244057 : ℕ)^8381*100000000000000^6333 ≤ 33317327046591^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358244057 10000000000 33317327046591 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485510737/10000000000 : ℝ)^8381 ≤ (34610903652287/100000000000000 : ℝ)^6333 := by
    have hnat : (4485510737 : ℕ)^8381*100000000000000^6333 ≤ 34610903652287^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485510737 10000000000 34610903652287 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117277767/5000000000 : ℝ)^8381 ≤ (3207176928671/10000000000000 : ℝ)^6333 := by
    have hnat : (2117277767 : ℕ)^8381*10000000000000^6333 ≤ 3207176928671^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117277767 5000000000 3207176928671 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358244057/10000000000 : ℝ), (4485510737/10000000000 : ℝ), (2117277767/5000000000 : ℝ)] ![(33317327046591/100000000000000 : ℝ), (34610903652287/100000000000000 : ℝ), (3207176928671/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358244057/10000000000 : ℝ)|^8381 ≤ (33317327046591/100000000000000 : ℝ)^6333
        have hw : |(4358244057/10000000000 : ℝ)|=(4358244057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485510737/10000000000 : ℝ)|^8381 ≤ (34610903652287/100000000000000 : ℝ)^6333
        have hw : |(4485510737/10000000000 : ℝ)|=(4485510737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117277767/5000000000 : ℝ)|^8381 ≤ (3207176928671/10000000000000 : ℝ)^6333
        have hw : |(2117277767/5000000000 : ℝ)|=(2117277767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s9_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-458737/125000000 : ℝ)*x 0 + (5815878093/10000000000 : ℝ)*x 1 + (752982901/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458737/125000000 : ℝ)^8381 ≤ (59854697123/100000000000000 : ℝ)^6333 := by
    have hnat : (458737 : ℕ)^8381*100000000000000^6333 ≤ 59854697123^6333*125000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458737 125000000 59854697123 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5815878093/10000000000 : ℝ)^8381 ≤ (48808482791901/100000000000000 : ℝ)^6333 := by
    have hnat : (5815878093 : ℕ)^8381*100000000000000^6333 ≤ 48808482791901^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5815878093 10000000000 48808482791901 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752982901/1250000000 : ℝ)^8381 ≤ (51131662499093/100000000000000 : ℝ)^6333 := by
    have hnat : (752982901 : ℕ)^8381*100000000000000^6333 ≤ 51131662499093^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752982901 1250000000 51131662499093 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458737/125000000 : ℝ), (5815878093/10000000000 : ℝ), (752982901/1250000000 : ℝ)] ![(59854697123/100000000000000 : ℝ), (48808482791901/100000000000000 : ℝ), (51131662499093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458737/125000000 : ℝ)|^8381 ≤ (59854697123/100000000000000 : ℝ)^6333
        have hw : |(-458737/125000000 : ℝ)|=(458737/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5815878093/10000000000 : ℝ)|^8381 ≤ (48808482791901/100000000000000 : ℝ)^6333
        have hw : |(5815878093/10000000000 : ℝ)|=(5815878093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752982901/1250000000 : ℝ)|^8381 ≤ (51131662499093/100000000000000 : ℝ)^6333
        have hw : |(752982901/1250000000 : ℝ)|=(752982901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11413/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (13901815420179961/100000000000000000000 : ℝ) := by
    have hpowers : (11413/100000 : ℝ)^2095 ≤ (13901815420179961/100000000000000000000 : ℝ)^512 := by
      have hnat : (11413 : ℕ)^2095*100000000000000000000^512 ≤ 13901815420179961^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11413 100000 13901815420179961 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11413/100000 : ℝ)) (X := (13901815420179961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (2095/512 : ℝ) ≤ (16390561926250167/50000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^2095 ≤ (16390561926250167/50000000000000000000 : ℝ)^512 := by
      have hnat : (563 : ℕ)^2095*50000000000000000000^512 ≤ 16390561926250167^512*4000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 16390561926250167 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (16390561926250167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013901815420179961/50000000000000000000 : ℝ) ≤ (1000067942548419/1000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50013901815420179961/50000000000000000000 : ℝ)^512 ≤ (1000067942548419/1000000000000000 : ℝ)^2095 := by
      have hnat : (50013901815420179961 : ℕ)^512*1000000000000000^2095 ≤ 1000067942548419^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013901815420179961 50000000000000000000 1000067942548419 1000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000067942548419/1000000000000000 : ℝ)) (X := (50013901815420179961/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009336587854536059/20000000000000000000 : ℝ) ≤ (2500285172440557/2500000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (20009336587854536059/20000000000000000000 : ℝ)^512 ≤ (2500285172440557/2500000000000000 : ℝ)^2095 := by
      have hnat : (20009336587854536059 : ℕ)^512*2500000000000000^2095 ≤ 2500285172440557^2095*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009336587854536059 20000000000000000000 2500285172440557 2500000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500285172440557/2500000000000000 : ℝ)) (X := (20009336587854536059/20000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016390561926250167/25000000000000000000 : ℝ) ≤ (5000800977020133/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25016390561926250167/25000000000000000000 : ℝ)^512 ≤ (5000800977020133/5000000000000000 : ℝ)^2095 := by
      have hnat : (25016390561926250167 : ℕ)^512*5000000000000000^2095 ≤ 5000800977020133^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016390561926250167 25000000000000000000 5000800977020133 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800977020133/5000000000000000 : ℝ)) (X := (25016390561926250167/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13901815420179961/100000000000000000000 : ℝ) ≤ ((3326409976528552299/3327500000000000000 : ℝ)+2*(230632139019/133100000000000 : ℝ)*(11413/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3326409976528552299/3327500000000000000 : ℝ)+2*(230632139019/133100000000000 : ℝ)*(11413/100000 : ℝ)=(1000067942548419/1000000000000000 : ℝ) by norm_num, show 1+2*(13901815420179961/100000000000000000000 : ℝ)=(50013901815420179961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16390561926250167/50000000000000000000 : ℝ)+(13901815420179961/100000000000000000000 : ℝ) ≤ ((3326409976528552299/3327500000000000000 : ℝ)+(230632139019/133100000000000 : ℝ)*((563/4000 : ℝ)+(11413/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (3326409976528552299/3327500000000000000 : ℝ)+(230632139019/133100000000000 : ℝ)*((563/4000 : ℝ)+(11413/100000 : ℝ))=(2500285172440557/2500000000000000 : ℝ) by norm_num, show 1+(16390561926250167/50000000000000000000 : ℝ)+(13901815420179961/100000000000000000000 : ℝ)=(20009336587854536059/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16390561926250167/50000000000000000000 : ℝ) ≤ ((3326409976528552299/3327500000000000000 : ℝ)+2*(230632139019/133100000000000 : ℝ)*(563/4000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3326409976528552299/3327500000000000000 : ℝ)+2*(230632139019/133100000000000 : ℝ)*(563/4000 : ℝ)=(5000800977020133/5000000000000000 : ℝ) by norm_num, show 1+2*(16390561926250167/50000000000000000000 : ℝ)=(25016390561926250167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3326409976528552299/3327500000000000000 : ℝ)*(X 1 0+X 2 0)+(230632139019/133100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (3326409976528552299/3327500000000000000 : ℝ)) (alpha := (230632139019/133100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3326409976528552299/3327500000000000000 : ℝ)*(X 0 1+X 2 1)+(230632139019/133100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (3326409976528552299/3327500000000000000 : ℝ)) (alpha := (230632139019/133100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3326409976528552299/3327500000000000000 : ℝ)*(X 0 2+X 1 2)+(230632139019/133100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (3326409976528552299/3327500000000000000 : ℝ)) (alpha := (230632139019/133100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429016303/2000000000 : ℝ)*X 0 0+(5392147137/10000000000 : ℝ)*X 0 1+(2633250627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336139883/2500000000 : ℝ)*X 1 0+(-2208799387/10000000000 : ℝ)*X 1 1+(5266501363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2145088077/10000000000 : ℝ)*X 0 0+(5266816853/10000000000 : ℝ)*X 0 1+(2695914529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1328155131/2500000000 : ℝ)*X 1 0+(-520867501/2500000000 : ℝ)*X 1 1+(2695915051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312620151/10000000000 : ℝ)*X 2 0+(1347957407/2500000000 : ℝ)*X 2 1+(-130216947/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4358244057/10000000000 : ℝ)*X 0 0+(4485510737/10000000000 : ℝ)*X 0 1+(2117277767/5000000000 : ℝ)*X 0 2+(4358244057/10000000000 : ℝ)*X 1 0+(4485510737/10000000000 : ℝ)*X 1 1+(2117277767/5000000000 : ℝ)*X 1 2+(4358244057/10000000000 : ℝ)*X 2 0+(4485510737/10000000000 : ℝ)*X 2 1+(2117277767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-458737/125000000 : ℝ)*X 0 0+(5815878093/10000000000 : ℝ)*X 0 1+(752982901/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s9_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1611731030048319289311/3327500000000000000000000000 : ℝ) := by norm_num
    linear_combination (81955721/50000000000000 : ℝ)*(upper1) + (203671359/100000000000000 : ℝ)*(upper2) + (237770671/100000000000000 : ℝ)*(lower4) + (32516553/12500000000000 : ℝ)*(lower5) + (93624847669819/1562500000000 : ℝ)*(major0) + (93624847669819/1562500000000 : ℝ)*(major1) + (93624847669819/1562500000000 : ℝ)*(major2) + (720624247/12500000000000 : ℝ)*(sp0) + (44795305237/100000000000000 : ℝ)*(sp1) + (999898631690291/12500000000000 : ℝ)*(sp2) + (124986845160479/1562500000000 : ℝ)*(sp3) + (7999202885575893/100000000000000 : ℝ)*(sp4) + (996194400003841/25000000000000 : ℝ)*(sp5) + (8067059589/100000000000000 : ℝ)*(sp6) + (996194400003841/25000000000000 : ℝ)*(f.failure) + (7999202885575893/100000000000000 : ℝ)*(f.sum) + (10030256400739/1663750000000000000000000000 : ℝ)*base66 + (206939028615821149/20796875000000000000000000000000 : ℝ)*base67 + (45002381467236119/5199218750000000000000000000000 : ℝ)*base70 + (63863926007138881/5199218750000000000000000000000 : ℝ)*base71 + (31960986318029/6655000000000000000000000000 : ℝ)*base73 + (155474838986022601/20796875000000000000000000000000 : ℝ)*base76 + (19344476888477399/20796875000000000000000000000000 : ℝ)*base77 + (34033809368548619/5199218750000000000000000000000 : ℝ)*base80 + (607653326287/831875000000000000000000000 : ℝ)*base82 + (5275477/625000000000000000000 : ℝ)*base90 + (5275477/625000000000000000000 : ℝ)*base92 + (5275477/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_box_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019693309/10000000000 : ℝ)*x 0 + (2687821043/5000000000 : ℝ)*x 1 + (335977637/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019693309/10000000000 : ℝ)^8381 ≤ (300998863981/2500000000000 : ℝ)^6333 := by
    have hnat : (2019693309 : ℕ)^8381*2500000000000^6333 ≤ 300998863981^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019693309 10000000000 300998863981 2500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687821043/5000000000 : ℝ)^8381 ≤ (1374375691857/3125000000000 : ℝ)^6333 := by
    have hnat : (2687821043 : ℕ)^8381*3125000000000^6333 ≤ 1374375691857^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687821043 5000000000 1374375691857 3125000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335977637/625000000 : ℝ)^8381 ≤ (8796004657419/20000000000000 : ℝ)^6333 := by
    have hnat : (335977637 : ℕ)^8381*20000000000000^6333 ≤ 8796004657419^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335977637 625000000 8796004657419 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019693309/10000000000 : ℝ), (2687821043/5000000000 : ℝ), (335977637/625000000 : ℝ)] ![(300998863981/2500000000000 : ℝ), (1374375691857/3125000000000 : ℝ), (8796004657419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019693309/10000000000 : ℝ)|^8381 ≤ (300998863981/2500000000000 : ℝ)^6333
        have hw : |(-2019693309/10000000000 : ℝ)|=(2019693309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687821043/5000000000 : ℝ)|^8381 ≤ (1374375691857/3125000000000 : ℝ)^6333
        have hw : |(2687821043/5000000000 : ℝ)|=(2687821043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(335977637/625000000 : ℝ)|^8381 ≤ (8796004657419/20000000000000 : ℝ)^6333
        have hw : |(335977637/625000000 : ℝ)|=(335977637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33102427/62500000 : ℝ)*x 0 + (-2127286369/10000000000 : ℝ)*x 1 + (5375642203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33102427/62500000 : ℝ)^8381 ≤ (10780996866769/25000000000000 : ℝ)^6333 := by
    have hnat : (33102427 : ℕ)^8381*25000000000000^6333 ≤ 10780996866769^6333*62500000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33102427 62500000 10780996866769 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127286369/10000000000 : ℝ)^8381 ≤ (12895989112749/100000000000000 : ℝ)^6333 := by
    have hnat : (2127286369 : ℕ)^8381*100000000000000^6333 ≤ 12895989112749^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127286369 10000000000 12895989112749 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375642203/10000000000 : ℝ)^8381 ≤ (43980023406193/100000000000000 : ℝ)^6333 := by
    have hnat : (5375642203 : ℕ)^8381*100000000000000^6333 ≤ 43980023406193^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375642203 10000000000 43980023406193 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33102427/62500000 : ℝ), (-2127286369/10000000000 : ℝ), (5375642203/10000000000 : ℝ)] ![(10780996866769/25000000000000 : ℝ), (12895989112749/100000000000000 : ℝ), (43980023406193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33102427/62500000 : ℝ)|^8381 ≤ (10780996866769/25000000000000 : ℝ)^6333
        have hw : |(33102427/62500000 : ℝ)|=(33102427/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127286369/10000000000 : ℝ)|^8381 ≤ (12895989112749/100000000000000 : ℝ)^6333
        have hw : |(-2127286369/10000000000 : ℝ)|=(2127286369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375642203/10000000000 : ℝ)|^8381 ≤ (43980023406193/100000000000000 : ℝ)^6333
        have hw : |(5375642203/10000000000 : ℝ)|=(5375642203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296387851/10000000000 : ℝ)*x 0 + (537564257/1000000000 : ℝ)*x 1 + (-265910813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296387851/10000000000 : ℝ)^8381 ≤ (43123982413507/100000000000000 : ℝ)^6333 := by
    have hnat : (5296387851 : ℕ)^8381*100000000000000^6333 ≤ 43123982413507^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296387851 10000000000 43123982413507 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537564257/1000000000 : ℝ)^8381 ≤ (10995006844933/25000000000000 : ℝ)^6333 := by
    have hnat : (537564257 : ℕ)^8381*25000000000000^6333 ≤ 10995006844933^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537564257 1000000000 10995006844933 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265910813/1250000000 : ℝ)^8381 ≤ (64479950979/500000000000 : ℝ)^6333 := by
    have hnat : (265910813 : ℕ)^8381*500000000000^6333 ≤ 64479950979^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265910813 1250000000 64479950979 500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296387851/10000000000 : ℝ), (537564257/1000000000 : ℝ), (-265910813/1250000000 : ℝ)] ![(43123982413507/100000000000000 : ℝ), (10995006844933/25000000000000 : ℝ), (64479950979/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296387851/10000000000 : ℝ)|^8381 ≤ (43123982413507/100000000000000 : ℝ)^6333
        have hw : |(5296387851/10000000000 : ℝ)|=(5296387851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537564257/1000000000 : ℝ)|^8381 ≤ (10995006844933/25000000000000 : ℝ)^6333
        have hw : |(537564257/1000000000 : ℝ)|=(537564257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265910813/1250000000 : ℝ)|^8381 ≤ (64479950979/500000000000 : ℝ)^6333
        have hw : |(-265910813/1250000000 : ℝ)|=(265910813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (893058929/2000000000 : ℝ)*x 0 + (2153391037/5000000000 : ℝ)*x 1 + (4306782011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893058929/2000000000 : ℝ)^8381 ≤ (6880923728717/20000000000000 : ℝ)^6333 := by
    have hnat : (893058929 : ℕ)^8381*20000000000000^6333 ≤ 6880923728717^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893058929 2000000000 6880923728717 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153391037/5000000000 : ℝ)^8381 ≤ (32797690991477/100000000000000 : ℝ)^6333 := by
    have hnat : (2153391037 : ℕ)^8381*100000000000000^6333 ≤ 32797690991477^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153391037 5000000000 32797690991477 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306782011/10000000000 : ℝ)^8381 ≤ (32797690356559/100000000000000 : ℝ)^6333 := by
    have hnat : (4306782011 : ℕ)^8381*100000000000000^6333 ≤ 32797690356559^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306782011 10000000000 32797690356559 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893058929/2000000000 : ℝ), (2153391037/5000000000 : ℝ), (4306782011/10000000000 : ℝ)] ![(6880923728717/20000000000000 : ℝ), (32797690991477/100000000000000 : ℝ), (32797690356559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893058929/2000000000 : ℝ)|^8381 ≤ (6880923728717/20000000000000 : ℝ)^6333
        have hw : |(893058929/2000000000 : ℝ)|=(893058929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2153391037/5000000000 : ℝ)|^8381 ≤ (32797690991477/100000000000000 : ℝ)^6333
        have hw : |(2153391037/5000000000 : ℝ)|=(2153391037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4306782011/10000000000 : ℝ)|^8381 ≤ (32797690356559/100000000000000 : ℝ)^6333
        have hw : |(4306782011/10000000000 : ℝ)|=(4306782011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2271858547/10000000000 : ℝ)*x 0 + (132042543/250000000 : ℝ)*x 1 + (2640850689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2271858547/10000000000 : ℝ)^8381 ≤ (14068388921451/100000000000000 : ℝ)^6333 := by
    have hnat : (2271858547 : ℕ)^8381*100000000000000^6333 ≤ 14068388921451^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271858547 10000000000 14068388921451 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132042543/250000000 : ℝ)^8381 ≤ (4296580737531/10000000000000 : ℝ)^6333 := by
    have hnat : (132042543 : ℕ)^8381*10000000000000^6333 ≤ 4296580737531^6333*250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132042543 250000000 4296580737531 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640850689/5000000000 : ℝ)^8381 ≤ (42965803693499/100000000000000 : ℝ)^6333 := by
    have hnat : (2640850689 : ℕ)^8381*100000000000000^6333 ≤ 42965803693499^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640850689 5000000000 42965803693499 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2271858547/10000000000 : ℝ), (132042543/250000000 : ℝ), (2640850689/5000000000 : ℝ)] ![(14068388921451/100000000000000 : ℝ), (4296580737531/10000000000000 : ℝ), (42965803693499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2271858547/10000000000 : ℝ)|^8381 ≤ (14068388921451/100000000000000 : ℝ)^6333
        have hw : |(-2271858547/10000000000 : ℝ)|=(2271858547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132042543/250000000 : ℝ)|^8381 ≤ (4296580737531/10000000000000 : ℝ)^6333
        have hw : |(132042543/250000000 : ℝ)|=(132042543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640850689/5000000000 : ℝ)|^8381 ≤ (42965803693499/100000000000000 : ℝ)^6333
        have hw : |(2640850689/5000000000 : ℝ)|=(2640850689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362688873/10000000000 : ℝ)*x 0 + (-4227293/19531250 : ℝ)*x 1 + (5281701479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362688873/10000000000 : ℝ)^8381 ≤ (5479978912973/12500000000000 : ℝ)^6333 := by
    have hnat : (5362688873 : ℕ)^8381*12500000000000^6333 ≤ 5479978912973^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362688873 10000000000 5479978912973 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227293/19531250 : ℝ)^8381 ≤ (13194363897233/100000000000000 : ℝ)^6333 := by
    have hnat : (4227293 : ℕ)^8381*100000000000000^6333 ≤ 13194363897233^6333*19531250^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227293 19531250 13194363897233 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281701479/10000000000 : ℝ)^8381 ≤ (42965804780817/100000000000000 : ℝ)^6333 := by
    have hnat : (5281701479 : ℕ)^8381*100000000000000^6333 ≤ 42965804780817^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281701479 10000000000 42965804780817 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362688873/10000000000 : ℝ), (-4227293/19531250 : ℝ), (5281701479/10000000000 : ℝ)] ![(5479978912973/12500000000000 : ℝ), (13194363897233/100000000000000 : ℝ), (42965804780817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362688873/10000000000 : ℝ)|^8381 ≤ (5479978912973/12500000000000 : ℝ)^6333
        have hw : |(5362688873/10000000000 : ℝ)|=(5362688873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4227293/19531250 : ℝ)|^8381 ≤ (13194363897233/100000000000000 : ℝ)^6333
        have hw : |(-4227293/19531250 : ℝ)|=(4227293/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281701479/10000000000 : ℝ)|^8381 ≤ (42965804780817/100000000000000 : ℝ)^6333
        have hw : |(5281701479/10000000000 : ℝ)|=(5281701479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362688879/10000000000 : ℝ)*x 0 + (1056340311/2000000000 : ℝ)*x 1 + (-1082186953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362688879/10000000000 : ℝ)^8381 ≤ (5479978921087/12500000000000 : ℝ)^6333 := by
    have hnat : (5362688879 : ℕ)^8381*12500000000000^6333 ≤ 5479978921087^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362688879 10000000000 5479978921087 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056340311/2000000000 : ℝ)^8381 ≤ (21482902799499/50000000000000 : ℝ)^6333 := by
    have hnat : (1056340311 : ℕ)^8381*50000000000000^6333 ≤ 21482902799499^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056340311 2000000000 21482902799499 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082186953/5000000000 : ℝ)^8381 ≤ (13194363009801/100000000000000 : ℝ)^6333 := by
    have hnat : (1082186953 : ℕ)^8381*100000000000000^6333 ≤ 13194363009801^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082186953 5000000000 13194363009801 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362688879/10000000000 : ℝ), (1056340311/2000000000 : ℝ), (-1082186953/5000000000 : ℝ)] ![(5479978921087/12500000000000 : ℝ), (21482902799499/50000000000000 : ℝ), (13194363009801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362688879/10000000000 : ℝ)|^8381 ≤ (5479978921087/12500000000000 : ℝ)^6333
        have hw : |(5362688879/10000000000 : ℝ)|=(5362688879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056340311/2000000000 : ℝ)|^8381 ≤ (21482902799499/50000000000000 : ℝ)^6333
        have hw : |(1056340311/2000000000 : ℝ)|=(1056340311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082186953/5000000000 : ℝ)|^8381 ≤ (13194363009801/100000000000000 : ℝ)^6333
        have hw : |(-1082186953/5000000000 : ℝ)|=(1082186953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4250795269/10000000000 : ℝ)*x 0 + (4414011243/10000000000 : ℝ)*x 1 + (882802249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250795269/10000000000 : ℝ)^8381 ≤ (6446928477689/20000000000000 : ℝ)^6333 := by
    have hnat : (4250795269 : ℕ)^8381*20000000000000^6333 ≤ 6446928477689^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250795269 10000000000 6446928477689 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414011243/10000000000 : ℝ)^8381 ≤ (33882678789919/100000000000000 : ℝ)^6333 := by
    have hnat : (4414011243 : ℕ)^8381*100000000000000^6333 ≤ 33882678789919^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414011243 10000000000 33882678789919 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882802249/2000000000 : ℝ)^8381 ≤ (8470669702559/25000000000000 : ℝ)^6333 := by
    have hnat : (882802249 : ℕ)^8381*25000000000000^6333 ≤ 8470669702559^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882802249 2000000000 8470669702559 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250795269/10000000000 : ℝ), (4414011243/10000000000 : ℝ), (882802249/2000000000 : ℝ)] ![(6446928477689/20000000000000 : ℝ), (33882678789919/100000000000000 : ℝ), (8470669702559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250795269/10000000000 : ℝ)|^8381 ≤ (6446928477689/20000000000000 : ℝ)^6333
        have hw : |(4250795269/10000000000 : ℝ)|=(4250795269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414011243/10000000000 : ℝ)|^8381 ≤ (33882678789919/100000000000000 : ℝ)^6333
        have hw : |(4414011243/10000000000 : ℝ)|=(4414011243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882802249/2000000000 : ℝ)|^8381 ≤ (8470669702559/25000000000000 : ℝ)^6333
        have hw : |(882802249/2000000000 : ℝ)|=(882802249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_8 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109537721/5000000000 : ℝ)*x 0 + (1304431381/2500000000 : ℝ)*x 1 + (5385253263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109537721/5000000000 : ℝ)^8381 ≤ (3409366121309/25000000000000 : ℝ)^6333 := by
    have hnat : (1109537721 : ℕ)^8381*25000000000000^6333 ≤ 3409366121309^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109537721 5000000000 3409366121309 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304431381/2500000000 : ℝ)^8381 ≤ (21139211141007/50000000000000 : ℝ)^6333 := by
    have hnat : (1304431381 : ℕ)^8381*50000000000000^6333 ≤ 21139211141007^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304431381 2500000000 21139211141007 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385253263/10000000000 : ℝ)^8381 ≤ (2204205660901/5000000000000 : ℝ)^6333 := by
    have hnat : (5385253263 : ℕ)^8381*5000000000000^6333 ≤ 2204205660901^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385253263 10000000000 2204205660901 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109537721/5000000000 : ℝ), (1304431381/2500000000 : ℝ), (5385253263/10000000000 : ℝ)] ![(3409366121309/25000000000000 : ℝ), (21139211141007/50000000000000 : ℝ), (2204205660901/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109537721/5000000000 : ℝ)|^8381 ≤ (3409366121309/25000000000000 : ℝ)^6333
        have hw : |(-1109537721/5000000000 : ℝ)|=(1109537721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304431381/2500000000 : ℝ)|^8381 ≤ (21139211141007/50000000000000 : ℝ)^6333
        have hw : |(1304431381/2500000000 : ℝ)|=(1304431381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385253263/10000000000 : ℝ)|^8381 ≤ (2204205660901/5000000000000 : ℝ)^6333
        have hw : |(5385253263/10000000000 : ℝ)|=(5385253263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_9 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644800813/5000000000 : ℝ)*x 0 + (-1061712069/5000000000 : ℝ)*x 1 + (5385253177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644800813/5000000000 : ℝ)^8381 ≤ (43050874620031/100000000000000 : ℝ)^6333 := by
    have hnat : (2644800813 : ℕ)^8381*100000000000000^6333 ≤ 43050874620031^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644800813 5000000000 43050874620031 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061712069/5000000000 : ℝ)^8381 ≤ (12865013084311/100000000000000 : ℝ)^6333 := by
    have hnat : (1061712069 : ℕ)^8381*100000000000000^6333 ≤ 12865013084311^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061712069 5000000000 12865013084311 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385253177/10000000000 : ℝ)^8381 ≤ (44084112286353/100000000000000 : ℝ)^6333 := by
    have hnat : (5385253177 : ℕ)^8381*100000000000000^6333 ≤ 44084112286353^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385253177 10000000000 44084112286353 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644800813/5000000000 : ℝ), (-1061712069/5000000000 : ℝ), (5385253177/10000000000 : ℝ)] ![(43050874620031/100000000000000 : ℝ), (12865013084311/100000000000000 : ℝ), (44084112286353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644800813/5000000000 : ℝ)|^8381 ≤ (43050874620031/100000000000000 : ℝ)^6333
        have hw : |(2644800813/5000000000 : ℝ)|=(2644800813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061712069/5000000000 : ℝ)|^8381 ≤ (12865013084311/100000000000000 : ℝ)^6333
        have hw : |(-1061712069/5000000000 : ℝ)|=(1061712069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385253177/10000000000 : ℝ)|^8381 ≤ (44084112286353/100000000000000 : ℝ)^6333
        have hw : |(5385253177/10000000000 : ℝ)|=(5385253177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_10 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289601751/10000000000 : ℝ)*x 0 + (5385253499/10000000000 : ℝ)*x 1 + (-424684707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289601751/10000000000 : ℝ)^8381 ≤ (43050875966373/100000000000000 : ℝ)^6333 := by
    have hnat : (5289601751 : ℕ)^8381*100000000000000^6333 ≤ 43050875966373^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289601751 10000000000 43050875966373 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385253499/10000000000 : ℝ)^8381 ≤ (1377628617959/3125000000000 : ℝ)^6333 := by
    have hnat : (5385253499 : ℕ)^8381*3125000000000^6333 ≤ 1377628617959^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385253499 10000000000 1377628617959 3125000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424684707/2000000000 : ℝ)^8381 ≤ (12865008249527/100000000000000 : ℝ)^6333 := by
    have hnat : (424684707 : ℕ)^8381*100000000000000^6333 ≤ 12865008249527^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424684707 2000000000 12865008249527 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289601751/10000000000 : ℝ), (5385253499/10000000000 : ℝ), (-424684707/2000000000 : ℝ)] ![(43050875966373/100000000000000 : ℝ), (1377628617959/3125000000000 : ℝ), (12865008249527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289601751/10000000000 : ℝ)|^8381 ≤ (43050875966373/100000000000000 : ℝ)^6333
        have hw : |(5289601751/10000000000 : ℝ)|=(5289601751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385253499/10000000000 : ℝ)|^8381 ≤ (1377628617959/3125000000000 : ℝ)^6333
        have hw : |(5385253499/10000000000 : ℝ)|=(5385253499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424684707/2000000000 : ℝ)|^8381 ≤ (12865008249527/100000000000000 : ℝ)^6333
        have hw : |(-424684707/2000000000 : ℝ)|=(424684707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_11 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4486966667/10000000000 : ℝ)*x 0 + (859161079/2000000000 : ℝ)*x 1 + (4295805627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486966667/10000000000 : ℝ)^8381 ≤ (6925154317611/20000000000000 : ℝ)^6333 := by
    have hnat : (4486966667 : ℕ)^8381*20000000000000^6333 ≤ 6925154317611^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486966667 10000000000 6925154317611 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859161079/2000000000 : ℝ)^8381 ≤ (16343556515619/50000000000000 : ℝ)^6333 := by
    have hnat : (859161079 : ℕ)^8381*50000000000000^6333 ≤ 16343556515619^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859161079 2000000000 16343556515619 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4295805627/10000000000 : ℝ)^8381 ≤ (16343557683709/50000000000000 : ℝ)^6333 := by
    have hnat : (4295805627 : ℕ)^8381*50000000000000^6333 ≤ 16343557683709^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295805627 10000000000 16343557683709 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486966667/10000000000 : ℝ), (859161079/2000000000 : ℝ), (4295805627/10000000000 : ℝ)] ![(6925154317611/20000000000000 : ℝ), (16343556515619/50000000000000 : ℝ), (16343557683709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486966667/10000000000 : ℝ)|^8381 ≤ (6925154317611/20000000000000 : ℝ)^6333
        have hw : |(4486966667/10000000000 : ℝ)|=(4486966667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859161079/2000000000 : ℝ)|^8381 ≤ (16343556515619/50000000000000 : ℝ)^6333
        have hw : |(859161079/2000000000 : ℝ)|=(859161079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4295805627/10000000000 : ℝ)|^8381 ≤ (16343557683709/50000000000000 : ℝ)^6333
        have hw : |(4295805627/10000000000 : ℝ)|=(4295805627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_12 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036383757/5000000000 : ℝ)*x 0 + (5438372903/10000000000 : ℝ)*x 1 + (5273643579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036383757/5000000000 : ℝ)^8381 ≤ (2492085860591/20000000000000 : ℝ)^6333 := by
    have hnat : (1036383757 : ℕ)^8381*20000000000000^6333 ≤ 2492085860591^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036383757 5000000000 2492085860591 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438372903/10000000000 : ℝ)^8381 ≤ (8932098413063/20000000000000 : ℝ)^6333 := by
    have hnat : (5438372903 : ℕ)^8381*20000000000000^6333 ≤ 8932098413063^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438372903 10000000000 8932098413063 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273643579/10000000000 : ℝ)^8381 ≤ (2679942413487/6250000000000 : ℝ)^6333 := by
    have hnat : (5273643579 : ℕ)^8381*6250000000000^6333 ≤ 2679942413487^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273643579 10000000000 2679942413487 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036383757/5000000000 : ℝ), (5438372903/10000000000 : ℝ), (5273643579/10000000000 : ℝ)] ![(2492085860591/20000000000000 : ℝ), (8932098413063/20000000000000 : ℝ), (2679942413487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036383757/5000000000 : ℝ)|^8381 ≤ (2492085860591/20000000000000 : ℝ)^6333
        have hw : |(-1036383757/5000000000 : ℝ)|=(1036383757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438372903/10000000000 : ℝ)|^8381 ≤ (8932098413063/20000000000000 : ℝ)^6333
        have hw : |(5438372903/10000000000 : ℝ)|=(5438372903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273643579/10000000000 : ℝ)|^8381 ≤ (2679942413487/6250000000000 : ℝ)^6333
        have hw : |(5273643579/10000000000 : ℝ)|=(5273643579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_13 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368374963/10000000000 : ℝ)*x 0 + (-433499641/2000000000 : ℝ)*x 1 + (2636821297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368374963/10000000000 : ℝ)^8381 ≤ (10975339400567/25000000000000 : ℝ)^6333 := by
    have hnat : (5368374963 : ℕ)^8381*25000000000000^6333 ≤ 10975339400567^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368374963 10000000000 10975339400567 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433499641/2000000000 : ℝ)^8381 ≤ (13219574377317/100000000000000 : ℝ)^6333 := by
    have hnat : (433499641 : ℕ)^8381*100000000000000^6333 ≤ 13219574377317^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433499641 2000000000 13219574377317 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636821297/5000000000 : ℝ)^8381 ≤ (42879068016979/100000000000000 : ℝ)^6333 := by
    have hnat : (2636821297 : ℕ)^8381*100000000000000^6333 ≤ 42879068016979^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636821297 5000000000 42879068016979 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368374963/10000000000 : ℝ), (-433499641/2000000000 : ℝ), (2636821297/5000000000 : ℝ)] ![(10975339400567/25000000000000 : ℝ), (13219574377317/100000000000000 : ℝ), (42879068016979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368374963/10000000000 : ℝ)|^8381 ≤ (10975339400567/25000000000000 : ℝ)^6333
        have hw : |(5368374963/10000000000 : ℝ)|=(5368374963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433499641/2000000000 : ℝ)|^8381 ≤ (13219574377317/100000000000000 : ℝ)^6333
        have hw : |(-433499641/2000000000 : ℝ)|=(433499641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636821297/5000000000 : ℝ)|^8381 ≤ (42879068016979/100000000000000 : ℝ)^6333
        have hw : |(2636821297/5000000000 : ℝ)|=(2636821297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_14 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368374751/10000000000 : ℝ)*x 0 + (5273642427/10000000000 : ℝ)*x 1 + (-216749871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368374751/10000000000 : ℝ)^8381 ≤ (4390135530793/10000000000000 : ℝ)^6333 := by
    have hnat : (5368374751 : ℕ)^8381*10000000000000^6333 ≤ 4390135530793^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368374751 10000000000 4390135530793 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273642427/10000000000 : ℝ)^8381 ≤ (21439533110011/50000000000000 : ℝ)^6333 := by
    have hnat : (5273642427 : ℕ)^8381*50000000000000^6333 ≤ 21439533110011^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273642427 10000000000 21439533110011 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216749871/1000000000 : ℝ)^8381 ≤ (13219578453339/100000000000000 : ℝ)^6333 := by
    have hnat : (216749871 : ℕ)^8381*100000000000000^6333 ≤ 13219578453339^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216749871 1000000000 13219578453339 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368374751/10000000000 : ℝ), (5273642427/10000000000 : ℝ), (-216749871/1000000000 : ℝ)] ![(4390135530793/10000000000000 : ℝ), (21439533110011/50000000000000 : ℝ), (13219578453339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368374751/10000000000 : ℝ)|^8381 ≤ (4390135530793/10000000000000 : ℝ)^6333
        have hw : |(5368374751/10000000000 : ℝ)|=(5368374751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273642427/10000000000 : ℝ)|^8381 ≤ (21439533110011/50000000000000 : ℝ)^6333
        have hw : |(5273642427/10000000000 : ℝ)|=(5273642427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216749871/1000000000 : ℝ)|^8381 ≤ (13219578453339/100000000000000 : ℝ)^6333
        have hw : |(-216749871/1000000000 : ℝ)|=(216749871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_box_15 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105804129/250000000 : ℝ)*x 0 + (56617/128000 : ℝ)*x 1 + (4423204607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105804129/250000000 : ℝ)^8381 ≤ (32047812550629/100000000000000 : ℝ)^6333 := by
    have hnat : (105804129 : ℕ)^8381*100000000000000^6333 ≤ 32047812550629^6333*250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105804129 250000000 32047812550629 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56617/128000 : ℝ)^8381 ≤ (1698804308991/5000000000000 : ℝ)^6333 := by
    have hnat : (56617 : ℕ)^8381*5000000000000^6333 ≤ 1698804308991^6333*128000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56617 128000 1698804308991 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4423204607/10000000000 : ℝ)^8381 ≤ (16988050622443/50000000000000 : ℝ)^6333 := by
    have hnat : (4423204607 : ℕ)^8381*50000000000000^6333 ≤ 16988050622443^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423204607 10000000000 16988050622443 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105804129/250000000 : ℝ), (56617/128000 : ℝ), (4423204607/10000000000 : ℝ)] ![(32047812550629/100000000000000 : ℝ), (1698804308991/5000000000000 : ℝ), (16988050622443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105804129/250000000 : ℝ)|^8381 ≤ (32047812550629/100000000000000 : ℝ)^6333
        have hw : |(105804129/250000000 : ℝ)|=(105804129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56617/128000 : ℝ)|^8381 ≤ (1698804308991/5000000000000 : ℝ)^6333
        have hw : |(56617/128000 : ℝ)|=(56617/128000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4423204607/10000000000 : ℝ)|^8381 ≤ (16988050622443/50000000000000 : ℝ)^6333
        have hw : |(4423204607/10000000000 : ℝ)|=(4423204607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62237/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29667/50000 : ℝ) ∧ (19987/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83227/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11413/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (13901815420179961/100000000000000000000 : ℝ) := by
    have hpowers : (11413/100000 : ℝ)^2095 ≤ (13901815420179961/100000000000000000000 : ℝ)^512 := by
      have hnat : (11413 : ℕ)^2095*100000000000000000000^512 ≤ 13901815420179961^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11413 100000 13901815420179961 100000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11413/100000 : ℝ)) (X := (13901815420179961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (2095/512 : ℝ) ≤ (16385797486869291/50000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^2095 ≤ (16385797486869291/50000000000000000000 : ℝ)^512 := by
      have hnat : (7037 : ℕ)^2095*50000000000000000000^512 ≤ 16385797486869291^512*50000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 16385797486869291 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (16385797486869291/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013901815420179961/50000000000000000000 : ℝ) ≤ (1000067942548419/1000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (50013901815420179961/50000000000000000000 : ℝ)^512 ≤ (1000067942548419/1000000000000000 : ℝ)^2095 := by
      have hnat : (50013901815420179961 : ℕ)^512*1000000000000000^2095 ≤ 1000067942548419^2095*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013901815420179961 50000000000000000000 1000067942548419 1000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000067942548419/1000000000000000 : ℝ)) (X := (50013901815420179961/50000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046673410393918543/100000000000000000000 : ℝ) ≤ (10001140456966721/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (100046673410393918543/100000000000000000000 : ℝ)^512 ≤ (10001140456966721/10000000000000000 : ℝ)^2095 := by
      have hnat : (100046673410393918543 : ℕ)^512*10000000000000000^2095 ≤ 10001140456966721^2095*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046673410393918543 100000000000000000000 10001140456966721 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001140456966721/10000000000000000 : ℝ)) (X := (100046673410393918543/100000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016385797486869291/25000000000000000000 : ℝ) ≤ (2500400372112313/2500000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25016385797486869291/25000000000000000000 : ℝ)^512 ≤ (2500400372112313/2500000000000000 : ℝ)^2095 := by
      have hnat : (25016385797486869291 : ℕ)^512*2500000000000000^2095 ≤ 2500400372112313^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016385797486869291 25000000000000000000 2500400372112313 2500000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500400372112313/2500000000000000 : ℝ)) (X := (25016385797486869291/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13901815420179961/100000000000000000000 : ℝ) ≤ ((3325160555824147123/3326250000000000000 : ℝ)+2*(461031482531/266100000000000 : ℝ)*(11413/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3325160555824147123/3326250000000000000 : ℝ)+2*(461031482531/266100000000000 : ℝ)*(11413/100000 : ℝ)=(1000067942548419/1000000000000000 : ℝ) by norm_num, show 1+2*(13901815420179961/100000000000000000000 : ℝ)=(50013901815420179961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16385797486869291/50000000000000000000 : ℝ)+(13901815420179961/100000000000000000000 : ℝ) ≤ ((3325160555824147123/3326250000000000000 : ℝ)+(461031482531/266100000000000 : ℝ)*((7037/50000 : ℝ)+(11413/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (3325160555824147123/3326250000000000000 : ℝ)+(461031482531/266100000000000 : ℝ)*((7037/50000 : ℝ)+(11413/100000 : ℝ))=(10001140456966721/10000000000000000 : ℝ) by norm_num, show 1+(16385797486869291/50000000000000000000 : ℝ)+(13901815420179961/100000000000000000000 : ℝ)=(100046673410393918543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16385797486869291/50000000000000000000 : ℝ) ≤ ((3325160555824147123/3326250000000000000 : ℝ)+2*(461031482531/266100000000000 : ℝ)*(7037/50000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (3325160555824147123/3326250000000000000 : ℝ)+2*(461031482531/266100000000000 : ℝ)*(7037/50000 : ℝ)=(2500400372112313/2500000000000000 : ℝ) by norm_num, show 1+2*(16385797486869291/50000000000000000000 : ℝ)=(25016385797486869291/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3325160555824147123/3326250000000000000 : ℝ)*(X 1 0+X 2 0)+(461031482531/266100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (3325160555824147123/3326250000000000000 : ℝ)) (alpha := (461031482531/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3325160555824147123/3326250000000000000 : ℝ)*(X 0 1+X 2 1)+(461031482531/266100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (3325160555824147123/3326250000000000000 : ℝ)) (alpha := (461031482531/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3325160555824147123/3326250000000000000 : ℝ)*(X 0 2+X 1 2)+(461031482531/266100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (3325160555824147123/3326250000000000000 : ℝ)) (alpha := (461031482531/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2019693309/10000000000 : ℝ)*X 0 0+(2687821043/5000000000 : ℝ)*X 0 1+(335977637/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33102427/62500000 : ℝ)*X 1 0+(-2127286369/10000000000 : ℝ)*X 1 1+(5375642203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296387851/10000000000 : ℝ)*X 2 0+(537564257/1000000000 : ℝ)*X 2 1+(-265910813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((893058929/2000000000 : ℝ)*X 0 0+(2153391037/5000000000 : ℝ)*X 0 1+(4306782011/10000000000 : ℝ)*X 0 2+(893058929/2000000000 : ℝ)*X 1 0+(2153391037/5000000000 : ℝ)*X 1 1+(4306782011/10000000000 : ℝ)*X 1 2+(893058929/2000000000 : ℝ)*X 2 0+(2153391037/5000000000 : ℝ)*X 2 1+(4306782011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2271858547/10000000000 : ℝ)*X 0 0+(132042543/250000000 : ℝ)*X 0 1+(2640850689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362688873/10000000000 : ℝ)*X 1 0+(-4227293/19531250 : ℝ)*X 1 1+(5281701479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362688879/10000000000 : ℝ)*X 2 0+(1056340311/2000000000 : ℝ)*X 2 1+(-1082186953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250795269/10000000000 : ℝ)*X 0 0+(4414011243/10000000000 : ℝ)*X 0 1+(882802249/2000000000 : ℝ)*X 0 2+(4250795269/10000000000 : ℝ)*X 1 0+(4414011243/10000000000 : ℝ)*X 1 1+(882802249/2000000000 : ℝ)*X 1 2+(4250795269/10000000000 : ℝ)*X 2 0+(4414011243/10000000000 : ℝ)*X 2 1+(882802249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1109537721/5000000000 : ℝ)*X 0 0+(1304431381/2500000000 : ℝ)*X 0 1+(5385253263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644800813/5000000000 : ℝ)*X 1 0+(-1061712069/5000000000 : ℝ)*X 1 1+(5385253177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289601751/10000000000 : ℝ)*X 2 0+(5385253499/10000000000 : ℝ)*X 2 1+(-424684707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4486966667/10000000000 : ℝ)*X 0 0+(859161079/2000000000 : ℝ)*X 0 1+(4295805627/10000000000 : ℝ)*X 0 2+(4486966667/10000000000 : ℝ)*X 1 0+(859161079/2000000000 : ℝ)*X 1 1+(4295805627/10000000000 : ℝ)*X 1 2+(4486966667/10000000000 : ℝ)*X 2 0+(859161079/2000000000 : ℝ)*X 2 1+(4295805627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1036383757/5000000000 : ℝ)*X 0 0+(5438372903/10000000000 : ℝ)*X 0 1+(5273643579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368374963/10000000000 : ℝ)*X 1 0+(-433499641/2000000000 : ℝ)*X 1 1+(2636821297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368374751/10000000000 : ℝ)*X 2 0+(5273642427/10000000000 : ℝ)*X 2 1+(-216749871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((105804129/250000000 : ℝ)*X 0 0+(56617/128000 : ℝ)*X 0 1+(4423204607/10000000000 : ℝ)*X 0 2+(105804129/250000000 : ℝ)*X 1 0+(56617/128000 : ℝ)*X 1 1+(4423204607/10000000000 : ℝ)*X 1 2+(105804129/250000000 : ℝ)*X 2 0+(56617/128000 : ℝ)*X 2 1+(4423204607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62237/100000 : ℝ) ≤ (-17250691681356963221774590944273/27718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5370751/25000000000000 : ℝ)*(upper0) + (20618723/100000000000000 : ℝ)*(lower2) + (31606007/100000000000000 : ℝ)*(upper4) + (4987341/50000000000000 : ℝ)*(upper5) + (1979460361226517/50000000000000 : ℝ)*(major0) + (1979460361226517/50000000000000 : ℝ)*(major1) + (1979460361226517/50000000000000 : ℝ)*(major2) + (7396805313/100000000000000 : ℝ)*(sp1) + (6521504801/100000000000000 : ℝ)*(sp3) + (5305823424096387/100000000000000 : ℝ)*(sp4) + (1326456978160801/25000000000000 : ℝ)*(sp5) + (5305835309448517/100000000000000 : ℝ)*(sp6) + (2632744526910401/100000000000000 : ℝ)*(sp7) + (1188535213/10000000000000 : ℝ)*(sp8) + (1316375524207601/50000000000000 : ℝ)*(f.failure) + (5305835309448517/100000000000000 : ℝ)*(f.sum) + (17731417794243/4435000000000000000000000000 : ℝ)*base65 + (1077858042383295197/55437500000000000000000000000000 : ℝ)*base67 + (719882135834232697/55437500000000000000000000000000 : ℝ)*base69 + (623244526174357697/55437500000000000000000000000000 : ℝ)*base71 + (4815129835921/2217500000000000000000000000 : ℝ)*base74 + (958579280960920197/55437500000000000000000000000000 : ℝ)*base75 + (925826326648295197/55437500000000000000000000000000 : ℝ)*base77 + (449258207431732697/55437500000000000000000000000000 : ℝ)*base79 + (2322096523/69296875000000000000000000 : ℝ)*base82 + (7984197/1250000000000000000000 : ℝ)*base90 + (7984197/1250000000000000000000 : ℝ)*base92 + (7984197/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29667/50000 : ℝ) ≤ (4111862317415489006177732758893/6929687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (58479421/50000000000000 : ℝ)*(lower0) + (10560637/10000000000000 : ℝ)*(upper2) + (19122963/20000000000000 : ℝ)*(lower4) + (1005958143292393/25000000000000 : ℝ)*(major0) + (1005958143292393/25000000000000 : ℝ)*(major1) + (1005958143292393/25000000000000 : ℝ)*(major2) + (2675981817503631/50000000000000 : ℝ)*(sp0) + (2675981333240579/50000000000000 : ℝ)*(sp1) + (267597757870897/5000000000000 : ℝ)*(sp2) + (668977661415841/25000000000000 : ℝ)*(sp3) + (2476869341/50000000000000 : ℝ)*(sp5) + (12462801901/100000000000000 : ℝ)*(sp6) + (1582204457/20000000000000 : ℝ)*(sp7) + (3985212579/100000000000000 : ℝ)*(sp12) + (53518371133713/2000000000000 : ℝ)*(f.failure) + (16724898813187/312500000000 : ℝ)*(f.sum) + (226086048204973/13305000000000000000000000000 : ℝ)*base66 + (1029886306267272839/83156250000000000000000000000000 : ℝ)*base67 + (213412024359335339/83156250000000000000000000000000 : ℝ)*base69 + (1577058208835570911/83156250000000000000000000000000 : ℝ)*base72 + (78154356227747/13305000000000000000000000000 : ℝ)*base73 + (569234025177241589/83156250000000000000000000000000 : ℝ)*base75 + (2007462150527852161/83156250000000000000000000000000 : ℝ)*base78 + (459169455040835339/83156250000000000000000000000000 : ℝ)*base79 + (55432106685017/13305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (210139/50000000000000000000 : ℝ)*base89 + (210139/50000000000000000000 : ℝ)*base91 + (210139/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19987/25000 : ℝ) ≤ (44322506493542739604501362587673/55437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28086593/100000000000000 : ℝ)*(upper0) + (19143601/20000000000000 : ℝ)*(lower1) + (36278049/20000000000000 : ℝ)*(lower3) + (292502943/100000000000000 : ℝ)*(upper4) + (4491310307722383/100000000000000 : ℝ)*(major0) + (4491310307722383/100000000000000 : ℝ)*(major1) + (4491310307722383/100000000000000 : ℝ)*(major2) + (35727251327/100000000000000 : ℝ)*(sp1) + (14272427269/4000000000000 : ℝ)*(sp2) + (63533625957/50000000000000 : ℝ)*(sp3) + (1193834221915707/20000000000000 : ℝ)*(sp8) + (746141922790901/12500000000000 : ℝ)*(sp9) + (596881429889681/10000000000000 : ℝ)*(sp10) + (1493336151590193/50000000000000 : ℝ)*(sp11) + (29867993704323/1000000000000 : ℝ)*(f.failure) + (1193834221915707/20000000000000 : ℝ)*(f.sum) + (7553299111279/4435000000000000000000000000 : ℝ)*base66 + (925668603599522203/110875000000000000000000000000000 : ℝ)*base67 + (513683565581397203/110875000000000000000000000000000 : ℝ)*base69 + (1291341516789772203/110875000000000000000000000000000 : ℝ)*base71 + (11485943440663/2217500000000000000000000000 : ℝ)*base73 + (404917020905897203/110875000000000000000000000000000 : ℝ)*base75 + (877345749337397203/110875000000000000000000000000000 : ℝ)*base77 + (1305809739012022203/110875000000000000000000000000000 : ℝ)*base79 + (36564549162019/4435000000000000000000000000 : ℝ)*base82 + (98031/25000000000000000000 : ℝ)*base90 + (98031/25000000000000000000 : ℝ)*base92 + (98031/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83227/100000 : ℝ) ≤ (-4613751798320457832789970682231/5543750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96051639/100000000000000 : ℝ)*(lower1) + (78225449/50000000000000 : ℝ)*(lower3) + (232429517/50000000000000 : ℝ)*(lower4) + (17955851/25000000000000 : ℝ)*(upper5) + (905305841931947/20000000000000 : ℝ)*(major0) + (905305841931947/20000000000000 : ℝ)*(major1) + (905305841931947/20000000000000 : ℝ)*(major2) + (333515622903/50000000000000 : ℝ)*(sp5) + (1258281441959/100000000000000 : ℝ)*(sp6) + (6621790663/5000000000000 : ℝ)*(sp7) + (24282317314913/400000000000 : ℝ)*(sp12) + (1517478074370611/25000000000000 : ℝ)*(sp13) + (1517330261821573/25000000000000 : ℝ)*(sp14) + (120403524646933/4000000000000 : ℝ)*(sp15) + (1505110275993293/50000000000000 : ℝ)*(f.failure) + (24282317314913/400000000000 : ℝ)*(f.sum) + (7061969414017/2661000000000000000000000000 : ℝ)*base65 + (928610640133675981/66525000000000000000000000000000 : ℝ)*base67 + (831118840049425981/66525000000000000000000000000000 : ℝ)*base69 + (954544906126300981/66525000000000000000000000000000 : ℝ)*base71 + (2783473474943/665250000000000000000000000 : ℝ)*base74 + (2665432502942074019/66525000000000000000000000000000 : ℝ)*base76 + (609365238740725981/66525000000000000000000000000000 : ℝ)*base77 + (865501886550700981/66525000000000000000000000000000 : ℝ)*base79 + (57347996221151/665250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4228879/1250000000000000000000 : ℝ)*base89 + (4228879/1250000000000000000000 : ℝ)*base91 + (4228879/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1188_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29667/50000 : ℝ) else (19987/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83227/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1188_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1188_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29667/50000 : ℝ) else (19987/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83227/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1188_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1188_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29667/50000 : ℝ) else (19987/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83227/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

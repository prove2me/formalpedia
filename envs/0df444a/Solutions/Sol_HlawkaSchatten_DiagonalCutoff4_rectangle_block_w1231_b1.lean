-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1231_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:58.048389+00:00
-- url     : https://prove2.me/submissions/82e7bcd6-aaf6-48ef-901a-bd84a320362e

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
theorem support_rectangle_w1231_s3_0 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061050497/5000000000 : ℝ)*x 0 + (2710317103/5000000000 : ℝ)*x 1 + (5239758933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061050497/5000000000 : ℝ)^1053 ≤ (2579587467771/20000000000000 : ℝ)^797 := by
    have hnat : (1061050497 : ℕ)^1053*20000000000000^797 ≤ 2579587467771^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061050497 5000000000 2579587467771 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710317103/5000000000 : ℝ)^1053 ≤ (11131810413767/25000000000000 : ℝ)^797 := by
    have hnat : (2710317103 : ℕ)^1053*25000000000000^797 ≤ 11131810413767^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710317103 5000000000 11131810413767 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239758933/10000000000 : ℝ)^1053 ≤ (42574820990659/100000000000000 : ℝ)^797 := by
    have hnat : (5239758933 : ℕ)^1053*100000000000000^797 ≤ 42574820990659^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239758933 10000000000 42574820990659 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061050497/5000000000 : ℝ), (2710317103/5000000000 : ℝ), (5239758933/10000000000 : ℝ)] ![(2579587467771/20000000000000 : ℝ), (11131810413767/25000000000000 : ℝ), (42574820990659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061050497/5000000000 : ℝ)|^1053 ≤ (2579587467771/20000000000000 : ℝ)^797
        have hw : |(-1061050497/5000000000 : ℝ)|=(1061050497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710317103/5000000000 : ℝ)|^1053 ≤ (11131810413767/25000000000000 : ℝ)^797
        have hw : |(2710317103/5000000000 : ℝ)|=(2710317103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239758933/10000000000 : ℝ)|^1053 ≤ (42574820990659/100000000000000 : ℝ)^797
        have hw : |(5239758933/10000000000 : ℝ)|=(5239758933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_1 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675867083/5000000000 : ℝ)*x 0 + (-442878263/2000000000 : ℝ)*x 1 + (5239759101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675867083/5000000000 : ℝ)^1053 ≤ (21890503695671/50000000000000 : ℝ)^797 := by
    have hnat : (2675867083 : ℕ)^1053*50000000000000^797 ≤ 21890503695671^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675867083 5000000000 21890503695671 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442878263/2000000000 : ℝ)^1053 ≤ (6822084899319/50000000000000 : ℝ)^797 := by
    have hnat : (442878263 : ℕ)^1053*50000000000000^797 ≤ 6822084899319^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442878263 2000000000 6822084899319 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239759101/10000000000 : ℝ)^1053 ≤ (42574822794179/100000000000000 : ℝ)^797 := by
    have hnat : (5239759101 : ℕ)^1053*100000000000000^797 ≤ 42574822794179^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239759101 10000000000 42574822794179 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675867083/5000000000 : ℝ), (-442878263/2000000000 : ℝ), (5239759101/10000000000 : ℝ)] ![(21890503695671/50000000000000 : ℝ), (6822084899319/50000000000000 : ℝ), (42574822794179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675867083/5000000000 : ℝ)|^1053 ≤ (21890503695671/50000000000000 : ℝ)^797
        have hw : |(2675867083/5000000000 : ℝ)|=(2675867083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442878263/2000000000 : ℝ)|^1053 ≤ (6822084899319/50000000000000 : ℝ)^797
        have hw : |(-442878263/2000000000 : ℝ)|=(442878263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239759101/10000000000 : ℝ)|^1053 ≤ (42574822794179/100000000000000 : ℝ)^797
        have hw : |(5239759101/10000000000 : ℝ)|=(5239759101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_2 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351734053/10000000000 : ℝ)*x 0 + (5239759509/10000000000 : ℝ)*x 1 + (-2214390927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351734053/10000000000 : ℝ)^1053 ≤ (21890503084997/50000000000000 : ℝ)^797 := by
    have hnat : (5351734053 : ℕ)^1053*50000000000000^797 ≤ 21890503084997^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351734053 10000000000 21890503084997 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239759509/10000000000 : ℝ)^1053 ≤ (8514965434831/20000000000000 : ℝ)^797 := by
    have hnat : (5239759509 : ℕ)^1053*20000000000000^797 ≤ 8514965434831^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239759509 10000000000 8514965434831 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214390927/10000000000 : ℝ)^1053 ≤ (13644166640039/100000000000000 : ℝ)^797 := by
    have hnat : (2214390927 : ℕ)^1053*100000000000000^797 ≤ 13644166640039^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214390927 10000000000 13644166640039 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351734053/10000000000 : ℝ), (5239759509/10000000000 : ℝ), (-2214390927/10000000000 : ℝ)] ![(21890503084997/50000000000000 : ℝ), (8514965434831/20000000000000 : ℝ), (13644166640039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351734053/10000000000 : ℝ)|^1053 ≤ (21890503084997/50000000000000 : ℝ)^797
        have hw : |(5351734053/10000000000 : ℝ)|=(5351734053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239759509/10000000000 : ℝ)|^1053 ≤ (8514965434831/20000000000000 : ℝ)^797
        have hw : |(5239759509/10000000000 : ℝ)|=(5239759509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214390927/10000000000 : ℝ)|^1053 ≤ (13644166640039/100000000000000 : ℝ)^797
        have hw : |(-2214390927/10000000000 : ℝ)|=(2214390927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_3 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1087632763/2500000000 : ℝ)*x 0 + (208560629/500000000 : ℝ)*x 1 + (4537350441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087632763/2500000000 : ℝ)^1053 ≤ (1040615857901/3125000000000 : ℝ)^797 := by
    have hnat : (1087632763 : ℕ)^1053*3125000000000^797 ≤ 1040615857901^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087632763 2500000000 1040615857901 3125000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208560629/500000000 : ℝ)^1053 ≤ (3937303380581/12500000000000 : ℝ)^797 := by
    have hnat : (208560629 : ℕ)^1053*12500000000000^797 ≤ 3937303380581^797*500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208560629 500000000 3937303380581 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537350441/10000000000 : ℝ)^1053 ≤ (704037309893/2000000000000 : ℝ)^797 := by
    have hnat : (4537350441 : ℕ)^1053*2000000000000^797 ≤ 704037309893^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537350441 10000000000 704037309893 2000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087632763/2500000000 : ℝ), (208560629/500000000 : ℝ), (4537350441/10000000000 : ℝ)] ![(1040615857901/3125000000000 : ℝ), (3937303380581/12500000000000 : ℝ), (704037309893/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087632763/2500000000 : ℝ)|^1053 ≤ (1040615857901/3125000000000 : ℝ)^797
        have hw : |(1087632763/2500000000 : ℝ)|=(1087632763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208560629/500000000 : ℝ)|^1053 ≤ (3937303380581/12500000000000 : ℝ)^797
        have hw : |(208560629/500000000 : ℝ)|=(208560629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537350441/10000000000 : ℝ)|^1053 ≤ (704037309893/2000000000000 : ℝ)^797
        have hw : |(4537350441/10000000000 : ℝ)|=(4537350441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_4 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-265264457/1250000000 : ℝ)*x 0 + (1048084181/2000000000 : ℝ)*x 1 + (677496067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265264457/1250000000 : ℝ)^1053 ≤ (12898055077209/100000000000000 : ℝ)^797 := by
    have hnat : (265264457 : ℕ)^1053*100000000000000^797 ≤ 12898055077209^797*1250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265264457 1250000000 12898055077209 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048084181/2000000000 : ℝ)^1053 ≤ (42581927560119/100000000000000 : ℝ)^797 := by
    have hnat : (1048084181 : ℕ)^1053*100000000000000^797 ≤ 42581927560119^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048084181 2000000000 42581927560119 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677496067/1250000000 : ℝ)^1053 ≤ (44520017348617/100000000000000 : ℝ)^797 := by
    have hnat : (677496067 : ℕ)^1053*100000000000000^797 ≤ 44520017348617^797*1250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677496067 1250000000 44520017348617 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265264457/1250000000 : ℝ), (1048084181/2000000000 : ℝ), (677496067/1250000000 : ℝ)] ![(12898055077209/100000000000000 : ℝ), (42581927560119/100000000000000 : ℝ), (44520017348617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265264457/1250000000 : ℝ)|^1053 ≤ (12898055077209/100000000000000 : ℝ)^797
        have hw : |(-265264457/1250000000 : ℝ)|=(265264457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048084181/2000000000 : ℝ)|^1053 ≤ (42581927560119/100000000000000 : ℝ)^797
        have hw : |(1048084181/2000000000 : ℝ)|=(1048084181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677496067/1250000000 : ℝ)|^1053 ≤ (44520017348617/100000000000000 : ℝ)^797
        have hw : |(677496067/1250000000 : ℝ)|=(677496067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_5 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061124657/2000000000 : ℝ)*x 0 + (-203418119/1000000000 : ℝ)*x 1 + (677496059/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061124657/2000000000 : ℝ)^1053 ≤ (5410414212653/12500000000000 : ℝ)^797 := by
    have hnat : (1061124657 : ℕ)^1053*12500000000000^797 ≤ 5410414212653^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061124657 2000000000 5410414212653 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203418119/1000000000 : ℝ)^1053 ≤ (12196669638797/100000000000000 : ℝ)^797 := by
    have hnat : (203418119 : ℕ)^1053*100000000000000^797 ≤ 12196669638797^797*1000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203418119 1000000000 12196669638797 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677496059/1250000000 : ℝ)^1053 ≤ (22260008327029/50000000000000 : ℝ)^797 := by
    have hnat : (677496059 : ℕ)^1053*50000000000000^797 ≤ 22260008327029^797*1250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677496059 1250000000 22260008327029 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061124657/2000000000 : ℝ), (-203418119/1000000000 : ℝ), (677496059/1250000000 : ℝ)] ![(5410414212653/12500000000000 : ℝ), (12196669638797/100000000000000 : ℝ), (22260008327029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061124657/2000000000 : ℝ)|^1053 ≤ (5410414212653/12500000000000 : ℝ)^797
        have hw : |(1061124657/2000000000 : ℝ)|=(1061124657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203418119/1000000000 : ℝ)|^1053 ≤ (12196669638797/100000000000000 : ℝ)^797
        have hw : |(-203418119/1000000000 : ℝ)|=(203418119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677496059/1250000000 : ℝ)|^1053 ≤ (22260008327029/50000000000000 : ℝ)^797
        have hw : |(677496059/1250000000 : ℝ)|=(677496059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_6 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305622249/10000000000 : ℝ)*x 0 + (2709984401/5000000000 : ℝ)*x 1 + (-508545537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305622249/10000000000 : ℝ)^1053 ≤ (21641651267403/50000000000000 : ℝ)^797 := by
    have hnat : (5305622249 : ℕ)^1053*50000000000000^797 ≤ 21641651267403^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305622249 10000000000 21641651267403 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709984401/5000000000 : ℝ)^1053 ≤ (22260010117687/50000000000000 : ℝ)^797 := by
    have hnat : (2709984401 : ℕ)^1053*50000000000000^797 ≤ 22260010117687^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709984401 5000000000 22260010117687 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508545537/2500000000 : ℝ)^1053 ≤ (3049169306961/25000000000000 : ℝ)^797 := by
    have hnat : (508545537 : ℕ)^1053*25000000000000^797 ≤ 3049169306961^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508545537 2500000000 3049169306961 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305622249/10000000000 : ℝ), (2709984401/5000000000 : ℝ), (-508545537/2500000000 : ℝ)] ![(21641651267403/50000000000000 : ℝ), (22260010117687/50000000000000 : ℝ), (3049169306961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305622249/10000000000 : ℝ)|^1053 ≤ (21641651267403/50000000000000 : ℝ)^797
        have hw : |(5305622249/10000000000 : ℝ)|=(5305622249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709984401/5000000000 : ℝ)|^1053 ≤ (22260010117687/50000000000000 : ℝ)^797
        have hw : |(2709984401/5000000000 : ℝ)|=(2709984401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508545537/2500000000 : ℝ)|^1053 ≤ (3049169306961/25000000000000 : ℝ)^797
        have hw : |(-508545537/2500000000 : ℝ)|=(508545537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s3_7 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2175280237/5000000000 : ℝ)*x 0 + (4536010257/10000000000 : ℝ)*x 1 + (2086279759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175280237/5000000000 : ℝ)^1053 ≤ (8325001247437/25000000000000 : ℝ)^797 := by
    have hnat : (2175280237 : ℕ)^1053*25000000000000^797 ≤ 8325001247437^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175280237 5000000000 8325001247437 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4536010257/10000000000 : ℝ)^1053 ≤ (3518812895857/10000000000000 : ℝ)^797 := by
    have hnat : (4536010257 : ℕ)^1053*10000000000000^797 ≤ 3518812895857^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536010257 10000000000 3518812895857 10000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086279759/5000000000 : ℝ)^1053 ≤ (15755933018687/50000000000000 : ℝ)^797 := by
    have hnat : (2086279759 : ℕ)^1053*50000000000000^797 ≤ 15755933018687^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086279759 5000000000 15755933018687 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175280237/5000000000 : ℝ), (4536010257/10000000000 : ℝ), (2086279759/5000000000 : ℝ)] ![(8325001247437/25000000000000 : ℝ), (3518812895857/10000000000000 : ℝ), (15755933018687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175280237/5000000000 : ℝ)|^1053 ≤ (8325001247437/25000000000000 : ℝ)^797
        have hw : |(2175280237/5000000000 : ℝ)|=(2175280237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4536010257/10000000000 : ℝ)|^1053 ≤ (3518812895857/10000000000000 : ℝ)^797
        have hw : |(4536010257/10000000000 : ℝ)|=(4536010257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086279759/5000000000 : ℝ)|^1053 ≤ (15755933018687/50000000000000 : ℝ)^797
        have hw : |(2086279759/5000000000 : ℝ)|=(2086279759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1231_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10883/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4727/50000 : ℝ) ^ (8423/2048 : ℝ) ≤ (6122362412354593/100000000000000000000 : ℝ) := by
    have hpowers : (4727/50000 : ℝ)^8423 ≤ (6122362412354593/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4727 : ℕ)^8423*100000000000000000000^2048 ≤ 6122362412354593^2048*50000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4727 50000 6122362412354593 100000000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4727/50000 : ℝ)) (X := (6122362412354593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4063/25000 : ℝ) ^ (8423/2048 : ℝ) ≤ (56835945810101227/100000000000000000000 : ℝ) := by
    have hpowers : (4063/25000 : ℝ)^8423 ≤ (56835945810101227/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4063 : ℕ)^8423*100000000000000000000^2048 ≤ 56835945810101227^2048*25000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4063 25000 56835945810101227 100000000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4063/25000 : ℝ)) (X := (56835945810101227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006122362412354593/50000000000000000000 : ℝ) ≤ (2500074427266147/2500000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (50006122362412354593/50000000000000000000 : ℝ)^2048 ≤ (2500074427266147/2500000000000000 : ℝ)^8423 := by
      have hnat : (50006122362412354593 : ℕ)^2048*2500000000000000^8423 ≤ 2500074427266147^8423*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006122362412354593 50000000000000000000 2500074427266147 2500000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074427266147/2500000000000000 : ℝ)) (X := (50006122362412354593/50000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5003147915411122791/5000000000000000000 : ℝ) ≤ (5000765213740271/5000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (5003147915411122791/5000000000000000000 : ℝ)^2048 ≤ (5000765213740271/5000000000000000 : ℝ)^8423 := by
      have hnat : (5003147915411122791 : ℕ)^2048*5000000000000000^8423 ≤ 5000765213740271^8423*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003147915411122791 5000000000000000000 5000765213740271 5000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000765213740271/5000000000000000 : ℝ)) (X := (5003147915411122791/5000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50056835945810101227/50000000000000000000 : ℝ) ≤ (625172696618531/625000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (50056835945810101227/50000000000000000000 : ℝ)^2048 ≤ (625172696618531/625000000000000 : ℝ)^8423 := by
      have hnat : (50056835945810101227 : ℕ)^2048*625000000000000^8423 ≤ 625172696618531^8423*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056835945810101227 50000000000000000000 625172696618531 625000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625172696618531/625000000000000 : ℝ)) (X := (50056835945810101227/50000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6122362412354593/100000000000000000000 : ℝ) ≤ ((4247419724150763187/4248750000000000000 : ℝ)+2*(616359207977/339900000000000 : ℝ)*(4727/50000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (4247419724150763187/4248750000000000000 : ℝ)+2*(616359207977/339900000000000 : ℝ)*(4727/50000 : ℝ)=(2500074427266147/2500000000000000 : ℝ) by norm_num, show 1+2*(6122362412354593/100000000000000000000 : ℝ)=(50006122362412354593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56835945810101227/100000000000000000000 : ℝ)+(6122362412354593/100000000000000000000 : ℝ) ≤ ((4247419724150763187/4248750000000000000 : ℝ)+(616359207977/339900000000000 : ℝ)*((4063/25000 : ℝ)+(4727/50000 : ℝ)))^(8423/2048 : ℝ) := by
    rw [show (4247419724150763187/4248750000000000000 : ℝ)+(616359207977/339900000000000 : ℝ)*((4063/25000 : ℝ)+(4727/50000 : ℝ))=(5000765213740271/5000000000000000 : ℝ) by norm_num, show 1+(56835945810101227/100000000000000000000 : ℝ)+(6122362412354593/100000000000000000000 : ℝ)=(5003147915411122791/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56835945810101227/100000000000000000000 : ℝ) ≤ ((4247419724150763187/4248750000000000000 : ℝ)+2*(616359207977/339900000000000 : ℝ)*(4063/25000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (4247419724150763187/4248750000000000000 : ℝ)+2*(616359207977/339900000000000 : ℝ)*(4063/25000 : ℝ)=(625172696618531/625000000000000 : ℝ) by norm_num, show 1+2*(56835945810101227/100000000000000000000 : ℝ)=(50056835945810101227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4247419724150763187/4248750000000000000 : ℝ)*(X 1 0+X 2 0)+(616359207977/339900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (4727/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (4247419724150763187/4248750000000000000 : ℝ)) (alpha := (616359207977/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4247419724150763187/4248750000000000000 : ℝ)*(X 0 1+X 2 1)+(616359207977/339900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (4727/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (4247419724150763187/4248750000000000000 : ℝ)) (alpha := (616359207977/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4247419724150763187/4248750000000000000 : ℝ)*(X 0 2+X 1 2)+(616359207977/339900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (4727/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (4247419724150763187/4248750000000000000 : ℝ)) (alpha := (616359207977/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061050497/5000000000 : ℝ)*X 0 0+(2710317103/5000000000 : ℝ)*X 0 1+(5239758933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675867083/5000000000 : ℝ)*X 1 0+(-442878263/2000000000 : ℝ)*X 1 1+(5239759101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351734053/10000000000 : ℝ)*X 2 0+(5239759509/10000000000 : ℝ)*X 2 1+(-2214390927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087632763/2500000000 : ℝ)*X 0 0+(208560629/500000000 : ℝ)*X 0 1+(4537350441/10000000000 : ℝ)*X 0 2+(1087632763/2500000000 : ℝ)*X 1 0+(208560629/500000000 : ℝ)*X 1 1+(4537350441/10000000000 : ℝ)*X 1 2+(1087632763/2500000000 : ℝ)*X 2 0+(208560629/500000000 : ℝ)*X 2 1+(4537350441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-265264457/1250000000 : ℝ)*X 0 0+(1048084181/2000000000 : ℝ)*X 0 1+(677496067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061124657/2000000000 : ℝ)*X 1 0+(-203418119/1000000000 : ℝ)*X 1 1+(677496059/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305622249/10000000000 : ℝ)*X 2 0+(2709984401/5000000000 : ℝ)*X 2 1+(-508545537/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175280237/5000000000 : ℝ)*X 0 0+(4536010257/10000000000 : ℝ)*X 0 1+(2086279759/5000000000 : ℝ)*X 0 2+(2175280237/5000000000 : ℝ)*X 1 0+(4536010257/10000000000 : ℝ)*X 1 1+(2086279759/5000000000 : ℝ)*X 1 2+(2175280237/5000000000 : ℝ)*X 2 0+(4536010257/10000000000 : ℝ)*X 2 1+(2086279759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27456300154300723887818487/7081250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144670037/50000000000000 : ℝ)*(base19) + (63385047/50000000000000 : ℝ)*(lower2) + (35940553/100000000000000 : ℝ)*(lower3) + (6622693/100000000000000 : ℝ)*(lower4) + (412996586095651/10000000000000 : ℝ)*(major0) + (412996586095651/10000000000000 : ℝ)*(major1) + (412996586095651/10000000000000 : ℝ)*(major2) + (5528689213135891/100000000000000 : ℝ)*(sp0) + (1105740743043087/20000000000000 : ℝ)*(sp1) + (276435501400801/5000000000000 : ℝ)*(sp2) + (682804129790603/25000000000000 : ℝ)*(sp3) + (20814880129/100000000000000 : ℝ)*(sp4) + (6023460511/100000000000000 : ℝ)*(sp5) + (1261372613/25000000000000 : ℝ)*(sp7) + (42675336947701/1562500000000 : ℝ)*(f.failure) + (276435501400801/5000000000000 : ℝ)*(f.sum) + (835747194553/212437500000000000000000000 : ℝ)*base65 + (23188448830715933/3862500000000000000000000000000 : ℝ)*base68 + (41805692435034067/3862500000000000000000000000000 : ℝ)*base69 + (22925679487190933/3862500000000000000000000000000 : ℝ)*base72 + (6589480040537/3399000000000000000000000000 : ℝ)*base74 + (12547977978965933/3862500000000000000000000000000 : ℝ)*base76 + (26190340907371567/3862500000000000000000000000000 : ℝ)*base77 + (18699257776978433/3862500000000000000000000000000 : ℝ)*base80 + (3205892333929/1699500000000000000000000000 : ℝ)*base82 + (168439/156250000000000000000 : ℝ)*base89 + (168439/156250000000000000000 : ℝ)*base91 + (168439/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110915438145860566288473163/17703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206124923/10000000000000 : ℝ)*(base19) + (397805419/50000000000000 : ℝ)*(base23) + (25888923/50000000000000 : ℝ)*(upper3) + (4008433/5000000000000 : ℝ)*(lower4) + (255694441/100000000000000 : ℝ)*(upper5) + (520059015298231/12500000000000 : ℝ)*(major0) + (520059015298231/12500000000000 : ℝ)*(major1) + (520059015298231/12500000000000 : ℝ)*(major2) + (11883894911/25000000000000 : ℝ)*(sp1) + (9656342207/100000000000000 : ℝ)*(sp2) + (1113909625111951/20000000000000 : ℝ)*(sp4) + (5569498528730881/100000000000000 : ℝ)*(sp5) + (556953767360671/10000000000000 : ℝ)*(sp6) + (687848977592127/25000000000000 : ℝ)*(sp7) + (687848977592127/25000000000000 : ℝ)*(f.failure) + (1113909625111951/20000000000000 : ℝ)*(f.sum) + (7911020068993/2124375000000000000000000000 : ℝ)*base66 + (1552981793222389/150878906250000000000000000000 : ℝ)*base68 + (29803219103805427/4828125000000000000000000000000 : ℝ)*base69 + (20678547797417599/2414062500000000000000000000000 : ℝ)*base72 + (8198949180487/8497500000000000000000000000 : ℝ)*base74 + (31341388014382073/4828125000000000000000000000000 : ℝ)*base76 + (1688771192323849/2414062500000000000000000000000 : ℝ)*base78 + (4427851095669737/1207031250000000000000000000000 : ℝ)*base80 + (44294239985371/16995000000000000000000000000 : ℝ)*base81 + (14643347/2500000000000000000000 : ℝ)*base90 + (14643347/2500000000000000000000 : ℝ)*base92 + (14643347/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1231_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10883/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1231_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1231_s4_0 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-531115231/2500000000 : ℝ)*x 0 + (5397941977/10000000000 : ℝ)*x 1 + (131522629/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531115231/2500000000 : ℝ)^1053 ≤ (6458445670469/50000000000000 : ℝ)^797 := by
    have hnat : (531115231 : ℕ)^1053*50000000000000^797 ≤ 6458445670469^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531115231 2500000000 6458445670469 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397941977/10000000000 : ℝ)^1053 ≤ (2767570683243/6250000000000 : ℝ)^797 := by
    have hnat : (5397941977 : ℕ)^1053*6250000000000^797 ≤ 2767570683243^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397941977 10000000000 2767570683243 6250000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131522629/250000000 : ℝ)^1053 ≤ (10700494429411/25000000000000 : ℝ)^797 := by
    have hnat : (131522629 : ℕ)^1053*25000000000000^797 ≤ 10700494429411^797*250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131522629 250000000 10700494429411 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531115231/2500000000 : ℝ), (5397941977/10000000000 : ℝ), (131522629/250000000 : ℝ)] ![(6458445670469/50000000000000 : ℝ), (2767570683243/6250000000000 : ℝ), (10700494429411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531115231/2500000000 : ℝ)|^1053 ≤ (6458445670469/50000000000000 : ℝ)^797
        have hw : |(-531115231/2500000000 : ℝ)|=(531115231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397941977/10000000000 : ℝ)|^1053 ≤ (2767570683243/6250000000000 : ℝ)^797
        have hw : |(5397941977/10000000000 : ℝ)|=(5397941977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131522629/250000000 : ℝ)|^1053 ≤ (10700494429411/25000000000000 : ℝ)^797
        have hw : |(131522629/250000000 : ℝ)|=(131522629/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_1 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336505017/2500000000 : ℝ)*x 0 + (-2194043011/10000000000 : ℝ)*x 1 + (5260905121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336505017/2500000000 : ℝ)^1053 ≤ (21859628873813/50000000000000 : ℝ)^797 := by
    have hnat : (1336505017 : ℕ)^1053*50000000000000^797 ≤ 21859628873813^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336505017 2500000000 21859628873813 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194043011/10000000000 : ℝ)^1053 ≤ (2695752987341/20000000000000 : ℝ)^797 := by
    have hnat : (2194043011 : ℕ)^1053*20000000000000^797 ≤ 2695752987341^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194043011 10000000000 2695752987341 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260905121/10000000000 : ℝ)^1053 ≤ (10700494324607/25000000000000 : ℝ)^797 := by
    have hnat : (5260905121 : ℕ)^1053*25000000000000^797 ≤ 10700494324607^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260905121 10000000000 10700494324607 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336505017/2500000000 : ℝ), (-2194043011/10000000000 : ℝ), (5260905121/10000000000 : ℝ)] ![(21859628873813/50000000000000 : ℝ), (2695752987341/20000000000000 : ℝ), (10700494324607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336505017/2500000000 : ℝ)|^1053 ≤ (21859628873813/50000000000000 : ℝ)^797
        have hw : |(1336505017/2500000000 : ℝ)|=(1336505017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194043011/10000000000 : ℝ)|^1053 ≤ (2695752987341/20000000000000 : ℝ)^797
        have hw : |(-2194043011/10000000000 : ℝ)|=(2194043011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260905121/10000000000 : ℝ)|^1053 ≤ (10700494324607/25000000000000 : ℝ)^797
        have hw : |(5260905121/10000000000 : ℝ)|=(5260905121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_2 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673009981/5000000000 : ℝ)*x 0 + (5260905051/10000000000 : ℝ)*x 1 + (-1097021623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673009981/5000000000 : ℝ)^1053 ≤ (4371925660233/10000000000000 : ℝ)^797 := by
    have hnat : (2673009981 : ℕ)^1053*10000000000000^797 ≤ 4371925660233^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673009981 5000000000 4371925660233 10000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260905051/10000000000 : ℝ)^1053 ≤ (10700494136497/25000000000000 : ℝ)^797 := by
    have hnat : (5260905051 : ℕ)^1053*25000000000000^797 ≤ 10700494136497^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260905051 10000000000 10700494136497 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097021623/5000000000 : ℝ)^1053 ≤ (1347876684411/10000000000000 : ℝ)^797 := by
    have hnat : (1097021623 : ℕ)^1053*10000000000000^797 ≤ 1347876684411^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097021623 5000000000 1347876684411 10000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673009981/5000000000 : ℝ), (5260905051/10000000000 : ℝ), (-1097021623/5000000000 : ℝ)] ![(4371925660233/10000000000000 : ℝ), (10700494136497/25000000000000 : ℝ), (1347876684411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673009981/5000000000 : ℝ)|^1053 ≤ (4371925660233/10000000000000 : ℝ)^797
        have hw : |(2673009981/5000000000 : ℝ)|=(2673009981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260905051/10000000000 : ℝ)|^1053 ≤ (10700494136497/25000000000000 : ℝ)^797
        have hw : |(5260905051/10000000000 : ℝ)|=(5260905051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097021623/5000000000 : ℝ)|^1053 ≤ (1347876684411/10000000000000 : ℝ)^797
        have hw : |(-1097021623/5000000000 : ℝ)|=(1097021623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_3 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2175973323/5000000000 : ℝ)*x 0 + (2107700647/5000000000 : ℝ)*x 1 + (2246399923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175973323/5000000000 : ℝ)^1053 ≤ (16657011856813/50000000000000 : ℝ)^797 := by
    have hnat : (2175973323 : ℕ)^1053*50000000000000^797 ≤ 16657011856813^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175973323 5000000000 16657011856813 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107700647/5000000000 : ℝ)^1053 ≤ (998126334549/3125000000000 : ℝ)^797 := by
    have hnat : (2107700647 : ℕ)^1053*3125000000000^797 ≤ 998126334549^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107700647 5000000000 998126334549 3125000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246399923/5000000000 : ℝ)^1053 ≤ (34745933565759/100000000000000 : ℝ)^797 := by
    have hnat : (2246399923 : ℕ)^1053*100000000000000^797 ≤ 34745933565759^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246399923 5000000000 34745933565759 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175973323/5000000000 : ℝ), (2107700647/5000000000 : ℝ), (2246399923/5000000000 : ℝ)] ![(16657011856813/50000000000000 : ℝ), (998126334549/3125000000000 : ℝ), (34745933565759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175973323/5000000000 : ℝ)|^1053 ≤ (16657011856813/50000000000000 : ℝ)^797
        have hw : |(2175973323/5000000000 : ℝ)|=(2175973323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107700647/5000000000 : ℝ)|^1053 ≤ (998126334549/3125000000000 : ℝ)^797
        have hw : |(2107700647/5000000000 : ℝ)|=(2107700647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246399923/5000000000 : ℝ)|^1053 ≤ (34745933565759/100000000000000 : ℝ)^797
        have hw : |(2246399923/5000000000 : ℝ)|=(2246399923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_4 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-531116747/2500000000 : ℝ)*x 0 + (5261285801/10000000000 : ℝ)*x 1 + (5397559963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531116747/2500000000 : ℝ)^1053 ≤ (2583388010649/20000000000000 : ℝ)^797 := by
    have hnat : (531116747 : ℕ)^1053*20000000000000^797 ≤ 2583388010649^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531116747 2500000000 2583388010649 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261285801/10000000000 : ℝ)^1053 ≤ (21403034662853/50000000000000 : ℝ)^797 := by
    have hnat : (5261285801 : ℕ)^1053*50000000000000^797 ≤ 21403034662853^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261285801 10000000000 21403034662853 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397559963/10000000000 : ℝ)^1053 ≤ (44276990602579/100000000000000 : ℝ)^797 := by
    have hnat : (5397559963 : ℕ)^1053*100000000000000^797 ≤ 44276990602579^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397559963 10000000000 44276990602579 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531116747/2500000000 : ℝ), (5261285801/10000000000 : ℝ), (5397559963/10000000000 : ℝ)] ![(2583388010649/20000000000000 : ℝ), (21403034662853/50000000000000 : ℝ), (44276990602579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531116747/2500000000 : ℝ)|^1053 ≤ (2583388010649/20000000000000 : ℝ)^797
        have hw : |(-531116747/2500000000 : ℝ)|=(531116747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261285801/10000000000 : ℝ)|^1053 ≤ (21403034662853/50000000000000 : ℝ)^797
        have hw : |(5261285801/10000000000 : ℝ)|=(5261285801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397559963/10000000000 : ℝ)|^1053 ≤ (44276990602579/100000000000000 : ℝ)^797
        have hw : |(5397559963/10000000000 : ℝ)|=(5397559963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_5 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (531108217/1000000000 : ℝ)*x 0 + (-514347139/2500000000 : ℝ)*x 1 + (5397559883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531108217/1000000000 : ℝ)^1053 ≤ (8668432289299/20000000000000 : ℝ)^797 := by
    have hnat : (531108217 : ℕ)^1053*20000000000000^797 ≤ 8668432289299^797*1000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531108217 1000000000 8668432289299 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514347139/2500000000 : ℝ)^1053 ≤ (1547606100537/12500000000000 : ℝ)^797 := by
    have hnat : (514347139 : ℕ)^1053*12500000000000^797 ≤ 1547606100537^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514347139 2500000000 1547606100537 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397559883/10000000000 : ℝ)^1053 ≤ (2767311858471/6250000000000 : ℝ)^797 := by
    have hnat : (5397559883 : ℕ)^1053*6250000000000^797 ≤ 2767311858471^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397559883 10000000000 2767311858471 6250000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531108217/1000000000 : ℝ), (-514347139/2500000000 : ℝ), (5397559883/10000000000 : ℝ)] ![(8668432289299/20000000000000 : ℝ), (1547606100537/12500000000000 : ℝ), (2767311858471/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531108217/1000000000 : ℝ)|^1053 ≤ (8668432289299/20000000000000 : ℝ)^797
        have hw : |(531108217/1000000000 : ℝ)|=(531108217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514347139/2500000000 : ℝ)|^1053 ≤ (1547606100537/12500000000000 : ℝ)^797
        have hw : |(-514347139/2500000000 : ℝ)|=(514347139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397559883/10000000000 : ℝ)|^1053 ≤ (2767311858471/6250000000000 : ℝ)^797
        have hw : |(5397559883/10000000000 : ℝ)|=(5397559883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_6 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (16597131/31250000 : ℝ)*x 0 + (2698780137/5000000000 : ℝ)*x 1 + (-1028694181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16597131/31250000 : ℝ)^1053 ≤ (8668431750201/20000000000000 : ℝ)^797 := by
    have hnat : (16597131 : ℕ)^1053*20000000000000^797 ≤ 8668431750201^797*31250000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16597131 31250000 8668431750201 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698780137/5000000000 : ℝ)^1053 ≤ (44276993973209/100000000000000 : ℝ)^797 := by
    have hnat : (2698780137 : ℕ)^1053*100000000000000^797 ≤ 44276993973209^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698780137 5000000000 44276993973209 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028694181/5000000000 : ℝ)^1053 ≤ (1547605907733/12500000000000 : ℝ)^797 := by
    have hnat : (1028694181 : ℕ)^1053*12500000000000^797 ≤ 1547605907733^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028694181 5000000000 1547605907733 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16597131/31250000 : ℝ), (2698780137/5000000000 : ℝ), (-1028694181/5000000000 : ℝ)] ![(8668431750201/20000000000000 : ℝ), (44276993973209/100000000000000 : ℝ), (1547605907733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16597131/31250000 : ℝ)|^1053 ≤ (8668431750201/20000000000000 : ℝ)^797
        have hw : |(16597131/31250000 : ℝ)|=(16597131/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698780137/5000000000 : ℝ)|^1053 ≤ (44276993973209/100000000000000 : ℝ)^797
        have hw : |(2698780137/5000000000 : ℝ)|=(2698780137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028694181/5000000000 : ℝ)|^1053 ≤ (1547605907733/12500000000000 : ℝ)^797
        have hw : |(-1028694181/5000000000 : ℝ)|=(1028694181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s4_7 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2175979743/5000000000 : ℝ)*x 0 + (4492029733/10000000000 : ℝ)*x 1 + (2108087159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175979743/5000000000 : ℝ)^1053 ≤ (16657076787323/50000000000000 : ℝ)^797 := by
    have hnat : (2175979743 : ℕ)^1053*50000000000000^797 ≤ 16657076787323^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175979743 5000000000 16657076787323 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492029733/10000000000 : ℝ)^1053 ≤ (34738064929643/100000000000000 : ℝ)^797 := by
    have hnat : (4492029733 : ℕ)^1053*100000000000000^797 ≤ 34738064929643^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492029733 10000000000 34738064929643 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108087159/5000000000 : ℝ)^1053 ≤ (3993472685439/12500000000000 : ℝ)^797 := by
    have hnat : (2108087159 : ℕ)^1053*12500000000000^797 ≤ 3993472685439^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108087159 5000000000 3993472685439 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175979743/5000000000 : ℝ), (4492029733/10000000000 : ℝ), (2108087159/5000000000 : ℝ)] ![(16657076787323/50000000000000 : ℝ), (34738064929643/100000000000000 : ℝ), (3993472685439/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175979743/5000000000 : ℝ)|^1053 ≤ (16657076787323/50000000000000 : ℝ)^797
        have hw : |(2175979743/5000000000 : ℝ)|=(2175979743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492029733/10000000000 : ℝ)|^1053 ≤ (34738064929643/100000000000000 : ℝ)^797
        have hw : |(4492029733/10000000000 : ℝ)|=(4492029733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108087159/5000000000 : ℝ)|^1053 ≤ (3993472685439/12500000000000 : ℝ)^797
        have hw : |(2108087159/5000000000 : ℝ)|=(2108087159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1231_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10883/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10883/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10883/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10883/100000 : ℝ) ^ (8423/2048 : ℝ) ≤ (136538946596379/1250000000000000000 : ℝ) := by
    have hpowers : (10883/100000 : ℝ)^8423 ≤ (136538946596379/1250000000000000000 : ℝ)^2048 := by
      have hnat : (10883 : ℕ)^8423*1250000000000000000^2048 ≤ 136538946596379^2048*100000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10883 100000 136538946596379 1250000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10883/100000 : ℝ)) (X := (136538946596379/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (8423/2048 : ℝ) ≤ (1179056714291773/3125000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^8423 ≤ (1179056714291773/3125000000000000000 : ℝ)^2048 := by
      have hnat : (14711 : ℕ)^8423*3125000000000000000^2048 ≤ 1179056714291773^2048*100000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 1179056714291773 3125000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (1179056714291773/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (625136538946596379/625000000000000000 : ℝ) ≤ (2500132783401539/2500000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (625136538946596379/625000000000000000 : ℝ)^2048 ≤ (2500132783401539/2500000000000000 : ℝ)^8423 := by
      have hnat : (625136538946596379 : ℕ)^2048*2500000000000000^8423 ≤ 2500132783401539^8423*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625136538946596379 625000000000000000 2500132783401539 2500000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500132783401539/2500000000000000 : ℝ)) (X := (625136538946596379/625000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253040808161565441/6250000000000000000 : ℝ) ≤ (2000236549593939/2000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (6253040808161565441/6250000000000000000 : ℝ)^2048 ≤ (2000236549593939/2000000000000000 : ℝ)^8423 := by
      have hnat : (6253040808161565441 : ℕ)^2048*2000000000000000^8423 ≤ 2000236549593939^8423*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253040808161565441 6250000000000000000 2000236549593939 2000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000236549593939/2000000000000000 : ℝ)) (X := (6253040808161565441/6250000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563679056714291773/1562500000000000000 : ℝ) ≤ (5000917181166617/5000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (1563679056714291773/1562500000000000000 : ℝ)^2048 ≤ (5000917181166617/5000000000000000 : ℝ)^8423 := by
      have hnat : (1563679056714291773 : ℕ)^2048*5000000000000000^8423 ≤ 5000917181166617^8423*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563679056714291773 1562500000000000000 5000917181166617 5000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000917181166617/5000000000000000 : ℝ)) (X := (1563679056714291773/1562500000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(136538946596379/1250000000000000000 : ℝ) ≤ ((19133925070603787647/19140000000000000000 : ℝ)+2*(651614363539/382800000000000 : ℝ)*(10883/100000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (19133925070603787647/19140000000000000000 : ℝ)+2*(651614363539/382800000000000 : ℝ)*(10883/100000 : ℝ)=(2500132783401539/2500000000000000 : ℝ) by norm_num, show 1+2*(136538946596379/1250000000000000000 : ℝ)=(625136538946596379/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1179056714291773/3125000000000000000 : ℝ)+(136538946596379/1250000000000000000 : ℝ) ≤ ((19133925070603787647/19140000000000000000 : ℝ)+(651614363539/382800000000000 : ℝ)*((14711/100000 : ℝ)+(10883/100000 : ℝ)))^(8423/2048 : ℝ) := by
    rw [show (19133925070603787647/19140000000000000000 : ℝ)+(651614363539/382800000000000 : ℝ)*((14711/100000 : ℝ)+(10883/100000 : ℝ))=(2000236549593939/2000000000000000 : ℝ) by norm_num, show 1+(1179056714291773/3125000000000000000 : ℝ)+(136538946596379/1250000000000000000 : ℝ)=(6253040808161565441/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1179056714291773/3125000000000000000 : ℝ) ≤ ((19133925070603787647/19140000000000000000 : ℝ)+2*(651614363539/382800000000000 : ℝ)*(14711/100000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (19133925070603787647/19140000000000000000 : ℝ)+2*(651614363539/382800000000000 : ℝ)*(14711/100000 : ℝ)=(5000917181166617/5000000000000000 : ℝ) by norm_num, show 1+2*(1179056714291773/3125000000000000000 : ℝ)=(1563679056714291773/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19133925070603787647/19140000000000000000 : ℝ)*(X 1 0+X 2 0)+(651614363539/382800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (10883/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (19133925070603787647/19140000000000000000 : ℝ)) (alpha := (651614363539/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19133925070603787647/19140000000000000000 : ℝ)*(X 0 1+X 2 1)+(651614363539/382800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (10883/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (19133925070603787647/19140000000000000000 : ℝ)) (alpha := (651614363539/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19133925070603787647/19140000000000000000 : ℝ)*(X 0 2+X 1 2)+(651614363539/382800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (10883/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (19133925070603787647/19140000000000000000 : ℝ)) (alpha := (651614363539/382800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531115231/2500000000 : ℝ)*X 0 0+(5397941977/10000000000 : ℝ)*X 0 1+(131522629/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336505017/2500000000 : ℝ)*X 1 0+(-2194043011/10000000000 : ℝ)*X 1 1+(5260905121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673009981/5000000000 : ℝ)*X 2 0+(5260905051/10000000000 : ℝ)*X 2 1+(-1097021623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175973323/5000000000 : ℝ)*X 0 0+(2107700647/5000000000 : ℝ)*X 0 1+(2246399923/5000000000 : ℝ)*X 0 2+(2175973323/5000000000 : ℝ)*X 1 0+(2107700647/5000000000 : ℝ)*X 1 1+(2246399923/5000000000 : ℝ)*X 1 2+(2175973323/5000000000 : ℝ)*X 2 0+(2107700647/5000000000 : ℝ)*X 2 1+(2246399923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531116747/2500000000 : ℝ)*X 0 0+(5261285801/10000000000 : ℝ)*X 0 1+(5397559963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531108217/1000000000 : ℝ)*X 1 0+(-514347139/2500000000 : ℝ)*X 1 1+(5397559883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((16597131/31250000 : ℝ)*X 2 0+(2698780137/5000000000 : ℝ)*X 2 1+(-1028694181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175979743/5000000000 : ℝ)*X 0 0+(4492029733/10000000000 : ℝ)*X 0 1+(2108087159/5000000000 : ℝ)*X 0 2+(2175979743/5000000000 : ℝ)*X 1 0+(4492029733/10000000000 : ℝ)*X 1 1+(2108087159/5000000000 : ℝ)*X 1 2+(2175979743/5000000000 : ℝ)*X 2 0+(4492029733/10000000000 : ℝ)*X 2 1+(2108087159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (228670854333956816781331989/159500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (495334261/50000000000000 : ℝ)*(base19) + (55180223/5000000000000 : ℝ)*(base23) + (76519997/50000000000000 : ℝ)*(upper2) + (192909427/100000000000000 : ℝ)*(upper3) + (15312217/100000000000000 : ℝ)*(upper4) + (2725576569828729/50000000000000 : ℝ)*(major0) + (2725576569828729/50000000000000 : ℝ)*(major1) + (2725576569828729/50000000000000 : ℝ)*(major2) + (1459468265032761/20000000000000 : ℝ)*(sp0) + (1824339622763263/25000000000000 : ℝ)*(sp1) + (3648679189058557/50000000000000 : ℝ)*(sp2) + (1802466623541437/50000000000000 : ℝ)*(sp3) + (18156557769/100000000000000 : ℝ)*(sp4) + (168784017/1250000000000 : ℝ)*(sp7) + (1802473374902117/50000000000000 : ℝ)*(f.failure) + (3648679740860787/50000000000000 : ℝ)*(f.sum) + (15510538246703/3190000000000000000000000000 : ℝ)*base66 + (3825924174819179779/319000000000000000000000000000000 : ℝ)*base68 + (258894865998179779/319000000000000000000000000000000 : ℝ)*base70 + (4185562481209179779/319000000000000000000000000000000 : ℝ)*base72 + (853714221817/3190000000000000000000000000 : ℝ)*base73 + (1703563865453179779/319000000000000000000000000000000 : ℝ)*base76 + (1306007581317179779/319000000000000000000000000000000 : ℝ)*base78 + (3323710467659179779/319000000000000000000000000000000 : ℝ)*base80 + (1869596594377/3190000000000000000000000000 : ℝ)*base81 + (29315263/5000000000000000000000 : ℝ)*base89 + (29315263/5000000000000000000000 : ℝ)*base91 + (29315263/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130938027246824113921373337/19937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864760689/100000000000000 : ℝ)*(base19) + (197067763/25000000000000 : ℝ)*(base23) + (53050317/20000000000000 : ℝ)*(upper3) + (35884811/50000000000000 : ℝ)*(lower4) + (47934251/100000000000000 : ℝ)*(upper5) + (685201515818271/12500000000000 : ℝ)*(major0) + (685201515818271/12500000000000 : ℝ)*(major1) + (685201515818271/12500000000000 : ℝ)*(major2) + (1083669069/20000000000000 : ℝ)*(sp1) + (25757023371/100000000000000 : ℝ)*(sp2) + (733813420217213/10000000000000 : ℝ)*(sp4) + (1467625583813219/20000000000000 : ℝ)*(sp5) + (3669053828438853/50000000000000 : ℝ)*(sp6) + (1812544916003023/50000000000000 : ℝ)*(sp7) + (1812544916003023/50000000000000 : ℝ)*(f.failure) + (733813420217213/10000000000000 : ℝ)*(f.sum) + (34624505987/797500000000000000000000000 : ℝ)*base66 + (1117842270484617221/79750000000000000000000000000000 : ℝ)*base68 + (94144631592117221/79750000000000000000000000000000 : ℝ)*base70 + (1144021812395117221/79750000000000000000000000000000 : ℝ)*base72 + (77407735239/1595000000000000000000000000 : ℝ)*base74 + (216325414932117221/79750000000000000000000000000000 : ℝ)*base76 + (361355312097882779/79750000000000000000000000000000 : ℝ)*base77 + (1043983581225867221/79750000000000000000000000000000 : ℝ)*base80 + (159270645999/398750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (41319197/5000000000000000000000 : ℝ)*base89 + (41319197/5000000000000000000000 : ℝ)*base91 + (41319197/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1231_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10883/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1231_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1231_s5_0 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124927973/10000000000 : ℝ)*x 0 + (5392673559/10000000000 : ℝ)*x 1 + (2632933321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124927973/10000000000 : ℝ)^1053 ≤ (6460321645667/50000000000000 : ℝ)^797 := by
    have hnat : (2124927973 : ℕ)^1053*50000000000000^797 ≤ 6460321645667^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124927973 10000000000 6460321645667 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392673559/10000000000 : ℝ)^1053 ≤ (221120196359/500000000000 : ℝ)^797 := by
    have hnat : (5392673559 : ℕ)^1053*500000000000^797 ≤ 221120196359^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392673559 10000000000 221120196359 500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632933321/5000000000 : ℝ)^1053 ≤ (42855317420709/100000000000000 : ℝ)^797 := by
    have hnat : (2632933321 : ℕ)^1053*100000000000000^797 ≤ 42855317420709^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632933321 5000000000 42855317420709 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124927973/10000000000 : ℝ), (5392673559/10000000000 : ℝ), (2632933321/5000000000 : ℝ)] ![(6460321645667/50000000000000 : ℝ), (221120196359/500000000000 : ℝ), (42855317420709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124927973/10000000000 : ℝ)|^1053 ≤ (6460321645667/50000000000000 : ℝ)^797
        have hw : |(-2124927973/10000000000 : ℝ)|=(2124927973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392673559/10000000000 : ℝ)|^1053 ≤ (221120196359/500000000000 : ℝ)^797
        have hw : |(5392673559/10000000000 : ℝ)|=(5392673559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632933321/5000000000 : ℝ)|^1053 ≤ (42855317420709/100000000000000 : ℝ)^797
        have hw : |(2632933321/5000000000 : ℝ)|=(2632933321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_1 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672344053/5000000000 : ℝ)*x 0 + (-1094621309/5000000000 : ℝ)*x 1 + (5265866641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672344053/5000000000 : ℝ)^1053 ≤ (43704866889199/100000000000000 : ℝ)^797 := by
    have hnat : (2672344053 : ℕ)^1053*100000000000000^797 ≤ 43704866889199^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672344053 5000000000 43704866889199 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094621309/5000000000 : ℝ)^1053 ≤ (13439815686743/100000000000000 : ℝ)^797 := by
    have hnat : (1094621309 : ℕ)^1053*100000000000000^797 ≤ 13439815686743^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094621309 5000000000 13439815686743 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265866641/10000000000 : ℝ)^1053 ≤ (10713829352489/25000000000000 : ℝ)^797 := by
    have hnat : (5265866641 : ℕ)^1053*25000000000000^797 ≤ 10713829352489^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265866641 10000000000 10713829352489 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672344053/5000000000 : ℝ), (-1094621309/5000000000 : ℝ), (5265866641/10000000000 : ℝ)] ![(43704866889199/100000000000000 : ℝ), (13439815686743/100000000000000 : ℝ), (10713829352489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672344053/5000000000 : ℝ)|^1053 ≤ (43704866889199/100000000000000 : ℝ)^797
        have hw : |(2672344053/5000000000 : ℝ)|=(2672344053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094621309/5000000000 : ℝ)|^1053 ≤ (13439815686743/100000000000000 : ℝ)^797
        have hw : |(-1094621309/5000000000 : ℝ)|=(1094621309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265866641/10000000000 : ℝ)|^1053 ≤ (10713829352489/25000000000000 : ℝ)^797
        have hw : |(5265866641/10000000000 : ℝ)|=(5265866641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_2 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344688271/10000000000 : ℝ)*x 0 + (1053173339/2000000000 : ℝ)*x 1 + (-1094621163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344688271/10000000000 : ℝ)^1053 ≤ (43704868671829/100000000000000 : ℝ)^797 := by
    have hnat : (5344688271 : ℕ)^1053*100000000000000^797 ≤ 43704868671829^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344688271 10000000000 43704868671829 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053173339/2000000000 : ℝ)^1053 ≤ (8571063598117/20000000000000 : ℝ)^797 := by
    have hnat : (1053173339 : ℕ)^1053*20000000000000^797 ≤ 8571063598117^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053173339 2000000000 8571063598117 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094621163/5000000000 : ℝ)^1053 ≤ (6719906659179/50000000000000 : ℝ)^797 := by
    have hnat : (1094621163 : ℕ)^1053*50000000000000^797 ≤ 6719906659179^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094621163 5000000000 6719906659179 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344688271/10000000000 : ℝ), (1053173339/2000000000 : ℝ), (-1094621163/5000000000 : ℝ)] ![(43704868671829/100000000000000 : ℝ), (8571063598117/20000000000000 : ℝ), (6719906659179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344688271/10000000000 : ℝ)|^1053 ≤ (43704868671829/100000000000000 : ℝ)^797
        have hw : |(5344688271/10000000000 : ℝ)|=(5344688271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053173339/2000000000 : ℝ)|^1053 ≤ (8571063598117/20000000000000 : ℝ)^797
        have hw : |(1053173339/2000000000 : ℝ)|=(1053173339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094621163/5000000000 : ℝ)|^1053 ≤ (6719906659179/50000000000000 : ℝ)^797
        have hw : |(-1094621163/5000000000 : ℝ)|=(1094621163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_3 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4352220531/10000000000 : ℝ)*x 0 + (2112860573/5000000000 : ℝ)*x 1 + (4482410169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352220531/10000000000 : ℝ)^1053 ≤ (33316793754741/100000000000000 : ℝ)^797 := by
    have hnat : (4352220531 : ℕ)^1053*100000000000000^797 ≤ 33316793754741^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352220531 10000000000 33316793754741 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112860573/5000000000 : ℝ)^1053 ≤ (32043392760689/100000000000000 : ℝ)^797 := by
    have hnat : (2112860573 : ℕ)^1053*100000000000000^797 ≤ 32043392760689^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112860573 5000000000 32043392760689 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482410169/10000000000 : ℝ)^1053 ≤ (17319906739031/50000000000000 : ℝ)^797 := by
    have hnat : (4482410169 : ℕ)^1053*50000000000000^797 ≤ 17319906739031^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482410169 10000000000 17319906739031 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352220531/10000000000 : ℝ), (2112860573/5000000000 : ℝ), (4482410169/10000000000 : ℝ)] ![(33316793754741/100000000000000 : ℝ), (32043392760689/100000000000000 : ℝ), (17319906739031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352220531/10000000000 : ℝ)|^1053 ≤ (33316793754741/100000000000000 : ℝ)^797
        have hw : |(4352220531/10000000000 : ℝ)|=(4352220531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112860573/5000000000 : ℝ)|^1053 ≤ (32043392760689/100000000000000 : ℝ)^797
        have hw : |(2112860573/5000000000 : ℝ)|=(2112860573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482410169/10000000000 : ℝ)|^1053 ≤ (17319906739031/50000000000000 : ℝ)^797
        have hw : |(4482410169/10000000000 : ℝ)|=(4482410169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_4 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-84997317/400000000 : ℝ)*x 0 + (2633096403/5000000000 : ℝ)*x 1 + (5392346201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84997317/400000000 : ℝ)^1053 ≤ (2584136614743/20000000000000 : ℝ)^797 := by
    have hnat : (84997317 : ℕ)^1053*20000000000000^797 ≤ 2584136614743^797*400000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84997317 400000000 2584136614743 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633096403/5000000000 : ℝ)^1053 ≤ (4285882449733/10000000000000 : ℝ)^797 := by
    have hnat : (2633096403 : ℕ)^1053*10000000000000^797 ≤ 4285882449733^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633096403 5000000000 4285882449733 10000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392346201/10000000000 : ℝ)^1053 ≤ (44220492419939/100000000000000 : ℝ)^797 := by
    have hnat : (5392346201 : ℕ)^1053*100000000000000^797 ≤ 44220492419939^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392346201 10000000000 44220492419939 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84997317/400000000 : ℝ), (2633096403/5000000000 : ℝ), (5392346201/10000000000 : ℝ)] ![(2584136614743/20000000000000 : ℝ), (4285882449733/10000000000000 : ℝ), (44220492419939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84997317/400000000 : ℝ)|^1053 ≤ (2584136614743/20000000000000 : ℝ)^797
        have hw : |(-84997317/400000000 : ℝ)|=(84997317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633096403/5000000000 : ℝ)|^1053 ≤ (4285882449733/10000000000000 : ℝ)^797
        have hw : |(2633096403/5000000000 : ℝ)|=(2633096403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392346201/10000000000 : ℝ)|^1053 ≤ (44220492419939/100000000000000 : ℝ)^797
        have hw : |(5392346201/10000000000 : ℝ)|=(5392346201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_5 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312357257/10000000000 : ℝ)*x 0 + (-2062763057/10000000000 : ℝ)*x 1 + (2696173101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312357257/10000000000 : ℝ)^1053 ≤ (10838977477433/25000000000000 : ℝ)^797 := by
    have hnat : (5312357257 : ℕ)^1053*25000000000000^797 ≤ 10838977477433^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312357257 10000000000 10838977477433 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062763057/10000000000 : ℝ)^1053 ≤ (12423597646431/100000000000000 : ℝ)^797 := by
    have hnat : (2062763057 : ℕ)^1053*100000000000000^797 ≤ 12423597646431^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062763057 10000000000 12423597646431 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696173101/5000000000 : ℝ)^1053 ≤ (22110246215387/50000000000000 : ℝ)^797 := by
    have hnat : (2696173101 : ℕ)^1053*50000000000000^797 ≤ 22110246215387^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696173101 5000000000 22110246215387 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312357257/10000000000 : ℝ), (-2062763057/10000000000 : ℝ), (2696173101/5000000000 : ℝ)] ![(10838977477433/25000000000000 : ℝ), (12423597646431/100000000000000 : ℝ), (22110246215387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312357257/10000000000 : ℝ)|^1053 ≤ (10838977477433/25000000000000 : ℝ)^797
        have hw : |(5312357257/10000000000 : ℝ)|=(5312357257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062763057/10000000000 : ℝ)|^1053 ≤ (12423597646431/100000000000000 : ℝ)^797
        have hw : |(-2062763057/10000000000 : ℝ)|=(2062763057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696173101/5000000000 : ℝ)|^1053 ≤ (22110246215387/50000000000000 : ℝ)^797
        have hw : |(2696173101/5000000000 : ℝ)|=(2696173101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_6 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312357253/10000000000 : ℝ)*x 0 + (2696173101/5000000000 : ℝ)*x 1 + (-1031381531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312357253/10000000000 : ℝ)^1053 ≤ (216779549333/500000000000 : ℝ)^797 := by
    have hnat : (5312357253 : ℕ)^1053*500000000000^797 ≤ 216779549333^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312357253 10000000000 216779549333 500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696173101/5000000000 : ℝ)^1053 ≤ (22110246215387/50000000000000 : ℝ)^797 := by
    have hnat : (2696173101 : ℕ)^1053*50000000000000^797 ≤ 22110246215387^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696173101 5000000000 22110246215387 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031381531/5000000000 : ℝ)^1053 ≤ (6211798843109/50000000000000 : ℝ)^797 := by
    have hnat : (1031381531 : ℕ)^1053*50000000000000^797 ≤ 6211798843109^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031381531 5000000000 6211798843109 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312357253/10000000000 : ℝ), (2696173101/5000000000 : ℝ), (-1031381531/5000000000 : ℝ)] ![(216779549333/500000000000 : ℝ), (22110246215387/50000000000000 : ℝ), (6211798843109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312357253/10000000000 : ℝ)|^1053 ≤ (216779549333/500000000000 : ℝ)^797
        have hw : |(5312357253/10000000000 : ℝ)|=(5312357253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696173101/5000000000 : ℝ)|^1053 ≤ (22110246215387/50000000000000 : ℝ)^797
        have hw : |(2696173101/5000000000 : ℝ)|=(2696173101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031381531/5000000000 : ℝ)|^1053 ≤ (6211798843109/50000000000000 : ℝ)^797
        have hw : |(-1031381531/5000000000 : ℝ)|=(1031381531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_s5_7 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (870446199/2000000000 : ℝ)*x 0 + (179270019/400000000 : ℝ)*x 1 + (4226382857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870446199/2000000000 : ℝ)^1053 ≤ (33316899587533/100000000000000 : ℝ)^797 := by
    have hnat : (870446199 : ℕ)^1053*100000000000000^797 ≤ 33316899587533^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870446199 2000000000 33316899587533 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179270019/400000000 : ℝ)^1053 ≤ (34633078033461/100000000000000 : ℝ)^797 := by
    have hnat : (179270019 : ℕ)^1053*100000000000000^797 ≤ 34633078033461^797*400000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179270019 400000000 34633078033461 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226382857/10000000000 : ℝ)^1053 ≤ (32050022355469/100000000000000 : ℝ)^797 := by
    have hnat : (4226382857 : ℕ)^1053*100000000000000^797 ≤ 32050022355469^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226382857 10000000000 32050022355469 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870446199/2000000000 : ℝ), (179270019/400000000 : ℝ), (4226382857/10000000000 : ℝ)] ![(33316899587533/100000000000000 : ℝ), (34633078033461/100000000000000 : ℝ), (32050022355469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870446199/2000000000 : ℝ)|^1053 ≤ (33316899587533/100000000000000 : ℝ)^797
        have hw : |(870446199/2000000000 : ℝ)|=(870446199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179270019/400000000 : ℝ)|^1053 ≤ (34633078033461/100000000000000 : ℝ)^797
        have hw : |(179270019/400000000 : ℝ)|=(179270019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226382857/10000000000 : ℝ)|^1053 ≤ (32050022355469/100000000000000 : ℝ)^797
        have hw : |(4226382857/10000000000 : ℝ)|=(4226382857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1231_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7063/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (8423/2048 : ℝ) ≤ (103267555083091/800000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^8423 ≤ (103267555083091/800000000000000000 : ℝ)^2048 := by
      have hnat : (5667 : ℕ)^8423*800000000000000000^2048 ≤ 103267555083091^2048*50000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 103267555083091 800000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (103267555083091/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8423/2048 : ℝ) ≤ (32965527849951899/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8423 ≤ (32965527849951899/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8423*100000000000000000000^2048 ≤ 32965527849951899^2048*25000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 32965527849951899 100000000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (32965527849951899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (400103267555083091/400000000000000000 : ℝ) ≤ (1000062766025619/1000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (400103267555083091/400000000000000000 : ℝ)^2048 ≤ (1000062766025619/1000000000000000 : ℝ)^8423 := by
      have hnat : (400103267555083091 : ℕ)^2048*1000000000000000^8423 ≤ 1000062766025619^8423*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400103267555083091 400000000000000000 1000062766025619 1000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000062766025619/1000000000000000 : ℝ)) (X := (400103267555083091/400000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022936986117669137/50000000000000000000 : ℝ) ≤ (5000557601744127/5000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (50022936986117669137/50000000000000000000 : ℝ)^2048 ≤ (5000557601744127/5000000000000000 : ℝ)^8423 := by
      have hnat : (50022936986117669137 : ℕ)^2048*5000000000000000^8423 ≤ 5000557601744127^8423*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022936986117669137 50000000000000000000 5000557601744127 5000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557601744127/5000000000000000 : ℝ)) (X := (50022936986117669137/50000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032965527849951899/50000000000000000000 : ℝ) ≤ (5000801373360159/5000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (50032965527849951899/50000000000000000000 : ℝ)^2048 ≤ (5000801373360159/5000000000000000 : ℝ)^8423 := by
      have hnat : (50032965527849951899 : ℕ)^2048*5000000000000000^8423 ≤ 5000801373360159^8423*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032965527849951899 50000000000000000000 5000801373360159 5000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000801373360159/5000000000000000 : ℝ)) (X := (50032965527849951899/50000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103267555083091/800000000000000000 : ℝ) ≤ ((7252692460019759157/7255000000000000000 : ℝ)+2*(7617863001/4534375000000 : ℝ)*(5667/50000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (7252692460019759157/7255000000000000000 : ℝ)+2*(7617863001/4534375000000 : ℝ)*(5667/50000 : ℝ)=(1000062766025619/1000000000000000 : ℝ) by norm_num, show 1+2*(103267555083091/800000000000000000 : ℝ)=(400103267555083091/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32965527849951899/100000000000000000000 : ℝ)+(103267555083091/800000000000000000 : ℝ) ≤ ((7252692460019759157/7255000000000000000 : ℝ)+(7617863001/4534375000000 : ℝ)*((3559/25000 : ℝ)+(5667/50000 : ℝ)))^(8423/2048 : ℝ) := by
    rw [show (7252692460019759157/7255000000000000000 : ℝ)+(7617863001/4534375000000 : ℝ)*((3559/25000 : ℝ)+(5667/50000 : ℝ))=(5000557601744127/5000000000000000 : ℝ) by norm_num, show 1+(32965527849951899/100000000000000000000 : ℝ)+(103267555083091/800000000000000000 : ℝ)=(50022936986117669137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32965527849951899/100000000000000000000 : ℝ) ≤ ((7252692460019759157/7255000000000000000 : ℝ)+2*(7617863001/4534375000000 : ℝ)*(3559/25000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (7252692460019759157/7255000000000000000 : ℝ)+2*(7617863001/4534375000000 : ℝ)*(3559/25000 : ℝ)=(5000801373360159/5000000000000000 : ℝ) by norm_num, show 1+2*(32965527849951899/100000000000000000000 : ℝ)=(50032965527849951899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7252692460019759157/7255000000000000000 : ℝ)*(X 1 0+X 2 0)+(7617863001/4534375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7252692460019759157/7255000000000000000 : ℝ)) (alpha := (7617863001/4534375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7252692460019759157/7255000000000000000 : ℝ)*(X 0 1+X 2 1)+(7617863001/4534375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7252692460019759157/7255000000000000000 : ℝ)) (alpha := (7617863001/4534375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7252692460019759157/7255000000000000000 : ℝ)*(X 0 2+X 1 2)+(7617863001/4534375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7252692460019759157/7255000000000000000 : ℝ)) (alpha := (7617863001/4534375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124927973/10000000000 : ℝ)*X 0 0+(5392673559/10000000000 : ℝ)*X 0 1+(2632933321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672344053/5000000000 : ℝ)*X 1 0+(-1094621309/5000000000 : ℝ)*X 1 1+(5265866641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344688271/10000000000 : ℝ)*X 2 0+(1053173339/2000000000 : ℝ)*X 2 1+(-1094621163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352220531/10000000000 : ℝ)*X 0 0+(2112860573/5000000000 : ℝ)*X 0 1+(4482410169/10000000000 : ℝ)*X 0 2+(4352220531/10000000000 : ℝ)*X 1 0+(2112860573/5000000000 : ℝ)*X 1 1+(4482410169/10000000000 : ℝ)*X 1 2+(4352220531/10000000000 : ℝ)*X 2 0+(2112860573/5000000000 : ℝ)*X 2 1+(4482410169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84997317/400000000 : ℝ)*X 0 0+(2633096403/5000000000 : ℝ)*X 0 1+(5392346201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312357257/10000000000 : ℝ)*X 1 0+(-2062763057/10000000000 : ℝ)*X 1 1+(2696173101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312357253/10000000000 : ℝ)*X 2 0+(2696173101/5000000000 : ℝ)*X 2 1+(-1031381531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870446199/2000000000 : ℝ)*X 0 0+(179270019/400000000 : ℝ)*X 0 1+(4226382857/10000000000 : ℝ)*X 0 2+(870446199/2000000000 : ℝ)*X 1 0+(179270019/400000000 : ℝ)*X 1 1+(4226382857/10000000000 : ℝ)*X 1 2+(870446199/2000000000 : ℝ)*X 2 0+(179270019/400000000 : ℝ)*X 2 1+(4226382857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3607221913616293687381201857/362750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59223489/3125000000000 : ℝ)*(base19) + (395746317/20000000000000 : ℝ)*(base23) + (10228413/10000000000000 : ℝ)*(upper4) + (49806087/20000000000000 : ℝ)*(upper5) + (5890973386570367/100000000000000 : ℝ)*(major0) + (5890973386570367/100000000000000 : ℝ)*(major1) + (5890973386570367/100000000000000 : ℝ)*(major2) + (3943031240265669/50000000000000 : ℝ)*(sp0) + (985766432325841/12500000000000 : ℝ)*(sp1) + (1971534145435049/25000000000000 : ℝ)*(sp2) + (1947893731082319/50000000000000 : ℝ)*(sp3) + (76079940443/100000000000000 : ℝ)*(sp4) + (1041342681/20000000000000 : ℝ)*(sp5) + (10209517171/50000000000000 : ℝ)*(sp7) + (194790394059949/5000000000000 : ℝ)*(f.failure) + (7886138560471781/100000000000000 : ℝ)*(f.sum) + (61754712511101/7255000000000000000000000000 : ℝ)*base66 + (5127024278088699381/725500000000000000000000000000000 : ℝ)*base68 + (1641005352907800619/725500000000000000000000000000000 : ℝ)*base69 + (2488311458874800619/725500000000000000000000000000000 : ℝ)*base71 + (46747927764551/7255000000000000000000000000 : ℝ)*base74 + (4410001583076699381/725500000000000000000000000000000 : ℝ)*base76 + (1637123758731699381/725500000000000000000000000000000 : ℝ)*base78 + (7100839326198699381/725500000000000000000000000000000 : ℝ)*base80 + (2360150571589/1813750000000000000000000000 : ℝ)*base82 + (7469911/500000000000000000000 : ℝ)*base89 + (7469911/500000000000000000000 : ℝ)*base91 + (7469911/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3719722053254417961845441427/362750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36991311/2000000000000 : ℝ)*(base19) + (499420133/25000000000000 : ℝ)*(base23) + (10311907/5000000000000 : ℝ)*(upper3) + (35639739/50000000000000 : ℝ)*(lower4) + (21093039/10000000000000 : ℝ)*(upper5) + (5921389358024963/100000000000000 : ℝ)*(major0) + (5921389358024963/100000000000000 : ℝ)*(major1) + (5921389358024963/100000000000000 : ℝ)*(major2) + (6392043833/12500000000000 : ℝ)*(sp1) + (27203504249/50000000000000 : ℝ)*(sp2) + (1585371171546131/20000000000000 : ℝ)*(sp4) + (3963401435907221/50000000000000 : ℝ)*(sp5) + (63414395624333/800000000000 : ℝ)*(sp6) + (1957961258255793/50000000000000 : ℝ)*(sp7) + (1957961258255793/50000000000000 : ℝ)*(f.failure) + (1585371171546131/20000000000000 : ℝ)*(f.sum) + (5721866132091/7255000000000000000000000000 : ℝ)*base65 + (1094607911154636191/725500000000000000000000000000000 : ℝ)*base67 + (1083924632958863809/725500000000000000000000000000000 : ℝ)*base70 + (1771684581970636191/725500000000000000000000000000000 : ℝ)*base71 + (7804086312199/1813750000000000000000000000 : ℝ)*base73 + (7782290020010363809/725500000000000000000000000000000 : ℝ)*base76 + (2427917393293136191/725500000000000000000000000000000 : ℝ)*base77 + (5977103617189636191/725500000000000000000000000000000 : ℝ)*base79 + (452005534261/113359375000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25535773/5000000000000000000000 : ℝ)*base90 + (25535773/5000000000000000000000 : ℝ)*base92 + (25535773/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1231_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1231_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1231_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1231_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1231_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1231_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1231_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

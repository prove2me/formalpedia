-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:20.971463+00:00
-- url     : https://prove2.me/submissions/2cb446a0-962b-443a-bdf8-ec71cb7ad9a1

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
theorem support_rectangle_w1194_s0_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-117216337/625000000 : ℝ)*x 0 + (1208477897/2000000000 : ℝ)*x 1 + (4787013471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117216337/625000000 : ℝ)^8387 ≤ (5460524739967/50000000000000 : ℝ)^6339 := by
    have hnat : (117216337 : ℕ)^8387*50000000000000^6339 ≤ 5460524739967^6339*625000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117216337 625000000 5460524739967 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208477897/2000000000 : ℝ)^8387 ≤ (25673895809671/50000000000000 : ℝ)^6339 := by
    have hnat : (1208477897 : ℕ)^8387*50000000000000^6339 ≤ 25673895809671^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208477897 2000000000 25673895809671 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787013471/10000000000 : ℝ)^8387 ≤ (9432789723751/25000000000000 : ℝ)^6339 := by
    have hnat : (4787013471 : ℕ)^8387*25000000000000^6339 ≤ 9432789723751^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787013471 10000000000 9432789723751 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117216337/625000000 : ℝ), (1208477897/2000000000 : ℝ), (4787013471/10000000000 : ℝ)] ![(5460524739967/50000000000000 : ℝ), (25673895809671/50000000000000 : ℝ), (9432789723751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117216337/625000000 : ℝ)|^8387 ≤ (5460524739967/50000000000000 : ℝ)^6339
        have hw : |(-117216337/625000000 : ℝ)|=(117216337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208477897/2000000000 : ℝ)|^8387 ≤ (25673895809671/50000000000000 : ℝ)^6339
        have hw : |(1208477897/2000000000 : ℝ)|=(1208477897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787013471/10000000000 : ℝ)|^8387 ≤ (9432789723751/25000000000000 : ℝ)^6339
        have hw : |(4787013471/10000000000 : ℝ)|=(4787013471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2756931949/5000000000 : ℝ)*x 0 + (-2594448653/10000000000 : ℝ)*x 1 + (598376683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756931949/5000000000 : ℝ)^8387 ≤ (45491036060993/100000000000000 : ℝ)^6339 := by
    have hnat : (2756931949 : ℕ)^8387*100000000000000^6339 ≤ 45491036060993^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756931949 5000000000 45491036060993 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594448653/10000000000 : ℝ)^8387 ≤ (8388902552431/50000000000000 : ℝ)^6339 := by
    have hnat : (2594448653 : ℕ)^8387*50000000000000^6339 ≤ 8388902552431^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594448653 10000000000 8388902552431 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598376683/1250000000 : ℝ)^8387 ≤ (7546231764401/20000000000000 : ℝ)^6339 := by
    have hnat : (598376683 : ℕ)^8387*20000000000000^6339 ≤ 7546231764401^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598376683 1250000000 7546231764401 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756931949/5000000000 : ℝ), (-2594448653/10000000000 : ℝ), (598376683/1250000000 : ℝ)] ![(45491036060993/100000000000000 : ℝ), (8388902552431/50000000000000 : ℝ), (7546231764401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756931949/5000000000 : ℝ)|^8387 ≤ (45491036060993/100000000000000 : ℝ)^6339
        have hw : |(2756931949/5000000000 : ℝ)|=(2756931949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2594448653/10000000000 : ℝ)|^8387 ≤ (8388902552431/50000000000000 : ℝ)^6339
        have hw : |(-2594448653/10000000000 : ℝ)|=(2594448653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598376683/1250000000 : ℝ)|^8387 ≤ (7546231764401/20000000000000 : ℝ)^6339
        have hw : |(598376683/1250000000 : ℝ)|=(598376683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (344616493/625000000 : ℝ)*x 0 + (191480539/400000000 : ℝ)*x 1 + (-648612163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344616493/625000000 : ℝ)^8387 ≤ (9098207190367/20000000000000 : ℝ)^6339 := by
    have hnat : (344616493 : ℕ)^8387*20000000000000^6339 ≤ 9098207190367^6339*625000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344616493 625000000 9098207190367 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191480539/400000000 : ℝ)^8387 ≤ (18865579468359/50000000000000 : ℝ)^6339 := by
    have hnat : (191480539 : ℕ)^8387*50000000000000^6339 ≤ 18865579468359^6339*400000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191480539 400000000 18865579468359 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648612163/2500000000 : ℝ)^8387 ≤ (8388902548153/50000000000000 : ℝ)^6339 := by
    have hnat : (648612163 : ℕ)^8387*50000000000000^6339 ≤ 8388902548153^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648612163 2500000000 8388902548153 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344616493/625000000 : ℝ), (191480539/400000000 : ℝ), (-648612163/2500000000 : ℝ)] ![(9098207190367/20000000000000 : ℝ), (18865579468359/50000000000000 : ℝ), (8388902548153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344616493/625000000 : ℝ)|^8387 ≤ (9098207190367/20000000000000 : ℝ)^6339
        have hw : |(344616493/625000000 : ℝ)|=(344616493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191480539/400000000 : ℝ)|^8387 ≤ (18865579468359/50000000000000 : ℝ)^6339
        have hw : |(191480539/400000000 : ℝ)|=(191480539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-648612163/2500000000 : ℝ)|^8387 ≤ (8388902548153/50000000000000 : ℝ)^6339
        have hw : |(-648612163/2500000000 : ℝ)|=(648612163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4196817663/10000000000 : ℝ)*x 0 + (623758221/2000000000 : ℝ)*x 1 + (5641828161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196817663/10000000000 : ℝ)^8387 ≤ (15851244932421/50000000000000 : ℝ)^6339 := by
    have hnat : (4196817663 : ℕ)^8387*50000000000000^6339 ≤ 15851244932421^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196817663 10000000000 15851244932421 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623758221/2000000000 : ℝ)^8387 ≤ (10702215944039/50000000000000 : ℝ)^6339 := by
    have hnat : (623758221 : ℕ)^8387*50000000000000^6339 ≤ 10702215944039^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623758221 2000000000 10702215944039 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641828161/10000000000 : ℝ)^8387 ≤ (46893078232137/100000000000000 : ℝ)^6339 := by
    have hnat : (5641828161 : ℕ)^8387*100000000000000^6339 ≤ 46893078232137^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641828161 10000000000 46893078232137 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196817663/10000000000 : ℝ), (623758221/2000000000 : ℝ), (5641828161/10000000000 : ℝ)] ![(15851244932421/50000000000000 : ℝ), (10702215944039/50000000000000 : ℝ), (46893078232137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196817663/10000000000 : ℝ)|^8387 ≤ (15851244932421/50000000000000 : ℝ)^6339
        have hw : |(4196817663/10000000000 : ℝ)|=(4196817663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623758221/2000000000 : ℝ)|^8387 ≤ (10702215944039/50000000000000 : ℝ)^6339
        have hw : |(623758221/2000000000 : ℝ)|=(623758221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641828161/10000000000 : ℝ)|^8387 ≤ (46893078232137/100000000000000 : ℝ)^6339
        have hw : |(5641828161/10000000000 : ℝ)|=(5641828161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880455693/10000000000 : ℝ)*x 0 + (4819370729/10000000000 : ℝ)*x 1 + (6008891011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880455693/10000000000 : ℝ)^8387 ≤ (10959544408811/100000000000000 : ℝ)^6339 := by
    have hnat : (1880455693 : ℕ)^8387*100000000000000^6339 ≤ 10959544408811^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880455693 10000000000 10959544408811 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819370729/10000000000 : ℝ)^8387 ≤ (3806896409351/10000000000000 : ℝ)^6339 := by
    have hnat : (4819370729 : ℕ)^8387*10000000000000^6339 ≤ 3806896409351^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819370729 10000000000 3806896409351 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008891011/10000000000 : ℝ)^8387 ≤ (49776847157/97656250000 : ℝ)^6339 := by
    have hnat : (6008891011 : ℕ)^8387*97656250000^6339 ≤ 49776847157^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008891011 10000000000 49776847157 97656250000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880455693/10000000000 : ℝ), (4819370729/10000000000 : ℝ), (6008891011/10000000000 : ℝ)] ![(10959544408811/100000000000000 : ℝ), (3806896409351/10000000000000 : ℝ), (49776847157/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880455693/10000000000 : ℝ)|^8387 ≤ (10959544408811/100000000000000 : ℝ)^6339
        have hw : |(-1880455693/10000000000 : ℝ)|=(1880455693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819370729/10000000000 : ℝ)|^8387 ≤ (3806896409351/10000000000000 : ℝ)^6339
        have hw : |(4819370729/10000000000 : ℝ)|=(4819370729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008891011/10000000000 : ℝ)|^8387 ≤ (49776847157/97656250000 : ℝ)^6339
        have hw : |(6008891011/10000000000 : ℝ)|=(6008891011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172505787/10000000000 : ℝ)*x 0 + (-343142769/2500000000 : ℝ)*x 1 + (6008891063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172505787/10000000000 : ℝ)^8387 ≤ (41802637649311/100000000000000 : ℝ)^6339 := by
    have hnat : (5172505787 : ℕ)^8387*100000000000000^6339 ≤ 41802637649311^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172505787 10000000000 41802637649311 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343142769/2500000000 : ℝ)^8387 ≤ (7225870273697/100000000000000 : ℝ)^6339 := by
    have hnat : (343142769 : ℕ)^8387*100000000000000^6339 ≤ 7225870273697^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343142769 2500000000 7225870273697 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008891063/10000000000 : ℝ)^8387 ≤ (50971492072377/100000000000000 : ℝ)^6339 := by
    have hnat : (6008891063 : ℕ)^8387*100000000000000^6339 ≤ 50971492072377^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008891063 10000000000 50971492072377 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172505787/10000000000 : ℝ), (-343142769/2500000000 : ℝ), (6008891063/10000000000 : ℝ)] ![(41802637649311/100000000000000 : ℝ), (7225870273697/100000000000000 : ℝ), (50971492072377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172505787/10000000000 : ℝ)|^8387 ≤ (41802637649311/100000000000000 : ℝ)^6339
        have hw : |(5172505787/10000000000 : ℝ)|=(5172505787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343142769/2500000000 : ℝ)|^8387 ≤ (7225870273697/100000000000000 : ℝ)^6339
        have hw : |(-343142769/2500000000 : ℝ)|=(343142769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008891063/10000000000 : ℝ)|^8387 ≤ (50971492072377/100000000000000 : ℝ)^6339
        have hw : |(6008891063/10000000000 : ℝ)|=(6008891063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (323281613/625000000 : ℝ)*x 0 + (6008891021/10000000000 : ℝ)*x 1 + (-137257111/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323281613/625000000 : ℝ)^8387 ≤ (41802637873859/100000000000000 : ℝ)^6339 := by
    have hnat : (323281613 : ℕ)^8387*100000000000000^6339 ≤ 41802637873859^6339*625000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323281613 625000000 41802637873859 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6008891021/10000000000 : ℝ)^8387 ≤ (50971491601/100000000000 : ℝ)^6339 := by
    have hnat : (6008891021 : ℕ)^8387*100000000000^6339 ≤ 50971491601^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008891021 10000000000 50971491601 100000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137257111/1000000000 : ℝ)^8387 ≤ (3612935255259/50000000000000 : ℝ)^6339 := by
    have hnat : (137257111 : ℕ)^8387*50000000000000^6339 ≤ 3612935255259^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137257111 1000000000 3612935255259 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323281613/625000000 : ℝ), (6008891021/10000000000 : ℝ), (-137257111/1000000000 : ℝ)] ![(41802637873859/100000000000000 : ℝ), (50971491601/100000000000 : ℝ), (3612935255259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323281613/625000000 : ℝ)|^8387 ≤ (41802637873859/100000000000000 : ℝ)^6339
        have hw : |(323281613/625000000 : ℝ)|=(323281613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6008891021/10000000000 : ℝ)|^8387 ≤ (50971491601/100000000000 : ℝ)^6339
        have hw : |(6008891021/10000000000 : ℝ)|=(6008891021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137257111/1000000000 : ℝ)|^8387 ≤ (3612935255259/50000000000000 : ℝ)^6339
        have hw : |(-137257111/1000000000 : ℝ)|=(137257111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s0_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206855187/10000000000 : ℝ)*x 0 + (5576797077/10000000000 : ℝ)*x 1 + (3186115801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206855187/10000000000 : ℝ)^8387 ≤ (7950712048831/25000000000000 : ℝ)^6339 := by
    have hnat : (4206855187 : ℕ)^8387*25000000000000^6339 ≤ 7950712048831^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206855187 10000000000 7950712048831 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576797077/10000000000 : ℝ)^8387 ≤ (46179265575993/100000000000000 : ℝ)^6339 := by
    have hnat : (5576797077 : ℕ)^8387*100000000000000^6339 ≤ 46179265575993^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576797077 10000000000 46179265575993 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186115801/10000000000 : ℝ)^8387 ≤ (2201788620867/10000000000000 : ℝ)^6339 := by
    have hnat : (3186115801 : ℕ)^8387*10000000000000^6339 ≤ 2201788620867^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186115801 10000000000 2201788620867 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206855187/10000000000 : ℝ), (5576797077/10000000000 : ℝ), (3186115801/10000000000 : ℝ)] ![(7950712048831/25000000000000 : ℝ), (46179265575993/100000000000000 : ℝ), (2201788620867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206855187/10000000000 : ℝ)|^8387 ≤ (7950712048831/25000000000000 : ℝ)^6339
        have hw : |(4206855187/10000000000 : ℝ)|=(4206855187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576797077/10000000000 : ℝ)|^8387 ≤ (46179265575993/100000000000000 : ℝ)^6339
        have hw : |(5576797077/10000000000 : ℝ)|=(5576797077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186115801/10000000000 : ℝ)|^8387 ≤ (2201788620867/10000000000000 : ℝ)^6339
        have hw : |(3186115801/10000000000 : ℝ)|=(3186115801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (313/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27617/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4193/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4193 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4193*1^1024 ≤ 0^1024*1^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4193/1024 : ℝ) ≤ (293396203077615947/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4193 ≤ (293396203077615947/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4193*12500000000000000000^1024 ≤ 293396203077615947^1024*5^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 293396203077615947 12500000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (293396203077615947/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4193 := by
      have hnat : (1 : ℕ)^1024*1^4193 ≤ 1^4193*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12793396203077615947/12500000000000000000 : ℝ) ≤ (10056820210179283/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (12793396203077615947/12500000000000000000 : ℝ)^1024 ≤ (10056820210179283/10000000000000000 : ℝ)^4193 := by
      have hnat : (12793396203077615947 : ℕ)^1024*10000000000000000^4193 ≤ 10056820210179283^4193*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12793396203077615947 12500000000000000000 10056820210179283 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056820210179283/10000000000000000 : ℝ)) (X := (12793396203077615947/12500000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6543396203077615947/6250000000000000000 : ℝ) ≤ (5056820210179283/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (6543396203077615947/6250000000000000000 : ℝ)^1024 ≤ (5056820210179283/5000000000000000 : ℝ)^4193 := by
      have hnat : (6543396203077615947 : ℕ)^1024*5000000000000000^4193 ≤ 5056820210179283^4193*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6543396203077615947 6250000000000000000 5056820210179283 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056820210179283/5000000000000000 : ℝ)) (X := (6543396203077615947/6250000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56820210179283/4000000000000000 : ℝ)*(0 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(56820210179283/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(293396203077615947/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56820210179283/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (1 : ℝ)+(56820210179283/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056820210179283/10000000000000000 : ℝ) by norm_num, show 1+(293396203077615947/12500000000000000000 : ℝ)+(0 : ℝ)=(12793396203077615947/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(293396203077615947/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56820210179283/4000000000000000 : ℝ)*(2/5 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(56820210179283/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056820210179283/5000000000000000 : ℝ) by norm_num, show 1+2*(293396203077615947/12500000000000000000 : ℝ)=(6543396203077615947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56820210179283/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56820210179283/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56820210179283/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56820210179283/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56820210179283/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56820210179283/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-117216337/625000000 : ℝ)*X 0 0+(1208477897/2000000000 : ℝ)*X 0 1+(4787013471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2756931949/5000000000 : ℝ)*X 1 0+(-2594448653/10000000000 : ℝ)*X 1 1+(598376683/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344616493/625000000 : ℝ)*X 2 0+(191480539/400000000 : ℝ)*X 2 1+(-648612163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196817663/10000000000 : ℝ)*X 0 0+(623758221/2000000000 : ℝ)*X 0 1+(5641828161/10000000000 : ℝ)*X 0 2+(4196817663/10000000000 : ℝ)*X 1 0+(623758221/2000000000 : ℝ)*X 1 1+(5641828161/10000000000 : ℝ)*X 1 2+(4196817663/10000000000 : ℝ)*X 2 0+(623758221/2000000000 : ℝ)*X 2 1+(5641828161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1880455693/10000000000 : ℝ)*X 0 0+(4819370729/10000000000 : ℝ)*X 0 1+(6008891011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172505787/10000000000 : ℝ)*X 1 0+(-343142769/2500000000 : ℝ)*X 1 1+(6008891063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((323281613/625000000 : ℝ)*X 2 0+(6008891021/10000000000 : ℝ)*X 2 1+(-137257111/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206855187/10000000000 : ℝ)*X 0 0+(5576797077/10000000000 : ℝ)*X 0 1+(3186115801/10000000000 : ℝ)*X 0 2+(4206855187/10000000000 : ℝ)*X 1 0+(5576797077/10000000000 : ℝ)*X 1 1+(3186115801/10000000000 : ℝ)*X 1 2+(4206855187/10000000000 : ℝ)*X 2 0+(5576797077/10000000000 : ℝ)*X 2 1+(3186115801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14282594458685238380421/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12446863/50000000000000 : ℝ)*(base1) + (562467523/100000000000000 : ℝ)*(base19) + (104515941/20000000000000 : ℝ)*(base23) + (19221569/50000000000000 : ℝ)*(base24) + (128430513/100000000000000 : ℝ)*(upper3) + (74557912105979/12500000000000 : ℝ)*(major0) + (74557912105979/12500000000000 : ℝ)*(major1) + (74557912105979/12500000000000 : ℝ)*(major2) + (796575984172871/100000000000000 : ℝ)*(sp0) + (99572080415743/12500000000000 : ℝ)*(sp1) + (796576644770623/100000000000000 : ℝ)*(sp2) + (99087075727671/25000000000000 : ℝ)*(sp3) + (1246514321/100000000000000 : ℝ)*(sp4) + (196784789/20000000000000 : ℝ)*(sp7) + (198174655864177/50000000000000 : ℝ)*(f.failure) + (398288602896733/50000000000000 : ℝ)*(f.sum) + (30173021816943/25000000000000000000000000000 : ℝ)*base66 + (234525615216943/50000000000000000000000000000 : ℝ)*base68 + (175565355816943/50000000000000000000000000000 : ℝ)*base70 + (256195009716943/50000000000000000000000000000 : ℝ)*base72 + (26913842591943/25000000000000000000000000000 : ℝ)*base74 + (418520168016943/50000000000000000000000000000 : ℝ)*base76 + (102924635316943/50000000000000000000000000000 : ℝ)*base78 + (60814289266943/50000000000000000000000000000 : ℝ)*base80 + (42337264408057/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9961127/2500000000000000000000 : ℝ)*base90 + (9961127/2500000000000000000000 : ℝ)*base92 + (9961127/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294950530601791530701607/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32422667/50000000000000 : ℝ)*(base1) + (1438474853/100000000000000 : ℝ)*(base19) + (1441117873/100000000000000 : ℝ)*(base23) + (83720777/50000000000000 : ℝ)*(upper3) + (81954067/50000000000000 : ℝ)*(upper5) + (629483012009057/100000000000000 : ℝ)*(major0) + (629483012009057/100000000000000 : ℝ)*(major1) + (629483012009057/100000000000000 : ℝ)*(major2) + (380639687/12500000000000 : ℝ)*(sp1) + (3033449353/100000000000000 : ℝ)*(sp2) + (840675010170447/100000000000000 : ℝ)*(sp4) + (210167615433191/25000000000000 : ℝ)*(sp5) + (840670470757887/100000000000000 : ℝ)*(sp6) + (418290817213971/100000000000000 : ℝ)*(sp7) + (83658176411861/20000000000000 : ℝ)*(f.failure) + (840674945325113/100000000000000 : ℝ)*(f.sum) + (177741428566131/200000000000000000000000000000 : ℝ)*base65 + (3411880537766131/400000000000000000000000000000 : ℝ)*base67 + (1800600914566131/400000000000000000000000000000 : ℝ)*base69 + (1547371088566131/400000000000000000000000000000 : ℝ)*base71 + (278584826766131/200000000000000000000000000000 : ℝ)*base73 + (2059919970966131/400000000000000000000000000000 : ℝ)*base75 + (2326208094966131/400000000000000000000000000000 : ℝ)*base77 + (3720833162166131/400000000000000000000000000000 : ℝ)*base79 + (356333819233869/200000000000000000000000000000 : ℝ)*base82 + (9618211/1000000000000000000000 : ℝ)*base90 + (9618211/1000000000000000000000 : ℝ)*base92 + (9618211/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1194_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27617/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s1_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1038179619/5000000000 : ℝ)*x 0 + (5687832631/10000000000 : ℝ)*x 1 + (2506484947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038179619/5000000000 : ℝ)^8387 ≤ (2499004416941/20000000000000 : ℝ)^6339 := by
    have hnat : (1038179619 : ℕ)^8387*20000000000000^6339 ≤ 2499004416941^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038179619 5000000000 2499004416941 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687832631/10000000000 : ℝ)^8387 ≤ (23699827605619/50000000000000 : ℝ)^6339 := by
    have hnat : (5687832631 : ℕ)^8387*50000000000000^6339 ≤ 23699827605619^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687832631 10000000000 23699827605619 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506484947/5000000000 : ℝ)^8387 ≤ (20052661346467/50000000000000 : ℝ)^6339 := by
    have hnat : (2506484947 : ℕ)^8387*50000000000000^6339 ≤ 20052661346467^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506484947 5000000000 20052661346467 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1038179619/5000000000 : ℝ), (5687832631/10000000000 : ℝ), (2506484947/5000000000 : ℝ)] ![(2499004416941/20000000000000 : ℝ), (23699827605619/50000000000000 : ℝ), (20052661346467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1038179619/5000000000 : ℝ)|^8387 ≤ (2499004416941/20000000000000 : ℝ)^6339
        have hw : |(-1038179619/5000000000 : ℝ)|=(1038179619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687832631/10000000000 : ℝ)|^8387 ≤ (23699827605619/50000000000000 : ℝ)^6339
        have hw : |(5687832631/10000000000 : ℝ)|=(5687832631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506484947/5000000000 : ℝ)|^8387 ≤ (20052661346467/50000000000000 : ℝ)^6339
        have hw : |(2506484947/5000000000 : ℝ)|=(2506484947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541627401/1000000000 : ℝ)*x 0 + (-487919931/2000000000 : ℝ)*x 1 + (5012970223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541627401/1000000000 : ℝ)^8387 ≤ (44428822062067/100000000000000 : ℝ)^6339 := by
    have hnat : (541627401 : ℕ)^8387*100000000000000^6339 ≤ 44428822062067^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541627401 1000000000 44428822062067 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487919931/2000000000 : ℝ)^8387 ≤ (15465851750907/100000000000000 : ℝ)^6339 := by
    have hnat : (487919931 : ℕ)^8387*100000000000000^6339 ≤ 15465851750907^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487919931 2000000000 15465851750907 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5012970223/10000000000 : ℝ)^8387 ≤ (8021065235083/20000000000000 : ℝ)^6339 := by
    have hnat : (5012970223 : ℕ)^8387*20000000000000^6339 ≤ 8021065235083^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012970223 10000000000 8021065235083 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541627401/1000000000 : ℝ), (-487919931/2000000000 : ℝ), (5012970223/10000000000 : ℝ)] ![(44428822062067/100000000000000 : ℝ), (15465851750907/100000000000000 : ℝ), (8021065235083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541627401/1000000000 : ℝ)|^8387 ≤ (44428822062067/100000000000000 : ℝ)^6339
        have hw : |(541627401/1000000000 : ℝ)|=(541627401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487919931/2000000000 : ℝ)|^8387 ≤ (15465851750907/100000000000000 : ℝ)^6339
        have hw : |(-487919931/2000000000 : ℝ)|=(487919931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5012970223/10000000000 : ℝ)|^8387 ≤ (8021065235083/20000000000000 : ℝ)^6339
        have hw : |(5012970223/10000000000 : ℝ)|=(5012970223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416273017/10000000000 : ℝ)*x 0 + (5012970869/10000000000 : ℝ)*x 1 + (-609900031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416273017/10000000000 : ℝ)^8387 ≤ (5553601410629/12500000000000 : ℝ)^6339 := by
    have hnat : (5416273017 : ℕ)^8387*12500000000000^6339 ≤ 5553601410629^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416273017 10000000000 5553601410629 12500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5012970869/10000000000 : ℝ)^8387 ≤ (10026333253339/25000000000000 : ℝ)^6339 := by
    have hnat : (5012970869 : ℕ)^8387*25000000000000^6339 ≤ 10026333253339^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012970869 10000000000 10026333253339 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609900031/2500000000 : ℝ)^8387 ≤ (7732927842361/50000000000000 : ℝ)^6339 := by
    have hnat : (609900031 : ℕ)^8387*50000000000000^6339 ≤ 7732927842361^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609900031 2500000000 7732927842361 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416273017/10000000000 : ℝ), (5012970869/10000000000 : ℝ), (-609900031/2500000000 : ℝ)] ![(5553601410629/12500000000000 : ℝ), (10026333253339/25000000000000 : ℝ), (7732927842361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416273017/10000000000 : ℝ)|^8387 ≤ (5553601410629/12500000000000 : ℝ)^6339
        have hw : |(5416273017/10000000000 : ℝ)|=(5416273017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5012970869/10000000000 : ℝ)|^8387 ≤ (10026333253339/25000000000000 : ℝ)^6339
        have hw : |(5012970869/10000000000 : ℝ)|=(5012970869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-609900031/2500000000 : ℝ)|^8387 ≤ (7732927842361/50000000000000 : ℝ)^6339
        have hw : |(-609900031/2500000000 : ℝ)|=(609900031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (269562609/625000000 : ℝ)*x 0 + (3686709539/10000000000 : ℝ)*x 1 + (5043039493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269562609/625000000 : ℝ)^8387 ≤ (32868847407801/100000000000000 : ℝ)^6339 := by
    have hnat : (269562609 : ℕ)^8387*100000000000000^6339 ≤ 32868847407801^6339*625000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269562609 625000000 32868847407801 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3686709539/10000000000 : ℝ)^8387 ≤ (20865026363/78125000000 : ℝ)^6339 := by
    have hnat : (3686709539 : ℕ)^8387*78125000000^6339 ≤ 20865026363^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686709539 10000000000 20865026363 78125000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5043039493/10000000000 : ℝ)^8387 ≤ (1010597970549/2500000000000 : ℝ)^6339 := by
    have hnat : (5043039493 : ℕ)^8387*2500000000000^6339 ≤ 1010597970549^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5043039493 10000000000 1010597970549 2500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269562609/625000000 : ℝ), (3686709539/10000000000 : ℝ), (5043039493/10000000000 : ℝ)] ![(32868847407801/100000000000000 : ℝ), (20865026363/78125000000 : ℝ), (1010597970549/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269562609/625000000 : ℝ)|^8387 ≤ (32868847407801/100000000000000 : ℝ)^6339
        have hw : |(269562609/625000000 : ℝ)|=(269562609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3686709539/10000000000 : ℝ)|^8387 ≤ (20865026363/78125000000 : ℝ)^6339
        have hw : |(3686709539/10000000000 : ℝ)|=(3686709539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5043039493/10000000000 : ℝ)|^8387 ≤ (1010597970549/2500000000000 : ℝ)^6339
        have hw : |(5043039493/10000000000 : ℝ)|=(5043039493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-519273739/2500000000 : ℝ)*x 0 + (5022002309/10000000000 : ℝ)*x 1 + (1419656283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519273739/2500000000 : ℝ)^8387 ≤ (12500880183101/100000000000000 : ℝ)^6339 := by
    have hnat : (519273739 : ℕ)^8387*100000000000000^6339 ≤ 12500880183101^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519273739 2500000000 12500880183101 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5022002309/10000000000 : ℝ)^8387 ≤ (1608038362053/4000000000000 : ℝ)^6339 := by
    have hnat : (5022002309 : ℕ)^8387*4000000000000^6339 ≤ 1608038362053^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022002309 10000000000 1608038362053 4000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419656283/2500000000 : ℝ)^8387 ≤ (5912270094387/12500000000000 : ℝ)^6339 := by
    have hnat : (1419656283 : ℕ)^8387*12500000000000^6339 ≤ 5912270094387^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419656283 2500000000 5912270094387 12500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519273739/2500000000 : ℝ), (5022002309/10000000000 : ℝ), (1419656283/2500000000 : ℝ)] ![(12500880183101/100000000000000 : ℝ), (1608038362053/4000000000000 : ℝ), (5912270094387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519273739/2500000000 : ℝ)|^8387 ≤ (12500880183101/100000000000000 : ℝ)^6339
        have hw : |(-519273739/2500000000 : ℝ)|=(519273739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5022002309/10000000000 : ℝ)|^8387 ≤ (1608038362053/4000000000000 : ℝ)^6339
        have hw : |(5022002309/10000000000 : ℝ)|=(5022002309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419656283/2500000000 : ℝ)|^8387 ≤ (5912270094387/12500000000000 : ℝ)^6339
        have hw : |(1419656283/2500000000 : ℝ)|=(1419656283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242806991/10000000000 : ℝ)*x 0 + (-886972451/5000000000 : ℝ)*x 1 + (1419656287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242806991/10000000000 : ℝ)^8387 ≤ (8511198961159/20000000000000 : ℝ)^6339 := by
    have hnat : (5242806991 : ℕ)^8387*20000000000000^6339 ≤ 8511198961159^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242806991 10000000000 8511198961159 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886972451/5000000000 : ℝ)^8387 ≤ (5072922123233/50000000000000 : ℝ)^6339 := by
    have hnat : (886972451 : ℕ)^8387*50000000000000^6339 ≤ 5072922123233^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886972451 5000000000 5072922123233 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419656287/2500000000 : ℝ)^8387 ≤ (23649080465709/50000000000000 : ℝ)^6339 := by
    have hnat : (1419656287 : ℕ)^8387*50000000000000^6339 ≤ 23649080465709^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419656287 2500000000 23649080465709 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242806991/10000000000 : ℝ), (-886972451/5000000000 : ℝ), (1419656287/2500000000 : ℝ)] ![(8511198961159/20000000000000 : ℝ), (5072922123233/50000000000000 : ℝ), (23649080465709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242806991/10000000000 : ℝ)|^8387 ≤ (8511198961159/20000000000000 : ℝ)^6339
        have hw : |(5242806991/10000000000 : ℝ)|=(5242806991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-886972451/5000000000 : ℝ)|^8387 ≤ (5072922123233/50000000000000 : ℝ)^6339
        have hw : |(-886972451/5000000000 : ℝ)|=(886972451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419656287/2500000000 : ℝ)|^8387 ≤ (23649080465709/50000000000000 : ℝ)^6339
        have hw : |(1419656287/2500000000 : ℝ)|=(1419656287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242806937/10000000000 : ℝ)*x 0 + (1419656449/2500000000 : ℝ)*x 1 + (-354788807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242806937/10000000000 : ℝ)^8387 ≤ (5319499278233/12500000000000 : ℝ)^6339 := by
    have hnat : (5242806937 : ℕ)^8387*12500000000000^6339 ≤ 5319499278233^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242806937 10000000000 5319499278233 12500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1419656449/2500000000 : ℝ)^8387 ≤ (47298168072467/100000000000000 : ℝ)^6339 := by
    have hnat : (1419656449 : ℕ)^8387*100000000000000^6339 ≤ 47298168072467^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419656449 2500000000 47298168072467 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354788807/2000000000 : ℝ)^8387 ≤ (10145837685723/100000000000000 : ℝ)^6339 := by
    have hnat : (354788807 : ℕ)^8387*100000000000000^6339 ≤ 10145837685723^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354788807 2000000000 10145837685723 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242806937/10000000000 : ℝ), (1419656449/2500000000 : ℝ), (-354788807/2000000000 : ℝ)] ![(5319499278233/12500000000000 : ℝ), (47298168072467/100000000000000 : ℝ), (10145837685723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242806937/10000000000 : ℝ)|^8387 ≤ (5319499278233/12500000000000 : ℝ)^6339
        have hw : |(5242806937/10000000000 : ℝ)|=(5242806937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1419656449/2500000000 : ℝ)|^8387 ≤ (47298168072467/100000000000000 : ℝ)^6339
        have hw : |(1419656449/2500000000 : ℝ)|=(1419656449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-354788807/2000000000 : ℝ)|^8387 ≤ (10145837685723/100000000000000 : ℝ)^6339
        have hw : |(-354788807/2000000000 : ℝ)|=(354788807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s1_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4314479981/10000000000 : ℝ)*x 0 + (5024886257/10000000000 : ℝ)*x 1 + (741042889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314479981/10000000000 : ℝ)^8387 ≤ (32883753329781/100000000000000 : ℝ)^6339 := by
    have hnat : (4314479981 : ℕ)^8387*100000000000000^6339 ≤ 32883753329781^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314479981 10000000000 32883753329781 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024886257/10000000000 : ℝ)^8387 ≤ (40231506370543/100000000000000 : ℝ)^6339 := by
    have hnat : (5024886257 : ℕ)^8387*100000000000000^6339 ≤ 40231506370543^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024886257 10000000000 40231506370543 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741042889/2000000000 : ℝ)^8387 ≤ (26884740283483/100000000000000 : ℝ)^6339 := by
    have hnat : (741042889 : ℕ)^8387*100000000000000^6339 ≤ 26884740283483^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741042889 2000000000 26884740283483 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314479981/10000000000 : ℝ), (5024886257/10000000000 : ℝ), (741042889/2000000000 : ℝ)] ![(32883753329781/100000000000000 : ℝ), (40231506370543/100000000000000 : ℝ), (26884740283483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314479981/10000000000 : ℝ)|^8387 ≤ (32883753329781/100000000000000 : ℝ)^6339
        have hw : |(4314479981/10000000000 : ℝ)|=(4314479981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024886257/10000000000 : ℝ)|^8387 ≤ (40231506370543/100000000000000 : ℝ)^6339
        have hw : |(5024886257/10000000000 : ℝ)|=(5024886257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741042889/2000000000 : ℝ)|^8387 ≤ (26884740283483/100000000000000 : ℝ)^6339
        have hw : |(741042889/2000000000 : ℝ)|=(741042889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27617/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (371/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4041/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27617/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27617/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27617/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27617/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27617/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27617/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (313/50000 : ℝ) ^ (4193/1024 : ℝ) ≤ (94967366231/100000000000000000000 : ℝ) := by
    have hpowers : (313/50000 : ℝ)^4193 ≤ (94967366231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (313 : ℕ)^4193*100000000000000000000^1024 ≤ 94967366231^1024*50000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        313 50000 94967366231 100000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (313/50000 : ℝ)) (X := (94967366231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27617/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (64369566382347637/12500000000000000000 : ℝ) := by
    have hpowers : (27617/100000 : ℝ)^4193 ≤ (64369566382347637/12500000000000000000 : ℝ)^1024 := by
      have hnat : (27617 : ℕ)^4193*12500000000000000000^1024 ≤ 64369566382347637^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27617 100000 64369566382347637 12500000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27617/100000 : ℝ)) (X := (64369566382347637/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000094967366231/50000000000000000000 : ℝ) ≤ (10000000004638521/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (50000000094967366231/50000000000000000000 : ℝ)^1024 ≤ (10000000004638521/10000000000000000 : ℝ)^4193 := by
      have hnat : (50000000094967366231 : ℕ)^1024*10000000000000000^4193 ≤ 10000000004638521^4193*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000094967366231 50000000000000000000 10000000004638521 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000004638521/10000000000000000 : ℝ)) (X := (50000000094967366231/50000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100514956626026147327/100000000000000000000 : ℝ) ≤ (2503137923455647/2500000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (100514956626026147327/100000000000000000000 : ℝ)^1024 ≤ (2503137923455647/2500000000000000 : ℝ)^4193 := by
      have hnat : (100514956626026147327 : ℕ)^1024*2500000000000000^4193 ≤ 2503137923455647^4193*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100514956626026147327 100000000000000000000 2503137923455647 2500000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503137923455647/2500000000000000 : ℝ)) (X := (100514956626026147327/100000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6314369566382347637/6250000000000000000 : ℝ) ≤ (2005020676601331/2000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (6314369566382347637/6250000000000000000 : ℝ)^1024 ≤ (2005020676601331/2000000000000000 : ℝ)^4193 := by
      have hnat : (6314369566382347637 : ℕ)^1024*2000000000000000^4193 ≤ 2005020676601331^4193*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6314369566382347637 6250000000000000000 2005020676601331 2000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005020676601331/2000000000000000 : ℝ)) (X := (6314369566382347637/6250000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(94967366231/100000000000000000000 : ℝ) ≤ ((29988253934482207603/29990000000000000000 : ℝ)+2*(1394632131563/299900000000000 : ℝ)*(313/50000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (29988253934482207603/29990000000000000000 : ℝ)+2*(1394632131563/299900000000000 : ℝ)*(313/50000 : ℝ)=(10000000004638521/10000000000000000 : ℝ) by norm_num, show 1+2*(94967366231/100000000000000000000 : ℝ)=(50000000094967366231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64369566382347637/12500000000000000000 : ℝ)+(94967366231/100000000000000000000 : ℝ) ≤ ((29988253934482207603/29990000000000000000 : ℝ)+(1394632131563/299900000000000 : ℝ)*((27617/100000 : ℝ)+(313/50000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (29988253934482207603/29990000000000000000 : ℝ)+(1394632131563/299900000000000 : ℝ)*((27617/100000 : ℝ)+(313/50000 : ℝ))=(2503137923455647/2500000000000000 : ℝ) by norm_num, show 1+(64369566382347637/12500000000000000000 : ℝ)+(94967366231/100000000000000000000 : ℝ)=(100514956626026147327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64369566382347637/12500000000000000000 : ℝ) ≤ ((29988253934482207603/29990000000000000000 : ℝ)+2*(1394632131563/299900000000000 : ℝ)*(27617/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (29988253934482207603/29990000000000000000 : ℝ)+2*(1394632131563/299900000000000 : ℝ)*(27617/100000 : ℝ)=(2005020676601331/2000000000000000 : ℝ) by norm_num, show 1+2*(64369566382347637/12500000000000000000 : ℝ)=(6314369566382347637/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29988253934482207603/29990000000000000000 : ℝ)*(X 1 0+X 2 0)+(1394632131563/299900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (313/50000 : ℝ)) (hi := (27617/100000 : ℝ)) (c := (29988253934482207603/29990000000000000000 : ℝ)) (alpha := (1394632131563/299900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29988253934482207603/29990000000000000000 : ℝ)*(X 0 1+X 2 1)+(1394632131563/299900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (313/50000 : ℝ)) (hi := (27617/100000 : ℝ)) (c := (29988253934482207603/29990000000000000000 : ℝ)) (alpha := (1394632131563/299900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29988253934482207603/29990000000000000000 : ℝ)*(X 0 2+X 1 2)+(1394632131563/299900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (313/50000 : ℝ)) (hi := (27617/100000 : ℝ)) (c := (29988253934482207603/29990000000000000000 : ℝ)) (alpha := (1394632131563/299900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1038179619/5000000000 : ℝ)*X 0 0+(5687832631/10000000000 : ℝ)*X 0 1+(2506484947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541627401/1000000000 : ℝ)*X 1 0+(-487919931/2000000000 : ℝ)*X 1 1+(5012970223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5416273017/10000000000 : ℝ)*X 2 0+(5012970869/10000000000 : ℝ)*X 2 1+(-609900031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269562609/625000000 : ℝ)*X 0 0+(3686709539/10000000000 : ℝ)*X 0 1+(5043039493/10000000000 : ℝ)*X 0 2+(269562609/625000000 : ℝ)*X 1 0+(3686709539/10000000000 : ℝ)*X 1 1+(5043039493/10000000000 : ℝ)*X 1 2+(269562609/625000000 : ℝ)*X 2 0+(3686709539/10000000000 : ℝ)*X 2 1+(5043039493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-519273739/2500000000 : ℝ)*X 0 0+(5022002309/10000000000 : ℝ)*X 0 1+(1419656283/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242806991/10000000000 : ℝ)*X 1 0+(-886972451/5000000000 : ℝ)*X 1 1+(1419656287/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242806937/10000000000 : ℝ)*X 2 0+(1419656449/2500000000 : ℝ)*X 2 1+(-354788807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314479981/10000000000 : ℝ)*X 0 0+(5024886257/10000000000 : ℝ)*X 0 1+(741042889/2000000000 : ℝ)*X 0 2+(4314479981/10000000000 : ℝ)*X 1 0+(5024886257/10000000000 : ℝ)*X 1 1+(741042889/2000000000 : ℝ)*X 1 2+(4314479981/10000000000 : ℝ)*X 2 0+(5024886257/10000000000 : ℝ)*X 2 1+(741042889/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1852250988289972283953657587/749750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968661/12500000000000 : ℝ)*(base16) + (144726443/20000000000000 : ℝ)*(base19) + (522586563/100000000000000 : ℝ)*(base23) + (34052863/100000000000000 : ℝ)*(upper2) + (84786727/50000000000000 : ℝ)*(upper3) + (1109540524085243/100000000000000 : ℝ)*(major0) + (1109540524085243/100000000000000 : ℝ)*(major1) + (1109540524085243/100000000000000 : ℝ)*(major2) + (370447190231909/25000000000000 : ℝ)*(sp0) + (1481791577484237/100000000000000 : ℝ)*(sp1) + (1481791786279177/100000000000000 : ℝ)*(sp2) + (737285944302277/100000000000000 : ℝ)*(sp3) + (709587621/20000000000000 : ℝ)*(sp4) + (2712652747/100000000000000 : ℝ)*(sp7) + (46080541059689/6250000000000 : ℝ)*(f.failure) + (74089615443287/5000000000000 : ℝ)*(f.sum) + (6296824783193/1874375000000000000000000000 : ℝ)*base65 + (27080112782681397471/2999000000000000000000000000000000 : ℝ)*base68 + (23687069305304397471/2999000000000000000000000000000000 : ℝ)*base70 + (16609152932459397471/2999000000000000000000000000000000 : ℝ)*base72 + (17506004744989/3748750000000000000000000000 : ℝ)*base74 + (7848838696897397471/2999000000000000000000000000000000 : ℝ)*base76 + (3885153437179602529/2999000000000000000000000000000000 : ℝ)*base77 + (17581440218629397471/2999000000000000000000000000000000 : ℝ)*base80 + (19199335905051/14995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2479161/312500000000000000000 : ℝ)*base89 + (2479161/312500000000000000000 : ℝ)*base91 + (2479161/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1217626171129834591154372001/1499500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (567919877/100000000000000 : ℝ)*(base19) + (157468473/20000000000000 : ℝ)*(base23) + (38653231/50000000000000 : ℝ)*(upper2) + (70366877/100000000000000 : ℝ)*(upper3) + (57123959/100000000000000 : ℝ)*(upper5) + (1140354052038089/100000000000000 : ℝ)*(major0) + (1140354052038089/100000000000000 : ℝ)*(major1) + (1140354052038089/100000000000000 : ℝ)*(major2) + (2666386049/100000000000000 : ℝ)*(sp1) + (2657851323/50000000000000 : ℝ)*(sp2) + (761471929546027/50000000000000 : ℝ)*(sp4) + (95183789049133/6250000000000 : ℝ)*(sp5) + (380734439011761/25000000000000 : ℝ)*(sp6) + (378882108958369/50000000000000 : ℝ)*(sp7) + (378882108958369/50000000000000 : ℝ)*(f.failure) + (761471929546027/50000000000000 : ℝ)*(f.sum) + (62416986495123/14995000000000000000000000000 : ℝ)*base66 + (3424955073175909333/2999000000000000000000000000000000 : ℝ)*base68 + (5695726128010090667/2999000000000000000000000000000000 : ℝ)*base69 + (2668028358211909333/2999000000000000000000000000000000 : ℝ)*base72 + (35561502468159/7497500000000000000000000000 : ℝ)*base74 + (3608227963753090667/2999000000000000000000000000000000 : ℝ)*base75 + (21631724634339909333/2999000000000000000000000000000000 : ℝ)*base78 + (21060915595463909333/2999000000000000000000000000000000 : ℝ)*base80 + (16903153461937/14995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6017481/2500000000000000000000 : ℝ)*base89 + (6017481/2500000000000000000000 : ℝ)*base91 + (6017481/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27617/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (371/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s2_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-26585629/125000000 : ℝ)*x 0 + (85955937/156250000 : ℝ)*x 1 + (5167466901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26585629/125000000 : ℝ)^8387 ≤ (12898601044941/100000000000000 : ℝ)^6339 := by
    have hnat : (26585629 : ℕ)^8387*100000000000000^6339 ≤ 12898601044941^6339*125000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26585629 125000000 12898601044941 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85955937/156250000 : ℝ)^8387 ≤ (22676316130259/50000000000000 : ℝ)^6339 := by
    have hnat : (85955937 : ℕ)^8387*50000000000000^6339 ≤ 22676316130259^6339*156250000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85955937 156250000 22676316130259 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167466901/10000000000 : ℝ)^8387 ≤ (41748766683629/100000000000000 : ℝ)^6339 := by
    have hnat : (5167466901 : ℕ)^8387*100000000000000^6339 ≤ 41748766683629^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167466901 10000000000 41748766683629 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26585629/125000000 : ℝ), (85955937/156250000 : ℝ), (5167466901/10000000000 : ℝ)] ![(12898601044941/100000000000000 : ℝ), (22676316130259/50000000000000 : ℝ), (41748766683629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26585629/125000000 : ℝ)|^8387 ≤ (12898601044941/100000000000000 : ℝ)^6339
        have hw : |(-26585629/125000000 : ℝ)|=(26585629/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85955937/156250000 : ℝ)|^8387 ≤ (22676316130259/50000000000000 : ℝ)^6339
        have hw : |(85955937/156250000 : ℝ)|=(85955937/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167466901/10000000000 : ℝ)|^8387 ≤ (41748766683629/100000000000000 : ℝ)^6339
        have hw : |(5167466901/10000000000 : ℝ)|=(5167466901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371657953/10000000000 : ℝ)*x 0 + (-2300004377/10000000000 : ℝ)*x 1 + (2583735551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371657953/10000000000 : ℝ)^8387 ≤ (8789049848263/20000000000000 : ℝ)^6339 := by
    have hnat : (5371657953 : ℕ)^8387*20000000000000^6339 ≤ 8789049848263^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371657953 10000000000 8789049848263 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2300004377/10000000000 : ℝ)^8387 ≤ (14305939155563/100000000000000 : ℝ)^6339 := by
    have hnat : (2300004377 : ℕ)^8387*100000000000000^6339 ≤ 14305939155563^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300004377 10000000000 14305939155563 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583735551/5000000000 : ℝ)^8387 ≤ (834976231793/2000000000000 : ℝ)^6339 := by
    have hnat : (2583735551 : ℕ)^8387*2000000000000^6339 ≤ 834976231793^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583735551 5000000000 834976231793 2000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371657953/10000000000 : ℝ), (-2300004377/10000000000 : ℝ), (2583735551/5000000000 : ℝ)] ![(8789049848263/20000000000000 : ℝ), (14305939155563/100000000000000 : ℝ), (834976231793/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371657953/10000000000 : ℝ)|^8387 ≤ (8789049848263/20000000000000 : ℝ)^6339
        have hw : |(5371657953/10000000000 : ℝ)|=(5371657953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2300004377/10000000000 : ℝ)|^8387 ≤ (14305939155563/100000000000000 : ℝ)^6339
        have hw : |(-2300004377/10000000000 : ℝ)|=(2300004377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583735551/5000000000 : ℝ)|^8387 ≤ (834976231793/2000000000000 : ℝ)^6339
        have hw : |(2583735551/5000000000 : ℝ)|=(2583735551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371659691/10000000000 : ℝ)*x 0 + (516746867/1000000000 : ℝ)*x 1 + (-9200021/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371659691/10000000000 : ℝ)^8387 ≤ (43945268053501/100000000000000 : ℝ)^6339 := by
    have hnat : (5371659691 : ℕ)^8387*100000000000000^6339 ≤ 43945268053501^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371659691 10000000000 43945268053501 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516746867/1000000000 : ℝ)^8387 ≤ (41748785593113/100000000000000 : ℝ)^6339 := by
    have hnat : (516746867 : ℕ)^8387*100000000000000^6339 ≤ 41748785593113^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516746867 1000000000 41748785593113 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9200021/40000000 : ℝ)^8387 ≤ (14305946339919/100000000000000 : ℝ)^6339 := by
    have hnat : (9200021 : ℕ)^8387*100000000000000^6339 ≤ 14305946339919^6339*40000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9200021 40000000 14305946339919 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371659691/10000000000 : ℝ), (516746867/1000000000 : ℝ), (-9200021/40000000 : ℝ)] ![(43945268053501/100000000000000 : ℝ), (41748785593113/100000000000000 : ℝ), (14305946339919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371659691/10000000000 : ℝ)|^8387 ≤ (43945268053501/100000000000000 : ℝ)^6339
        have hw : |(5371659691/10000000000 : ℝ)|=(5371659691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516746867/1000000000 : ℝ)|^8387 ≤ (41748785593113/100000000000000 : ℝ)^6339
        have hw : |(516746867/1000000000 : ℝ)|=(516746867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9200021/40000000 : ℝ)|^8387 ≤ (14305946339919/100000000000000 : ℝ)^6339
        have hw : |(-9200021/40000000 : ℝ)|=(9200021/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347765191/10000000000 : ℝ)*x 0 + (2012542773/5000000000 : ℝ)*x 1 + (4695773253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347765191/10000000000 : ℝ)^8387 ≤ (33219823585763/100000000000000 : ℝ)^6339 := by
    have hnat : (4347765191 : ℕ)^8387*100000000000000^6339 ≤ 33219823585763^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347765191 10000000000 33219823585763 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012542773/5000000000 : ℝ)^8387 ≤ (468712074989/1562500000000 : ℝ)^6339 := by
    have hnat : (2012542773 : ℕ)^8387*1562500000000^6339 ≤ 468712074989^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012542773 5000000000 468712074989 1562500000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4695773253/10000000000 : ℝ)^8387 ≤ (18391301795259/50000000000000 : ℝ)^6339 := by
    have hnat : (4695773253 : ℕ)^8387*50000000000000^6339 ≤ 18391301795259^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695773253 10000000000 18391301795259 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347765191/10000000000 : ℝ), (2012542773/5000000000 : ℝ), (4695773253/10000000000 : ℝ)] ![(33219823585763/100000000000000 : ℝ), (468712074989/1562500000000 : ℝ), (18391301795259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347765191/10000000000 : ℝ)|^8387 ≤ (33219823585763/100000000000000 : ℝ)^6339
        have hw : |(4347765191/10000000000 : ℝ)|=(4347765191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012542773/5000000000 : ℝ)|^8387 ≤ (468712074989/1562500000000 : ℝ)^6339
        have hw : |(2012542773/5000000000 : ℝ)|=(2012542773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4695773253/10000000000 : ℝ)|^8387 ≤ (18391301795259/50000000000000 : ℝ)^6339
        have hw : |(4695773253/10000000000 : ℝ)|=(4695773253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2658673/12500000 : ℝ)*x 0 + (161552709/312500000 : ℝ)*x 1 + (5498939517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2658673/12500000 : ℝ)^8387 ≤ (6449653902327/50000000000000 : ℝ)^6339 := by
    have hnat : (2658673 : ℕ)^8387*50000000000000^6339 ≤ 6449653902327^6339*12500000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2658673 12500000 6449653902327 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161552709/312500000 : ℝ)^8387 ≤ (41772496439733/100000000000000 : ℝ)^6339 := by
    have hnat : (161552709 : ℕ)^8387*100000000000000^6339 ≤ 41772496439733^6339*312500000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161552709 312500000 41772496439733 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498939517/10000000000 : ℝ)^8387 ≤ (22664097868767/50000000000000 : ℝ)^6339 := by
    have hnat : (5498939517 : ℕ)^8387*50000000000000^6339 ≤ 22664097868767^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498939517 10000000000 22664097868767 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2658673/12500000 : ℝ), (161552709/312500000 : ℝ), (5498939517/10000000000 : ℝ)] ![(6449653902327/50000000000000 : ℝ), (41772496439733/100000000000000 : ℝ), (22664097868767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2658673/12500000 : ℝ)|^8387 ≤ (6449653902327/50000000000000 : ℝ)^6339
        have hw : |(-2658673/12500000 : ℝ)|=(2658673/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161552709/312500000 : ℝ)|^8387 ≤ (41772496439733/100000000000000 : ℝ)^6339
        have hw : |(161552709/312500000 : ℝ)|=(161552709/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498939517/10000000000 : ℝ)|^8387 ≤ (22664097868767/50000000000000 : ℝ)^6339
        have hw : |(5498939517/10000000000 : ℝ)|=(5498939517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132167439/250000000 : ℝ)*x 0 + (-1968534337/10000000000 : ℝ)*x 1 + (5498939533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132167439/250000000 : ℝ)^8387 ≤ (43027992409279/100000000000000 : ℝ)^6339 := by
    have hnat : (132167439 : ℕ)^8387*100000000000000^6339 ≤ 43027992409279^6339*250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132167439 250000000 43027992409279 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968534337/10000000000 : ℝ)^8387 ≤ (11643811658639/100000000000000 : ℝ)^6339 := by
    have hnat : (1968534337 : ℕ)^8387*100000000000000^6339 ≤ 11643811658639^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968534337 10000000000 11643811658639 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498939533/10000000000 : ℝ)^8387 ≤ (22664097956017/50000000000000 : ℝ)^6339 := by
    have hnat : (5498939533 : ℕ)^8387*50000000000000^6339 ≤ 22664097956017^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498939533 10000000000 22664097956017 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132167439/250000000 : ℝ), (-1968534337/10000000000 : ℝ), (5498939533/10000000000 : ℝ)] ![(43027992409279/100000000000000 : ℝ), (11643811658639/100000000000000 : ℝ), (22664097956017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132167439/250000000 : ℝ)|^8387 ≤ (43027992409279/100000000000000 : ℝ)^6339
        have hw : |(132167439/250000000 : ℝ)|=(132167439/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968534337/10000000000 : ℝ)|^8387 ≤ (11643811658639/100000000000000 : ℝ)^6339
        have hw : |(-1968534337/10000000000 : ℝ)|=(1968534337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498939533/10000000000 : ℝ)|^8387 ≤ (22664097956017/50000000000000 : ℝ)^6339
        have hw : |(5498939533/10000000000 : ℝ)|=(5498939533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643348863/5000000000 : ℝ)*x 0 + (2749469773/5000000000 : ℝ)*x 1 + (-1968534091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643348863/5000000000 : ℝ)^8387 ≤ (21513997098419/50000000000000 : ℝ)^6339 := by
    have hnat : (2643348863 : ℕ)^8387*50000000000000^6339 ≤ 21513997098419^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643348863 5000000000 21513997098419 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749469773/5000000000 : ℝ)^8387 ≤ (9065639210763/20000000000000 : ℝ)^6339 := by
    have hnat : (2749469773 : ℕ)^8387*20000000000000^6339 ≤ 9065639210763^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749469773 5000000000 9065639210763 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968534091/10000000000 : ℝ)^8387 ≤ (11643809733451/100000000000000 : ℝ)^6339 := by
    have hnat : (1968534091 : ℕ)^8387*100000000000000^6339 ≤ 11643809733451^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968534091 10000000000 11643809733451 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643348863/5000000000 : ℝ), (2749469773/5000000000 : ℝ), (-1968534091/10000000000 : ℝ)] ![(21513997098419/50000000000000 : ℝ), (9065639210763/20000000000000 : ℝ), (11643809733451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643348863/5000000000 : ℝ)|^8387 ≤ (21513997098419/50000000000000 : ℝ)^6339
        have hw : |(2643348863/5000000000 : ℝ)|=(2643348863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749469773/5000000000 : ℝ)|^8387 ≤ (9065639210763/20000000000000 : ℝ)^6339
        have hw : |(2749469773/5000000000 : ℝ)|=(2749469773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968534091/10000000000 : ℝ)|^8387 ≤ (11643809733451/100000000000000 : ℝ)^6339
        have hw : |(-1968534091/10000000000 : ℝ)|=(1968534091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s2_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217397223/500000000 : ℝ)*x 0 + (4691314669/10000000000 : ℝ)*x 1 + (1007396607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217397223/500000000 : ℝ)^8387 ≤ (33221635865441/100000000000000 : ℝ)^6339 := by
    have hnat : (217397223 : ℕ)^8387*100000000000000^6339 ≤ 33221635865441^6339*500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217397223 500000000 33221635865441 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4691314669/10000000000 : ℝ)^8387 ≤ (18368201285359/50000000000000 : ℝ)^6339 := by
    have hnat : (4691314669 : ℕ)^8387*50000000000000^6339 ≤ 18368201285359^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4691314669 10000000000 18368201285359 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007396607/2500000000 : ℝ)^8387 ≤ (30041961551949/100000000000000 : ℝ)^6339 := by
    have hnat : (1007396607 : ℕ)^8387*100000000000000^6339 ≤ 30041961551949^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007396607 2500000000 30041961551949 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217397223/500000000 : ℝ), (4691314669/10000000000 : ℝ), (1007396607/2500000000 : ℝ)] ![(33221635865441/100000000000000 : ℝ), (18368201285359/50000000000000 : ℝ), (30041961551949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217397223/500000000 : ℝ)|^8387 ≤ (33221635865441/100000000000000 : ℝ)^6339
        have hw : |(217397223/500000000 : ℝ)|=(217397223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4691314669/10000000000 : ℝ)|^8387 ≤ (18368201285359/50000000000000 : ℝ)^6339
        have hw : |(4691314669/10000000000 : ℝ)|=(4691314669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007396607/2500000000 : ℝ)|^8387 ≤ (30041961551949/100000000000000 : ℝ)^6339
        have hw : |(1007396607/2500000000 : ℝ)|=(1007396607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (511/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4041/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (371/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4041/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (371/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4041/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (371/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4041/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (371/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4041/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (371/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4041/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (371/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (371/6250 : ℝ) ^ (4193/1024 : ℝ) ≤ (95015150723161/10000000000000000000 : ℝ) := by
    have hpowers : (371/6250 : ℝ)^4193 ≤ (95015150723161/10000000000000000000 : ℝ)^1024 := by
      have hnat : (371 : ℕ)^4193*10000000000000000000^1024 ≤ 95015150723161^1024*6250^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        371 6250 95015150723161 10000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (371/6250 : ℝ)) (X := (95015150723161/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4041/20000 : ℝ) ^ (4193/1024 : ℝ) ≤ (71616637800121757/50000000000000000000 : ℝ) := by
    have hpowers : (4041/20000 : ℝ)^4193 ≤ (71616637800121757/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4041 : ℕ)^4193*50000000000000000000^1024 ≤ 71616637800121757^1024*20000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4041 20000 71616637800121757 50000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4041/20000 : ℝ)) (X := (71616637800121757/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000095015150723161/5000000000000000000 : ℝ) ≤ (500002320410581/500000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (5000095015150723161/5000000000000000000 : ℝ)^1024 ≤ (500002320410581/500000000000000 : ℝ)^4193 := by
      have hnat : (5000095015150723161 : ℕ)^1024*500000000000000^4193 ≤ 500002320410581^4193*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000095015150723161 5000000000000000000 500002320410581 500000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002320410581/500000000000000 : ℝ)) (X := (5000095015150723161/5000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25036045856776868781/25000000000000000000 : ℝ) ≤ (10003519281000831/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (25036045856776868781/25000000000000000000 : ℝ)^1024 ≤ (10003519281000831/10000000000000000 : ℝ)^4193 := by
      have hnat : (25036045856776868781 : ℕ)^1024*10000000000000000^4193 ≤ 10003519281000831^4193*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036045856776868781 25000000000000000000 10003519281000831 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003519281000831/10000000000000000 : ℝ)) (X := (25036045856776868781/25000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25071616637800121757/25000000000000000000 : ℝ) ≤ (5003496076895021/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (25071616637800121757/25000000000000000000 : ℝ)^1024 ≤ (5003496076895021/5000000000000000 : ℝ)^4193 := by
      have hnat : (25071616637800121757 : ℕ)^1024*5000000000000000^4193 ≤ 5003496076895021^4193*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071616637800121757 25000000000000000000 5003496076895021 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003496076895021/5000000000000000 : ℝ)) (X := (25071616637800121757/25000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(95015150723161/10000000000000000000 : ℝ) ≤ ((35662358063254523197/35672500000000000000 : ℝ)+2*(3472872789211/1426900000000000 : ℝ)*(371/6250 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (35662358063254523197/35672500000000000000 : ℝ)+2*(3472872789211/1426900000000000 : ℝ)*(371/6250 : ℝ)=(500002320410581/500000000000000 : ℝ) by norm_num, show 1+2*(95015150723161/10000000000000000000 : ℝ)=(5000095015150723161/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71616637800121757/50000000000000000000 : ℝ)+(95015150723161/10000000000000000000 : ℝ) ≤ ((35662358063254523197/35672500000000000000 : ℝ)+(3472872789211/1426900000000000 : ℝ)*((4041/20000 : ℝ)+(371/6250 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (35662358063254523197/35672500000000000000 : ℝ)+(3472872789211/1426900000000000 : ℝ)*((4041/20000 : ℝ)+(371/6250 : ℝ))=(10003519281000831/10000000000000000 : ℝ) by norm_num, show 1+(71616637800121757/50000000000000000000 : ℝ)+(95015150723161/10000000000000000000 : ℝ)=(25036045856776868781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71616637800121757/50000000000000000000 : ℝ) ≤ ((35662358063254523197/35672500000000000000 : ℝ)+2*(3472872789211/1426900000000000 : ℝ)*(4041/20000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (35662358063254523197/35672500000000000000 : ℝ)+2*(3472872789211/1426900000000000 : ℝ)*(4041/20000 : ℝ)=(5003496076895021/5000000000000000 : ℝ) by norm_num, show 1+2*(71616637800121757/50000000000000000000 : ℝ)=(25071616637800121757/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35662358063254523197/35672500000000000000 : ℝ)*(X 1 0+X 2 0)+(3472872789211/1426900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (371/6250 : ℝ)) (hi := (4041/20000 : ℝ)) (c := (35662358063254523197/35672500000000000000 : ℝ)) (alpha := (3472872789211/1426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35662358063254523197/35672500000000000000 : ℝ)*(X 0 1+X 2 1)+(3472872789211/1426900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (371/6250 : ℝ)) (hi := (4041/20000 : ℝ)) (c := (35662358063254523197/35672500000000000000 : ℝ)) (alpha := (3472872789211/1426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35662358063254523197/35672500000000000000 : ℝ)*(X 0 2+X 1 2)+(3472872789211/1426900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (371/6250 : ℝ)) (hi := (4041/20000 : ℝ)) (c := (35662358063254523197/35672500000000000000 : ℝ)) (alpha := (3472872789211/1426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-26585629/125000000 : ℝ)*X 0 0+(85955937/156250000 : ℝ)*X 0 1+(5167466901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371657953/10000000000 : ℝ)*X 1 0+(-2300004377/10000000000 : ℝ)*X 1 1+(2583735551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371659691/10000000000 : ℝ)*X 2 0+(516746867/1000000000 : ℝ)*X 2 1+(-9200021/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347765191/10000000000 : ℝ)*X 0 0+(2012542773/5000000000 : ℝ)*X 0 1+(4695773253/10000000000 : ℝ)*X 0 2+(4347765191/10000000000 : ℝ)*X 1 0+(2012542773/5000000000 : ℝ)*X 1 1+(4695773253/10000000000 : ℝ)*X 1 2+(4347765191/10000000000 : ℝ)*X 2 0+(2012542773/5000000000 : ℝ)*X 2 1+(4695773253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2658673/12500000 : ℝ)*X 0 0+(161552709/312500000 : ℝ)*X 0 1+(5498939517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132167439/250000000 : ℝ)*X 1 0+(-1968534337/10000000000 : ℝ)*X 1 1+(5498939533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643348863/5000000000 : ℝ)*X 2 0+(2749469773/5000000000 : ℝ)*X 2 1+(-1968534091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217397223/500000000 : ℝ)*X 0 0+(4691314669/10000000000 : ℝ)*X 0 1+(1007396607/2500000000 : ℝ)*X 0 2+(217397223/500000000 : ℝ)*X 1 0+(4691314669/10000000000 : ℝ)*X 1 1+(1007396607/2500000000 : ℝ)*X 1 2+(217397223/500000000 : ℝ)*X 2 0+(4691314669/10000000000 : ℝ)*X 2 1+(1007396607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7198801939364019185465534247/891812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124751253/10000000000000 : ℝ)*(base19) + (1872770349/100000000000000 : ℝ)*(base23) + (76804579/100000000000000 : ℝ)*(upper2) + (635453989/100000000000000 : ℝ)*(upper3) + (130878849/50000000000000 : ℝ)*(upper4) + (1121925961912261/50000000000000 : ℝ)*(major0) + (1121925961912261/50000000000000 : ℝ)*(major1) + (1121925961912261/50000000000000 : ℝ)*(major2) + (374578630599747/12500000000000 : ℝ)*(sp0) + (1498332396542567/50000000000000 : ℝ)*(sp1) + (599332833565463/20000000000000 : ℝ)*(sp2) + (14910182317373/1000000000000 : ℝ)*(sp3) + (4624474961/12500000000000 : ℝ)*(sp4) + (19306243987/100000000000000 : ℝ)*(sp7) + (745518768990643/50000000000000 : ℝ)*(f.failure) + (93645813768677/3125000000000 : ℝ)*(f.sum) + (14430953286929/35672500000000000000000000000 : ℝ)*base66 + (7743610763700618417/1783625000000000000000000000000000 : ℝ)*base67 + (985457078085993417/1783625000000000000000000000000000 : ℝ)*base69 + (910636481440243417/1783625000000000000000000000000000 : ℝ)*base71 + (50013186659683/71345000000000000000000000000 : ℝ)*base74 + (10261137184295493417/1783625000000000000000000000000000 : ℝ)*base75 + (5232201179809368417/1783625000000000000000000000000000 : ℝ)*base77 + (2238589650910368417/1783625000000000000000000000000000 : ℝ)*base79 + (56545671030257/17836250000000000000000000000 : ℝ)*base82 + (33180693/2500000000000000000000 : ℝ)*base90 + (33180693/2500000000000000000000 : ℝ)*base92 + (33180693/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1023267927582977872590263547/445906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373693473/50000000000000 : ℝ)*(base19) + (199220579/20000000000000 : ℝ)*(base23) + (22658759/50000000000000 : ℝ)*(upper2) + (55437139/50000000000000 : ℝ)*(upper3) + (781547/1562500000000 : ℝ)*(upper5) + (568546710194411/25000000000000 : ℝ)*(major0) + (568546710194411/25000000000000 : ℝ)*(major1) + (568546710194411/25000000000000 : ℝ)*(major2) + (1737636003/25000000000000 : ℝ)*(sp1) + (11158643739/100000000000000 : ℝ)*(sp2) + (759294635671887/25000000000000 : ℝ)*(sp4) + (303717084475659/10000000000000 : ℝ)*(sp5) + (1518583193970457/50000000000000 : ℝ)*(sp6) + (188899382796779/12500000000000 : ℝ)*(sp7) + (188899382796779/12500000000000 : ℝ)*(f.failure) + (759294635671887/25000000000000 : ℝ)*(f.sum) + (21892020798879/17836250000000000000000000000 : ℝ)*base66 + (7701714299446776967/891812500000000000000000000000000 : ℝ)*base67 + (3446888116620526967/891812500000000000000000000000000 : ℝ)*base69 + (5932151109999526967/891812500000000000000000000000000 : ℝ)*base71 + (14101893747373/35672500000000000000000000000 : ℝ)*base74 + (8243609220077901967/891812500000000000000000000000000 : ℝ)*base75 + (5933276241161214467/891812500000000000000000000000000 : ℝ)*base77 + (4276100935112401967/891812500000000000000000000000000 : ℝ)*base79 + (12131040195983/2229531250000000000000000000 : ℝ)*base82 + (814429/625000000000000000000 : ℝ)*base90 + (814429/625000000000000000000 : ℝ)*base92 + (814429/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1194_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1194_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1194_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1194_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1194_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (511/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

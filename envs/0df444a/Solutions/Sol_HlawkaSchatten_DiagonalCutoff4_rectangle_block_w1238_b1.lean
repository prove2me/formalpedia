-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:58.738198+00:00
-- url     : https://prove2.me/submissions/4999b94a-642d-470d-bc08-2137f8019a9c

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
theorem support_rectangle_w1238_s3_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118925371/10000000000 : ℝ)*x 0 + (5420016119/10000000000 : ℝ)*x 1 + (2620152617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118925371/10000000000 : ℝ)^8431 ≤ (12879480482853/100000000000000 : ℝ)^6383 := by
    have hnat : (2118925371 : ℕ)^8431*100000000000000^6383 ≤ 12879480482853^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118925371 10000000000 12879480482853 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420016119/10000000000 : ℝ)^8431 ≤ (44530140093059/100000000000000 : ℝ)^6383 := by
    have hnat : (5420016119 : ℕ)^8431*100000000000000^6383 ≤ 44530140093059^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420016119 10000000000 44530140093059 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620152617/5000000000 : ℝ)^8431 ≤ (2129518970583/5000000000000 : ℝ)^6383 := by
    have hnat : (2620152617 : ℕ)^8431*5000000000000^6383 ≤ 2129518970583^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620152617 5000000000 2129518970583 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118925371/10000000000 : ℝ), (5420016119/10000000000 : ℝ), (2620152617/5000000000 : ℝ)] ![(12879480482853/100000000000000 : ℝ), (44530140093059/100000000000000 : ℝ), (2129518970583/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118925371/10000000000 : ℝ)|^8431 ≤ (12879480482853/100000000000000 : ℝ)^6383
        have hw : |(-2118925371/10000000000 : ℝ)|=(2118925371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420016119/10000000000 : ℝ)|^8431 ≤ (44530140093059/100000000000000 : ℝ)^6383
        have hw : |(5420016119/10000000000 : ℝ)|=(5420016119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620152617/5000000000 : ℝ)|^8431 ≤ (2129518970583/5000000000000 : ℝ)^6383
        have hw : |(2620152617/5000000000 : ℝ)|=(2620152617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675790121/5000000000 : ℝ)*x 0 + (-552652429/2500000000 : ℝ)*x 1 + (1310076343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675790121/5000000000 : ℝ)^8431 ≤ (43788986149907/100000000000000 : ℝ)^6383 := by
    have hnat : (2675790121 : ℕ)^8431*100000000000000^6383 ≤ 43788986149907^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675790121 5000000000 43788986149907 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552652429/2500000000 : ℝ)^8431 ≤ (13620632949759/100000000000000 : ℝ)^6383 := by
    have hnat : (552652429 : ℕ)^8431*100000000000000^6383 ≤ 13620632949759^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552652429 2500000000 13620632949759 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310076343/2500000000 : ℝ)^8431 ≤ (21295190446557/50000000000000 : ℝ)^6383 := by
    have hnat : (1310076343 : ℕ)^8431*50000000000000^6383 ≤ 21295190446557^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310076343 2500000000 21295190446557 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675790121/5000000000 : ℝ), (-552652429/2500000000 : ℝ), (1310076343/2500000000 : ℝ)] ![(43788986149907/100000000000000 : ℝ), (13620632949759/100000000000000 : ℝ), (21295190446557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675790121/5000000000 : ℝ)|^8431 ≤ (43788986149907/100000000000000 : ℝ)^6383
        have hw : |(2675790121/5000000000 : ℝ)|=(2675790121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552652429/2500000000 : ℝ)|^8431 ≤ (13620632949759/100000000000000 : ℝ)^6383
        have hw : |(-552652429/2500000000 : ℝ)|=(552652429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310076343/2500000000 : ℝ)|^8431 ≤ (21295190446557/50000000000000 : ℝ)^6383
        have hw : |(1310076343/2500000000 : ℝ)|=(1310076343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351580151/10000000000 : ℝ)*x 0 + (1048061159/2000000000 : ℝ)*x 1 + (-2210609279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351580151/10000000000 : ℝ)^8431 ≤ (21894492583199/50000000000000 : ℝ)^6383 := by
    have hnat : (5351580151 : ℕ)^8431*50000000000000^6383 ≤ 21894492583199^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351580151 10000000000 21894492583199 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048061159/2000000000 : ℝ)^8431 ≤ (42590385434093/100000000000000 : ℝ)^6383 := by
    have hnat : (1048061159 : ℕ)^8431*100000000000000^6383 ≤ 42590385434093^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048061159 2000000000 42590385434093 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210609279/10000000000 : ℝ)^8431 ≤ (544825175731/4000000000000 : ℝ)^6383 := by
    have hnat : (2210609279 : ℕ)^8431*4000000000000^6383 ≤ 544825175731^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210609279 10000000000 544825175731 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351580151/10000000000 : ℝ), (1048061159/2000000000 : ℝ), (-2210609279/10000000000 : ℝ)] ![(21894492583199/50000000000000 : ℝ), (42590385434093/100000000000000 : ℝ), (544825175731/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351580151/10000000000 : ℝ)|^8431 ≤ (21894492583199/50000000000000 : ℝ)^6383
        have hw : |(5351580151/10000000000 : ℝ)|=(5351580151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048061159/2000000000 : ℝ)|^8431 ≤ (42590385434093/100000000000000 : ℝ)^6383
        have hw : |(1048061159/2000000000 : ℝ)|=(1048061159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210609279/10000000000 : ℝ)|^8431 ≤ (544825175731/4000000000000 : ℝ)^6383
        have hw : |(-2210609279/10000000000 : ℝ)|=(2210609279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349603579/10000000000 : ℝ)*x 0 + (16293649/39062500 : ℝ)*x 1 + (4535447467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349603579/10000000000 : ℝ)^8431 ≤ (8325023085841/25000000000000 : ℝ)^6383 := by
    have hnat : (4349603579 : ℕ)^8431*25000000000000^6383 ≤ 8325023085841^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349603579 10000000000 8325023085841 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16293649/39062500 : ℝ)^8431 ≤ (15753873322151/50000000000000 : ℝ)^6383 := by
    have hnat : (16293649 : ℕ)^8431*50000000000000^6383 ≤ 15753873322151^6383*39062500^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16293649 39062500 15753873322151 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535447467/10000000000 : ℝ)^8431 ≤ (17596080501681/50000000000000 : ℝ)^6383 := by
    have hnat : (4535447467 : ℕ)^8431*50000000000000^6383 ≤ 17596080501681^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535447467 10000000000 17596080501681 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349603579/10000000000 : ℝ), (16293649/39062500 : ℝ), (4535447467/10000000000 : ℝ)] ![(8325023085841/25000000000000 : ℝ), (15753873322151/50000000000000 : ℝ), (17596080501681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349603579/10000000000 : ℝ)|^8431 ≤ (8325023085841/25000000000000 : ℝ)^6383
        have hw : |(4349603579/10000000000 : ℝ)|=(4349603579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16293649/39062500 : ℝ)|^8431 ≤ (15753873322151/50000000000000 : ℝ)^6383
        have hw : |(16293649/39062500 : ℝ)|=(16293649/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535447467/10000000000 : ℝ)|^8431 ≤ (17596080501681/50000000000000 : ℝ)^6383
        have hw : |(4535447467/10000000000 : ℝ)|=(4535447467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-10594697/50000000 : ℝ)*x 0 + (524095997/1000000000 : ℝ)*x 1 + (5419358023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10594697/50000000 : ℝ)^8431 ≤ (3219898278863/25000000000000 : ℝ)^6383 := by
    have hnat : (10594697 : ℕ)^8431*25000000000000^6383 ≤ 3219898278863^6383*50000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10594697 50000000 3219898278863 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524095997/1000000000 : ℝ)^8431 ≤ (42597408258743/100000000000000 : ℝ)^6383 := by
    have hnat : (524095997 : ℕ)^8431*100000000000000^6383 ≤ 42597408258743^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524095997 1000000000 42597408258743 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419358023/10000000000 : ℝ)^8431 ≤ (22261499304103/50000000000000 : ℝ)^6383 := by
    have hnat : (5419358023 : ℕ)^8431*50000000000000^6383 ≤ 22261499304103^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419358023 10000000000 22261499304103 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10594697/50000000 : ℝ), (524095997/1000000000 : ℝ), (5419358023/10000000000 : ℝ)] ![(3219898278863/25000000000000 : ℝ), (42597408258743/100000000000000 : ℝ), (22261499304103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10594697/50000000 : ℝ)|^8431 ≤ (3219898278863/25000000000000 : ℝ)^6383
        have hw : |(-10594697/50000000 : ℝ)|=(10594697/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524095997/1000000000 : ℝ)|^8431 ≤ (42597408258743/100000000000000 : ℝ)^6383
        have hw : |(524095997/1000000000 : ℝ)|=(524095997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419358023/10000000000 : ℝ)|^8431 ≤ (22261499304103/50000000000000 : ℝ)^6383
        have hw : |(5419358023/10000000000 : ℝ)|=(5419358023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305743117/10000000000 : ℝ)*x 0 + (-1015779077/5000000000 : ℝ)*x 1 + (2709678961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305743117/10000000000 : ℝ)^8431 ≤ (4329426994449/10000000000000 : ℝ)^6383 := by
    have hnat : (5305743117 : ℕ)^8431*10000000000000^6383 ≤ 4329426994449^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305743117 10000000000 4329426994449 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015779077/5000000000 : ℝ)^8431 ≤ (12182732527153/100000000000000 : ℝ)^6383 := by
    have hnat : (1015779077 : ℕ)^8431*100000000000000^6383 ≤ 12182732527153^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015779077 5000000000 12182732527153 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709678961/5000000000 : ℝ)^8431 ≤ (22261498756101/50000000000000 : ℝ)^6383 := by
    have hnat : (2709678961 : ℕ)^8431*50000000000000^6383 ≤ 22261498756101^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709678961 5000000000 22261498756101 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305743117/10000000000 : ℝ), (-1015779077/5000000000 : ℝ), (2709678961/5000000000 : ℝ)] ![(4329426994449/10000000000000 : ℝ), (12182732527153/100000000000000 : ℝ), (22261498756101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305743117/10000000000 : ℝ)|^8431 ≤ (4329426994449/10000000000000 : ℝ)^6383
        have hw : |(5305743117/10000000000 : ℝ)|=(5305743117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015779077/5000000000 : ℝ)|^8431 ≤ (12182732527153/100000000000000 : ℝ)^6383
        have hw : |(-1015779077/5000000000 : ℝ)|=(1015779077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709678961/5000000000 : ℝ)|^8431 ≤ (22261498756101/50000000000000 : ℝ)^6383
        have hw : |(2709678961/5000000000 : ℝ)|=(2709678961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061148909/2000000000 : ℝ)*x 0 + (2709678509/5000000000 : ℝ)*x 1 + (-2031557449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061148909/2000000000 : ℝ)^8431 ≤ (10823571333871/25000000000000 : ℝ)^6383 := by
    have hnat : (1061148909 : ℕ)^8431*25000000000000^6383 ≤ 10823571333871^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061148909 2000000000 10823571333871 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709678509/5000000000 : ℝ)^8431 ≤ (44522987702423/100000000000000 : ℝ)^6383 := by
    have hnat : (2709678509 : ℕ)^8431*100000000000000^6383 ≤ 44522987702423^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709678509 5000000000 44522987702423 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031557449/10000000000 : ℝ)^8431 ≤ (12182726942981/100000000000000 : ℝ)^6383 := by
    have hnat : (2031557449 : ℕ)^8431*100000000000000^6383 ≤ 12182726942981^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031557449 10000000000 12182726942981 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061148909/2000000000 : ℝ), (2709678509/5000000000 : ℝ), (-2031557449/10000000000 : ℝ)] ![(10823571333871/25000000000000 : ℝ), (44522987702423/100000000000000 : ℝ), (12182726942981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061148909/2000000000 : ℝ)|^8431 ≤ (10823571333871/25000000000000 : ℝ)^6383
        have hw : |(1061148909/2000000000 : ℝ)|=(1061148909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709678509/5000000000 : ℝ)|^8431 ≤ (44522987702423/100000000000000 : ℝ)^6383
        have hw : |(2709678509/5000000000 : ℝ)|=(2709678509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031557449/10000000000 : ℝ)|^8431 ≤ (12182726942981/100000000000000 : ℝ)^6383
        have hw : |(-2031557449/10000000000 : ℝ)|=(2031557449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s3_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349632763/10000000000 : ℝ)*x 0 + (1133530089/2500000000 : ℝ)*x 1 + (2086253839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349632763/10000000000 : ℝ)^8431 ≤ (16650193730543/50000000000000 : ℝ)^6383 := by
    have hnat : (4349632763 : ℕ)^8431*50000000000000^6383 ≤ 16650193730543^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349632763 10000000000 16650193730543 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133530089/2500000000 : ℝ)^8431 ≤ (35178560126767/100000000000000 : ℝ)^6383 := by
    have hnat : (1133530089 : ℕ)^8431*100000000000000^6383 ≤ 35178560126767^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133530089 2500000000 35178560126767 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086253839/5000000000 : ℝ)^8431 ≤ (15760526201343/50000000000000 : ℝ)^6383 := by
    have hnat : (2086253839 : ℕ)^8431*50000000000000^6383 ≤ 15760526201343^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086253839 5000000000 15760526201343 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349632763/10000000000 : ℝ), (1133530089/2500000000 : ℝ), (2086253839/5000000000 : ℝ)] ![(16650193730543/50000000000000 : ℝ), (35178560126767/100000000000000 : ℝ), (15760526201343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349632763/10000000000 : ℝ)|^8431 ≤ (16650193730543/50000000000000 : ℝ)^6383
        have hw : |(4349632763/10000000000 : ℝ)|=(4349632763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133530089/2500000000 : ℝ)|^8431 ≤ (35178560126767/100000000000000 : ℝ)^6383
        have hw : |(1133530089/2500000000 : ℝ)|=(1133530089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086253839/5000000000 : ℝ)|^8431 ≤ (15760526201343/50000000000000 : ℝ)^6383
        have hw : |(2086253839/5000000000 : ℝ)|=(2086253839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9483/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (768781496289787/12500000000000000000 : ℝ) := by
    have hpowers : (9483/100000 : ℝ)^4215 ≤ (768781496289787/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9483 : ℕ)^4215*12500000000000000000^1024 ≤ 768781496289787^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9483 100000 768781496289787 12500000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9483/100000 : ℝ)) (X := (768781496289787/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8117/50000 : ℝ) ^ (4215/1024 : ℝ) ≤ (56227008572140367/100000000000000000000 : ℝ) := by
    have hpowers : (8117/50000 : ℝ)^4215 ≤ (56227008572140367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8117 : ℕ)^4215*100000000000000000000^1024 ≤ 56227008572140367^1024*50000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8117 50000 56227008572140367 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8117/50000 : ℝ)) (X := (56227008572140367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250768781496289787/6250000000000000000 : ℝ) ≤ (2500074704208829/2500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (6250768781496289787/6250000000000000000 : ℝ)^1024 ≤ (2500074704208829/2500000000000000 : ℝ)^4215 := by
      have hnat : (6250768781496289787 : ℕ)^1024*2500000000000000^4215 ≤ 2500074704208829^4215*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250768781496289787 6250000000000000000 2500074704208829 2500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074704208829/2500000000000000 : ℝ)) (X := (6250768781496289787/6250000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062377260542458663/100000000000000000000 : ℝ) ≤ (10001515047177971/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100062377260542458663/100000000000000000000 : ℝ)^1024 ≤ (10001515047177971/10000000000000000 : ℝ)^4215 := by
      have hnat : (100062377260542458663 : ℕ)^1024*10000000000000000^4215 ≤ 10001515047177971^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062377260542458663 100000000000000000000 10001515047177971 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001515047177971/10000000000000000 : ℝ)) (X := (100062377260542458663/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50056227008572140367/50000000000000000000 : ℝ) ≤ (5001365638760313/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50056227008572140367/50000000000000000000 : ℝ)^1024 ≤ (5001365638760313/5000000000000000 : ℝ)^4215 := by
      have hnat : (50056227008572140367 : ℕ)^1024*5000000000000000^4215 ≤ 5001365638760313^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056227008572140367 50000000000000000000 5001365638760313 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001365638760313/5000000000000000 : ℝ)) (X := (50056227008572140367/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(768781496289787/12500000000000000000 : ℝ) ≤ ((33744475143888211793/33755000000000000000 : ℝ)+2*(243246068531/135020000000000 : ℝ)*(9483/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (33744475143888211793/33755000000000000000 : ℝ)+2*(243246068531/135020000000000 : ℝ)*(9483/100000 : ℝ)=(2500074704208829/2500000000000000 : ℝ) by norm_num, show 1+2*(768781496289787/12500000000000000000 : ℝ)=(6250768781496289787/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56227008572140367/100000000000000000000 : ℝ)+(768781496289787/12500000000000000000 : ℝ) ≤ ((33744475143888211793/33755000000000000000 : ℝ)+(243246068531/135020000000000 : ℝ)*((8117/50000 : ℝ)+(9483/100000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (33744475143888211793/33755000000000000000 : ℝ)+(243246068531/135020000000000 : ℝ)*((8117/50000 : ℝ)+(9483/100000 : ℝ))=(10001515047177971/10000000000000000 : ℝ) by norm_num, show 1+(56227008572140367/100000000000000000000 : ℝ)+(768781496289787/12500000000000000000 : ℝ)=(100062377260542458663/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56227008572140367/100000000000000000000 : ℝ) ≤ ((33744475143888211793/33755000000000000000 : ℝ)+2*(243246068531/135020000000000 : ℝ)*(8117/50000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (33744475143888211793/33755000000000000000 : ℝ)+2*(243246068531/135020000000000 : ℝ)*(8117/50000 : ℝ)=(5001365638760313/5000000000000000 : ℝ) by norm_num, show 1+2*(56227008572140367/100000000000000000000 : ℝ)=(50056227008572140367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33744475143888211793/33755000000000000000 : ℝ)*(X 1 0+X 2 0)+(243246068531/135020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (33744475143888211793/33755000000000000000 : ℝ)) (alpha := (243246068531/135020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33744475143888211793/33755000000000000000 : ℝ)*(X 0 1+X 2 1)+(243246068531/135020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (33744475143888211793/33755000000000000000 : ℝ)) (alpha := (243246068531/135020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33744475143888211793/33755000000000000000 : ℝ)*(X 0 2+X 1 2)+(243246068531/135020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (8117/50000 : ℝ)) (c := (33744475143888211793/33755000000000000000 : ℝ)) (alpha := (243246068531/135020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118925371/10000000000 : ℝ)*X 0 0+(5420016119/10000000000 : ℝ)*X 0 1+(2620152617/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675790121/5000000000 : ℝ)*X 1 0+(-552652429/2500000000 : ℝ)*X 1 1+(1310076343/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351580151/10000000000 : ℝ)*X 2 0+(1048061159/2000000000 : ℝ)*X 2 1+(-2210609279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349603579/10000000000 : ℝ)*X 0 0+(16293649/39062500 : ℝ)*X 0 1+(4535447467/10000000000 : ℝ)*X 0 2+(4349603579/10000000000 : ℝ)*X 1 0+(16293649/39062500 : ℝ)*X 1 1+(4535447467/10000000000 : ℝ)*X 1 2+(4349603579/10000000000 : ℝ)*X 2 0+(16293649/39062500 : ℝ)*X 2 1+(4535447467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10594697/50000000 : ℝ)*X 0 0+(524095997/1000000000 : ℝ)*X 0 1+(5419358023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305743117/10000000000 : ℝ)*X 1 0+(-1015779077/5000000000 : ℝ)*X 1 1+(2709678961/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061148909/2000000000 : ℝ)*X 2 0+(2709678509/5000000000 : ℝ)*X 2 1+(-2031557449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349632763/10000000000 : ℝ)*X 0 0+(1133530089/2500000000 : ℝ)*X 0 1+(2086253839/5000000000 : ℝ)*X 0 2+(4349632763/10000000000 : ℝ)*X 1 0+(1133530089/2500000000 : ℝ)*X 1 1+(2086253839/5000000000 : ℝ)*X 1 2+(4349632763/10000000000 : ℝ)*X 2 0+(1133530089/2500000000 : ℝ)*X 2 1+(2086253839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82105021381508983975651557/16877500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244419709/50000000000000 : ℝ)*(base19) + (29781891/20000000000000 : ℝ)*(base23) + (81080417/50000000000000 : ℝ)*(lower2) + (4341919/25000000000000 : ℝ)*(lower3) + (83097438024483/2000000000000 : ℝ)*(major0) + (83097438024483/2000000000000 : ℝ)*(major1) + (83097438024483/2000000000000 : ℝ)*(major2) + (2782257218609253/50000000000000 : ℝ)*(sp0) + (2782266100849807/50000000000000 : ℝ)*(sp1) + (5564539278940077/100000000000000 : ℝ)*(sp2) + (2745197377995533/100000000000000 : ℝ)*(sp3) + (12495315513/50000000000000 : ℝ)*(sp4) + (13474621/200000000000 : ℝ)*(sp5) + (1708611123/25000000000000 : ℝ)*(sp7) + (1372602106220013/50000000000000 : ℝ)*(f.failure) + (1391134856962383/25000000000000 : ℝ)*(f.sum) + (31949083090023/6751000000000000000000000000 : ℝ)*base65 + (222736252826801981/67510000000000000000000000000000 : ℝ)*base68 + (363545313030811981/67510000000000000000000000000000 : ℝ)*base70 + (340787867691831981/67510000000000000000000000000000 : ℝ)*base72 + (3467144137237/675100000000000000000000000 : ℝ)*base73 + (45293531810128019/67510000000000000000000000000000 : ℝ)*base75 + (531392667639721981/67510000000000000000000000000000 : ℝ)*base78 + (803978367732111981/67510000000000000000000000000000 : ℝ)*base80 + (11543063198323/3375500000000000000000000000 : ℝ)*base81 + (37116261/2500000000000000000000 : ℝ)*base89 + (37116261/2500000000000000000000 : ℝ)*base91 + (37116261/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86707474626444888234603/6751000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81211069/25000000000000 : ℝ)*(base19) + (2903277733/100000000000000 : ℝ)*(base23) + (16401033/100000000000000 : ℝ)*(lower2) + (92184433/100000000000000 : ℝ)*(upper3) + (409690493/100000000000000 : ℝ)*(lower4) + (81029903/25000000000000 : ℝ)*(upper5) + (83708460770589/2000000000000 : ℝ)*(major0) + (83708460770589/2000000000000 : ℝ)*(major1) + (83708460770589/2000000000000 : ℝ)*(major2) + (7605547323/20000000000000 : ℝ)*(sp2) + (44843645674231/800000000000 : ℝ)*(sp4) + (5605455384434599/100000000000000 : ℝ)*(sp5) + (5605414778264527/100000000000000 : ℝ)*(sp6) + (1382694969829193/50000000000000 : ℝ)*(sp7) + (1382694969829193/50000000000000 : ℝ)*(f.failure) + (44843645674231/800000000000 : ℝ)*(f.sum) + (5613341591483/1687750000000000000000000000 : ℝ)*base65 + (420543813389553923/67510000000000000000000000000000 : ℝ)*base68 + (31988363461276077/67510000000000000000000000000000 : ℝ)*base69 + (308417930583596077/67510000000000000000000000000000 : ℝ)*base71 + (299427007467/42193750000000000000000000 : ℝ)*base74 + (157436538157753923/67510000000000000000000000000000 : ℝ)*base76 + (821070035496126077/67510000000000000000000000000000 : ℝ)*base77 + (497130577513663923/67510000000000000000000000000000 : ℝ)*base80 + (54233222251/135020000000000000000000000 : ℝ)*base82 + (3706721/2500000000000000000000 : ℝ)*base89 + (3706721/2500000000000000000000 : ℝ)*base91 + (3706721/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1238_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s4_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121241989/10000000000 : ℝ)*x 0 + (1079532083/2000000000 : ℝ)*x 1 + (210445721/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121241989/10000000000 : ℝ)^8431 ≤ (12898082819631/100000000000000 : ℝ)^6383 := by
    have hnat : (2121241989 : ℕ)^8431*100000000000000^6383 ≤ 12898082819631^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121241989 10000000000 12898082819631 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079532083/2000000000 : ℝ)^8431 ≤ (8857539564689/20000000000000 : ℝ)^6383 := by
    have hnat : (1079532083 : ℕ)^8431*20000000000000^6383 ≤ 8857539564689^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079532083 2000000000 8857539564689 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210445721/400000000 : ℝ)^8431 ≤ (42814219339903/100000000000000 : ℝ)^6383 := by
    have hnat : (210445721 : ℕ)^8431*100000000000000^6383 ≤ 42814219339903^6383*400000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210445721 400000000 42814219339903 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121241989/10000000000 : ℝ), (1079532083/2000000000 : ℝ), (210445721/400000000 : ℝ)] ![(12898082819631/100000000000000 : ℝ), (8857539564689/20000000000000 : ℝ), (42814219339903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121241989/10000000000 : ℝ)|^8431 ≤ (12898082819631/100000000000000 : ℝ)^6383
        have hw : |(-2121241989/10000000000 : ℝ)|=(2121241989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079532083/2000000000 : ℝ)|^8431 ≤ (8857539564689/20000000000000 : ℝ)^6383
        have hw : |(1079532083/2000000000 : ℝ)|=(1079532083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210445721/400000000 : ℝ)|^8431 ≤ (42814219339903/100000000000000 : ℝ)^6383
        have hw : |(210445721/400000000 : ℝ)|=(210445721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672973377/5000000000 : ℝ)*x 0 + (-1095278257/5000000000 : ℝ)*x 1 + (328821439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672973377/5000000000 : ℝ)^8431 ≤ (2733006928239/6250000000000 : ℝ)^6383 := by
    have hnat : (2672973377 : ℕ)^8431*6250000000000^6383 ≤ 2733006928239^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672973377 5000000000 2733006928239 6250000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095278257/5000000000 : ℝ)^8431 ≤ (6728834901311/50000000000000 : ℝ)^6383 := by
    have hnat : (1095278257 : ℕ)^8431*50000000000000^6383 ≤ 6728834901311^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095278257 5000000000 6728834901311 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328821439/625000000 : ℝ)^8431 ≤ (8562843865831/20000000000000 : ℝ)^6383 := by
    have hnat : (328821439 : ℕ)^8431*20000000000000^6383 ≤ 8562843865831^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328821439 625000000 8562843865831 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672973377/5000000000 : ℝ), (-1095278257/5000000000 : ℝ), (328821439/625000000 : ℝ)] ![(2733006928239/6250000000000 : ℝ), (6728834901311/50000000000000 : ℝ), (8562843865831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672973377/5000000000 : ℝ)|^8431 ≤ (2733006928239/6250000000000 : ℝ)^6383
        have hw : |(2672973377/5000000000 : ℝ)|=(2672973377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095278257/5000000000 : ℝ)|^8431 ≤ (6728834901311/50000000000000 : ℝ)^6383
        have hw : |(-1095278257/5000000000 : ℝ)|=(1095278257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328821439/625000000 : ℝ)|^8431 ≤ (8562843865831/20000000000000 : ℝ)^6383
        have hw : |(328821439/625000000 : ℝ)|=(328821439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672973387/5000000000 : ℝ)*x 0 + (1052228591/2000000000 : ℝ)*x 1 + (-2190556579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672973387/5000000000 : ℝ)^8431 ≤ (43728111067907/100000000000000 : ℝ)^6383 := by
    have hnat : (2672973387 : ℕ)^8431*100000000000000^6383 ≤ 43728111067907^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672973387 5000000000 43728111067907 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052228591/2000000000 : ℝ)^8431 ≤ (10703554646871/25000000000000 : ℝ)^6383 := by
    have hnat : (1052228591 : ℕ)^8431*25000000000000^6383 ≤ 10703554646871^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052228591 2000000000 10703554646871 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190556579/10000000000 : ℝ)^8431 ≤ (6728835165037/50000000000000 : ℝ)^6383 := by
    have hnat : (2190556579 : ℕ)^8431*50000000000000^6383 ≤ 6728835165037^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190556579 10000000000 6728835165037 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672973387/5000000000 : ℝ), (1052228591/2000000000 : ℝ), (-2190556579/10000000000 : ℝ)] ![(43728111067907/100000000000000 : ℝ), (10703554646871/25000000000000 : ℝ), (6728835165037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672973387/5000000000 : ℝ)|^8431 ≤ (43728111067907/100000000000000 : ℝ)^6383
        have hw : |(2672973387/5000000000 : ℝ)|=(2672973387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052228591/2000000000 : ℝ)|^8431 ≤ (10703554646871/25000000000000 : ℝ)^6383
        have hw : |(1052228591/2000000000 : ℝ)|=(1052228591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190556579/10000000000 : ℝ)|^8431 ≤ (6728835165037/50000000000000 : ℝ)^6383
        have hw : |(-2190556579/10000000000 : ℝ)|=(2190556579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175496523/5000000000 : ℝ)*x 0 + (4214772693/10000000000 : ℝ)*x 1 + (4491494049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175496523/5000000000 : ℝ)^8431 ≤ (16657071886233/50000000000000 : ℝ)^6383 := by
    have hnat : (2175496523 : ℕ)^8431*50000000000000^6383 ≤ 16657071886233^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175496523 5000000000 16657071886233 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4214772693/10000000000 : ℝ)^8431 ≤ (15971735190049/50000000000000 : ℝ)^6383 := by
    have hnat : (4214772693 : ℕ)^8431*50000000000000^6383 ≤ 15971735190049^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214772693 10000000000 15971735190049 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491494049/10000000000 : ℝ)^8431 ≤ (34742385830973/100000000000000 : ℝ)^6383 := by
    have hnat : (4491494049 : ℕ)^8431*100000000000000^6383 ≤ 34742385830973^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491494049 10000000000 34742385830973 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175496523/5000000000 : ℝ), (4214772693/10000000000 : ℝ), (4491494049/10000000000 : ℝ)] ![(16657071886233/50000000000000 : ℝ), (15971735190049/50000000000000 : ℝ), (34742385830973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175496523/5000000000 : ℝ)|^8431 ≤ (16657071886233/50000000000000 : ℝ)^6383
        have hw : |(2175496523/5000000000 : ℝ)|=(2175496523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4214772693/10000000000 : ℝ)|^8431 ≤ (15971735190049/50000000000000 : ℝ)^6383
        have hw : |(4214772693/10000000000 : ℝ)|=(4214772693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491494049/10000000000 : ℝ)|^8431 ≤ (34742385830973/100000000000000 : ℝ)^6383
        have hw : |(4491494049/10000000000 : ℝ)|=(4491494049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42424963/200000000 : ℝ)*x 0 + (5261521423/10000000000 : ℝ)*x 1 + (5397280541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42424963/200000000 : ℝ)^8431 ≤ (6449066150437/50000000000000 : ℝ)^6383 := by
    have hnat : (42424963 : ℕ)^8431*50000000000000^6383 ≤ 6449066150437^6383*200000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42424963 200000000 6449066150437 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261521423/10000000000 : ℝ)^8431 ≤ (4281828673171/10000000000000 : ℝ)^6383 := by
    have hnat : (5261521423 : ℕ)^8431*10000000000000^6383 ≤ 4281828673171^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261521423 10000000000 4281828673171 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397280541/10000000000 : ℝ)^8431 ≤ (44283580960033/100000000000000 : ℝ)^6383 := by
    have hnat : (5397280541 : ℕ)^8431*100000000000000^6383 ≤ 44283580960033^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397280541 10000000000 44283580960033 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42424963/200000000 : ℝ), (5261521423/10000000000 : ℝ), (5397280541/10000000000 : ℝ)] ![(6449066150437/50000000000000 : ℝ), (4281828673171/10000000000000 : ℝ), (44283580960033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42424963/200000000 : ℝ)|^8431 ≤ (6449066150437/50000000000000 : ℝ)^6383
        have hw : |(-42424963/200000000 : ℝ)|=(42424963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261521423/10000000000 : ℝ)|^8431 ≤ (4281828673171/10000000000000 : ℝ)^6383
        have hw : |(5261521423/10000000000 : ℝ)|=(5261521423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397280541/10000000000 : ℝ)|^8431 ≤ (44283580960033/100000000000000 : ℝ)^6383
        have hw : |(5397280541/10000000000 : ℝ)|=(5397280541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311124863/10000000000 : ℝ)*x 0 + (-513604737/2500000000 : ℝ)*x 1 + (5397280589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311124863/10000000000 : ℝ)^8431 ≤ (43352283875101/100000000000000 : ℝ)^6383 := by
    have hnat : (5311124863 : ℕ)^8431*100000000000000^6383 ≤ 43352283875101^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311124863 10000000000 43352283875101 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513604737/2500000000 : ℝ)^8431 ≤ (12364134633043/100000000000000 : ℝ)^6383 := by
    have hnat : (513604737 : ℕ)^8431*100000000000000^6383 ≤ 12364134633043^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513604737 2500000000 12364134633043 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397280589/10000000000 : ℝ)^8431 ≤ (1383861921257/3125000000000 : ℝ)^6383 := by
    have hnat : (5397280589 : ℕ)^8431*3125000000000^6383 ≤ 1383861921257^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397280589 10000000000 1383861921257 3125000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311124863/10000000000 : ℝ), (-513604737/2500000000 : ℝ), (5397280589/10000000000 : ℝ)] ![(43352283875101/100000000000000 : ℝ), (12364134633043/100000000000000 : ℝ), (1383861921257/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311124863/10000000000 : ℝ)|^8431 ≤ (43352283875101/100000000000000 : ℝ)^6383
        have hw : |(5311124863/10000000000 : ℝ)|=(5311124863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513604737/2500000000 : ℝ)|^8431 ≤ (12364134633043/100000000000000 : ℝ)^6383
        have hw : |(-513604737/2500000000 : ℝ)|=(513604737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397280589/10000000000 : ℝ)|^8431 ≤ (1383861921257/3125000000000 : ℝ)^6383
        have hw : |(5397280589/10000000000 : ℝ)|=(5397280589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311124913/10000000000 : ℝ)*x 0 + (337330031/625000000 : ℝ)*x 1 + (-2054419007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311124913/10000000000 : ℝ)^8431 ≤ (43352284414177/100000000000000 : ℝ)^6383 := by
    have hnat : (5311124913 : ℕ)^8431*100000000000000^6383 ≤ 43352284414177^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311124913 10000000000 43352284414177 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337330031/625000000 : ℝ)^8431 ≤ (44283580472353/100000000000000 : ℝ)^6383 := by
    have hnat : (337330031 : ℕ)^8431*100000000000000^6383 ≤ 44283580472353^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337330031 625000000 44283580472353 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054419007/10000000000 : ℝ)^8431 ≤ (3091033775513/25000000000000 : ℝ)^6383 := by
    have hnat : (2054419007 : ℕ)^8431*25000000000000^6383 ≤ 3091033775513^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054419007 10000000000 3091033775513 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311124913/10000000000 : ℝ), (337330031/625000000 : ℝ), (-2054419007/10000000000 : ℝ)] ![(43352284414177/100000000000000 : ℝ), (44283580472353/100000000000000 : ℝ), (3091033775513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311124913/10000000000 : ℝ)|^8431 ≤ (43352284414177/100000000000000 : ℝ)^6383
        have hw : |(5311124913/10000000000 : ℝ)|=(5311124913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337330031/625000000 : ℝ)|^8431 ≤ (44283580472353/100000000000000 : ℝ)^6383
        have hw : |(337330031/625000000 : ℝ)|=(337330031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054419007/10000000000 : ℝ)|^8431 ≤ (3091033775513/25000000000000 : ℝ)^6383
        have hw : |(-2054419007/10000000000 : ℝ)|=(2054419007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s4_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175502803/5000000000 : ℝ)*x 0 + (4490726953/10000000000 : ℝ)*x 1 + (4215542867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175502803/5000000000 : ℝ)^8431 ≤ (33314270796047/100000000000000 : ℝ)^6383 := by
    have hnat : (2175502803 : ℕ)^8431*100000000000000^6383 ≤ 33314270796047^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175502803 5000000000 33314270796047 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490726953/10000000000 : ℝ)^8431 ≤ (34734548631987/100000000000000 : ℝ)^6383 := by
    have hnat : (4490726953 : ℕ)^8431*100000000000000^6383 ≤ 34734548631987^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490726953 10000000000 34734548631987 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4215542867/10000000000 : ℝ)^8431 ≤ (31951180546797/100000000000000 : ℝ)^6383 := by
    have hnat : (4215542867 : ℕ)^8431*100000000000000^6383 ≤ 31951180546797^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215542867 10000000000 31951180546797 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175502803/5000000000 : ℝ), (4490726953/10000000000 : ℝ), (4215542867/10000000000 : ℝ)] ![(33314270796047/100000000000000 : ℝ), (34734548631987/100000000000000 : ℝ), (31951180546797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175502803/5000000000 : ℝ)|^8431 ≤ (33314270796047/100000000000000 : ℝ)^6383
        have hw : |(2175502803/5000000000 : ℝ)|=(2175502803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490726953/10000000000 : ℝ)|^8431 ≤ (34734548631987/100000000000000 : ℝ)^6383
        have hw : |(4490726953/10000000000 : ℝ)|=(4490726953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4215542867/10000000000 : ℝ)|^8431 ≤ (31951180546797/100000000000000 : ℝ)^6383
        have hw : |(4215542867/10000000000 : ℝ)|=(4215542867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10901/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (1091461496059711/10000000000000000000 : ℝ) := by
    have hpowers : (10901/100000 : ℝ)^4215 ≤ (1091461496059711/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10901 : ℕ)^4215*10000000000000000000^1024 ≤ 1091461496059711^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10901 100000 1091461496059711 10000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10901/100000 : ℝ)) (X := (1091461496059711/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (4215/1024 : ℝ) ≤ (9355143520400159/25000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^4215 ≤ (9355143520400159/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2941 : ℕ)^4215*25000000000000000000^1024 ≤ 9355143520400159^1024*20000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 9355143520400159 25000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (9355143520400159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001091461496059711/5000000000000000000 : ℝ) ≤ (5000265139794029/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (5001091461496059711/5000000000000000000 : ℝ)^1024 ≤ (5000265139794029/5000000000000000 : ℝ)^4215 := by
      have hnat : (5001091461496059711 : ℕ)^1024*5000000000000000^4215 ≤ 5000265139794029^4215*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001091461496059711 5000000000000000000 5000265139794029 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000265139794029/5000000000000000 : ℝ)) (X := (5001091461496059711/5000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024167594521098873/50000000000000000000 : ℝ) ≤ (400046961974243/400000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50024167594521098873/50000000000000000000 : ℝ)^1024 ≤ (400046961974243/400000000000000 : ℝ)^4215 := by
      have hnat : (50024167594521098873 : ℕ)^1024*400000000000000^4215 ≤ 400046961974243^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024167594521098873 50000000000000000000 400046961974243 400000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400046961974243/400000000000000 : ℝ)) (X := (50024167594521098873/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509355143520400159/12500000000000000000 : ℝ) ≤ (2500454454781023/2500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (12509355143520400159/12500000000000000000 : ℝ)^1024 ≤ (2500454454781023/2500000000000000 : ℝ)^4215 := by
      have hnat : (12509355143520400159 : ℕ)^1024*2500000000000000^4215 ≤ 2500454454781023^4215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509355143520400159 12500000000000000000 2500454454781023 2500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500454454781023/2500000000000000 : ℝ)) (X := (12509355143520400159/12500000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1091461496059711/10000000000000000000 : ℝ) ≤ ((19013990857535332999/19020000000000000000 : ℝ)+2*(643769768017/380400000000000 : ℝ)*(10901/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (19013990857535332999/19020000000000000000 : ℝ)+2*(643769768017/380400000000000 : ℝ)*(10901/100000 : ℝ)=(5000265139794029/5000000000000000 : ℝ) by norm_num, show 1+2*(1091461496059711/10000000000000000000 : ℝ)=(5001091461496059711/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9355143520400159/25000000000000000000 : ℝ)+(1091461496059711/10000000000000000000 : ℝ) ≤ ((19013990857535332999/19020000000000000000 : ℝ)+(643769768017/380400000000000 : ℝ)*((2941/20000 : ℝ)+(10901/100000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (19013990857535332999/19020000000000000000 : ℝ)+(643769768017/380400000000000 : ℝ)*((2941/20000 : ℝ)+(10901/100000 : ℝ))=(400046961974243/400000000000000 : ℝ) by norm_num, show 1+(9355143520400159/25000000000000000000 : ℝ)+(1091461496059711/10000000000000000000 : ℝ)=(50024167594521098873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9355143520400159/25000000000000000000 : ℝ) ≤ ((19013990857535332999/19020000000000000000 : ℝ)+2*(643769768017/380400000000000 : ℝ)*(2941/20000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (19013990857535332999/19020000000000000000 : ℝ)+2*(643769768017/380400000000000 : ℝ)*(2941/20000 : ℝ)=(2500454454781023/2500000000000000 : ℝ) by norm_num, show 1+2*(9355143520400159/25000000000000000000 : ℝ)=(12509355143520400159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19013990857535332999/19020000000000000000 : ℝ)*(X 1 0+X 2 0)+(643769768017/380400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19013990857535332999/19020000000000000000 : ℝ)) (alpha := (643769768017/380400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19013990857535332999/19020000000000000000 : ℝ)*(X 0 1+X 2 1)+(643769768017/380400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19013990857535332999/19020000000000000000 : ℝ)) (alpha := (643769768017/380400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19013990857535332999/19020000000000000000 : ℝ)*(X 0 2+X 1 2)+(643769768017/380400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (10901/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19013990857535332999/19020000000000000000 : ℝ)) (alpha := (643769768017/380400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121241989/10000000000 : ℝ)*X 0 0+(1079532083/2000000000 : ℝ)*X 0 1+(210445721/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672973377/5000000000 : ℝ)*X 1 0+(-1095278257/5000000000 : ℝ)*X 1 1+(328821439/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672973387/5000000000 : ℝ)*X 2 0+(1052228591/2000000000 : ℝ)*X 2 1+(-2190556579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175496523/5000000000 : ℝ)*X 0 0+(4214772693/10000000000 : ℝ)*X 0 1+(4491494049/10000000000 : ℝ)*X 0 2+(2175496523/5000000000 : ℝ)*X 1 0+(4214772693/10000000000 : ℝ)*X 1 1+(4491494049/10000000000 : ℝ)*X 1 2+(2175496523/5000000000 : ℝ)*X 2 0+(4214772693/10000000000 : ℝ)*X 2 1+(4491494049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42424963/200000000 : ℝ)*X 0 0+(5261521423/10000000000 : ℝ)*X 0 1+(5397280541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311124863/10000000000 : ℝ)*X 1 0+(-513604737/2500000000 : ℝ)*X 1 1+(5397280589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311124913/10000000000 : ℝ)*X 2 0+(337330031/625000000 : ℝ)*X 2 1+(-2054419007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175502803/5000000000 : ℝ)*X 0 0+(4490726953/10000000000 : ℝ)*X 0 1+(4215542867/10000000000 : ℝ)*X 0 2+(2175502803/5000000000 : ℝ)*X 1 0+(4490726953/10000000000 : ℝ)*X 1 1+(4215542867/10000000000 : ℝ)*X 1 2+(2175502803/5000000000 : ℝ)*X 2 0+(4490726953/10000000000 : ℝ)*X 2 1+(4215542867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23485775708144215501527/3170000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206706359/12500000000000 : ℝ)*(base19) + (413904833/25000000000000 : ℝ)*(base23) + (244347547/100000000000000 : ℝ)*(upper3) + (424937/3125000000000 : ℝ)*(upper4) + (66605759/50000000000000 : ℝ)*(upper5) + (2734735884527223/50000000000000 : ℝ)*(major0) + (2734735884527223/50000000000000 : ℝ)*(major1) + (2734735884527223/50000000000000 : ℝ)*(major2) + (3662558982037617/50000000000000 : ℝ)*(sp0) + (11445556047701/156250000000 : ℝ)*(sp1) + (7325155868560181/100000000000000 : ℝ)*(sp2) + (180688170651019/5000000000000 : ℝ)*(sp3) + (19780052139/50000000000000 : ℝ)*(sp4) + (4470790051/20000000000000 : ℝ)*(sp7) + (903446441742659/25000000000000 : ℝ)*(f.failure) + (915644690522439/12500000000000 : ℝ)*(f.sum) + (13550890873317/3170000000000000000000000000 : ℝ)*base65 + (324730325405427259/317000000000000000000000000000000 : ℝ)*base67 + (762605317992572741/317000000000000000000000000000000 : ℝ)*base70 + (882293538418427259/317000000000000000000000000000000 : ℝ)*base71 + (13884931173447/3170000000000000000000000000 : ℝ)*base73 + (5204919723496572741/317000000000000000000000000000000 : ℝ)*base76 + (765075962140427259/317000000000000000000000000000000 : ℝ)*base77 + (1199109327461572741/317000000000000000000000000000000 : ℝ)*base80 + (22043961143577/3170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6137077/1250000000000000000000 : ℝ)*base90 + (6137077/1250000000000000000000 : ℝ)*base92 + (6137077/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60405632150854646549137/6340000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1953408807/100000000000000 : ℝ)*(base19) + (2050566543/100000000000000 : ℝ)*(base23) + (4626219/2500000000000 : ℝ)*(upper3) + (27042803/100000000000000 : ℝ)*(lower4) + (238645737/100000000000000 : ℝ)*(upper5) + (5499960122078159/100000000000000 : ℝ)*(major0) + (5499960122078159/100000000000000 : ℝ)*(major1) + (5499960122078159/100000000000000 : ℝ)*(major2) + (55047793453/100000000000000 : ℝ)*(sp1) + (51523889101/100000000000000 : ℝ)*(sp2) + (1841497478791553/25000000000000 : ℝ)*(sp4) + (460370807122747/6250000000000 : ℝ)*(sp5) + (7365936340710567/100000000000000 : ℝ)*(sp6) + (454241251425003/12500000000000 : ℝ)*(sp7) + (454241251425003/12500000000000 : ℝ)*(f.failure) + (1841497478791553/25000000000000 : ℝ)*(f.sum) + (55220163769823/19020000000000000000000000000 : ℝ)*base65 + (679463287430327053/634000000000000000000000000000000 : ℝ)*base68 + (6671716158998327053/634000000000000000000000000000000 : ℝ)*base70 + (520148315613672947/634000000000000000000000000000000 : ℝ)*base71 + (163954559664023/19020000000000000000000000000 : ℝ)*base73 + (465407046670327053/634000000000000000000000000000000 : ℝ)*base76 + (5807692017375672947/634000000000000000000000000000000 : ℝ)*base77 + (2532459955595672947/634000000000000000000000000000000 : ℝ)*base79 + (3348305126497/19020000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3499709/625000000000000000000 : ℝ)*base90 + (3499709/625000000000000000000 : ℝ)*base92 + (3499709/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1238_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1238_s5_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212169877/1000000000 : ℝ)*x 0 + (2696254991/5000000000 : ℝ)*x 1 + (5265993143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212169877/1000000000 : ℝ)^8431 ≤ (2580350303967/20000000000000 : ℝ)^6383 := by
    have hnat : (212169877 : ℕ)^8431*20000000000000^6383 ≤ 2580350303967^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212169877 1000000000 2580350303967 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696254991/5000000000 : ℝ)^8431 ≤ (22115944103779/50000000000000 : ℝ)^6383 := by
    have hnat : (2696254991 : ℕ)^8431*50000000000000^6383 ≤ 22115944103779^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696254991 5000000000 22115944103779 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265993143/10000000000 : ℝ)^8431 ≤ (42866360258959/100000000000000 : ℝ)^6383 := by
    have hnat : (5265993143 : ℕ)^8431*100000000000000^6383 ≤ 42866360258959^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265993143 10000000000 42866360258959 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212169877/1000000000 : ℝ), (2696254991/5000000000 : ℝ), (5265993143/10000000000 : ℝ)] ![(2580350303967/20000000000000 : ℝ), (22115944103779/50000000000000 : ℝ), (42866360258959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212169877/1000000000 : ℝ)|^8431 ≤ (2580350303967/20000000000000 : ℝ)^6383
        have hw : |(-212169877/1000000000 : ℝ)|=(212169877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696254991/5000000000 : ℝ)|^8431 ≤ (22115944103779/50000000000000 : ℝ)^6383
        have hw : |(2696254991/5000000000 : ℝ)|=(2696254991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265993143/10000000000 : ℝ)|^8431 ≤ (42866360258959/100000000000000 : ℝ)^6383
        have hw : |(5265993143/10000000000 : ℝ)|=(5265993143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672321819/5000000000 : ℝ)*x 0 + (-1092932211/5000000000 : ℝ)*x 1 + (658249133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672321819/5000000000 : ℝ)^8431 ≤ (21857016175281/50000000000000 : ℝ)^6383 := by
    have hnat : (2672321819 : ℕ)^8431*50000000000000^6383 ≤ 21857016175281^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672321819 5000000000 21857016175281 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092932211/5000000000 : ℝ)^8431 ≤ (13419608220511/100000000000000 : ℝ)^6383 := by
    have hnat : (1092932211 : ℕ)^8431*100000000000000^6383 ≤ 13419608220511^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092932211 5000000000 13419608220511 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658249133/1250000000 : ℝ)^8431 ≤ (10716589852387/25000000000000 : ℝ)^6383 := by
    have hnat : (658249133 : ℕ)^8431*25000000000000^6383 ≤ 10716589852387^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658249133 1250000000 10716589852387 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672321819/5000000000 : ℝ), (-1092932211/5000000000 : ℝ), (658249133/1250000000 : ℝ)] ![(21857016175281/50000000000000 : ℝ), (13419608220511/100000000000000 : ℝ), (10716589852387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672321819/5000000000 : ℝ)|^8431 ≤ (21857016175281/50000000000000 : ℝ)^6383
        have hw : |(2672321819/5000000000 : ℝ)|=(2672321819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092932211/5000000000 : ℝ)|^8431 ≤ (13419608220511/100000000000000 : ℝ)^6383
        have hw : |(-1092932211/5000000000 : ℝ)|=(1092932211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658249133/1250000000 : ℝ)|^8431 ≤ (10716589852387/25000000000000 : ℝ)^6383
        have hw : |(658249133/1250000000 : ℝ)|=(658249133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068928829/2000000000 : ℝ)*x 0 + (2632996469/5000000000 : ℝ)*x 1 + (-1092931957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068928829/2000000000 : ℝ)^8431 ≤ (21857018913917/50000000000000 : ℝ)^6383 := by
    have hnat : (1068928829 : ℕ)^8431*50000000000000^6383 ≤ 21857018913917^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068928829 2000000000 21857018913917 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632996469/5000000000 : ℝ)^8431 ≤ (5358294756849/12500000000000 : ℝ)^6383 := by
    have hnat : (2632996469 : ℕ)^8431*12500000000000^6383 ≤ 5358294756849^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632996469 5000000000 5358294756849 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092931957/5000000000 : ℝ)^8431 ≤ (6709802050553/50000000000000 : ℝ)^6383 := by
    have hnat : (1092931957 : ℕ)^8431*50000000000000^6383 ≤ 6709802050553^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092931957 5000000000 6709802050553 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068928829/2000000000 : ℝ), (2632996469/5000000000 : ℝ), (-1092931957/5000000000 : ℝ)] ![(21857018913917/50000000000000 : ℝ), (5358294756849/12500000000000 : ℝ), (6709802050553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068928829/2000000000 : ℝ)|^8431 ≤ (21857018913917/50000000000000 : ℝ)^6383
        have hw : |(1068928829/2000000000 : ℝ)|=(1068928829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632996469/5000000000 : ℝ)|^8431 ≤ (5358294756849/12500000000000 : ℝ)^6383
        have hw : |(2632996469/5000000000 : ℝ)|=(2632996469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092931957/5000000000 : ℝ)|^8431 ≤ (6709802050553/50000000000000 : ℝ)^6383
        have hw : |(-1092931957/5000000000 : ℝ)|=(1092931957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271953733/625000000 : ℝ)*x 0 + (33799007/80000000 : ℝ)*x 1 + (4481323433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271953733/625000000 : ℝ)^8431 ≤ (33316840844123/100000000000000 : ℝ)^6383 := by
    have hnat : (271953733 : ℕ)^8431*100000000000000^6383 ≤ 33316840844123^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271953733 625000000 33316840844123 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33799007/80000000 : ℝ)^8431 ≤ (1281785945993/4000000000000 : ℝ)^6383 := by
    have hnat : (33799007 : ℕ)^8431*4000000000000^6383 ≤ 1281785945993^6383*80000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33799007 80000000 1281785945993 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481323433/10000000000 : ℝ)^8431 ≤ (34638510496249/100000000000000 : ℝ)^6383 := by
    have hnat : (4481323433 : ℕ)^8431*100000000000000^6383 ≤ 34638510496249^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481323433 10000000000 34638510496249 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271953733/625000000 : ℝ), (33799007/80000000 : ℝ), (4481323433/10000000000 : ℝ)] ![(33316840844123/100000000000000 : ℝ), (1281785945993/4000000000000 : ℝ), (34638510496249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271953733/625000000 : ℝ)|^8431 ≤ (33316840844123/100000000000000 : ℝ)^6383
        have hw : |(271953733/625000000 : ℝ)|=(271953733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33799007/80000000 : ℝ)|^8431 ≤ (1281785945993/4000000000000 : ℝ)^6383
        have hw : |(33799007/80000000 : ℝ)|=(33799007/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481323433/10000000000 : ℝ)|^8431 ≤ (34638510496249/100000000000000 : ℝ)^6383
        have hw : |(4481323433/10000000000 : ℝ)|=(4481323433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060851993/5000000000 : ℝ)*x 0 + (526631853/1000000000 : ℝ)*x 1 + (5392183191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060851993/5000000000 : ℝ)^8431 ≤ (12901793414329/100000000000000 : ℝ)^6383 := by
    have hnat : (1060851993 : ℕ)^8431*100000000000000^6383 ≤ 12901793414329^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060851993 5000000000 12901793414329 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526631853/1000000000 : ℝ)^8431 ≤ (42869858865211/100000000000000 : ℝ)^6383 := by
    have hnat : (526631853 : ℕ)^8431*100000000000000^6383 ≤ 42869858865211^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526631853 1000000000 42869858865211 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392183191/10000000000 : ℝ)^8431 ≤ (4422834770729/10000000000000 : ℝ)^6383 := by
    have hnat : (5392183191 : ℕ)^8431*10000000000000^6383 ≤ 4422834770729^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392183191 10000000000 4422834770729 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060851993/5000000000 : ℝ), (526631853/1000000000 : ℝ), (5392183191/10000000000 : ℝ)] ![(12901793414329/100000000000000 : ℝ), (42869858865211/100000000000000 : ℝ), (4422834770729/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060851993/5000000000 : ℝ)|^8431 ≤ (12901793414329/100000000000000 : ℝ)^6383
        have hw : |(-1060851993/5000000000 : ℝ)|=(1060851993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526631853/1000000000 : ℝ)|^8431 ≤ (42869858865211/100000000000000 : ℝ)^6383
        have hw : |(526631853/1000000000 : ℝ)|=(526631853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392183191/10000000000 : ℝ)|^8431 ≤ (4422834770729/10000000000000 : ℝ)^6383
        have hw : |(5392183191/10000000000 : ℝ)|=(5392183191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656185707/5000000000 : ℝ)*x 0 + (-2059674299/10000000000 : ℝ)*x 1 + (1348045799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656185707/5000000000 : ℝ)^8431 ≤ (43365724087057/100000000000000 : ℝ)^6383 := by
    have hnat : (2656185707 : ℕ)^8431*100000000000000^6383 ≤ 43365724087057^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656185707 5000000000 43365724087057 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059674299/10000000000 : ℝ)^8431 ≤ (12405928135929/100000000000000 : ℝ)^6383 := by
    have hnat : (2059674299 : ℕ)^8431*100000000000000^6383 ≤ 12405928135929^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059674299 10000000000 12405928135929 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348045799/2500000000 : ℝ)^8431 ≤ (2211417388073/5000000000000 : ℝ)^6383 := by
    have hnat : (1348045799 : ℕ)^8431*5000000000000^6383 ≤ 2211417388073^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348045799 2500000000 2211417388073 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656185707/5000000000 : ℝ), (-2059674299/10000000000 : ℝ), (1348045799/2500000000 : ℝ)] ![(43365724087057/100000000000000 : ℝ), (12405928135929/100000000000000 : ℝ), (2211417388073/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656185707/5000000000 : ℝ)|^8431 ≤ (43365724087057/100000000000000 : ℝ)^6383
        have hw : |(2656185707/5000000000 : ℝ)|=(2656185707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059674299/10000000000 : ℝ)|^8431 ≤ (12405928135929/100000000000000 : ℝ)^6383
        have hw : |(-2059674299/10000000000 : ℝ)|=(2059674299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348045799/2500000000 : ℝ)|^8431 ≤ (2211417388073/5000000000000 : ℝ)^6383
        have hw : |(1348045799/2500000000 : ℝ)|=(1348045799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312371413/10000000000 : ℝ)*x 0 + (1348045799/2500000000 : ℝ)*x 1 + (-2059674301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312371413/10000000000 : ℝ)^8431 ≤ (1734628963051/4000000000000 : ℝ)^6383 := by
    have hnat : (5312371413 : ℕ)^8431*4000000000000^6383 ≤ 1734628963051^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312371413 10000000000 1734628963051 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348045799/2500000000 : ℝ)^8431 ≤ (2211417388073/5000000000000 : ℝ)^6383 := by
    have hnat : (1348045799 : ℕ)^8431*5000000000000^6383 ≤ 2211417388073^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348045799 2500000000 2211417388073 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2059674301/10000000000 : ℝ)^8431 ≤ (77537050949/625000000000 : ℝ)^6383 := by
    have hnat : (2059674301 : ℕ)^8431*625000000000^6383 ≤ 77537050949^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059674301 10000000000 77537050949 625000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312371413/10000000000 : ℝ), (1348045799/2500000000 : ℝ), (-2059674301/10000000000 : ℝ)] ![(1734628963051/4000000000000 : ℝ), (2211417388073/5000000000000 : ℝ), (77537050949/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312371413/10000000000 : ℝ)|^8431 ≤ (1734628963051/4000000000000 : ℝ)^6383
        have hw : |(5312371413/10000000000 : ℝ)|=(5312371413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348045799/2500000000 : ℝ)|^8431 ≤ (2211417388073/5000000000000 : ℝ)^6383
        have hw : |(1348045799/2500000000 : ℝ)|=(1348045799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2059674301/10000000000 : ℝ)|^8431 ≤ (77537050949/625000000000 : ℝ)^6383
        have hw : |(-2059674301/10000000000 : ℝ)|=(2059674301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_s5_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351270699/10000000000 : ℝ)*x 0 + (4480664471/10000000000 : ℝ)*x 1 + (4225536307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351270699/10000000000 : ℝ)^8431 ≤ (16658475899889/50000000000000 : ℝ)^6383 := by
    have hnat : (4351270699 : ℕ)^8431*50000000000000^6383 ≤ 16658475899889^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351270699 10000000000 16658475899889 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480664471/10000000000 : ℝ)^8431 ≤ (34631782940747/100000000000000 : ℝ)^6383 := by
    have hnat : (4480664471 : ℕ)^8431*100000000000000^6383 ≤ 34631782940747^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480664471 10000000000 34631782940747 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225536307/10000000000 : ℝ)^8431 ≤ (8012816312163/25000000000000 : ℝ)^6383 := by
    have hnat : (4225536307 : ℕ)^8431*25000000000000^6383 ≤ 8012816312163^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225536307 10000000000 8012816312163 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351270699/10000000000 : ℝ), (4480664471/10000000000 : ℝ), (4225536307/10000000000 : ℝ)] ![(16658475899889/50000000000000 : ℝ), (34631782940747/100000000000000 : ℝ), (8012816312163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351270699/10000000000 : ℝ)|^8431 ≤ (16658475899889/50000000000000 : ℝ)^6383
        have hw : |(4351270699/10000000000 : ℝ)|=(4351270699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480664471/10000000000 : ℝ)|^8431 ≤ (34631782940747/100000000000000 : ℝ)^6383
        have hw : |(4480664471/10000000000 : ℝ)|=(4480664471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225536307/10000000000 : ℝ)|^8431 ≤ (8012816312163/25000000000000 : ℝ)^6383
        have hw : |(4225536307/10000000000 : ℝ)|=(4225536307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14129/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (4215/1024 : ℝ) ≤ (12863997462396329/100000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^4215 ≤ (12863997462396329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2269 : ℕ)^4215*100000000000000000000^1024 ≤ 12863997462396329^1024*20000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 12863997462396329 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (12863997462396329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4215/1024 : ℝ) ≤ (16378039453517251/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4215 ≤ (16378039453517251/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4215*50000000000000000000^1024 ≤ 16378039453517251^1024*100000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 16378039453517251 50000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (16378039453517251/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012863997462396329/50000000000000000000 : ℝ) ≤ (5000312489934269/5000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50012863997462396329/50000000000000000000 : ℝ)^1024 ≤ (5000312489934269/5000000000000000 : ℝ)^4215 := by
      have hnat : (50012863997462396329 : ℕ)^1024*5000000000000000^4215 ≤ 5000312489934269^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012863997462396329 50000000000000000000 5000312489934269 5000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000312489934269/5000000000000000 : ℝ)) (X := (50012863997462396329/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045620076369430831/100000000000000000000 : ℝ) ≤ (10001108111349299/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100045620076369430831/100000000000000000000 : ℝ)^1024 ≤ (10001108111349299/10000000000000000 : ℝ)^4215 := by
      have hnat : (100045620076369430831 : ℕ)^1024*10000000000000000^4215 ≤ 10001108111349299^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045620076369430831 100000000000000000000 10001108111349299 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001108111349299/10000000000000000 : ℝ)) (X := (100045620076369430831/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016378039453517251/25000000000000000000 : ℝ) ≤ (500079562141503/500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (25016378039453517251/25000000000000000000 : ℝ)^1024 ≤ (500079562141503/500000000000000 : ℝ)^4215 := by
      have hnat : (25016378039453517251 : ℕ)^1024*500000000000000^4215 ≤ 500079562141503^4215*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016378039453517251 25000000000000000000 500079562141503 500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500079562141503/500000000000000 : ℝ)) (X := (25016378039453517251/25000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12863997462396329/100000000000000000000 : ℝ) ≤ ((14455422594240672403/14460000000000000000 : ℝ)+2*(483131480761/289200000000000 : ℝ)*(2269/20000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (14455422594240672403/14460000000000000000 : ℝ)+2*(483131480761/289200000000000 : ℝ)*(2269/20000 : ℝ)=(5000312489934269/5000000000000000 : ℝ) by norm_num, show 1+2*(12863997462396329/100000000000000000000 : ℝ)=(50012863997462396329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16378039453517251/50000000000000000000 : ℝ)+(12863997462396329/100000000000000000000 : ℝ) ≤ ((14455422594240672403/14460000000000000000 : ℝ)+(483131480761/289200000000000 : ℝ)*((14237/100000 : ℝ)+(2269/20000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (14455422594240672403/14460000000000000000 : ℝ)+(483131480761/289200000000000 : ℝ)*((14237/100000 : ℝ)+(2269/20000 : ℝ))=(10001108111349299/10000000000000000 : ℝ) by norm_num, show 1+(16378039453517251/50000000000000000000 : ℝ)+(12863997462396329/100000000000000000000 : ℝ)=(100045620076369430831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16378039453517251/50000000000000000000 : ℝ) ≤ ((14455422594240672403/14460000000000000000 : ℝ)+2*(483131480761/289200000000000 : ℝ)*(14237/100000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (14455422594240672403/14460000000000000000 : ℝ)+2*(483131480761/289200000000000 : ℝ)*(14237/100000 : ℝ)=(500079562141503/500000000000000 : ℝ) by norm_num, show 1+2*(16378039453517251/50000000000000000000 : ℝ)=(25016378039453517251/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14455422594240672403/14460000000000000000 : ℝ)*(X 1 0+X 2 0)+(483131480761/289200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14455422594240672403/14460000000000000000 : ℝ)) (alpha := (483131480761/289200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14455422594240672403/14460000000000000000 : ℝ)*(X 0 1+X 2 1)+(483131480761/289200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14455422594240672403/14460000000000000000 : ℝ)) (alpha := (483131480761/289200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14455422594240672403/14460000000000000000 : ℝ)*(X 0 2+X 1 2)+(483131480761/289200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14455422594240672403/14460000000000000000 : ℝ)) (alpha := (483131480761/289200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212169877/1000000000 : ℝ)*X 0 0+(2696254991/5000000000 : ℝ)*X 0 1+(5265993143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672321819/5000000000 : ℝ)*X 1 0+(-1092932211/5000000000 : ℝ)*X 1 1+(658249133/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068928829/2000000000 : ℝ)*X 2 0+(2632996469/5000000000 : ℝ)*X 2 1+(-1092931957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271953733/625000000 : ℝ)*X 0 0+(33799007/80000000 : ℝ)*X 0 1+(4481323433/10000000000 : ℝ)*X 0 2+(271953733/625000000 : ℝ)*X 1 0+(33799007/80000000 : ℝ)*X 1 1+(4481323433/10000000000 : ℝ)*X 1 2+(271953733/625000000 : ℝ)*X 2 0+(33799007/80000000 : ℝ)*X 2 1+(4481323433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060851993/5000000000 : ℝ)*X 0 0+(526631853/1000000000 : ℝ)*X 0 1+(5392183191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656185707/5000000000 : ℝ)*X 1 0+(-2059674299/10000000000 : ℝ)*X 1 1+(1348045799/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312371413/10000000000 : ℝ)*X 2 0+(1348045799/2500000000 : ℝ)*X 2 1+(-2059674301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351270699/10000000000 : ℝ)*X 0 0+(4480664471/10000000000 : ℝ)*X 0 1+(4225536307/10000000000 : ℝ)*X 0 2+(4351270699/10000000000 : ℝ)*X 1 0+(4480664471/10000000000 : ℝ)*X 1 1+(4225536307/10000000000 : ℝ)*X 1 2+(4351270699/10000000000 : ℝ)*X 2 0+(4480664471/10000000000 : ℝ)*X 2 1+(4225536307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55215937747510001334785059/24100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (444592727/100000000000000 : ℝ)*(base23) + (53117369/100000000000000 : ℝ)*(lower2) + (232210149/100000000000000 : ℝ)*(lower3) + (195128177/100000000000000 : ℝ)*(upper4) + (257367639/100000000000000 : ℝ)*(lower5) + (1180357544220953/20000000000000 : ℝ)*(major0) + (1180357544220953/20000000000000 : ℝ)*(major1) + (1180357544220953/20000000000000 : ℝ)*(major2) + (7904110258955349/100000000000000 : ℝ)*(sp0) + (1976030928070299/25000000000000 : ℝ)*(sp1) + (3952074822294813/50000000000000 : ℝ)*(sp2) + (60928519947759/1562500000000 : ℝ)*(sp3) + (7966045401/20000000000000 : ℝ)*(sp4) + (26376901157/100000000000000 : ℝ)*(sp5) + (60928519947759/1562500000000 : ℝ)*(f.failure) + (7904150089182353/100000000000000 : ℝ)*(f.sum) + (13332343682623/2892000000000000000000000000 : ℝ)*base66 + (52605866547496647/96400000000000000000000000000000 : ℝ)*base68 + (278103773100296647/96400000000000000000000000000000 : ℝ)*base70 + (1784694846325896647/96400000000000000000000000000000 : ℝ)*base72 + (877143535493/2892000000000000000000000000 : ℝ)*base73 + (1129271183665896647/96400000000000000000000000000000 : ℝ)*base76 + (98647540919496647/96400000000000000000000000000000 : ℝ)*base78 + (1344098564804503353/96400000000000000000000000000000 : ℝ)*base79 + (2697277058317/578400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (398627/78125000000000000000 : ℝ)*base90 + (398627/78125000000000000000 : ℝ)*base92 + (398627/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1211532862219175561946915387/120500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1814106879/100000000000000 : ℝ)*(base19) + (1962377533/100000000000000 : ℝ)*(base23) + (101577451/50000000000000 : ℝ)*(upper3) + (68152861/100000000000000 : ℝ)*(lower4) + (101777543/50000000000000 : ℝ)*(upper5) + (5932319166226929/100000000000000 : ℝ)*(major0) + (5932319166226929/100000000000000 : ℝ)*(major1) + (5932319166226929/100000000000000 : ℝ)*(major2) + (12614394311/25000000000000 : ℝ)*(sp1) + (53991817361/100000000000000 : ℝ)*(sp2) + (7945040004444633/100000000000000 : ℝ)*(sp4) + (7944987732760509/100000000000000 : ℝ)*(sp5) + (3972492025124869/50000000000000 : ℝ)*(sp6) + (391959799286873/10000000000000 : ℝ)*(sp7) + (391959799286873/10000000000000 : ℝ)*(f.failure) + (7945040004444633/100000000000000 : ℝ)*(f.sum) + (4901646131917/4820000000000000000000000000 : ℝ)*base66 + (302902883124730129/482000000000000000000000000000000 : ℝ)*base67 + (7838849614901269871/482000000000000000000000000000000 : ℝ)*base70 + (725089532611269871/482000000000000000000000000000000 : ℝ)*base72 + (9442498429897/4820000000000000000000000000 : ℝ)*base74 + (9341570640815269871/482000000000000000000000000000000 : ℝ)*base76 + (2981851003773269871/482000000000000000000000000000000 : ℝ)*base78 + (2845448708907269871/482000000000000000000000000000000 : ℝ)*base80 + (10662852597563/4820000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (101681/500000000000000000000 : ℝ)*base89 + (101681/500000000000000000000 : ℝ)*base91 + (101681/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1238_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1238_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1238_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1238_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1238_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1238_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

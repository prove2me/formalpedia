-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:18.284546+00:00
-- url     : https://prove2.me/submissions/3318206a-a83d-4c6d-bc5b-3407ddadf16f

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
theorem support_rectangle_w1310_s0_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828215731/10000000000 : ℝ)*x 0 + (601085259/1000000000 : ℝ)*x 1 + (4803217031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828215731/10000000000 : ℝ)^2135 ≤ (10696034367713/100000000000000 : ℝ)^1623 := by
    have hnat : (1828215731 : ℕ)^2135*100000000000000^1623 ≤ 10696034367713^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828215731 10000000000 10696034367713 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601085259/1000000000 : ℝ)^2135 ≤ (51191529502179/100000000000000 : ℝ)^1623 := by
    have hnat : (601085259 : ℕ)^2135*100000000000000^1623 ≤ 51191529502179^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601085259 1000000000 51191529502179 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4803217031/10000000000 : ℝ)^2135 ≤ (19056218057179/50000000000000 : ℝ)^1623 := by
    have hnat : (4803217031 : ℕ)^2135*50000000000000^1623 ≤ 19056218057179^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803217031 10000000000 19056218057179 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828215731/10000000000 : ℝ), (601085259/1000000000 : ℝ), (4803217031/10000000000 : ℝ)] ![(10696034367713/100000000000000 : ℝ), (51191529502179/100000000000000 : ℝ), (19056218057179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828215731/10000000000 : ℝ)|^2135 ≤ (10696034367713/100000000000000 : ℝ)^1623
        have hw : |(-1828215731/10000000000 : ℝ)|=(1828215731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601085259/1000000000 : ℝ)|^2135 ≤ (51191529502179/100000000000000 : ℝ)^1623
        have hw : |(601085259/1000000000 : ℝ)|=(601085259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4803217031/10000000000 : ℝ)|^2135 ≤ (19056218057179/50000000000000 : ℝ)^1623
        have hw : |(4803217031/10000000000 : ℝ)|=(4803217031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5505399413/10000000000 : ℝ)*x 0 + (-629060713/2500000000 : ℝ)*x 1 + (600402119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5505399413/10000000000 : ℝ)^2135 ≤ (4560544864469/10000000000000 : ℝ)^1623 := by
    have hnat : (5505399413 : ℕ)^2135*10000000000000^1623 ≤ 4560544864469^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505399413 10000000000 4560544864469 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629060713/2500000000 : ℝ)^2135 ≤ (8141058029499/50000000000000 : ℝ)^1623 := by
    have hnat : (629060713 : ℕ)^2135*50000000000000^1623 ≤ 8141058029499^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629060713 2500000000 8141058029499 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600402119/1250000000 : ℝ)^2135 ≤ (19056217644881/50000000000000 : ℝ)^1623 := by
    have hnat : (600402119 : ℕ)^2135*50000000000000^1623 ≤ 19056217644881^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600402119 1250000000 19056217644881 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5505399413/10000000000 : ℝ), (-629060713/2500000000 : ℝ), (600402119/1250000000 : ℝ)] ![(4560544864469/10000000000000 : ℝ), (8141058029499/50000000000000 : ℝ), (19056217644881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5505399413/10000000000 : ℝ)|^2135 ≤ (4560544864469/10000000000000 : ℝ)^1623
        have hw : |(5505399413/10000000000 : ℝ)|=(5505399413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-629060713/2500000000 : ℝ)|^2135 ≤ (8141058029499/50000000000000 : ℝ)^1623
        have hw : |(-629060713/2500000000 : ℝ)|=(629060713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600402119/1250000000 : ℝ)|^2135 ≤ (19056217644881/50000000000000 : ℝ)^1623
        have hw : |(600402119/1250000000 : ℝ)|=(600402119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5505398817/10000000000 : ℝ)*x 0 + (2401608739/5000000000 : ℝ)*x 1 + (-2516242969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5505398817/10000000000 : ℝ)^2135 ≤ (22802721075037/50000000000000 : ℝ)^1623 := by
    have hnat : (5505398817 : ℕ)^2135*50000000000000^1623 ≤ 22802721075037^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505398817 10000000000 22802721075037 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401608739/5000000000 : ℝ)^2135 ≤ (38112440780107/100000000000000 : ℝ)^1623 := by
    have hnat : (2401608739 : ℕ)^2135*100000000000000^1623 ≤ 38112440780107^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401608739 5000000000 38112440780107 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2516242969/10000000000 : ℝ)^2135 ≤ (4070529263729/25000000000000 : ℝ)^1623 := by
    have hnat : (2516242969 : ℕ)^2135*25000000000000^1623 ≤ 4070529263729^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516242969 10000000000 4070529263729 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5505398817/10000000000 : ℝ), (2401608739/5000000000 : ℝ), (-2516242969/10000000000 : ℝ)] ![(22802721075037/50000000000000 : ℝ), (38112440780107/100000000000000 : ℝ), (4070529263729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5505398817/10000000000 : ℝ)|^2135 ≤ (22802721075037/50000000000000 : ℝ)^1623
        have hw : |(5505398817/10000000000 : ℝ)|=(5505398817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401608739/5000000000 : ℝ)|^2135 ≤ (38112440780107/100000000000000 : ℝ)^1623
        have hw : |(2401608739/5000000000 : ℝ)|=(2401608739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2516242969/10000000000 : ℝ)|^2135 ≤ (4070529263729/25000000000000 : ℝ)^1623
        have hw : |(-2516242969/10000000000 : ℝ)|=(2516242969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4183577693/10000000000 : ℝ)*x 0 + (124332423/400000000 : ℝ)*x 1 + (5607368997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183577693/10000000000 : ℝ)^2135 ≤ (496568746981/1562500000000 : ℝ)^1623 := by
    have hnat : (4183577693 : ℕ)^2135*1562500000000^1623 ≤ 496568746981^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183577693 10000000000 496568746981 1562500000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124332423/400000000 : ℝ)^2135 ≤ (10749877781699/50000000000000 : ℝ)^1623 := by
    have hnat : (124332423 : ℕ)^2135*50000000000000^1623 ≤ 10749877781699^1623*400000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124332423 400000000 10749877781699 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5607368997/10000000000 : ℝ)^2135 ≤ (46719844622383/100000000000000 : ℝ)^1623 := by
    have hnat : (5607368997 : ℕ)^2135*100000000000000^1623 ≤ 46719844622383^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607368997 10000000000 46719844622383 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183577693/10000000000 : ℝ), (124332423/400000000 : ℝ), (5607368997/10000000000 : ℝ)] ![(496568746981/1562500000000 : ℝ), (10749877781699/50000000000000 : ℝ), (46719844622383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183577693/10000000000 : ℝ)|^2135 ≤ (496568746981/1562500000000 : ℝ)^1623
        have hw : |(4183577693/10000000000 : ℝ)|=(4183577693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124332423/400000000 : ℝ)|^2135 ≤ (10749877781699/50000000000000 : ℝ)^1623
        have hw : |(124332423/400000000 : ℝ)|=(124332423/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5607368997/10000000000 : ℝ)|^2135 ≤ (46719844622383/100000000000000 : ℝ)^1623
        have hw : |(5607368997/10000000000 : ℝ)|=(5607368997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-183284277/1000000000 : ℝ)*x 0 + (1208588579/2500000000 : ℝ)*x 1 + (5978605411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183284277/1000000000 : ℝ)^2135 ≤ (10731659058723/100000000000000 : ℝ)^1623 := by
    have hnat : (183284277 : ℕ)^2135*100000000000000^1623 ≤ 10731659058723^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183284277 1000000000 10731659058723 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208588579/2500000000 : ℝ)^2135 ≤ (38437776361229/100000000000000 : ℝ)^1623 := by
    have hnat : (1208588579 : ℕ)^2135*100000000000000^1623 ≤ 38437776361229^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208588579 2500000000 38437776361229 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5978605411/10000000000 : ℝ)^2135 ≤ (50830564575361/100000000000000 : ℝ)^1623 := by
    have hnat : (5978605411 : ℕ)^2135*100000000000000^1623 ≤ 50830564575361^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978605411 10000000000 50830564575361 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183284277/1000000000 : ℝ), (1208588579/2500000000 : ℝ), (5978605411/10000000000 : ℝ)] ![(10731659058723/100000000000000 : ℝ), (38437776361229/100000000000000 : ℝ), (50830564575361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183284277/1000000000 : ℝ)|^2135 ≤ (10731659058723/100000000000000 : ℝ)^1623
        have hw : |(-183284277/1000000000 : ℝ)|=(183284277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208588579/2500000000 : ℝ)|^2135 ≤ (38437776361229/100000000000000 : ℝ)^1623
        have hw : |(1208588579/2500000000 : ℝ)|=(1208588579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5978605411/10000000000 : ℝ)|^2135 ≤ (50830564575361/100000000000000 : ℝ)^1623
        have hw : |(5978605411/10000000000 : ℝ)|=(5978605411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517649711/1000000000 : ℝ)*x 0 + (-134085519/1000000000 : ℝ)*x 1 + (1195721061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517649711/1000000000 : ℝ)^2135 ≤ (42055643374717/100000000000000 : ℝ)^1623 := by
    have hnat : (517649711 : ℕ)^2135*100000000000000^1623 ≤ 42055643374717^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517649711 1000000000 42055643374717 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134085519/1000000000 : ℝ)^2135 ≤ (7113793221737/100000000000000 : ℝ)^1623 := by
    have hnat : (134085519 : ℕ)^2135*100000000000000^1623 ≤ 7113793221737^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134085519 1000000000 7113793221737 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195721061/2000000000 : ℝ)^2135 ≤ (50830563389837/100000000000000 : ℝ)^1623 := by
    have hnat : (1195721061 : ℕ)^2135*100000000000000^1623 ≤ 50830563389837^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195721061 2000000000 50830563389837 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517649711/1000000000 : ℝ), (-134085519/1000000000 : ℝ), (1195721061/2000000000 : ℝ)] ![(42055643374717/100000000000000 : ℝ), (7113793221737/100000000000000 : ℝ), (50830563389837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517649711/1000000000 : ℝ)|^2135 ≤ (42055643374717/100000000000000 : ℝ)^1623
        have hw : |(517649711/1000000000 : ℝ)|=(517649711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134085519/1000000000 : ℝ)|^2135 ≤ (7113793221737/100000000000000 : ℝ)^1623
        have hw : |(-134085519/1000000000 : ℝ)|=(134085519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195721061/2000000000 : ℝ)|^2135 ≤ (50830563389837/100000000000000 : ℝ)^1623
        have hw : |(1195721061/2000000000 : ℝ)|=(1195721061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2588248569/5000000000 : ℝ)*x 0 + (5978605363/10000000000 : ℝ)*x 1 + (-670427527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588248569/5000000000 : ℝ)^2135 ≤ (21027821836981/50000000000000 : ℝ)^1623 := by
    have hnat : (2588248569 : ℕ)^2135*50000000000000^1623 ≤ 21027821836981^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588248569 5000000000 21027821836981 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5978605363/10000000000 : ℝ)^2135 ≤ (1270764100963/2500000000000 : ℝ)^1623 := by
    have hnat : (5978605363 : ℕ)^2135*2500000000000^1623 ≤ 1270764100963^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978605363 10000000000 1270764100963 2500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (670427527/5000000000 : ℝ)^2135 ≤ (7113792272581/100000000000000 : ℝ)^1623 := by
    have hnat : (670427527 : ℕ)^2135*100000000000000^1623 ≤ 7113792272581^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670427527 5000000000 7113792272581 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588248569/5000000000 : ℝ), (5978605363/10000000000 : ℝ), (-670427527/5000000000 : ℝ)] ![(21027821836981/50000000000000 : ℝ), (1270764100963/2500000000000 : ℝ), (7113792272581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588248569/5000000000 : ℝ)|^2135 ≤ (21027821836981/50000000000000 : ℝ)^1623
        have hw : |(2588248569/5000000000 : ℝ)|=(2588248569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5978605363/10000000000 : ℝ)|^2135 ≤ (1270764100963/2500000000000 : ℝ)^1623
        have hw : |(5978605363/10000000000 : ℝ)|=(5978605363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-670427527/5000000000 : ℝ)|^2135 ≤ (7113792272581/100000000000000 : ℝ)^1623
        have hw : |(-670427527/5000000000 : ℝ)|=(670427527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s0_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (838630403/2000000000 : ℝ)*x 0 + (5542934547/10000000000 : ℝ)*x 1 + (793760457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838630403/2000000000 : ℝ)^2135 ≤ (31876109421463/100000000000000 : ℝ)^1623 := by
    have hnat : (838630403 : ℕ)^2135*100000000000000^1623 ≤ 31876109421463^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838630403 2000000000 31876109421463 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5542934547/10000000000 : ℝ)^2135 ≤ (23007454234913/50000000000000 : ℝ)^1623 := by
    have hnat : (5542934547 : ℕ)^2135*50000000000000^1623 ≤ 23007454234913^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5542934547 10000000000 23007454234913 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793760457/2500000000 : ℝ)^2135 ≤ (11054491048329/50000000000000 : ℝ)^1623 := by
    have hnat : (793760457 : ℕ)^2135*50000000000000^1623 ≤ 11054491048329^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793760457 2500000000 11054491048329 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838630403/2000000000 : ℝ), (5542934547/10000000000 : ℝ), (793760457/2500000000 : ℝ)] ![(31876109421463/100000000000000 : ℝ), (23007454234913/50000000000000 : ℝ), (11054491048329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838630403/2000000000 : ℝ)|^2135 ≤ (31876109421463/100000000000000 : ℝ)^1623
        have hw : |(838630403/2000000000 : ℝ)|=(838630403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5542934547/10000000000 : ℝ)|^2135 ≤ (23007454234913/50000000000000 : ℝ)^1623
        have hw : |(5542934547/10000000000 : ℝ)|=(5542934547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793760457/2500000000 : ℝ)|^2135 ≤ (11054491048329/50000000000000 : ℝ)^1623
        have hw : |(793760457/2500000000 : ℝ)|=(793760457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1171/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27103/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4269/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4269 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4269*1^1024 ≤ 0^1024*1^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4269/1024 : ℝ) ≤ (2192854751495642077/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4269 ≤ (2192854751495642077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4269*100000000000000000000^1024 ≤ 2192854751495642077^1024*5^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2192854751495642077 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2192854751495642077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4269 := by
      have hnat : (1 : ℕ)^1024*1^4269 ≤ 1^4269*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102192854751495642077/100000000000000000000 : ℝ) ≤ (5026083461655011/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (102192854751495642077/100000000000000000000 : ℝ)^1024 ≤ (5026083461655011/5000000000000000 : ℝ)^4269 := by
      have hnat : (102192854751495642077 : ℕ)^1024*5000000000000000^4269 ≤ 5026083461655011^4269*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102192854751495642077 100000000000000000000 5026083461655011 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026083461655011/5000000000000000 : ℝ)) (X := (102192854751495642077/100000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52192854751495642077/50000000000000000000 : ℝ) ≤ (2526083461655011/2500000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (52192854751495642077/50000000000000000000 : ℝ)^1024 ≤ (2526083461655011/2500000000000000 : ℝ)^4269 := by
      have hnat : (52192854751495642077 : ℕ)^1024*2500000000000000^4269 ≤ 2526083461655011^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52192854751495642077 50000000000000000000 2526083461655011 2500000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526083461655011/2500000000000000 : ℝ)) (X := (52192854751495642077/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26083461655011/2000000000000000 : ℝ)*(0 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26083461655011/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2192854751495642077/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26083461655011/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26083461655011/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026083461655011/5000000000000000 : ℝ) by norm_num, show 1+(2192854751495642077/100000000000000000000 : ℝ)+(0 : ℝ)=(102192854751495642077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2192854751495642077/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26083461655011/2000000000000000 : ℝ)*(2/5 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26083461655011/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526083461655011/2500000000000000 : ℝ) by norm_num, show 1+2*(2192854751495642077/100000000000000000000 : ℝ)=(52192854751495642077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26083461655011/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26083461655011/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26083461655011/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26083461655011/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26083461655011/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26083461655011/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1828215731/10000000000 : ℝ)*X 0 0+(601085259/1000000000 : ℝ)*X 0 1+(4803217031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5505399413/10000000000 : ℝ)*X 1 0+(-629060713/2500000000 : ℝ)*X 1 1+(600402119/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5505398817/10000000000 : ℝ)*X 2 0+(2401608739/5000000000 : ℝ)*X 2 1+(-2516242969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183577693/10000000000 : ℝ)*X 0 0+(124332423/400000000 : ℝ)*X 0 1+(5607368997/10000000000 : ℝ)*X 0 2+(4183577693/10000000000 : ℝ)*X 1 0+(124332423/400000000 : ℝ)*X 1 1+(5607368997/10000000000 : ℝ)*X 1 2+(4183577693/10000000000 : ℝ)*X 2 0+(124332423/400000000 : ℝ)*X 2 1+(5607368997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-183284277/1000000000 : ℝ)*X 0 0+(1208588579/2500000000 : ℝ)*X 0 1+(5978605411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517649711/1000000000 : ℝ)*X 1 0+(-134085519/1000000000 : ℝ)*X 1 1+(1195721061/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588248569/5000000000 : ℝ)*X 2 0+(5978605363/10000000000 : ℝ)*X 2 1+(-670427527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838630403/2000000000 : ℝ)*X 0 0+(5542934547/10000000000 : ℝ)*X 0 1+(793760457/2500000000 : ℝ)*X 0 2+(838630403/2000000000 : ℝ)*X 1 0+(5542934547/10000000000 : ℝ)*X 1 1+(793760457/2500000000 : ℝ)*X 1 2+(838630403/2000000000 : ℝ)*X 2 0+(5542934547/10000000000 : ℝ)*X 2 1+(793760457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172111625380175171867139/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98444797/100000000000000 : ℝ)*(base1) + (1756255801/100000000000000 : ℝ)*(base19) + (208326341/12500000000000 : ℝ)*(base23) + (54292643/25000000000000 : ℝ)*(upper3) + (39594617/25000000000000 : ℝ)*(upper5) + (307057901951039/50000000000000 : ℝ)*(major0) + (307057901951039/50000000000000 : ℝ)*(major1) + (307057901951039/50000000000000 : ℝ)*(major2) + (828070022519241/100000000000000 : ℝ)*(sp0) + (828073627209837/100000000000000 : ℝ)*(sp1) + (82807371685491/10000000000000 : ℝ)*(sp2) + (100038294595969/25000000000000 : ℝ)*(sp3) + (2729695597/50000000000000 : ℝ)*(sp4) + (2718027671/100000000000000 : ℝ)*(sp7) + (50019499357043/12500000000000 : ℝ)*(f.failure) + (414037691732819/50000000000000 : ℝ)*(f.sum) + (66433951906429/50000000000000000000000000000 : ℝ)*base65 + (852669207906429/100000000000000000000000000000 : ℝ)*base67 + (548674914506429/100000000000000000000000000000 : ℝ)*base69 + (417929749606429/100000000000000000000000000000 : ℝ)*base71 + (282440650356429/50000000000000000000000000000 : ℝ)*base73 + (305773652606429/100000000000000000000000000000 : ℝ)*base75 + (715228170706429/100000000000000000000000000000 : ℝ)*base77 + (116055259306429/100000000000000000000000000000 : ℝ)*base79 + (160436472506429/50000000000000000000000000000 : ℝ)*base81 + (71287/12500000000000000000 : ℝ)*base90 + (71287/12500000000000000000 : ℝ)*base92 + (71287/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9704455014894629096757/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466928163/50000000000000 : ℝ)*(base19) + (949411667/100000000000000 : ℝ)*(base23) + (161939/800000000000 : ℝ)*(base32) + (15568199/12500000000000 : ℝ)*(upper3) + (799461/800000000000 : ℝ)*(upper5) + (64812524457371/10000000000000 : ℝ)*(major0) + (64812524457371/10000000000000 : ℝ)*(major1) + (64812524457371/10000000000000 : ℝ)*(major2) + (1028303519/50000000000000 : ℝ)*(sp1) + (556758211/25000000000000 : ℝ)*(sp2) + (436966958263441/50000000000000 : ℝ)*(sp4) + (873930926063517/100000000000000 : ℝ)*(sp5) + (873930740082371/100000000000000 : ℝ)*(sp6) + (422316422985421/100000000000000 : ℝ)*(sp7) + (105579110806949/25000000000000 : ℝ)*(f.failure) + (436966958263441/50000000000000 : ℝ)*(f.sum) + (12875923713919/10000000000000000000000000000 : ℝ)*base66 + (245799138056081/20000000000000000000000000000 : ℝ)*base67 + (71871416236081/20000000000000000000000000000 : ℝ)*base69 + (107386820456081/20000000000000000000000000000 : ℝ)*base71 + (67510941226081/10000000000000000000000000000 : ℝ)*base73 + (172369269056081/20000000000000000000000000000 : ℝ)*base75 + (88592916816081/20000000000000000000000000000 : ℝ)*base77 + (106269530196081/20000000000000000000000000000 : ℝ)*base79 + (5793750856081/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (132241/25000000000000000000 : ℝ)*base90 + (132241/25000000000000000000 : ℝ)*base92 + (132241/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_s1_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017657563/10000000000 : ℝ)*x 0 + (707099101/1250000000 : ℝ)*x 1 + (2517991789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017657563/10000000000 : ℝ)^2135 ≤ (6088650384687/50000000000000 : ℝ)^1623 := by
    have hnat : (2017657563 : ℕ)^2135*50000000000000^1623 ≤ 6088650384687^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017657563 10000000000 6088650384687 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707099101/1250000000 : ℝ)^2135 ≤ (23631147491117/50000000000000 : ℝ)^1623 := by
    have hnat : (707099101 : ℕ)^2135*50000000000000^1623 ≤ 23631147491117^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707099101 1250000000 23631147491117 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2517991789/5000000000 : ℝ)^2135 ≤ (5070050528973/12500000000000 : ℝ)^1623 := by
    have hnat : (2517991789 : ℕ)^2135*12500000000000^1623 ≤ 5070050528973^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517991789 5000000000 5070050528973 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017657563/10000000000 : ℝ), (707099101/1250000000 : ℝ), (2517991789/5000000000 : ℝ)] ![(6088650384687/50000000000000 : ℝ), (23631147491117/50000000000000 : ℝ), (5070050528973/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017657563/10000000000 : ℝ)|^2135 ≤ (6088650384687/50000000000000 : ℝ)^1623
        have hw : |(-2017657563/10000000000 : ℝ)|=(2017657563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707099101/1250000000 : ℝ)|^2135 ≤ (23631147491117/50000000000000 : ℝ)^1623
        have hw : |(707099101/1250000000 : ℝ)|=(707099101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2517991789/5000000000 : ℝ)|^2135 ≤ (5070050528973/12500000000000 : ℝ)^1623
        have hw : |(2517991789/5000000000 : ℝ)|=(2517991789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5409076727/10000000000 : ℝ)*x 0 + (-1174931231/5000000000 : ℝ)*x 1 + (201439347/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409076727/10000000000 : ℝ)^2135 ≤ (11139681973929/25000000000000 : ℝ)^1623 := by
    have hnat : (5409076727 : ℕ)^2135*25000000000000^1623 ≤ 11139681973929^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409076727 10000000000 11139681973929 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1174931231/5000000000 : ℝ)^2135 ≤ (14880866822493/100000000000000 : ℝ)^1623 := by
    have hnat : (1174931231 : ℕ)^2135*100000000000000^1623 ≤ 14880866822493^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174931231 5000000000 14880866822493 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201439347/400000000 : ℝ)^2135 ≤ (40560405259491/100000000000000 : ℝ)^1623 := by
    have hnat : (201439347 : ℕ)^2135*100000000000000^1623 ≤ 40560405259491^1623*400000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201439347 400000000 40560405259491 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409076727/10000000000 : ℝ), (-1174931231/5000000000 : ℝ), (201439347/400000000 : ℝ)] ![(11139681973929/25000000000000 : ℝ), (14880866822493/100000000000000 : ℝ), (40560405259491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409076727/10000000000 : ℝ)|^2135 ≤ (11139681973929/25000000000000 : ℝ)^1623
        have hw : |(5409076727/10000000000 : ℝ)|=(5409076727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1174931231/5000000000 : ℝ)|^2135 ≤ (14880866822493/100000000000000 : ℝ)^1623
        have hw : |(-1174931231/5000000000 : ℝ)|=(1174931231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201439347/400000000 : ℝ)|^2135 ≤ (40560405259491/100000000000000 : ℝ)^1623
        have hw : |(201439347/400000000 : ℝ)|=(201439347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5409076937/10000000000 : ℝ)*x 0 + (629497911/1250000000 : ℝ)*x 1 + (-1174931341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409076937/10000000000 : ℝ)^2135 ≤ (44558730171381/100000000000000 : ℝ)^1623 := by
    have hnat : (5409076937 : ℕ)^2135*100000000000000^1623 ≤ 44558730171381^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409076937 10000000000 44558730171381 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629497911/1250000000 : ℝ)^2135 ≤ (2028020057963/5000000000000 : ℝ)^1623 := by
    have hnat : (629497911 : ℕ)^2135*5000000000000^1623 ≤ 2028020057963^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629497911 1250000000 2028020057963 5000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174931341/5000000000 : ℝ)^2135 ≤ (7440434327589/50000000000000 : ℝ)^1623 := by
    have hnat : (1174931341 : ℕ)^2135*50000000000000^1623 ≤ 7440434327589^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174931341 5000000000 7440434327589 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409076937/10000000000 : ℝ), (629497911/1250000000 : ℝ), (-1174931341/5000000000 : ℝ)] ![(44558730171381/100000000000000 : ℝ), (2028020057963/5000000000000 : ℝ), (7440434327589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409076937/10000000000 : ℝ)|^2135 ≤ (44558730171381/100000000000000 : ℝ)^1623
        have hw : |(5409076937/10000000000 : ℝ)|=(5409076937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(629497911/1250000000 : ℝ)|^2135 ≤ (2028020057963/5000000000000 : ℝ)^1623
        have hw : |(629497911/1250000000 : ℝ)|=(629497911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1174931341/5000000000 : ℝ)|^2135 ≤ (7440434327589/50000000000000 : ℝ)^1623
        have hw : |(-1174931341/5000000000 : ℝ)|=(1174931341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297979021/10000000000 : ℝ)*x 0 + (231296599/625000000 : ℝ)*x 1 + (2492718639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297979021/10000000000 : ℝ)^2135 ≤ (16464249788187/50000000000000 : ℝ)^1623 := by
    have hnat : (4297979021 : ℕ)^2135*50000000000000^1623 ≤ 16464249788187^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297979021 10000000000 16464249788187 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231296599/625000000 : ℝ)^2135 ≤ (3380722494189/12500000000000 : ℝ)^1623 := by
    have hnat : (231296599 : ℕ)^2135*12500000000000^1623 ≤ 3380722494189^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231296599 625000000 3380722494189 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2492718639/5000000000 : ℝ)^2135 ≤ (20012860225397/50000000000000 : ℝ)^1623 := by
    have hnat : (2492718639 : ℕ)^2135*50000000000000^1623 ≤ 20012860225397^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492718639 5000000000 20012860225397 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297979021/10000000000 : ℝ), (231296599/625000000 : ℝ), (2492718639/5000000000 : ℝ)] ![(16464249788187/50000000000000 : ℝ), (3380722494189/12500000000000 : ℝ), (20012860225397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297979021/10000000000 : ℝ)|^2135 ≤ (16464249788187/50000000000000 : ℝ)^1623
        have hw : |(4297979021/10000000000 : ℝ)|=(4297979021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231296599/625000000 : ℝ)|^2135 ≤ (3380722494189/12500000000000 : ℝ)^1623
        have hw : |(231296599/625000000 : ℝ)|=(231296599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2492718639/5000000000 : ℝ)|^2135 ≤ (20012860225397/50000000000000 : ℝ)^1623
        have hw : |(2492718639/5000000000 : ℝ)|=(2492718639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-504564097/2500000000 : ℝ)*x 0 + (5043966559/10000000000 : ℝ)*x 1 + (5648660917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504564097/2500000000 : ℝ)^2135 ≤ (1522756906391/12500000000000 : ℝ)^1623 := by
    have hnat : (504564097 : ℕ)^2135*12500000000000^1623 ≤ 1522756906391^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504564097 2500000000 1522756906391 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5043966559/10000000000 : ℝ)^2135 ≤ (8129000869649/20000000000000 : ℝ)^1623 := by
    have hnat : (5043966559 : ℕ)^2135*20000000000000^1623 ≤ 8129000869649^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5043966559 10000000000 8129000869649 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5648660917/10000000000 : ℝ)^2135 ≤ (47172940380407/100000000000000 : ℝ)^1623 := by
    have hnat : (5648660917 : ℕ)^2135*100000000000000^1623 ≤ 47172940380407^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648660917 10000000000 47172940380407 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504564097/2500000000 : ℝ), (5043966559/10000000000 : ℝ), (5648660917/10000000000 : ℝ)] ![(1522756906391/12500000000000 : ℝ), (8129000869649/20000000000000 : ℝ), (47172940380407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504564097/2500000000 : ℝ)|^2135 ≤ (1522756906391/12500000000000 : ℝ)^1623
        have hw : |(-504564097/2500000000 : ℝ)|=(504564097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5043966559/10000000000 : ℝ)|^2135 ≤ (8129000869649/20000000000000 : ℝ)^1623
        have hw : |(5043966559/10000000000 : ℝ)|=(5043966559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5648660917/10000000000 : ℝ)|^2135 ≤ (47172940380407/100000000000000 : ℝ)^1623
        have hw : |(5648660917/10000000000 : ℝ)|=(5648660917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5248426033/10000000000 : ℝ)*x 0 + (-43429631/250000000 : ℝ)*x 1 + (2824330323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248426033/10000000000 : ℝ)^2135 ≤ (10706512073673/25000000000000 : ℝ)^1623 := by
    have hnat : (5248426033 : ℕ)^2135*25000000000000^1623 ≤ 10706512073673^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248426033 10000000000 10706512073673 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43429631/250000000 : ℝ)^2135 ≤ (2500253570643/25000000000000 : ℝ)^1623 := by
    have hnat : (43429631 : ℕ)^2135*25000000000000^1623 ≤ 2500253570643^1623*250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43429631 250000000 2500253570643 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2824330323/5000000000 : ℝ)^2135 ≤ (47172937403289/100000000000000 : ℝ)^1623 := by
    have hnat : (2824330323 : ℕ)^2135*100000000000000^1623 ≤ 47172937403289^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824330323 5000000000 47172937403289 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248426033/10000000000 : ℝ), (-43429631/250000000 : ℝ), (2824330323/5000000000 : ℝ)] ![(10706512073673/25000000000000 : ℝ), (2500253570643/25000000000000 : ℝ), (47172937403289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248426033/10000000000 : ℝ)|^2135 ≤ (10706512073673/25000000000000 : ℝ)^1623
        have hw : |(5248426033/10000000000 : ℝ)|=(5248426033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43429631/250000000 : ℝ)|^2135 ≤ (2500253570643/25000000000000 : ℝ)^1623
        have hw : |(-43429631/250000000 : ℝ)|=(43429631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2824330323/5000000000 : ℝ)|^2135 ≤ (47172937403289/100000000000000 : ℝ)^1623
        have hw : |(2824330323/5000000000 : ℝ)|=(2824330323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049685197/2000000000 : ℝ)*x 0 + (5648660499/10000000000 : ℝ)*x 1 + (-1737185523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049685197/2000000000 : ℝ)^2135 ≤ (5353255972433/12500000000000 : ℝ)^1623 := by
    have hnat : (1049685197 : ℕ)^2135*12500000000000^1623 ≤ 5353255972433^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049685197 2000000000 5353255972433 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5648660499/10000000000 : ℝ)^2135 ≤ (23586467894197/50000000000000 : ℝ)^1623 := by
    have hnat : (5648660499 : ℕ)^2135*50000000000000^1623 ≤ 23586467894197^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648660499 10000000000 23586467894197 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737185523/10000000000 : ℝ)^2135 ≤ (10001016425777/100000000000000 : ℝ)^1623 := by
    have hnat : (1737185523 : ℕ)^2135*100000000000000^1623 ≤ 10001016425777^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737185523 10000000000 10001016425777 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049685197/2000000000 : ℝ), (5648660499/10000000000 : ℝ), (-1737185523/10000000000 : ℝ)] ![(5353255972433/12500000000000 : ℝ), (23586467894197/50000000000000 : ℝ), (10001016425777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049685197/2000000000 : ℝ)|^2135 ≤ (5353255972433/12500000000000 : ℝ)^1623
        have hw : |(1049685197/2000000000 : ℝ)|=(1049685197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5648660499/10000000000 : ℝ)|^2135 ≤ (23586467894197/50000000000000 : ℝ)^1623
        have hw : |(5648660499/10000000000 : ℝ)|=(5648660499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1737185523/10000000000 : ℝ)|^2135 ≤ (10001016425777/100000000000000 : ℝ)^1623
        have hw : |(-1737185523/10000000000 : ℝ)|=(1737185523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s1_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4299217653/10000000000 : ℝ)*x 0 + (4968916809/10000000000 : ℝ)*x 1 + (743514857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299217653/10000000000 : ℝ)^2135 ≤ (8235245860217/25000000000000 : ℝ)^1623 := by
    have hnat : (4299217653 : ℕ)^2135*25000000000000^1623 ≤ 8235245860217^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299217653 10000000000 8235245860217 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4968916809/10000000000 : ℝ)^2135 ≤ (7970266987647/20000000000000 : ℝ)^1623 := by
    have hnat : (4968916809 : ℕ)^2135*20000000000000^1623 ≤ 7970266987647^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968916809 10000000000 7970266987647 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743514857/2000000000 : ℝ)^2135 ≤ (27207681615487/100000000000000 : ℝ)^1623 := by
    have hnat : (743514857 : ℕ)^2135*100000000000000^1623 ≤ 27207681615487^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743514857 2000000000 27207681615487 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299217653/10000000000 : ℝ), (4968916809/10000000000 : ℝ), (743514857/2000000000 : ℝ)] ![(8235245860217/25000000000000 : ℝ), (7970266987647/20000000000000 : ℝ), (27207681615487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299217653/10000000000 : ℝ)|^2135 ≤ (8235245860217/25000000000000 : ℝ)^1623
        have hw : |(4299217653/10000000000 : ℝ)|=(4299217653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4968916809/10000000000 : ℝ)|^2135 ≤ (7970266987647/20000000000000 : ℝ)^1623
        have hw : |(4968916809/10000000000 : ℝ)|=(4968916809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743514857/2000000000 : ℝ)|^2135 ≤ (27207681615487/100000000000000 : ℝ)^1623
        have hw : |(743514857/2000000000 : ℝ)|=(743514857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3293/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1171/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (443495610429/50000000000000000000 : ℝ) := by
    have hpowers : (1171/100000 : ℝ)^4269 ≤ (443495610429/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1171 : ℕ)^4269*50000000000000000000^1024 ≤ 443495610429^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1171 100000 443495610429 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1171/100000 : ℝ)) (X := (443495610429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27103/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (432793173465285639/100000000000000000000 : ℝ) := by
    have hpowers : (27103/100000 : ℝ)^4269 ≤ (432793173465285639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27103 : ℕ)^4269*100000000000000000000^1024 ≤ 432793173465285639^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27103 100000 432793173465285639 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27103/100000 : ℝ)) (X := (432793173465285639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000443495610429/25000000000000000000 : ℝ) ≤ (2500000010638077/2500000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25000000443495610429/25000000000000000000 : ℝ)^1024 ≤ (2500000010638077/2500000000000000 : ℝ)^4269 := by
      have hnat : (25000000443495610429 : ℕ)^1024*2500000000000000^4269 ≤ 2500000010638077^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000443495610429 25000000000000000000 2500000010638077 2500000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000010638077/2500000000000000 : ℝ)) (X := (25000000443495610429/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100432794060456506497/100000000000000000000 : ℝ) ≤ (5005182173510031/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (100432794060456506497/100000000000000000000 : ℝ)^1024 ≤ (5005182173510031/5000000000000000 : ℝ)^4269 := by
      have hnat : (100432794060456506497 : ℕ)^1024*5000000000000000^4269 ≤ 5005182173510031^4269*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100432794060456506497 100000000000000000000 5005182173510031 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005182173510031/5000000000000000 : ℝ)) (X := (100432794060456506497/100000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50432793173465285639/50000000000000000000 : ℝ) ≤ (1252591081435977/1250000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50432793173465285639/50000000000000000000 : ℝ)^1024 ≤ (1252591081435977/1250000000000000 : ℝ)^4269 := by
      have hnat : (50432793173465285639 : ℕ)^1024*1250000000000000^4269 ≤ 1252591081435977^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50432793173465285639 50000000000000000000 1252591081435977 1250000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252591081435977/1250000000000000 : ℝ)) (X := (50432793173465285639/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(443495610429/50000000000000000000 : ℝ) ≤ ((21607977325200247599/21610000000000000000 : ℝ)+2*(1727384077959/432200000000000 : ℝ)*(1171/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (21607977325200247599/21610000000000000000 : ℝ)+2*(1727384077959/432200000000000 : ℝ)*(1171/100000 : ℝ)=(2500000010638077/2500000000000000 : ℝ) by norm_num, show 1+2*(443495610429/50000000000000000000 : ℝ)=(25000000443495610429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(432793173465285639/100000000000000000000 : ℝ)+(443495610429/50000000000000000000 : ℝ) ≤ ((21607977325200247599/21610000000000000000 : ℝ)+(1727384077959/432200000000000 : ℝ)*((27103/100000 : ℝ)+(1171/100000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (21607977325200247599/21610000000000000000 : ℝ)+(1727384077959/432200000000000 : ℝ)*((27103/100000 : ℝ)+(1171/100000 : ℝ))=(5005182173510031/5000000000000000 : ℝ) by norm_num, show 1+(432793173465285639/100000000000000000000 : ℝ)+(443495610429/50000000000000000000 : ℝ)=(100432794060456506497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(432793173465285639/100000000000000000000 : ℝ) ≤ ((21607977325200247599/21610000000000000000 : ℝ)+2*(1727384077959/432200000000000 : ℝ)*(27103/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (21607977325200247599/21610000000000000000 : ℝ)+2*(1727384077959/432200000000000 : ℝ)*(27103/100000 : ℝ)=(1252591081435977/1250000000000000 : ℝ) by norm_num, show 1+2*(432793173465285639/100000000000000000000 : ℝ)=(50432793173465285639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21607977325200247599/21610000000000000000 : ℝ)*(X 1 0+X 2 0)+(1727384077959/432200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (1171/100000 : ℝ)) (hi := (27103/100000 : ℝ)) (c := (21607977325200247599/21610000000000000000 : ℝ)) (alpha := (1727384077959/432200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21607977325200247599/21610000000000000000 : ℝ)*(X 0 1+X 2 1)+(1727384077959/432200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (1171/100000 : ℝ)) (hi := (27103/100000 : ℝ)) (c := (21607977325200247599/21610000000000000000 : ℝ)) (alpha := (1727384077959/432200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21607977325200247599/21610000000000000000 : ℝ)*(X 0 2+X 1 2)+(1727384077959/432200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (1171/100000 : ℝ)) (hi := (27103/100000 : ℝ)) (c := (21607977325200247599/21610000000000000000 : ℝ)) (alpha := (1727384077959/432200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2017657563/10000000000 : ℝ)*X 0 0+(707099101/1250000000 : ℝ)*X 0 1+(2517991789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409076727/10000000000 : ℝ)*X 1 0+(-1174931231/5000000000 : ℝ)*X 1 1+(201439347/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5409076937/10000000000 : ℝ)*X 2 0+(629497911/1250000000 : ℝ)*X 2 1+(-1174931341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297979021/10000000000 : ℝ)*X 0 0+(231296599/625000000 : ℝ)*X 0 1+(2492718639/5000000000 : ℝ)*X 0 2+(4297979021/10000000000 : ℝ)*X 1 0+(231296599/625000000 : ℝ)*X 1 1+(2492718639/5000000000 : ℝ)*X 1 2+(4297979021/10000000000 : ℝ)*X 2 0+(231296599/625000000 : ℝ)*X 2 1+(2492718639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-504564097/2500000000 : ℝ)*X 0 0+(5043966559/10000000000 : ℝ)*X 0 1+(5648660917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5248426033/10000000000 : ℝ)*X 1 0+(-43429631/250000000 : ℝ)*X 1 1+(2824330323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049685197/2000000000 : ℝ)*X 2 0+(5648660499/10000000000 : ℝ)*X 2 1+(-1737185523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299217653/10000000000 : ℝ)*X 0 0+(4968916809/10000000000 : ℝ)*X 0 1+(743514857/2000000000 : ℝ)*X 0 2+(4299217653/10000000000 : ℝ)*X 1 0+(4968916809/10000000000 : ℝ)*X 1 1+(743514857/2000000000 : ℝ)*X 1 2+(4299217653/10000000000 : ℝ)*X 2 0+(4968916809/10000000000 : ℝ)*X 2 1+(743514857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (990721638832266191345387871/270125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45721487/100000000000000 : ℝ)*(base1) + (503916773/100000000000000 : ℝ)*(base19) + (566454067/100000000000000 : ℝ)*(base23) + (7333811/6250000000000 : ℝ)*(upper3) + (45956919/100000000000000 : ℝ)*(upper5) + (597301220669157/50000000000000 : ℝ)*(major0) + (597301220669157/50000000000000 : ℝ)*(major1) + (597301220669157/50000000000000 : ℝ)*(major2) + (1610803432468867/100000000000000 : ℝ)*(sp0) + (402701232411249/25000000000000 : ℝ)*(sp1) + (805402433553851/50000000000000 : ℝ)*(sp2) + (48649866411283/6250000000000 : ℝ)*(sp3) + (2046814389/100000000000000 : ℝ)*(sp4) + (354639531/25000000000000 : ℝ)*(sp7) + (778399326860139/100000000000000 : ℝ)*(f.failure) + (1610805433561769/100000000000000 : ℝ)*(f.sum) + (1112300424683/675312500000000000000000000 : ℝ)*base65 + (576482884336745957/1080500000000000000000000000000000 : ℝ)*base68 + (7345479140869254043/1080500000000000000000000000000000 : ℝ)*base69 + (9785670412154754043/1080500000000000000000000000000000 : ℝ)*base71 + (23053078734817/10805000000000000000000000000 : ℝ)*base74 + (3352340703258754043/1080500000000000000000000000000000 : ℝ)*base75 + (9193923045253754043/1080500000000000000000000000000000 : ℝ)*base77 + (2619032992448754043/1080500000000000000000000000000000 : ℝ)*base79 + (49525912385763/10805000000000000000000000000 : ℝ)*base81 + (417951/100000000000000000000 : ℝ)*base90 + (417951/100000000000000000000 : ℝ)*base92 + (417951/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6233424810436738647002735769/1080500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43034853/4000000000000 : ℝ)*(base19) + (205752941/20000000000000 : ℝ)*(base23) + (1063751/50000000000000 : ℝ)*(upper2) + (105163099/100000000000000 : ℝ)*(upper3) + (33074813/20000000000000 : ℝ)*(upper5) + (1226435056473277/100000000000000 : ℝ)*(major0) + (1226435056473277/100000000000000 : ℝ)*(major1) + (1226435056473277/100000000000000 : ℝ)*(major2) + (1038619029/20000000000000 : ℝ)*(sp1) + (2007901689/50000000000000 : ℝ)*(sp2) + (1653728558330463/100000000000000 : ℝ)*(sp4) + (1653722289363993/100000000000000 : ℝ)*(sp5) + (82686175688119/5000000000000 : ℝ)*(sp6) + (799141362315461/100000000000000 : ℝ)*(sp7) + (799141362315461/100000000000000 : ℝ)*(f.failure) + (1653728558330463/100000000000000 : ℝ)*(f.sum) + (107168009054647/21610000000000000000000000000 : ℝ)*base66 + (8179875612883061923/2161000000000000000000000000000000 : ℝ)*base67 + (2505111501706938077/2161000000000000000000000000000000 : ℝ)*base70 + (2625302563727938077/2161000000000000000000000000000000 : ℝ)*base72 + (75540472862853/21610000000000000000000000000 : ℝ)*base73 + (9964154773608938077/2161000000000000000000000000000000 : ℝ)*base76 + (15556115653349938077/2161000000000000000000000000000000 : ℝ)*base78 + (3777513064496061923/2161000000000000000000000000000000 : ℝ)*base79 + (97252424304753/21610000000000000000000000000 : ℝ)*base81 + (157551/100000000000000000000 : ℝ)*base89 + (157551/100000000000000000000 : ℝ)*base91 + (157551/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1310_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3293/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_s2_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-257584079/1250000000 : ℝ)*x 0 + (1372208461/2500000000 : ℝ)*x 1 + (1294109859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257584079/1250000000 : ℝ)^2135 ≤ (12519953749013/100000000000000 : ℝ)^1623 := by
    have hnat : (257584079 : ℕ)^2135*100000000000000^1623 ≤ 12519953749013^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257584079 1250000000 12519953749013 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372208461/2500000000 : ℝ)^2135 ≤ (22712509622253/50000000000000 : ℝ)^1623 := by
    have hnat : (1372208461 : ℕ)^2135*50000000000000^1623 ≤ 22712509622253^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372208461 2500000000 22712509622253 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294109859/2500000000 : ℝ)^2135 ≤ (42055026996937/100000000000000 : ℝ)^1623 := by
    have hnat : (1294109859 : ℕ)^2135*100000000000000^1623 ≤ 42055026996937^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294109859 2500000000 42055026996937 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257584079/1250000000 : ℝ), (1372208461/2500000000 : ℝ), (1294109859/2500000000 : ℝ)] ![(12519953749013/100000000000000 : ℝ), (22712509622253/50000000000000 : ℝ), (42055026996937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257584079/1250000000 : ℝ)|^2135 ≤ (12519953749013/100000000000000 : ℝ)^1623
        have hw : |(-257584079/1250000000 : ℝ)|=(257584079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372208461/2500000000 : ℝ)|^2135 ≤ (22712509622253/50000000000000 : ℝ)^1623
        have hw : |(1372208461/2500000000 : ℝ)|=(1372208461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294109859/2500000000 : ℝ)|^2135 ≤ (42055026996937/100000000000000 : ℝ)^1623
        have hw : |(1294109859/2500000000 : ℝ)|=(1294109859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684125337/5000000000 : ℝ)*x 0 + (-2222385071/10000000000 : ℝ)*x 1 + (5176439077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684125337/5000000000 : ℝ)^2135 ≤ (22058422007753/50000000000000 : ℝ)^1623 := by
    have hnat : (2684125337 : ℕ)^2135*50000000000000^1623 ≤ 22058422007753^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684125337 5000000000 22058422007753 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222385071/10000000000 : ℝ)^2135 ≤ (13828132816489/100000000000000 : ℝ)^1623 := by
    have hnat : (2222385071 : ℕ)^2135*100000000000000^1623 ≤ 13828132816489^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222385071 10000000000 13828132816489 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176439077/10000000000 : ℝ)^2135 ≤ (10513755790053/25000000000000 : ℝ)^1623 := by
    have hnat : (5176439077 : ℕ)^2135*25000000000000^1623 ≤ 10513755790053^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176439077 10000000000 10513755790053 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684125337/5000000000 : ℝ), (-2222385071/10000000000 : ℝ), (5176439077/10000000000 : ℝ)] ![(22058422007753/50000000000000 : ℝ), (13828132816489/100000000000000 : ℝ), (10513755790053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684125337/5000000000 : ℝ)|^2135 ≤ (22058422007753/50000000000000 : ℝ)^1623
        have hw : |(2684125337/5000000000 : ℝ)|=(2684125337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222385071/10000000000 : ℝ)|^2135 ≤ (13828132816489/100000000000000 : ℝ)^1623
        have hw : |(-2222385071/10000000000 : ℝ)|=(2222385071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176439077/10000000000 : ℝ)|^2135 ≤ (10513755790053/25000000000000 : ℝ)^1623
        have hw : |(5176439077/10000000000 : ℝ)|=(5176439077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684125081/5000000000 : ℝ)*x 0 + (5176439549/10000000000 : ℝ)*x 1 + (-222238513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684125081/5000000000 : ℝ)^2135 ≤ (44116838480463/100000000000000 : ℝ)^1623 := by
    have hnat : (2684125081 : ℕ)^2135*100000000000000^1623 ≤ 44116838480463^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684125081 5000000000 44116838480463 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176439549/10000000000 : ℝ)^2135 ≤ (10513757051149/25000000000000 : ℝ)^1623 := by
    have hnat : (5176439549 : ℕ)^2135*25000000000000^1623 ≤ 10513757051149^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176439549 10000000000 10513757051149 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222238513/1000000000 : ℝ)^2135 ≤ (13828133299409/100000000000000 : ℝ)^1623 := by
    have hnat : (222238513 : ℕ)^2135*100000000000000^1623 ≤ 13828133299409^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222238513 1000000000 13828133299409 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684125081/5000000000 : ℝ), (5176439549/10000000000 : ℝ), (-222238513/1000000000 : ℝ)] ![(44116838480463/100000000000000 : ℝ), (10513757051149/25000000000000 : ℝ), (13828133299409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684125081/5000000000 : ℝ)|^2135 ≤ (44116838480463/100000000000000 : ℝ)^1623
        have hw : |(2684125081/5000000000 : ℝ)|=(2684125081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176439549/10000000000 : ℝ)|^2135 ≤ (10513757051149/25000000000000 : ℝ)^1623
        have hw : |(5176439549/10000000000 : ℝ)|=(5176439549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222238513/1000000000 : ℝ)|^2135 ≤ (13828133299409/100000000000000 : ℝ)^1623
        have hw : |(-222238513/1000000000 : ℝ)|=(222238513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4327948389/10000000000 : ℝ)*x 0 + (4016121417/10000000000 : ℝ)*x 1 + (4662592879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327948389/10000000000 : ℝ)^2135 ≤ (8307717835451/25000000000000 : ℝ)^1623 := by
    have hnat : (4327948389 : ℕ)^2135*25000000000000^1623 ≤ 8307717835451^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327948389 10000000000 8307717835451 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016121417/10000000000 : ℝ)^2135 ≤ (7529422911943/25000000000000 : ℝ)^1623 := by
    have hnat : (4016121417 : ℕ)^2135*25000000000000^1623 ≤ 7529422911943^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016121417 10000000000 7529422911943 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4662592879/10000000000 : ℝ)^2135 ≤ (36651437004793/100000000000000 : ℝ)^1623 := by
    have hnat : (4662592879 : ℕ)^2135*100000000000000^1623 ≤ 36651437004793^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662592879 10000000000 36651437004793 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327948389/10000000000 : ℝ), (4016121417/10000000000 : ℝ), (4662592879/10000000000 : ℝ)] ![(8307717835451/25000000000000 : ℝ), (7529422911943/25000000000000 : ℝ), (36651437004793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327948389/10000000000 : ℝ)|^2135 ≤ (8307717835451/25000000000000 : ℝ)^1623
        have hw : |(4327948389/10000000000 : ℝ)|=(4327948389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016121417/10000000000 : ℝ)|^2135 ≤ (7529422911943/25000000000000 : ℝ)^1623
        have hw : |(4016121417/10000000000 : ℝ)|=(4016121417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4662592879/10000000000 : ℝ)|^2135 ≤ (36651437004793/100000000000000 : ℝ)^1623
        have hw : |(4662592879/10000000000 : ℝ)|=(4662592879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060748453/10000000000 : ℝ)*x 0 + (2589235083/5000000000 : ℝ)*x 1 + (5486784401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060748453/10000000000 : ℝ)^2135 ≤ (12520559738527/100000000000000 : ℝ)^1623 := by
    have hnat : (2060748453 : ℕ)^2135*100000000000000^1623 ≤ 12520559738527^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060748453 10000000000 12520559738527 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589235083/5000000000 : ℝ)^2135 ≤ (42076731267447/100000000000000 : ℝ)^1623 := by
    have hnat : (2589235083 : ℕ)^2135*100000000000000^1623 ≤ 42076731267447^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589235083 5000000000 42076731267447 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486784401/10000000000 : ℝ)^2135 ≤ (11350677245777/25000000000000 : ℝ)^1623 := by
    have hnat : (5486784401 : ℕ)^2135*25000000000000^1623 ≤ 11350677245777^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486784401 10000000000 11350677245777 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060748453/10000000000 : ℝ), (2589235083/5000000000 : ℝ), (5486784401/10000000000 : ℝ)] ![(12520559738527/100000000000000 : ℝ), (42076731267447/100000000000000 : ℝ), (11350677245777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060748453/10000000000 : ℝ)|^2135 ≤ (12520559738527/100000000000000 : ℝ)^1623
        have hw : |(-2060748453/10000000000 : ℝ)|=(2060748453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589235083/5000000000 : ℝ)|^2135 ≤ (42076731267447/100000000000000 : ℝ)^1623
        have hw : |(2589235083/5000000000 : ℝ)|=(2589235083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486784401/10000000000 : ℝ)|^2135 ≤ (11350677245777/25000000000000 : ℝ)^1623
        have hw : |(5486784401/10000000000 : ℝ)|=(5486784401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165250527/312500000 : ℝ)*x 0 + (-239004907/1250000000 : ℝ)*x 1 + (2743392247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165250527/312500000 : ℝ)^2135 ≤ (2703219862899/6250000000000 : ℝ)^1623 := by
    have hnat : (165250527 : ℕ)^2135*6250000000000^1623 ≤ 2703219862899^1623*312500000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165250527 312500000 2703219862899 6250000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239004907/1250000000 : ℝ)^2135 ≤ (11345772183247/100000000000000 : ℝ)^1623 := by
    have hnat : (239004907 : ℕ)^2135*100000000000000^1623 ≤ 11345772183247^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239004907 1250000000 11345772183247 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743392247/5000000000 : ℝ)^2135 ≤ (45402709995447/100000000000000 : ℝ)^1623 := by
    have hnat : (2743392247 : ℕ)^2135*100000000000000^1623 ≤ 45402709995447^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743392247 5000000000 45402709995447 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165250527/312500000 : ℝ), (-239004907/1250000000 : ℝ), (2743392247/5000000000 : ℝ)] ![(2703219862899/6250000000000 : ℝ), (11345772183247/100000000000000 : ℝ), (45402709995447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165250527/312500000 : ℝ)|^2135 ≤ (2703219862899/6250000000000 : ℝ)^1623
        have hw : |(165250527/312500000 : ℝ)|=(165250527/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239004907/1250000000 : ℝ)|^2135 ≤ (11345772183247/100000000000000 : ℝ)^1623
        have hw : |(-239004907/1250000000 : ℝ)|=(239004907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743392247/5000000000 : ℝ)|^2135 ≤ (45402709995447/100000000000000 : ℝ)^1623
        have hw : |(2743392247/5000000000 : ℝ)|=(2743392247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057603397/2000000000 : ℝ)*x 0 + (685848051/1250000000 : ℝ)*x 1 + (-191203921/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057603397/2000000000 : ℝ)^2135 ≤ (4325151910827/10000000000000 : ℝ)^1623 := by
    have hnat : (1057603397 : ℕ)^2135*10000000000000^1623 ≤ 4325151910827^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057603397 2000000000 4325151910827 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685848051/1250000000 : ℝ)^2135 ≤ (9080541811861/20000000000000 : ℝ)^1623 := by
    have hnat : (685848051 : ℕ)^2135*20000000000000^1623 ≤ 9080541811861^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685848051 1250000000 9080541811861 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191203921/1000000000 : ℝ)^2135 ≤ (11345771824181/100000000000000 : ℝ)^1623 := by
    have hnat : (191203921 : ℕ)^2135*100000000000000^1623 ≤ 11345771824181^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191203921 1000000000 11345771824181 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057603397/2000000000 : ℝ), (685848051/1250000000 : ℝ), (-191203921/1000000000 : ℝ)] ![(4325151910827/10000000000000 : ℝ), (9080541811861/20000000000000 : ℝ), (11345771824181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057603397/2000000000 : ℝ)|^2135 ≤ (4325151910827/10000000000000 : ℝ)^1623
        have hw : |(1057603397/2000000000 : ℝ)|=(1057603397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685848051/1250000000 : ℝ)|^2135 ≤ (9080541811861/20000000000000 : ℝ)^1623
        have hw : |(685848051/1250000000 : ℝ)|=(685848051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191203921/1000000000 : ℝ)|^2135 ≤ (11345771824181/100000000000000 : ℝ)^1623
        have hw : |(-191203921/1000000000 : ℝ)|=(191203921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s2_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2164052053/5000000000 : ℝ)*x 0 + (4658388489/10000000000 : ℝ)*x 1 + (2010183867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164052053/5000000000 : ℝ)^2135 ≤ (16616222078159/50000000000000 : ℝ)^1623 := by
    have hnat : (2164052053 : ℕ)^2135*50000000000000^1623 ≤ 16616222078159^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164052053 5000000000 16616222078159 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4658388489/10000000000 : ℝ)^2135 ≤ (36607967561613/100000000000000 : ℝ)^1623 := by
    have hnat : (4658388489 : ℕ)^2135*100000000000000^1623 ≤ 36607967561613^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4658388489 10000000000 36607967561613 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010183867/5000000000 : ℝ)^2135 ≤ (30159588271431/100000000000000 : ℝ)^1623 := by
    have hnat : (2010183867 : ℕ)^2135*100000000000000^1623 ≤ 30159588271431^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010183867 5000000000 30159588271431 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164052053/5000000000 : ℝ), (4658388489/10000000000 : ℝ), (2010183867/5000000000 : ℝ)] ![(16616222078159/50000000000000 : ℝ), (36607967561613/100000000000000 : ℝ), (30159588271431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164052053/5000000000 : ℝ)|^2135 ≤ (16616222078159/50000000000000 : ℝ)^1623
        have hw : |(2164052053/5000000000 : ℝ)|=(2164052053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4658388489/10000000000 : ℝ)|^2135 ≤ (36607967561613/100000000000000 : ℝ)^1623
        have hw : |(4658388489/10000000000 : ℝ)|=(4658388489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010183867/5000000000 : ℝ)|^2135 ≤ (30159588271431/100000000000000 : ℝ)^1623
        have hw : |(2010183867/5000000000 : ℝ)|=(2010183867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3293/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4817/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3293/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3293/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3293/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3293/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3293/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3293/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3293/50000 : ℝ) ^ (4269/1024 : ℝ) ≤ (594112360855217/50000000000000000000 : ℝ) := by
    have hpowers : (3293/50000 : ℝ)^4269 ≤ (594112360855217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3293 : ℕ)^4269*50000000000000000000^1024 ≤ 594112360855217^1024*50000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3293 50000 594112360855217 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3293/50000 : ℝ)) (X := (594112360855217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19707/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (28658372133864297/25000000000000000000 : ℝ) := by
    have hpowers : (19707/100000 : ℝ)^4269 ≤ (28658372133864297/25000000000000000000 : ℝ)^1024 := by
      have hnat : (19707 : ℕ)^4269*25000000000000000000^1024 ≤ 28658372133864297^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19707 100000 28658372133864297 25000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19707/100000 : ℝ)) (X := (28658372133864297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000594112360855217/25000000000000000000 : ℝ) ≤ (10000057003097939/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25000594112360855217/25000000000000000000 : ℝ)^1024 ≤ (10000057003097939/10000000000000000 : ℝ)^4269 := by
      have hnat : (25000594112360855217 : ℕ)^1024*10000000000000000^4269 ≤ 10000057003097939^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000594112360855217 25000000000000000000 10000057003097939 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057003097939/10000000000000000 : ℝ)) (X := (25000594112360855217/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50057910856628583811/50000000000000000000 : ℝ) ≤ (5001388489829629/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50057910856628583811/50000000000000000000 : ℝ)^1024 ≤ (5001388489829629/5000000000000000 : ℝ)^4269 := by
      have hnat : (50057910856628583811 : ℕ)^1024*5000000000000000^4269 ≤ 5001388489829629^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057910856628583811 50000000000000000000 5001388489829629 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001388489829629/5000000000000000 : ℝ)) (X := (50057910856628583811/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12528658372133864297/12500000000000000000 : ℝ) ≤ (10005496956220577/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (12528658372133864297/12500000000000000000 : ℝ)^1024 ≤ (10005496956220577/10000000000000000 : ℝ)^4269 := by
      have hnat : (12528658372133864297 : ℕ)^1024*10000000000000000^4269 ≤ 10005496956220577^4269*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12528658372133864297 12500000000000000000 10005496956220577 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005496956220577/10000000000000000 : ℝ)) (X := (12528658372133864297/12500000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(594112360855217/50000000000000000000 : ℝ) ≤ ((131174920406382363751/131210000000000000000 : ℝ)+2*(2719976561319/1312100000000000 : ℝ)*(3293/50000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (131174920406382363751/131210000000000000000 : ℝ)+2*(2719976561319/1312100000000000 : ℝ)*(3293/50000 : ℝ)=(10000057003097939/10000000000000000 : ℝ) by norm_num, show 1+2*(594112360855217/50000000000000000000 : ℝ)=(25000594112360855217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28658372133864297/25000000000000000000 : ℝ)+(594112360855217/50000000000000000000 : ℝ) ≤ ((131174920406382363751/131210000000000000000 : ℝ)+(2719976561319/1312100000000000 : ℝ)*((19707/100000 : ℝ)+(3293/50000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (131174920406382363751/131210000000000000000 : ℝ)+(2719976561319/1312100000000000 : ℝ)*((19707/100000 : ℝ)+(3293/50000 : ℝ))=(5001388489829629/5000000000000000 : ℝ) by norm_num, show 1+(28658372133864297/25000000000000000000 : ℝ)+(594112360855217/50000000000000000000 : ℝ)=(50057910856628583811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28658372133864297/25000000000000000000 : ℝ) ≤ ((131174920406382363751/131210000000000000000 : ℝ)+2*(2719976561319/1312100000000000 : ℝ)*(19707/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (131174920406382363751/131210000000000000000 : ℝ)+2*(2719976561319/1312100000000000 : ℝ)*(19707/100000 : ℝ)=(10005496956220577/10000000000000000 : ℝ) by norm_num, show 1+2*(28658372133864297/25000000000000000000 : ℝ)=(12528658372133864297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131174920406382363751/131210000000000000000 : ℝ)*(X 1 0+X 2 0)+(2719976561319/1312100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (3293/50000 : ℝ)) (hi := (19707/100000 : ℝ)) (c := (131174920406382363751/131210000000000000000 : ℝ)) (alpha := (2719976561319/1312100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131174920406382363751/131210000000000000000 : ℝ)*(X 0 1+X 2 1)+(2719976561319/1312100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (3293/50000 : ℝ)) (hi := (19707/100000 : ℝ)) (c := (131174920406382363751/131210000000000000000 : ℝ)) (alpha := (2719976561319/1312100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131174920406382363751/131210000000000000000 : ℝ)*(X 0 2+X 1 2)+(2719976561319/1312100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (3293/50000 : ℝ)) (hi := (19707/100000 : ℝ)) (c := (131174920406382363751/131210000000000000000 : ℝ)) (alpha := (2719976561319/1312100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257584079/1250000000 : ℝ)*X 0 0+(1372208461/2500000000 : ℝ)*X 0 1+(1294109859/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684125337/5000000000 : ℝ)*X 1 0+(-2222385071/10000000000 : ℝ)*X 1 1+(5176439077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684125081/5000000000 : ℝ)*X 2 0+(5176439549/10000000000 : ℝ)*X 2 1+(-222238513/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327948389/10000000000 : ℝ)*X 0 0+(4016121417/10000000000 : ℝ)*X 0 1+(4662592879/10000000000 : ℝ)*X 0 2+(4327948389/10000000000 : ℝ)*X 1 0+(4016121417/10000000000 : ℝ)*X 1 1+(4662592879/10000000000 : ℝ)*X 1 2+(4327948389/10000000000 : ℝ)*X 2 0+(4016121417/10000000000 : ℝ)*X 2 1+(4662592879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2060748453/10000000000 : ℝ)*X 0 0+(2589235083/5000000000 : ℝ)*X 0 1+(5486784401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165250527/312500000 : ℝ)*X 1 0+(-239004907/1250000000 : ℝ)*X 1 1+(2743392247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057603397/2000000000 : ℝ)*X 2 0+(685848051/1250000000 : ℝ)*X 2 1+(-191203921/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164052053/5000000000 : ℝ)*X 0 0+(4658388489/10000000000 : ℝ)*X 0 1+(2010183867/5000000000 : ℝ)*X 0 2+(2164052053/5000000000 : ℝ)*X 1 0+(4658388489/10000000000 : ℝ)*X 1 1+(2010183867/5000000000 : ℝ)*X 1 2+(2164052053/5000000000 : ℝ)*X 2 0+(4658388489/10000000000 : ℝ)*X 2 1+(2010183867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11361084606339501742546584447/1640125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1182450723/50000000000000 : ℝ)*(base19) + (391404563/25000000000000 : ℝ)*(base23) + (265178439/100000000000000 : ℝ)*(lower2) + (703493883/100000000000000 : ℝ)*(upper3) + (23563107/12500000000000 : ℝ)*(upper5) + (1187000991033101/50000000000000 : ℝ)*(major0) + (1187000991033101/50000000000000 : ℝ)*(major1) + (1187000991033101/50000000000000 : ℝ)*(major2) + (2500860045207/78125000000 : ℝ)*(sp0) + (3201108878530531/100000000000000 : ℝ)*(sp1) + (128044387112549/4000000000000 : ℝ)*(sp2) + (773436500136193/50000000000000 : ℝ)*(sp3) + (10385567017/100000000000000 : ℝ)*(sp4) + (779581171/4000000000000 : ℝ)*(sp7) + (1546892489801661/100000000000000 : ℝ)*(f.failure) + (3201111243431977/100000000000000 : ℝ)*(f.sum) + (405497582916223/65605000000000000000000000000 : ℝ)*base65 + (11656280695304078149/6560500000000000000000000000000000 : ℝ)*base68 + (38902284575864921851/6560500000000000000000000000000000 : ℝ)*base69 + (95522675384406421851/6560500000000000000000000000000000 : ℝ)*base71 + (209725059079921/32802500000000000000000000000 : ℝ)*base74 + (19983800182509921851/6560500000000000000000000000000000 : ℝ)*base75 + (96396891164268421851/6560500000000000000000000000000000 : ℝ)*base77 + (31727066112934421851/6560500000000000000000000000000000 : ℝ)*base79 + (2875584101277/4100312500000000000000000000 : ℝ)*base82 + (1078249/100000000000000000000 : ℝ)*base90 + (1078249/100000000000000000000 : ℝ)*base92 + (1078249/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23907186566815647939386895951/3280250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1424753727/100000000000000 : ℝ)*(base19) + (861267913/50000000000000 : ℝ)*(base23) + (207803873/100000000000000 : ℝ)*(upper3) + (84484687/100000000000000 : ℝ)*(lower4) + (97947221/100000000000000 : ℝ)*(upper5) + (1202697383994067/50000000000000 : ℝ)*(major0) + (1202697383994067/50000000000000 : ℝ)*(major1) + (1202697383994067/50000000000000 : ℝ)*(major2) + (7497809991/50000000000000 : ℝ)*(sp1) + (9600326689/50000000000000 : ℝ)*(sp2) + (3243441359159541/100000000000000 : ℝ)*(sp4) + (405428117348229/12500000000000 : ℝ)*(sp5) + (3243420435970337/100000000000000 : ℝ)*(sp6) + (1567347933876027/100000000000000 : ℝ)*(sp7) + (1567347933876027/100000000000000 : ℝ)*(f.failure) + (3243441359159541/100000000000000 : ℝ)*(f.sum) + (99622949396401/65605000000000000000000000000 : ℝ)*base65 + (44890692902287334683/6560500000000000000000000000000000 : ℝ)*base68 + (46583470835162334683/6560500000000000000000000000000000 : ℝ)*base70 + (1283427585788165317/6560500000000000000000000000000000 : ℝ)*base71 + (144783013207099/65605000000000000000000000000 : ℝ)*base74 + (375238794637165317/6560500000000000000000000000000000 : ℝ)*base75 + (6896744825844334683/6560500000000000000000000000000000 : ℝ)*base78 + (18773330672113334683/6560500000000000000000000000000000 : ℝ)*base80 + (106223559612797/32802500000000000000000000000 : ℝ)*base82 + (247343/100000000000000000000 : ℝ)*base90 + (247343/100000000000000000000 : ℝ)*base92 + (247343/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3293/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1310_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1310_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1310_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1310_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

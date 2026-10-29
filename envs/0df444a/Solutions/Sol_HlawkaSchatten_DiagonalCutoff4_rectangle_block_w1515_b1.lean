-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:23.284432+00:00
-- url     : https://prove2.me/submissions/aa2df105-47bf-4995-a4f3-fe4005e9a46c

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
theorem support_rectangle_w1515_s3_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-931557041/5000000000 : ℝ)*x 0 + (2718003463/5000000000 : ℝ)*x 1 + (2607470289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931557041/5000000000 : ℝ)^4527 ≤ (11400271929163/100000000000000 : ℝ)^3503 := by
    have hnat : (931557041 : ℕ)^4527*100000000000000^3503 ≤ 11400271929163^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931557041 5000000000 11400271929163 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718003463/5000000000 : ℝ)^4527 ≤ (4548799783439/10000000000000 : ℝ)^3503 := by
    have hnat : (2718003463 : ℕ)^4527*10000000000000^3503 ≤ 4548799783439^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718003463 5000000000 4548799783439 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607470289/5000000000 : ℝ)^4527 ≤ (5388966277991/12500000000000 : ℝ)^3503 := by
    have hnat : (2607470289 : ℕ)^4527*12500000000000^3503 ≤ 5388966277991^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607470289 5000000000 5388966277991 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931557041/5000000000 : ℝ), (2718003463/5000000000 : ℝ), (2607470289/5000000000 : ℝ)] ![(11400271929163/100000000000000 : ℝ), (4548799783439/10000000000000 : ℝ), (5388966277991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931557041/5000000000 : ℝ)|^4527 ≤ (11400271929163/100000000000000 : ℝ)^3503
        have hw : |(-931557041/5000000000 : ℝ)|=(931557041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718003463/5000000000 : ℝ)|^4527 ≤ (4548799783439/10000000000000 : ℝ)^3503
        have hw : |(2718003463/5000000000 : ℝ)|=(2718003463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607470289/5000000000 : ℝ)|^4527 ≤ (5388966277991/12500000000000 : ℝ)^3503
        have hw : |(2607470289/5000000000 : ℝ)|=(2607470289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352251659/10000000000 : ℝ)*x 0 + (-395280241/2000000000 : ℝ)*x 1 + (2607470363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352251659/10000000000 : ℝ)^4527 ≤ (44584313821907/100000000000000 : ℝ)^3503 := by
    have hnat : (5352251659 : ℕ)^4527*100000000000000^3503 ≤ 44584313821907^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352251659 10000000000 44584313821907 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395280241/2000000000 : ℝ)^4527 ≤ (2460790869751/20000000000000 : ℝ)^3503 := by
    have hnat : (395280241 : ℕ)^4527*20000000000000^3503 ≤ 2460790869751^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395280241 2000000000 2460790869751 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607470363/5000000000 : ℝ)^4527 ≤ (43111731805097/100000000000000 : ℝ)^3503 := by
    have hnat : (2607470363 : ℕ)^4527*100000000000000^3503 ≤ 43111731805097^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607470363 5000000000 43111731805097 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352251659/10000000000 : ℝ), (-395280241/2000000000 : ℝ), (2607470363/5000000000 : ℝ)] ![(44584313821907/100000000000000 : ℝ), (2460790869751/20000000000000 : ℝ), (43111731805097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352251659/10000000000 : ℝ)|^4527 ≤ (44584313821907/100000000000000 : ℝ)^3503
        have hw : |(5352251659/10000000000 : ℝ)|=(5352251659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395280241/2000000000 : ℝ)|^4527 ≤ (2460790869751/20000000000000 : ℝ)^3503
        have hw : |(-395280241/2000000000 : ℝ)|=(395280241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607470363/5000000000 : ℝ)|^4527 ≤ (43111731805097/100000000000000 : ℝ)^3503
        have hw : |(2607470363/5000000000 : ℝ)|=(2607470363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352251823/10000000000 : ℝ)*x 0 + (521494063/1000000000 : ℝ)*x 1 + (-988200557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352251823/10000000000 : ℝ)^4527 ≤ (22292157793687/50000000000000 : ℝ)^3503 := by
    have hnat : (5352251823 : ℕ)^4527*50000000000000^3503 ≤ 22292157793687^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352251823 10000000000 22292157793687 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521494063/1000000000 : ℝ)^4527 ≤ (21555865389737/50000000000000 : ℝ)^3503 := by
    have hnat : (521494063 : ℕ)^4527*50000000000000^3503 ≤ 21555865389737^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521494063 1000000000 21555865389737 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988200557/5000000000 : ℝ)^4527 ≤ (12303953616637/100000000000000 : ℝ)^3503 := by
    have hnat : (988200557 : ℕ)^4527*100000000000000^3503 ≤ 12303953616637^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988200557 5000000000 12303953616637 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352251823/10000000000 : ℝ), (521494063/1000000000 : ℝ), (-988200557/5000000000 : ℝ)] ![(22292157793687/50000000000000 : ℝ), (21555865389737/50000000000000 : ℝ), (12303953616637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352251823/10000000000 : ℝ)|^4527 ≤ (22292157793687/50000000000000 : ℝ)^3503
        have hw : |(5352251823/10000000000 : ℝ)|=(5352251823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521494063/1000000000 : ℝ)|^4527 ≤ (21555865389737/50000000000000 : ℝ)^3503
        have hw : |(521494063/1000000000 : ℝ)|=(521494063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988200557/5000000000 : ℝ)|^4527 ≤ (12303953616637/100000000000000 : ℝ)^3503
        have hw : |(-988200557/5000000000 : ℝ)|=(988200557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268076509/10000000000 : ℝ)*x 0 + (4023161221/10000000000 : ℝ)*x 1 + (4525508289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268076509/10000000000 : ℝ)^4527 ≤ (2079799013597/6250000000000 : ℝ)^3503 := by
    have hnat : (4268076509 : ℕ)^4527*6250000000000^3503 ≤ 2079799013597^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268076509 10000000000 2079799013597 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023161221/10000000000 : ℝ)^4527 ≤ (30830051228203/100000000000000 : ℝ)^3503 := by
    have hnat : (4023161221 : ℕ)^4527*100000000000000^3503 ≤ 30830051228203^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023161221 10000000000 30830051228203 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525508289/10000000000 : ℝ)^4527 ≤ (897329113691/2500000000000 : ℝ)^3503 := by
    have hnat : (4525508289 : ℕ)^4527*2500000000000^3503 ≤ 897329113691^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525508289 10000000000 897329113691 2500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268076509/10000000000 : ℝ), (4023161221/10000000000 : ℝ), (4525508289/10000000000 : ℝ)] ![(2079799013597/6250000000000 : ℝ), (30830051228203/100000000000000 : ℝ), (897329113691/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268076509/10000000000 : ℝ)|^4527 ≤ (2079799013597/6250000000000 : ℝ)^3503
        have hw : |(4268076509/10000000000 : ℝ)|=(4268076509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023161221/10000000000 : ℝ)|^4527 ≤ (30830051228203/100000000000000 : ℝ)^3503
        have hw : |(4023161221/10000000000 : ℝ)|=(4023161221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525508289/10000000000 : ℝ)|^4527 ≤ (897329113691/2500000000000 : ℝ)^3503
        have hw : |(4525508289/10000000000 : ℝ)|=(4525508289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863144963/10000000000 : ℝ)*x 0 + (260805547/500000000 : ℝ)*x 1 + (217393121/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863144963/10000000000 : ℝ)^4527 ≤ (356266128911/3125000000000 : ℝ)^3503 := by
    have hnat : (1863144963 : ℕ)^4527*3125000000000^3503 ≤ 356266128911^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863144963 10000000000 356266128911 3125000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260805547/500000000 : ℝ)^4527 ≤ (43124234279729/100000000000000 : ℝ)^3503 := by
    have hnat : (260805547 : ℕ)^4527*100000000000000^3503 ≤ 43124234279729^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260805547 500000000 43124234279729 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217393121/400000000 : ℝ)^4527 ≤ (45475249579257/100000000000000 : ℝ)^3503 := by
    have hnat : (217393121 : ℕ)^4527*100000000000000^3503 ≤ 45475249579257^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217393121 400000000 45475249579257 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863144963/10000000000 : ℝ), (260805547/500000000 : ℝ), (217393121/400000000 : ℝ)] ![(356266128911/3125000000000 : ℝ), (43124234279729/100000000000000 : ℝ), (45475249579257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863144963/10000000000 : ℝ)|^4527 ≤ (356266128911/3125000000000 : ℝ)^3503
        have hw : |(-1863144963/10000000000 : ℝ)|=(1863144963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260805547/500000000 : ℝ)|^4527 ≤ (43124234279729/100000000000000 : ℝ)^3503
        have hw : |(260805547/500000000 : ℝ)|=(260805547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217393121/400000000 : ℝ)|^4527 ≤ (45475249579257/100000000000000 : ℝ)^3503
        have hw : |(217393121/400000000 : ℝ)|=(217393121/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323547891/2500000000 : ℝ)*x 0 + (-1756513427/10000000000 : ℝ)*x 1 + (5434828197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323547891/2500000000 : ℝ)^4527 ≤ (21980143857139/50000000000000 : ℝ)^3503 := by
    have hnat : (1323547891 : ℕ)^4527*50000000000000^3503 ≤ 21980143857139^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323547891 2500000000 21980143857139 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1756513427/10000000000 : ℝ)^4527 ≤ (10564460831913/100000000000000 : ℝ)^3503 := by
    have hnat : (1756513427 : ℕ)^4527*100000000000000^3503 ≤ 10564460831913^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756513427 10000000000 10564460831913 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434828197/10000000000 : ℝ)^4527 ≤ (909505028783/2000000000000 : ℝ)^3503 := by
    have hnat : (5434828197 : ℕ)^4527*2000000000000^3503 ≤ 909505028783^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434828197 10000000000 909505028783 2000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323547891/2500000000 : ℝ), (-1756513427/10000000000 : ℝ), (5434828197/10000000000 : ℝ)] ![(21980143857139/50000000000000 : ℝ), (10564460831913/100000000000000 : ℝ), (909505028783/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323547891/2500000000 : ℝ)|^4527 ≤ (21980143857139/50000000000000 : ℝ)^3503
        have hw : |(1323547891/2500000000 : ℝ)|=(1323547891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1756513427/10000000000 : ℝ)|^4527 ≤ (10564460831913/100000000000000 : ℝ)^3503
        have hw : |(-1756513427/10000000000 : ℝ)|=(1756513427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434828197/10000000000 : ℝ)|^4527 ≤ (909505028783/2000000000000 : ℝ)^3503
        have hw : |(5434828197/10000000000 : ℝ)|=(5434828197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647095859/5000000000 : ℝ)*x 0 + (5434827939/10000000000 : ℝ)*x 1 + (-878256787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647095859/5000000000 : ℝ)^4527 ≤ (21980144683409/50000000000000 : ℝ)^3503 := by
    have hnat : (2647095859 : ℕ)^4527*50000000000000^3503 ≤ 21980144683409^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647095859 5000000000 21980144683409 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434827939/10000000000 : ℝ)^4527 ≤ (4547524864931/10000000000000 : ℝ)^3503 := by
    have hnat : (5434827939 : ℕ)^4527*10000000000000^3503 ≤ 4547524864931^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434827939 10000000000 4547524864931 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878256787/5000000000 : ℝ)^4527 ≤ (2112892394897/20000000000000 : ℝ)^3503 := by
    have hnat : (878256787 : ℕ)^4527*20000000000000^3503 ≤ 2112892394897^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878256787 5000000000 2112892394897 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647095859/5000000000 : ℝ), (5434827939/10000000000 : ℝ), (-878256787/5000000000 : ℝ)] ![(21980144683409/50000000000000 : ℝ), (4547524864931/10000000000000 : ℝ), (2112892394897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647095859/5000000000 : ℝ)|^4527 ≤ (21980144683409/50000000000000 : ℝ)^3503
        have hw : |(2647095859/5000000000 : ℝ)|=(2647095859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434827939/10000000000 : ℝ)|^4527 ≤ (4547524864931/10000000000000 : ℝ)^3503
        have hw : |(5434827939/10000000000 : ℝ)|=(5434827939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-878256787/5000000000 : ℝ)|^4527 ≤ (2112892394897/20000000000000 : ℝ)^3503
        have hw : |(-878256787/5000000000 : ℝ)|=(878256787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s3_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268147741/10000000000 : ℝ)*x 0 + (565356141/1250000000 : ℝ)*x 1 + (251615029/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268147741/10000000000 : ℝ)^4527 ≤ (8319375484661/25000000000000 : ℝ)^3503 := by
    have hnat : (4268147741 : ℕ)^4527*25000000000000^3503 ≤ 8319375484661^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268147741 10000000000 8319375484661 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565356141/1250000000 : ℝ)^4527 ≤ (35865911061081/100000000000000 : ℝ)^3503 := by
    have hnat : (565356141 : ℕ)^4527*100000000000000^3503 ≤ 35865911061081^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565356141 1250000000 35865911061081 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251615029/625000000 : ℝ)^4527 ≤ (30856586988511/100000000000000 : ℝ)^3503 := by
    have hnat : (251615029 : ℕ)^4527*100000000000000^3503 ≤ 30856586988511^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251615029 625000000 30856586988511 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268147741/10000000000 : ℝ), (565356141/1250000000 : ℝ), (251615029/625000000 : ℝ)] ![(8319375484661/25000000000000 : ℝ), (35865911061081/100000000000000 : ℝ), (30856586988511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268147741/10000000000 : ℝ)|^4527 ≤ (8319375484661/25000000000000 : ℝ)^3503
        have hw : |(4268147741/10000000000 : ℝ)|=(4268147741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565356141/1250000000 : ℝ)|^4527 ≤ (35865911061081/100000000000000 : ℝ)^3503
        have hw : |(565356141/1250000000 : ℝ)|=(565356141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251615029/625000000 : ℝ)|^4527 ≤ (30856586988511/100000000000000 : ℝ)^3503
        have hw : |(251615029/625000000 : ℝ)|=(251615029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10867/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3887/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3197/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2093/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3197/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2093/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3197/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2093/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3197/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2093/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3197/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2093/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3197/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2093/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2093/20000 : ℝ) ^ (4525/1024 : ℝ) ≤ (4658877348657587/100000000000000000000 : ℝ) := by
    have hpowers : (2093/20000 : ℝ)^4525 ≤ (4658877348657587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2093 : ℕ)^4525*100000000000000000000^1024 ≤ 4658877348657587^1024*20000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2093 20000 4658877348657587 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2093/20000 : ℝ)) (X := (4658877348657587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3197/20000 : ℝ) ^ (4525/1024 : ℝ) ≤ (30286543095433351/100000000000000000000 : ℝ) := by
    have hpowers : (3197/20000 : ℝ)^4525 ≤ (30286543095433351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3197 : ℕ)^4525*100000000000000000000^1024 ≤ 30286543095433351^1024*20000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3197 20000 30286543095433351 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3197/20000 : ℝ)) (X := (30286543095433351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004658877348657587/50000000000000000000 : ℝ) ≤ (1250026356455531/1250000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50004658877348657587/50000000000000000000 : ℝ)^1024 ≤ (1250026356455531/1250000000000000 : ℝ)^4525 := by
      have hnat : (50004658877348657587 : ℕ)^1024*1250000000000000^4525 ≤ 1250026356455531^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004658877348657587 50000000000000000000 1250026356455531 1250000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026356455531/1250000000000000 : ℝ)) (X := (50004658877348657587/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017472710222045469/50000000000000000000 : ℝ) ≤ (5000395351093923/5000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50017472710222045469/50000000000000000000 : ℝ)^1024 ≤ (5000395351093923/5000000000000000 : ℝ)^4525 := by
      have hnat : (50017472710222045469 : ℕ)^1024*5000000000000000^4525 ≤ 5000395351093923^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017472710222045469 50000000000000000000 5000395351093923 5000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000395351093923/5000000000000000 : ℝ)) (X := (50017472710222045469/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030286543095433351/50000000000000000000 : ℝ) ≤ (2500342638182861/2500000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50030286543095433351/50000000000000000000 : ℝ)^1024 ≤ (2500342638182861/2500000000000000 : ℝ)^4525 := by
      have hnat : (50030286543095433351 : ℕ)^1024*2500000000000000^4525 ≤ 2500342638182861^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030286543095433351 50000000000000000000 2500342638182861 2500000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500342638182861/2500000000000000 : ℝ)) (X := (50030286543095433351/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4658877348657587/100000000000000000000 : ℝ) ≤ ((119976147019997267/120000000000000000 : ℝ)+2*(289925271799/276000000000000 : ℝ)*(2093/20000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (119976147019997267/120000000000000000 : ℝ)+2*(289925271799/276000000000000 : ℝ)*(2093/20000 : ℝ)=(1250026356455531/1250000000000000 : ℝ) by norm_num, show 1+2*(4658877348657587/100000000000000000000 : ℝ)=(50004658877348657587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30286543095433351/100000000000000000000 : ℝ)+(4658877348657587/100000000000000000000 : ℝ) ≤ ((119976147019997267/120000000000000000 : ℝ)+(289925271799/276000000000000 : ℝ)*((3197/20000 : ℝ)+(2093/20000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (119976147019997267/120000000000000000 : ℝ)+(289925271799/276000000000000 : ℝ)*((3197/20000 : ℝ)+(2093/20000 : ℝ))=(5000395351093923/5000000000000000 : ℝ) by norm_num, show 1+(30286543095433351/100000000000000000000 : ℝ)+(4658877348657587/100000000000000000000 : ℝ)=(50017472710222045469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30286543095433351/100000000000000000000 : ℝ) ≤ ((119976147019997267/120000000000000000 : ℝ)+2*(289925271799/276000000000000 : ℝ)*(3197/20000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (119976147019997267/120000000000000000 : ℝ)+2*(289925271799/276000000000000 : ℝ)*(3197/20000 : ℝ)=(2500342638182861/2500000000000000 : ℝ) by norm_num, show 1+2*(30286543095433351/100000000000000000000 : ℝ)=(50030286543095433351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119976147019997267/120000000000000000 : ℝ)*(X 1 0+X 2 0)+(289925271799/276000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3197/20000 : ℝ)) (c := (119976147019997267/120000000000000000 : ℝ)) (alpha := (289925271799/276000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119976147019997267/120000000000000000 : ℝ)*(X 0 1+X 2 1)+(289925271799/276000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3197/20000 : ℝ)) (c := (119976147019997267/120000000000000000 : ℝ)) (alpha := (289925271799/276000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119976147019997267/120000000000000000 : ℝ)*(X 0 2+X 1 2)+(289925271799/276000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2093/20000 : ℝ)) (hi := (3197/20000 : ℝ)) (c := (119976147019997267/120000000000000000 : ℝ)) (alpha := (289925271799/276000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-931557041/5000000000 : ℝ)*X 0 0+(2718003463/5000000000 : ℝ)*X 0 1+(2607470289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352251659/10000000000 : ℝ)*X 1 0+(-395280241/2000000000 : ℝ)*X 1 1+(2607470363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352251823/10000000000 : ℝ)*X 2 0+(521494063/1000000000 : ℝ)*X 2 1+(-988200557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268076509/10000000000 : ℝ)*X 0 0+(4023161221/10000000000 : ℝ)*X 0 1+(4525508289/10000000000 : ℝ)*X 0 2+(4268076509/10000000000 : ℝ)*X 1 0+(4023161221/10000000000 : ℝ)*X 1 1+(4525508289/10000000000 : ℝ)*X 1 2+(4268076509/10000000000 : ℝ)*X 2 0+(4023161221/10000000000 : ℝ)*X 2 1+(4525508289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1863144963/10000000000 : ℝ)*X 0 0+(260805547/500000000 : ℝ)*X 0 1+(217393121/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323547891/2500000000 : ℝ)*X 1 0+(-1756513427/10000000000 : ℝ)*X 1 1+(5434828197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647095859/5000000000 : ℝ)*X 2 0+(5434827939/10000000000 : ℝ)*X 2 1+(-878256787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268147741/10000000000 : ℝ)*X 0 0+(565356141/1250000000 : ℝ)*X 0 1+(251615029/625000000 : ℝ)*X 0 2+(4268147741/10000000000 : ℝ)*X 1 0+(565356141/1250000000 : ℝ)*X 1 1+(251615029/625000000 : ℝ)*X 1 2+(4268147741/10000000000 : ℝ)*X 2 0+(565356141/1250000000 : ℝ)*X 2 1+(251615029/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26077568499765641313322129/23000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155369809/25000000000000 : ℝ)*(base19) + (15743453/3125000000000 : ℝ)*(base23) + (17283409/10000000000000 : ℝ)*(upper3) + (17147013/12500000000000 : ℝ)*(upper4) + (50763323/50000000000000 : ℝ)*(upper5) + (3257104608318469/100000000000000 : ℝ)*(major0) + (3257104608318469/100000000000000 : ℝ)*(major1) + (3257104608318469/100000000000000 : ℝ)*(major2) + (4523536166765811/100000000000000 : ℝ)*(sp0) + (2261772127049923/50000000000000 : ℝ)*(sp1) + (2261772185894293/50000000000000 : ℝ)*(sp2) + (1990659031634057/100000000000000 : ℝ)*(sp3) + (8708813271/100000000000000 : ℝ)*(sp4) + (5271630217/100000000000000 : ℝ)*(sp7) + (995332151632137/50000000000000 : ℝ)*(f.failure) + (2261772437789541/50000000000000 : ℝ)*(f.sum) + (22005755667269/13800000000000000000000000000 : ℝ)*base66 + (378769547317332871/276000000000000000000000000000000 : ℝ)*base68 + (145025587537332871/276000000000000000000000000000000 : ℝ)*base70 + (1050444589417332871/276000000000000000000000000000000 : ℝ)*base72 + (82087815342331/13800000000000000000000000000 : ℝ)*base73 + (2034529774525332871/276000000000000000000000000000000 : ℝ)*base76 + (1465585827718667129/276000000000000000000000000000000 : ℝ)*base77 + (2036248204621332871/276000000000000000000000000000000 : ℝ)*base80 + (11911221570869/13800000000000000000000000000 : ℝ)*base82 + (10471877/5000000000000000000000 : ℝ)*base90 + (10471877/5000000000000000000000 : ℝ)*base92 + (10471877/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3301430616332900794521/920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (800224379/100000000000000 : ℝ)*(base19) + (139772913/12500000000000 : ℝ)*(base23) + (124356053/100000000000000 : ℝ)*(upper3) + (44756657/50000000000000 : ℝ)*(lower4) + (702923/1250000000000 : ℝ)*(upper5) + (658415160997147/20000000000000 : ℝ)*(major0) + (658415160997147/20000000000000 : ℝ)*(major1) + (658415160997147/20000000000000 : ℝ)*(major2) + (3633682229/25000000000000 : ℝ)*(sp1) + (7991586829/50000000000000 : ℝ)*(sp2) + (2286056814761521/50000000000000 : ℝ)*(sp4) + (4572098294569747/100000000000000 : ℝ)*(sp5) + (14287801650519/312500000000 : ℝ)*(sp6) + (1006018930415687/50000000000000 : ℝ)*(sp7) + (1006018930415687/50000000000000 : ℝ)*(f.failure) + (2286056814761521/50000000000000 : ℝ)*(f.sum) + (9418041778573/2760000000000000000000000000 : ℝ)*base65 + (133771056444466727/55200000000000000000000000000000 : ℝ)*base67 + (70453993927666727/55200000000000000000000000000000 : ℝ)*base69 + (366461647927666727/55200000000000000000000000000000 : ℝ)*base71 + (3894132417973/2760000000000000000000000000 : ℝ)*base73 + (59383975372333273/55200000000000000000000000000000 : ℝ)*base76 + (45734306886733273/55200000000000000000000000000000 : ℝ)*base78 + (479376974291533273/55200000000000000000000000000000 : ℝ)*base80 + (1602814970413/2760000000000000000000000000 : ℝ)*base81 + (2523573/5000000000000000000000 : ℝ)*base89 + (2523573/5000000000000000000000 : ℝ)*base91 + (2523573/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1515_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3887/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_s4_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372707407/2000000000 : ℝ)*x 0 + (543322041/1000000000 : ℝ)*x 1 + (326090479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372707407/2000000000 : ℝ)^4527 ≤ (570180829713/5000000000000 : ℝ)^3503 := by
    have hnat : (372707407 : ℕ)^4527*5000000000000^3503 ≤ 570180829713^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372707407 2000000000 570180829713 5000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543322041/1000000000 : ℝ)^4527 ≤ (2841116665747/6250000000000 : ℝ)^3503 := by
    have hnat : (543322041 : ℕ)^4527*6250000000000^3503 ≤ 2841116665747^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543322041 1000000000 2841116665747 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326090479/625000000 : ℝ)^4527 ≤ (43138516737399/100000000000000 : ℝ)^3503 := by
    have hnat : (326090479 : ℕ)^4527*100000000000000^3503 ≤ 43138516737399^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326090479 625000000 43138516737399 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372707407/2000000000 : ℝ), (543322041/1000000000 : ℝ), (326090479/625000000 : ℝ)] ![(570180829713/5000000000000 : ℝ), (2841116665747/6250000000000 : ℝ), (43138516737399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372707407/2000000000 : ℝ)|^4527 ≤ (570180829713/5000000000000 : ℝ)^3503
        have hw : |(-372707407/2000000000 : ℝ)|=(372707407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543322041/1000000000 : ℝ)|^4527 ≤ (2841116665747/6250000000000 : ℝ)^3503
        have hw : |(543322041/1000000000 : ℝ)|=(543322041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326090479/625000000 : ℝ)|^4527 ≤ (43138516737399/100000000000000 : ℝ)^3503
        have hw : |(326090479/625000000 : ℝ)|=(326090479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675761307/5000000000 : ℝ)*x 0 + (-1974047757/10000000000 : ℝ)*x 1 + (1043489419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675761307/5000000000 : ℝ)^4527 ≤ (1114411644367/2500000000000 : ℝ)^3503 := by
    have hnat : (2675761307 : ℕ)^4527*2500000000000^3503 ≤ 1114411644367^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675761307 5000000000 1114411644367 2500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974047757/10000000000 : ℝ)^4527 ≤ (6142511774733/50000000000000 : ℝ)^3503 := by
    have hnat : (1974047757 : ℕ)^4527*50000000000000^3503 ≤ 6142511774733^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974047757 10000000000 6142511774733 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043489419/2000000000 : ℝ)^4527 ≤ (43138510657593/100000000000000 : ℝ)^3503 := by
    have hnat : (1043489419 : ℕ)^4527*100000000000000^3503 ≤ 43138510657593^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043489419 2000000000 43138510657593 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675761307/5000000000 : ℝ), (-1974047757/10000000000 : ℝ), (1043489419/2000000000 : ℝ)] ![(1114411644367/2500000000000 : ℝ), (6142511774733/50000000000000 : ℝ), (43138510657593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675761307/5000000000 : ℝ)|^4527 ≤ (1114411644367/2500000000000 : ℝ)^3503
        have hw : |(2675761307/5000000000 : ℝ)|=(2675761307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974047757/10000000000 : ℝ)|^4527 ≤ (6142511774733/50000000000000 : ℝ)^3503
        have hw : |(-1974047757/10000000000 : ℝ)|=(1974047757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043489419/2000000000 : ℝ)|^4527 ≤ (43138510657593/100000000000000 : ℝ)^3503
        have hw : |(1043489419/2000000000 : ℝ)|=(1043489419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351522287/10000000000 : ℝ)*x 0 + (2608723809/5000000000 : ℝ)*x 1 + (-789619/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351522287/10000000000 : ℝ)^4527 ≤ (891529245093/2000000000000 : ℝ)^3503 := by
    have hnat : (5351522287 : ℕ)^4527*2000000000000^3503 ≤ 891529245093^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351522287 10000000000 891529245093 2000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608723809/5000000000 : ℝ)^4527 ≤ (21569258122943/50000000000000 : ℝ)^3503 := by
    have hnat : (2608723809 : ℕ)^4527*50000000000000^3503 ≤ 21569258122943^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608723809 5000000000 21569258122943 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789619/4000000 : ℝ)^4527 ≤ (2457004296511/20000000000000 : ℝ)^3503 := by
    have hnat : (789619 : ℕ)^4527*20000000000000^3503 ≤ 2457004296511^3503*4000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789619 4000000 2457004296511 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351522287/10000000000 : ℝ), (2608723809/5000000000 : ℝ), (-789619/4000000 : ℝ)] ![(891529245093/2000000000000 : ℝ), (21569258122943/50000000000000 : ℝ), (2457004296511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351522287/10000000000 : ℝ)|^4527 ≤ (891529245093/2000000000000 : ℝ)^3503
        have hw : |(5351522287/10000000000 : ℝ)|=(5351522287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608723809/5000000000 : ℝ)|^4527 ≤ (21569258122943/50000000000000 : ℝ)^3503
        have hw : |(2608723809/5000000000 : ℝ)|=(2608723809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-789619/4000000 : ℝ)|^4527 ≤ (2457004296511/20000000000000 : ℝ)^3503
        have hw : |(-789619/4000000 : ℝ)|=(789619/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268341307/10000000000 : ℝ)*x 0 + (16116581/40000000 : ℝ)*x 1 + (2259731919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268341307/10000000000 : ℝ)^4527 ≤ (33279452293271/100000000000000 : ℝ)^3503 := by
    have hnat : (4268341307 : ℕ)^4527*100000000000000^3503 ≤ 33279452293271^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268341307 10000000000 33279452293271 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16116581/40000000 : ℝ)^4527 ≤ (15444662681817/50000000000000 : ℝ)^3503 := by
    have hnat : (16116581 : ℕ)^4527*50000000000000^3503 ≤ 15444662681817^3503*40000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16116581 40000000 15444662681817 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259731919/5000000000 : ℝ)^4527 ≤ (35831222324741/100000000000000 : ℝ)^3503 := by
    have hnat : (2259731919 : ℕ)^4527*100000000000000^3503 ≤ 35831222324741^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259731919 5000000000 35831222324741 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268341307/10000000000 : ℝ), (16116581/40000000 : ℝ), (2259731919/5000000000 : ℝ)] ![(33279452293271/100000000000000 : ℝ), (15444662681817/50000000000000 : ℝ), (35831222324741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268341307/10000000000 : ℝ)|^4527 ≤ (33279452293271/100000000000000 : ℝ)^3503
        have hw : |(4268341307/10000000000 : ℝ)|=(4268341307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16116581/40000000 : ℝ)|^4527 ≤ (15444662681817/50000000000000 : ℝ)^3503
        have hw : |(16116581/40000000 : ℝ)|=(16116581/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259731919/5000000000 : ℝ)|^4527 ≤ (35831222324741/100000000000000 : ℝ)^3503
        have hw : |(2259731919/5000000000 : ℝ)|=(2259731919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116472867/625000000 : ℝ)*x 0 + (5218562927/10000000000 : ℝ)*x 1 + (5432097121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116472867/625000000 : ℝ)^4527 ≤ (5701922321059/50000000000000 : ℝ)^3503 := by
    have hnat : (116472867 : ℕ)^4527*50000000000000^3503 ≤ 5701922321059^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116472867 625000000 5701922321059 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218562927/10000000000 : ℝ)^4527 ≤ (10787608443863/25000000000000 : ℝ)^3503 := by
    have hnat : (5218562927 : ℕ)^4527*25000000000000^3503 ≤ 10787608443863^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218562927 10000000000 10787608443863 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432097121/10000000000 : ℝ)^4527 ≤ (908914431391/2000000000000 : ℝ)^3503 := by
    have hnat : (5432097121 : ℕ)^4527*2000000000000^3503 ≤ 908914431391^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432097121 10000000000 908914431391 2000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116472867/625000000 : ℝ), (5218562927/10000000000 : ℝ), (5432097121/10000000000 : ℝ)] ![(5701922321059/50000000000000 : ℝ), (10787608443863/25000000000000 : ℝ), (908914431391/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116472867/625000000 : ℝ)|^4527 ≤ (5701922321059/50000000000000 : ℝ)^3503
        have hw : |(-116472867/625000000 : ℝ)|=(116472867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218562927/10000000000 : ℝ)|^4527 ≤ (10787608443863/25000000000000 : ℝ)^3503
        have hw : |(5218562927/10000000000 : ℝ)|=(5218562927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432097121/10000000000 : ℝ)|^4527 ≤ (908914431391/2000000000000 : ℝ)^3503
        have hw : |(5432097121/10000000000 : ℝ)|=(5432097121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294853221/10000000000 : ℝ)*x 0 + (-219924749/1250000000 : ℝ)*x 1 + (5432097463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294853221/10000000000 : ℝ)^4527 ≤ (43967387938701/100000000000000 : ℝ)^3503 := by
    have hnat : (5294853221 : ℕ)^4527*100000000000000^3503 ≤ 43967387938701^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294853221 10000000000 43967387938701 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219924749/1250000000 : ℝ)^4527 ≤ (10586886776227/100000000000000 : ℝ)^3503 := by
    have hnat : (219924749 : ℕ)^4527*100000000000000^3503 ≤ 10586886776227^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219924749 1250000000 10586886776227 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432097463/10000000000 : ℝ)^4527 ≤ (45445725267167/100000000000000 : ℝ)^3503 := by
    have hnat : (5432097463 : ℕ)^4527*100000000000000^3503 ≤ 45445725267167^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432097463 10000000000 45445725267167 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294853221/10000000000 : ℝ), (-219924749/1250000000 : ℝ), (5432097463/10000000000 : ℝ)] ![(43967387938701/100000000000000 : ℝ), (10586886776227/100000000000000 : ℝ), (45445725267167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294853221/10000000000 : ℝ)|^4527 ≤ (43967387938701/100000000000000 : ℝ)^3503
        have hw : |(5294853221/10000000000 : ℝ)|=(5294853221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219924749/1250000000 : ℝ)|^4527 ≤ (10586886776227/100000000000000 : ℝ)^3503
        have hw : |(-219924749/1250000000 : ℝ)|=(219924749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432097463/10000000000 : ℝ)|^4527 ≤ (45445725267167/100000000000000 : ℝ)^3503
        have hw : |(5432097463/10000000000 : ℝ)|=(5432097463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647426553/5000000000 : ℝ)*x 0 + (2716048821/5000000000 : ℝ)*x 1 + (-1759397903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647426553/5000000000 : ℝ)^4527 ≤ (5495923338077/12500000000000 : ℝ)^3503 := by
    have hnat : (2647426553 : ℕ)^4527*12500000000000^3503 ≤ 5495923338077^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647426553 5000000000 5495923338077 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716048821/5000000000 : ℝ)^4527 ≤ (4544572720247/10000000000000 : ℝ)^3503 := by
    have hnat : (2716048821 : ℕ)^4527*10000000000000^3503 ≤ 4544572720247^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716048821 5000000000 4544572720247 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759397903/10000000000 : ℝ)^4527 ≤ (5293443042067/50000000000000 : ℝ)^3503 := by
    have hnat : (1759397903 : ℕ)^4527*50000000000000^3503 ≤ 5293443042067^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759397903 10000000000 5293443042067 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647426553/5000000000 : ℝ), (2716048821/5000000000 : ℝ), (-1759397903/10000000000 : ℝ)] ![(5495923338077/12500000000000 : ℝ), (4544572720247/10000000000000 : ℝ), (5293443042067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647426553/5000000000 : ℝ)|^4527 ≤ (5495923338077/12500000000000 : ℝ)^3503
        have hw : |(2647426553/5000000000 : ℝ)|=(2647426553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716048821/5000000000 : ℝ)|^4527 ≤ (4544572720247/10000000000000 : ℝ)^3503
        have hw : |(2716048821/5000000000 : ℝ)|=(2716048821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759397903/10000000000 : ℝ)|^4527 ≤ (5293443042067/50000000000000 : ℝ)^3503
        have hw : |(-1759397903/10000000000 : ℝ)|=(1759397903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s4_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533550939/1250000000 : ℝ)*x 0 + (4516930083/10000000000 : ℝ)*x 1 + (161267909/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533550939/1250000000 : ℝ)^4527 ≤ (33280119375179/100000000000000 : ℝ)^3503 := by
    have hnat : (533550939 : ℕ)^4527*100000000000000^3503 ≤ 33280119375179^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533550939 1250000000 33280119375179 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516930083/10000000000 : ℝ)^4527 ≤ (2237829009603/6250000000000 : ℝ)^3503 := by
    have hnat : (4516930083 : ℕ)^4527*6250000000000^3503 ≤ 2237829009603^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516930083 10000000000 2237829009603 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161267909/400000000 : ℝ)^4527 ≤ (6182923290859/20000000000000 : ℝ)^3503 := by
    have hnat : (161267909 : ℕ)^4527*20000000000000^3503 ≤ 6182923290859^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161267909 400000000 6182923290859 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533550939/1250000000 : ℝ), (4516930083/10000000000 : ℝ), (161267909/400000000 : ℝ)] ![(33280119375179/100000000000000 : ℝ), (2237829009603/6250000000000 : ℝ), (6182923290859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533550939/1250000000 : ℝ)|^4527 ≤ (33280119375179/100000000000000 : ℝ)^3503
        have hw : |(533550939/1250000000 : ℝ)|=(533550939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516930083/10000000000 : ℝ)|^4527 ≤ (2237829009603/6250000000000 : ℝ)^3503
        have hw : |(4516930083/10000000000 : ℝ)|=(4516930083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161267909/400000000 : ℝ)|^4527 ≤ (6182923290859/20000000000000 : ℝ)^3503
        have hw : |(161267909/400000000 : ℝ)|=(161267909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3887/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (273/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3887/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3887/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3887/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3887/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3887/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3887/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10867/100000 : ℝ) ^ (4525/1024 : ℝ) ≤ (343954779638137/6250000000000000000 : ℝ) := by
    have hpowers : (10867/100000 : ℝ)^4525 ≤ (343954779638137/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10867 : ℕ)^4525*6250000000000000000^1024 ≤ 343954779638137^1024*100000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10867 100000 343954779638137 6250000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10867/100000 : ℝ)) (X := (343954779638137/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3887/25000 : ℝ) ^ (4525/1024 : ℝ) ≤ (6698753094872331/25000000000000000000 : ℝ) := by
    have hpowers : (3887/25000 : ℝ)^4525 ≤ (6698753094872331/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3887 : ℕ)^4525*25000000000000000000^1024 ≤ 6698753094872331^1024*25000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3887 25000 6698753094872331 25000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3887/25000 : ℝ)) (X := (6698753094872331/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125343954779638137/3125000000000000000 : ℝ) ≤ (1000024906586421/1000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (3125343954779638137/3125000000000000000 : ℝ)^1024 ≤ (1000024906586421/1000000000000000 : ℝ)^4525 := by
      have hnat : (3125343954779638137 : ℕ)^1024*1000000000000000^4525 ≤ 1000024906586421^4525*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125343954779638137 3125000000000000000 1000024906586421 1000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000024906586421/1000000000000000 : ℝ)) (X := (3125343954779638137/3125000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008074572213424879/25000000000000000000 : ℝ) ≤ (1250091351702137/1250000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (25008074572213424879/25000000000000000000 : ℝ)^1024 ≤ (1250091351702137/1250000000000000 : ℝ)^4525 := by
      have hnat : (25008074572213424879 : ℕ)^1024*1250000000000000^4525 ≤ 1250091351702137^4525*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008074572213424879 25000000000000000000 1250091351702137 1250000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250091351702137/1250000000000000 : ℝ)) (X := (25008074572213424879/25000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506698753094872331/12500000000000000000 : ℝ) ≤ (5000606280684991/5000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (12506698753094872331/12500000000000000000 : ℝ)^1024 ≤ (5000606280684991/5000000000000000 : ℝ)^4525 := by
      have hnat : (12506698753094872331 : ℕ)^1024*5000000000000000^4525 ≤ 5000606280684991^4525*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506698753094872331 12500000000000000000 5000606280684991 5000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000606280684991/5000000000000000 : ℝ)) (X := (12506698753094872331/12500000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(343954779638137/6250000000000000000 : ℝ) ≤ ((23400347785824571343/23405000000000000000 : ℝ)+2*(240873876443/234050000000000 : ℝ)*(10867/100000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (23400347785824571343/23405000000000000000 : ℝ)+2*(240873876443/234050000000000 : ℝ)*(10867/100000 : ℝ)=(1000024906586421/1000000000000000 : ℝ) by norm_num, show 1+2*(343954779638137/6250000000000000000 : ℝ)=(3125343954779638137/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6698753094872331/25000000000000000000 : ℝ)+(343954779638137/6250000000000000000 : ℝ) ≤ ((23400347785824571343/23405000000000000000 : ℝ)+(240873876443/234050000000000 : ℝ)*((3887/25000 : ℝ)+(10867/100000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (23400347785824571343/23405000000000000000 : ℝ)+(240873876443/234050000000000 : ℝ)*((3887/25000 : ℝ)+(10867/100000 : ℝ))=(1250091351702137/1250000000000000 : ℝ) by norm_num, show 1+(6698753094872331/25000000000000000000 : ℝ)+(343954779638137/6250000000000000000 : ℝ)=(25008074572213424879/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6698753094872331/25000000000000000000 : ℝ) ≤ ((23400347785824571343/23405000000000000000 : ℝ)+2*(240873876443/234050000000000 : ℝ)*(3887/25000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (23400347785824571343/23405000000000000000 : ℝ)+2*(240873876443/234050000000000 : ℝ)*(3887/25000 : ℝ)=(5000606280684991/5000000000000000 : ℝ) by norm_num, show 1+2*(6698753094872331/25000000000000000000 : ℝ)=(12506698753094872331/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23400347785824571343/23405000000000000000 : ℝ)*(X 1 0+X 2 0)+(240873876443/234050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (3887/25000 : ℝ)) (c := (23400347785824571343/23405000000000000000 : ℝ)) (alpha := (240873876443/234050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23400347785824571343/23405000000000000000 : ℝ)*(X 0 1+X 2 1)+(240873876443/234050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (3887/25000 : ℝ)) (c := (23400347785824571343/23405000000000000000 : ℝ)) (alpha := (240873876443/234050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23400347785824571343/23405000000000000000 : ℝ)*(X 0 2+X 1 2)+(240873876443/234050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (3887/25000 : ℝ)) (c := (23400347785824571343/23405000000000000000 : ℝ)) (alpha := (240873876443/234050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-372707407/2000000000 : ℝ)*X 0 0+(543322041/1000000000 : ℝ)*X 0 1+(326090479/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675761307/5000000000 : ℝ)*X 1 0+(-1974047757/10000000000 : ℝ)*X 1 1+(1043489419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351522287/10000000000 : ℝ)*X 2 0+(2608723809/5000000000 : ℝ)*X 2 1+(-789619/4000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268341307/10000000000 : ℝ)*X 0 0+(16116581/40000000 : ℝ)*X 0 1+(2259731919/5000000000 : ℝ)*X 0 2+(4268341307/10000000000 : ℝ)*X 1 0+(16116581/40000000 : ℝ)*X 1 1+(2259731919/5000000000 : ℝ)*X 1 2+(4268341307/10000000000 : ℝ)*X 2 0+(16116581/40000000 : ℝ)*X 2 1+(2259731919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-116472867/625000000 : ℝ)*X 0 0+(5218562927/10000000000 : ℝ)*X 0 1+(5432097121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294853221/10000000000 : ℝ)*X 1 0+(-219924749/1250000000 : ℝ)*X 1 1+(5432097463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647426553/5000000000 : ℝ)*X 2 0+(2716048821/5000000000 : ℝ)*X 2 1+(-1759397903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533550939/1250000000 : ℝ)*X 0 0+(4516930083/10000000000 : ℝ)*X 0 1+(161267909/400000000 : ℝ)*X 0 2+(533550939/1250000000 : ℝ)*X 1 0+(4516930083/10000000000 : ℝ)*X 1 1+(161267909/400000000 : ℝ)*X 1 2+(533550939/1250000000 : ℝ)*X 2 0+(4516930083/10000000000 : ℝ)*X 2 1+(161267909/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2663237681903867721747082851/292562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (849456859/50000000000000 : ℝ)*(base19) + (669654061/50000000000000 : ℝ)*(base23) + (20447027/50000000000000 : ℝ)*(lower2) + (9512177/20000000000000 : ℝ)*(upper3) + (38633453/20000000000000 : ℝ)*(upper5) + (834257800454073/25000000000000 : ℝ)*(major0) + (834257800454073/25000000000000 : ℝ)*(major1) + (834257800454073/25000000000000 : ℝ)*(major2) + (1158631306483223/25000000000000 : ℝ)*(sp0) + (4634546878942873/100000000000000 : ℝ)*(sp1) + (4634547238548469/100000000000000 : ℝ)*(sp2) + (1019751422844047/50000000000000 : ℝ)*(sp3) + (23351923699/100000000000000 : ℝ)*(sp4) + (5338324929/50000000000000 : ℝ)*(sp7) + (2039513522337951/100000000000000 : ℝ)*(f.failure) + (4634548577856591/100000000000000 : ℝ)*(f.sum) + (9804558018141/11702500000000000000000000000 : ℝ)*base65 + (2527462192428544961/585125000000000000000000000000000 : ℝ)*base68 + (7671815823433794961/585125000000000000000000000000000 : ℝ)*base70 + (8443484224514669961/585125000000000000000000000000000 : ℝ)*base72 + (30502518129247/23405000000000000000000000000 : ℝ)*base73 + (10403804861847294961/585125000000000000000000000000000 : ℝ)*base76 + (3826613094222294961/585125000000000000000000000000000 : ℝ)*base78 + (12780469565112169961/585125000000000000000000000000000 : ℝ)*base80 + (9549784458849/11702500000000000000000000000 : ℝ)*base82 + (35572029/10000000000000000000000 : ℝ)*base89 + (35572029/10000000000000000000000 : ℝ)*base91 + (35572029/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39482175542487573440499243/4718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34341923/50000000000000 : ℝ)*(base19) + (78278461/20000000000000 : ℝ)*(base23) + (73442411/100000000000000 : ℝ)*(upper3) + (35106951/20000000000000 : ℝ)*(lower4) + (842994790411473/25000000000000 : ℝ)*(major0) + (842994790411473/25000000000000 : ℝ)*(major1) + (842994790411473/25000000000000 : ℝ)*(major2) + (2750827173/50000000000000 : ℝ)*(sp1) + (7090948837/50000000000000 : ℝ)*(sp2) + (1204652843/50000000000000 : ℝ)*(sp3) + (234154258314121/5000000000000 : ℝ)*(sp4) + (1170769898986057/25000000000000 : ℝ)*(sp5) + (4683070592992441/100000000000000 : ℝ)*(sp6) + (2060870468800889/100000000000000 : ℝ)*(sp7) + (82434915124263/4000000000000 : ℝ)*(f.failure) + (234154258314121/5000000000000 : ℝ)*(f.sum) + (57855299177669/11702500000000000000000000000 : ℝ)*base66 + (2584286665744743239/585125000000000000000000000000000 : ℝ)*base67 + (1045235546111493239/585125000000000000000000000000000 : ℝ)*base69 + (4653130295877131761/585125000000000000000000000000000 : ℝ)*base72 + (56034019294233/23405000000000000000000000000 : ℝ)*base74 + (293229611219743239/585125000000000000000000000000000 : ℝ)*base75 + (475318681533868239/585125000000000000000000000000000 : ℝ)*base77 + (2006697306890493239/585125000000000000000000000000000 : ℝ)*base79 + (63240961002269/11702500000000000000000000000 : ℝ)*base82 + (2187477/400000000000000000000 : ℝ)*base89 + (2187477/400000000000000000000 : ℝ)*base91 + (2187477/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1515_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3887/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_s5_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29118583/156250000 : ℝ)*x 0 + (217315323/400000000 : ℝ)*x 1 + (2608875161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29118583/156250000 : ℝ)^4527 ≤ (11404030010349/100000000000000 : ℝ)^3503 := by
    have hnat : (29118583 : ℕ)^4527*100000000000000^3503 ≤ 11404030010349^3503*156250000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29118583 156250000 11404030010349 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217315323/400000000 : ℝ)^4527 ≤ (5681777410533/12500000000000 : ℝ)^3503 := by
    have hnat : (217315323 : ℕ)^4527*12500000000000^3503 ≤ 5681777410533^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217315323 400000000 5681777410533 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608875161/5000000000 : ℝ)^4527 ≤ (43141750687423/100000000000000 : ℝ)^3503 := by
    have hnat : (2608875161 : ℕ)^4527*100000000000000^3503 ≤ 43141750687423^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608875161 5000000000 43141750687423 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29118583/156250000 : ℝ), (217315323/400000000 : ℝ), (2608875161/5000000000 : ℝ)] ![(11404030010349/100000000000000 : ℝ), (5681777410533/12500000000000 : ℝ), (43141750687423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29118583/156250000 : ℝ)|^4527 ≤ (11404030010349/100000000000000 : ℝ)^3503
        have hw : |(-29118583/156250000 : ℝ)|=(29118583/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217315323/400000000 : ℝ)|^4527 ≤ (5681777410533/12500000000000 : ℝ)^3503
        have hw : |(217315323/400000000 : ℝ)|=(217315323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608875161/5000000000 : ℝ)|^4527 ≤ (43141750687423/100000000000000 : ℝ)^3503
        have hw : |(2608875161/5000000000 : ℝ)|=(2608875161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675716753/5000000000 : ℝ)*x 0 + (-394752813/2000000000 : ℝ)*x 1 + (5217750389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675716753/5000000000 : ℝ)^4527 ≤ (44575506563429/100000000000000 : ℝ)^3503 := by
    have hnat : (2675716753 : ℕ)^4527*100000000000000^3503 ≤ 44575506563429^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675716753 5000000000 44575506563429 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394752813/2000000000 : ℝ)^4527 ≤ (2456548403391/20000000000000 : ℝ)^3503 := by
    have hnat : (394752813 : ℕ)^4527*20000000000000^3503 ≤ 2456548403391^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394752813 2000000000 2456548403391 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217750389/10000000000 : ℝ)^4527 ≤ (8628350280667/20000000000000 : ℝ)^3503 := by
    have hnat : (5217750389 : ℕ)^4527*20000000000000^3503 ≤ 8628350280667^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217750389 10000000000 8628350280667 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675716753/5000000000 : ℝ), (-394752813/2000000000 : ℝ), (5217750389/10000000000 : ℝ)] ![(44575506563429/100000000000000 : ℝ), (2456548403391/20000000000000 : ℝ), (8628350280667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675716753/5000000000 : ℝ)|^4527 ≤ (44575506563429/100000000000000 : ℝ)^3503
        have hw : |(2675716753/5000000000 : ℝ)|=(2675716753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394752813/2000000000 : ℝ)|^4527 ≤ (2456548403391/20000000000000 : ℝ)^3503
        have hw : |(-394752813/2000000000 : ℝ)|=(394752813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217750389/10000000000 : ℝ)|^4527 ≤ (8628350280667/20000000000000 : ℝ)^3503
        have hw : |(5217750389/10000000000 : ℝ)|=(5217750389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337858377/2500000000 : ℝ)*x 0 + (5217750389/10000000000 : ℝ)*x 1 + (-1973764063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337858377/2500000000 : ℝ)^4527 ≤ (22287753292479/50000000000000 : ℝ)^3503 := by
    have hnat : (1337858377 : ℕ)^4527*50000000000000^3503 ≤ 22287753292479^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337858377 2500000000 22287753292479 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217750389/10000000000 : ℝ)^4527 ≤ (8628350280667/20000000000000 : ℝ)^3503 := by
    have hnat : (5217750389 : ℕ)^4527*20000000000000^3503 ≤ 8628350280667^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217750389 10000000000 8628350280667 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973764063/10000000000 : ℝ)^4527 ≤ (12282742000871/100000000000000 : ℝ)^3503 := by
    have hnat : (1973764063 : ℕ)^4527*100000000000000^3503 ≤ 12282742000871^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973764063 10000000000 12282742000871 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337858377/2500000000 : ℝ), (5217750389/10000000000 : ℝ), (-1973764063/10000000000 : ℝ)] ![(22287753292479/50000000000000 : ℝ), (8628350280667/20000000000000 : ℝ), (12282742000871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337858377/2500000000 : ℝ)|^4527 ≤ (22287753292479/50000000000000 : ℝ)^3503
        have hw : |(1337858377/2500000000 : ℝ)|=(1337858377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217750389/10000000000 : ℝ)|^4527 ≤ (8628350280667/20000000000000 : ℝ)^3503
        have hw : |(5217750389/10000000000 : ℝ)|=(5217750389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973764063/10000000000 : ℝ)|^4527 ≤ (12282742000871/100000000000000 : ℝ)^3503
        have hw : |(-1973764063/10000000000 : ℝ)|=(1973764063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268373329/10000000000 : ℝ)*x 0 + (4029869237/10000000000 : ℝ)*x 1 + (180749289/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268373329/10000000000 : ℝ)^4527 ≤ (8319943736681/25000000000000 : ℝ)^3503 := by
    have hnat : (4268373329 : ℕ)^4527*25000000000000^3503 ≤ 8319943736681^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268373329 10000000000 8319943736681 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029869237/10000000000 : ℝ)^4527 ≤ (30896498482537/100000000000000 : ℝ)^3503 := by
    have hnat : (4029869237 : ℕ)^4527*100000000000000^3503 ≤ 30896498482537^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029869237 10000000000 30896498482537 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180749289/400000000 : ℝ)^4527 ≤ (7164745311119/20000000000000 : ℝ)^3503 := by
    have hnat : (180749289 : ℕ)^4527*20000000000000^3503 ≤ 7164745311119^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180749289 400000000 7164745311119 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268373329/10000000000 : ℝ), (4029869237/10000000000 : ℝ), (180749289/400000000 : ℝ)] ![(8319943736681/25000000000000 : ℝ), (30896498482537/100000000000000 : ℝ), (7164745311119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268373329/10000000000 : ℝ)|^4527 ≤ (8319943736681/25000000000000 : ℝ)^3503
        have hw : |(4268373329/10000000000 : ℝ)|=(4268373329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029869237/10000000000 : ℝ)|^4527 ≤ (30896498482537/100000000000000 : ℝ)^3503
        have hw : |(4029869237/10000000000 : ℝ)|=(4029869237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180749289/400000000 : ℝ)|^4527 ≤ (7164745311119/20000000000000 : ℝ)^3503
        have hw : |(180749289/400000000 : ℝ)|=(180749289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863618199/10000000000 : ℝ)*x 0 + (5218858823/10000000000 : ℝ)*x 1 + (5431766393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863618199/10000000000 : ℝ)^4527 ≤ (11404258455489/100000000000000 : ℝ)^3503 := by
    have hnat : (1863618199 : ℕ)^4527*100000000000000^3503 ≤ 11404258455489^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863618199 10000000000 11404258455489 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218858823/10000000000 : ℝ)^4527 ≤ (8630719133869/20000000000000 : ℝ)^3503 := by
    have hnat : (5218858823 : ℕ)^4527*20000000000000^3503 ≤ 8630719133869^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218858823 10000000000 8630719133869 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431766393/10000000000 : ℝ)^4527 ≤ (22721072927119/50000000000000 : ℝ)^3503 := by
    have hnat : (5431766393 : ℕ)^4527*50000000000000^3503 ≤ 22721072927119^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431766393 10000000000 22721072927119 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863618199/10000000000 : ℝ), (5218858823/10000000000 : ℝ), (5431766393/10000000000 : ℝ)] ![(11404258455489/100000000000000 : ℝ), (8630719133869/20000000000000 : ℝ), (22721072927119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863618199/10000000000 : ℝ)|^4527 ≤ (11404258455489/100000000000000 : ℝ)^3503
        have hw : |(-1863618199/10000000000 : ℝ)|=(1863618199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218858823/10000000000 : ℝ)|^4527 ≤ (8630719133869/20000000000000 : ℝ)^3503
        have hw : |(5218858823/10000000000 : ℝ)|=(5218858823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431766393/10000000000 : ℝ)|^4527 ≤ (22721072927119/50000000000000 : ℝ)^3503
        have hw : |(5431766393/10000000000 : ℝ)|=(5431766393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294933063/10000000000 : ℝ)*x 0 + (-879874013/5000000000 : ℝ)*x 1 + (1357941611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294933063/10000000000 : ℝ)^4527 ≤ (10992061184677/25000000000000 : ℝ)^3503 := by
    have hnat : (5294933063 : ℕ)^4527*25000000000000^3503 ≤ 10992061184677^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294933063 10000000000 10992061184677 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879874013/5000000000 : ℝ)^4527 ≤ (10589608834339/100000000000000 : ℝ)^3503 := by
    have hnat : (879874013 : ℕ)^4527*100000000000000^3503 ≤ 10589608834339^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879874013 5000000000 10589608834339 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357941611/2500000000 : ℝ)^4527 ≤ (45442146405627/100000000000000 : ℝ)^3503 := by
    have hnat : (1357941611 : ℕ)^4527*100000000000000^3503 ≤ 45442146405627^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357941611 2500000000 45442146405627 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294933063/10000000000 : ℝ), (-879874013/5000000000 : ℝ), (1357941611/2500000000 : ℝ)] ![(10992061184677/25000000000000 : ℝ), (10589608834339/100000000000000 : ℝ), (45442146405627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294933063/10000000000 : ℝ)|^4527 ≤ (10992061184677/25000000000000 : ℝ)^3503
        have hw : |(5294933063/10000000000 : ℝ)|=(5294933063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-879874013/5000000000 : ℝ)|^4527 ≤ (10589608834339/100000000000000 : ℝ)^3503
        have hw : |(-879874013/5000000000 : ℝ)|=(879874013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357941611/2500000000 : ℝ)|^4527 ≤ (45442146405627/100000000000000 : ℝ)^3503
        have hw : |(1357941611/2500000000 : ℝ)|=(1357941611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647466543/5000000000 : ℝ)*x 0 + (5431766431/10000000000 : ℝ)*x 1 + (-1759748013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647466543/5000000000 : ℝ)^4527 ≤ (21984122492763/50000000000000 : ℝ)^3503 := by
    have hnat : (2647466543 : ℕ)^4527*50000000000000^3503 ≤ 21984122492763^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647466543 5000000000 21984122492763 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431766431/10000000000 : ℝ)^4527 ≤ (45442146265077/100000000000000 : ℝ)^3503 := by
    have hnat : (5431766431 : ℕ)^4527*100000000000000^3503 ≤ 45442146265077^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431766431 10000000000 45442146265077 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759748013/10000000000 : ℝ)^4527 ≤ (10589608733241/100000000000000 : ℝ)^3503 := by
    have hnat : (1759748013 : ℕ)^4527*100000000000000^3503 ≤ 10589608733241^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759748013 10000000000 10589608733241 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647466543/5000000000 : ℝ), (5431766431/10000000000 : ℝ), (-1759748013/10000000000 : ℝ)] ![(21984122492763/50000000000000 : ℝ), (45442146265077/100000000000000 : ℝ), (10589608733241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647466543/5000000000 : ℝ)|^4527 ≤ (21984122492763/50000000000000 : ℝ)^3503
        have hw : |(2647466543/5000000000 : ℝ)|=(2647466543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431766431/10000000000 : ℝ)|^4527 ≤ (45442146265077/100000000000000 : ℝ)^3503
        have hw : |(5431766431/10000000000 : ℝ)|=(5431766431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759748013/10000000000 : ℝ)|^4527 ≤ (10589608733241/100000000000000 : ℝ)^3503
        have hw : |(-1759748013/10000000000 : ℝ)|=(1759748013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s5_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533554863/1250000000 : ℝ)*x 0 + (4516213511/10000000000 : ℝ)*x 1 + (4032406547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533554863/1250000000 : ℝ)^4527 ≤ (33280435682183/100000000000000 : ℝ)^3503 := by
    have hnat : (533554863 : ℕ)^4527*100000000000000^3503 ≤ 33280435682183^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533554863 1250000000 33280435682183 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516213511/10000000000 : ℝ)^4527 ≤ (35797923687593/100000000000000 : ℝ)^3503 := by
    have hnat : (4516213511 : ℕ)^4527*100000000000000^3503 ≤ 35797923687593^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516213511 10000000000 35797923687593 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032406547/10000000000 : ℝ)^4527 ≤ (7730410154417/25000000000000 : ℝ)^3503 := by
    have hnat : (4032406547 : ℕ)^4527*25000000000000^3503 ≤ 7730410154417^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032406547 10000000000 7730410154417 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533554863/1250000000 : ℝ), (4516213511/10000000000 : ℝ), (4032406547/10000000000 : ℝ)] ![(33280435682183/100000000000000 : ℝ), (35797923687593/100000000000000 : ℝ), (7730410154417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533554863/1250000000 : ℝ)|^4527 ≤ (33280435682183/100000000000000 : ℝ)^3503
        have hw : |(533554863/1250000000 : ℝ)|=(533554863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516213511/10000000000 : ℝ)|^4527 ≤ (35797923687593/100000000000000 : ℝ)^3503
        have hw : |(4516213511/10000000000 : ℝ)|=(4516213511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032406547/10000000000 : ℝ)|^4527 ≤ (7730410154417/25000000000000 : ℝ)^3503
        have hw : |(4032406547/10000000000 : ℝ)|=(4032406547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10927/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (273/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (273/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (273/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (273/2500 : ℝ) ^ (4525/1024 : ℝ) ≤ (44983000742639/800000000000000000 : ℝ) := by
    have hpowers : (273/2500 : ℝ)^4525 ≤ (44983000742639/800000000000000000 : ℝ)^1024 := by
      have hnat : (273 : ℕ)^4525*800000000000000000^1024 ≤ 44983000742639^1024*2500^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        273 2500 44983000742639 800000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (273/2500 : ℝ)) (X := (44983000742639/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4525/1024 : ℝ) ≤ (1054244879885237/4000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4525 ≤ (1054244879885237/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4525*4000000000000000000^1024 ≤ 1054244879885237^1024*10000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 1054244879885237 4000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (1054244879885237/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (400044983000742639/400000000000000000 : ℝ) ≤ (10000254478392121/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (400044983000742639/400000000000000000 : ℝ)^1024 ≤ (10000254478392121/10000000000000000 : ℝ)^4525 := by
      have hnat : (400044983000742639 : ℕ)^1024*10000000000000000^4525 ≤ 10000254478392121^4525*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400044983000742639 400000000000000000 10000254478392121 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000254478392121/10000000000000000 : ℝ)) (X := (400044983000742639/400000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (125039973746362451/125000000000000000 : ℝ) ≤ (10000723589893569/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (125039973746362451/125000000000000000 : ℝ)^1024 ≤ (10000723589893569/10000000000000000 : ℝ)^4525 := by
      have hnat : (125039973746362451 : ℕ)^1024*10000000000000000^4525 ≤ 10000723589893569^4525*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125039973746362451 125000000000000000 10000723589893569 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000723589893569/10000000000000000 : ℝ)) (X := (125039973746362451/125000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001054244879885237/2000000000000000000 : ℝ) ≤ (10001192701395017/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (2001054244879885237/2000000000000000000 : ℝ)^1024 ≤ (10001192701395017/10000000000000000 : ℝ)^4525 := by
      have hnat : (2001054244879885237 : ℕ)^1024*10000000000000000^4525 ≤ 10001192701395017^4525*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001054244879885237 2000000000000000000 10001192701395017 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001192701395017/10000000000000000 : ℝ)) (X := (2001054244879885237/2000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44983000742639/800000000000000000 : ℝ) ≤ ((913818351421207373/914000000000000000 : ℝ)+2*(58638937681/57125000000000 : ℝ)*(273/2500 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (913818351421207373/914000000000000000 : ℝ)+2*(58638937681/57125000000000 : ℝ)*(273/2500 : ℝ)=(10000254478392121/10000000000000000 : ℝ) by norm_num, show 1+2*(44983000742639/800000000000000000 : ℝ)=(400044983000742639/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1054244879885237/4000000000000000000 : ℝ)+(44983000742639/800000000000000000 : ℝ) ≤ ((913818351421207373/914000000000000000 : ℝ)+(58638937681/57125000000000 : ℝ)*((1549/10000 : ℝ)+(273/2500 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (913818351421207373/914000000000000000 : ℝ)+(58638937681/57125000000000 : ℝ)*((1549/10000 : ℝ)+(273/2500 : ℝ))=(10000723589893569/10000000000000000 : ℝ) by norm_num, show 1+(1054244879885237/4000000000000000000 : ℝ)+(44983000742639/800000000000000000 : ℝ)=(125039973746362451/125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1054244879885237/4000000000000000000 : ℝ) ≤ ((913818351421207373/914000000000000000 : ℝ)+2*(58638937681/57125000000000 : ℝ)*(1549/10000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (913818351421207373/914000000000000000 : ℝ)+2*(58638937681/57125000000000 : ℝ)*(1549/10000 : ℝ)=(10001192701395017/10000000000000000 : ℝ) by norm_num, show 1+2*(1054244879885237/4000000000000000000 : ℝ)=(2001054244879885237/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (913818351421207373/914000000000000000 : ℝ)*(X 1 0+X 2 0)+(58638937681/57125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (913818351421207373/914000000000000000 : ℝ)) (alpha := (58638937681/57125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (913818351421207373/914000000000000000 : ℝ)*(X 0 1+X 2 1)+(58638937681/57125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (913818351421207373/914000000000000000 : ℝ)) (alpha := (58638937681/57125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (913818351421207373/914000000000000000 : ℝ)*(X 0 2+X 1 2)+(58638937681/57125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (273/2500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (913818351421207373/914000000000000000 : ℝ)) (alpha := (58638937681/57125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-29118583/156250000 : ℝ)*X 0 0+(217315323/400000000 : ℝ)*X 0 1+(2608875161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675716753/5000000000 : ℝ)*X 1 0+(-394752813/2000000000 : ℝ)*X 1 1+(5217750389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337858377/2500000000 : ℝ)*X 2 0+(5217750389/10000000000 : ℝ)*X 2 1+(-1973764063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268373329/10000000000 : ℝ)*X 0 0+(4029869237/10000000000 : ℝ)*X 0 1+(180749289/400000000 : ℝ)*X 0 2+(4268373329/10000000000 : ℝ)*X 1 0+(4029869237/10000000000 : ℝ)*X 1 1+(180749289/400000000 : ℝ)*X 1 2+(4268373329/10000000000 : ℝ)*X 2 0+(4029869237/10000000000 : ℝ)*X 2 1+(180749289/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1863618199/10000000000 : ℝ)*X 0 0+(5218858823/10000000000 : ℝ)*X 0 1+(5431766393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294933063/10000000000 : ℝ)*X 1 0+(-879874013/5000000000 : ℝ)*X 1 1+(1357941611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647466543/5000000000 : ℝ)*X 2 0+(5431766431/10000000000 : ℝ)*X 2 1+(-1759748013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533554863/1250000000 : ℝ)*X 0 0+(4516213511/10000000000 : ℝ)*X 0 1+(4032406547/10000000000 : ℝ)*X 0 2+(533554863/1250000000 : ℝ)*X 1 0+(4516213511/10000000000 : ℝ)*X 1 1+(4032406547/10000000000 : ℝ)*X 1 2+(533554863/1250000000 : ℝ)*X 2 0+(4516213511/10000000000 : ℝ)*X 2 1+(4032406547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86456372224279668804313593/22850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672981207/100000000000000 : ℝ)*(base19) + (127474701/20000000000000 : ℝ)*(base23) + (19984889/100000000000000 : ℝ)*(lower2) + (1425977/1562500000000 : ℝ)*(upper3) + (66478951/100000000000000 : ℝ)*(upper5) + (1673472532941953/50000000000000 : ℝ)*(major0) + (1673472532941953/50000000000000 : ℝ)*(major1) + (1673472532941953/50000000000000 : ℝ)*(major2) + (232415256911441/5000000000000 : ℝ)*(sp0) + (4648316694124119/100000000000000 : ℝ)*(sp1) + (2324158364865911/50000000000000 : ℝ)*(sp2) + (409113512132577/20000000000000 : ℝ)*(sp3) + (12228876507/100000000000000 : ℝ)*(sp4) + (5077877969/100000000000000 : ℝ)*(sp7) + (409114527708171/20000000000000 : ℝ)*(f.failure) + (4648317367105327/100000000000000 : ℝ)*(f.sum) + (6546307195193/1428125000000000000000000000 : ℝ)*base65 + (255780267490007469/45700000000000000000000000000000 : ℝ)*base67 + (55315206795792531/45700000000000000000000000000000 : ℝ)*base70 + (101504804957007469/45700000000000000000000000000000 : ℝ)*base71 + (24298698317119/11425000000000000000000000000 : ℝ)*base73 + (356349342104207469/45700000000000000000000000000000 : ℝ)*base75 + (176207836413607469/45700000000000000000000000000000 : ℝ)*base77 + (499027712572892531/45700000000000000000000000000000 : ℝ)*base80 + (12518912245703/5712500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28977409/2000000000000000000000 : ℝ)*base89 + (28977409/2000000000000000000000 : ℝ)*base91 + (28977409/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14345440741689322275523893/2285000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258485331/25000000000000 : ℝ)*(base19) + (1112939777/100000000000000 : ℝ)*(base23) + (351515071/100000000000000 : ℝ)*(lower1) + (144767441/100000000000000 : ℝ)*(upper3) + (1077521/5000000000000 : ℝ)*(lower4) + (14523781/12500000000000 : ℝ)*(upper5) + (169094739012253/5000000000000 : ℝ)*(major0) + (169094739012253/5000000000000 : ℝ)*(major1) + (169094739012253/5000000000000 : ℝ)*(major2) + (335429779/20000000000000 : ℝ)*(sp2) + (1174214071145811/25000000000000 : ℝ)*(sp4) + (917354541141/19531250000 : ℝ)*(sp5) + (1174213373623643/25000000000000 : ℝ)*(sp6) + (2066933066637129/100000000000000 : ℝ)*(sp7) + (2066933066637129/100000000000000 : ℝ)*(f.failure) + (1174214071145811/25000000000000 : ℝ)*(f.sum) + (117479554353/571250000000000000000000000 : ℝ)*base66 + (44090948425040631/4570000000000000000000000000000 : ℝ)*base68 + (8607591966279369/4570000000000000000000000000000 : ℝ)*base69 + (119705509636690631/4570000000000000000000000000000 : ℝ)*base72 + (5372593513027/2285000000000000000000000000 : ℝ)*base74 + (630137869119369/4570000000000000000000000000000 : ℝ)*base75 + (23990911116869369/4570000000000000000000000000000 : ℝ)*base77 + (15451029176209369/4570000000000000000000000000000 : ℝ)*base79 + (11956813377891/1142500000000000000000000000 : ℝ)*base82 + (10471291/10000000000000000000000 : ℝ)*base89 + (10471291/10000000000000000000000 : ℝ)*base91 + (10471291/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1515_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1515_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1515_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1515_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1515_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

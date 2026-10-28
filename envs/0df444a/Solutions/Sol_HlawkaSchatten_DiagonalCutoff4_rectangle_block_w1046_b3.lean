-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:51:27.689807+00:00
-- url     : https://prove2.me/submissions/b35e26cb-5415-42e5-b8ce-4c0714e4c15e

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
theorem support_rectangle_w1046_s9_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88546393/400000000 : ℝ)*x 0 + (1348669469/2500000000 : ℝ)*x 1 + (5264101941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88546393/400000000 : ℝ)^8239 ≤ (1344224306173/10000000000000 : ℝ)^6191 := by
    have hnat : (88546393 : ℕ)^8239*10000000000000^6191 ≤ 1344224306173^6191*400000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88546393 400000000 1344224306173 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348669469/2500000000 : ℝ)^8239 ≤ (43984429765899/100000000000000 : ℝ)^6191 := by
    have hnat : (1348669469 : ℕ)^8239*100000000000000^6191 ≤ 43984429765899^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348669469 2500000000 43984429765899 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264101941/10000000000 : ℝ)^8239 ≤ (5321665894783/12500000000000 : ℝ)^6191 := by
    have hnat : (5264101941 : ℕ)^8239*12500000000000^6191 ≤ 5321665894783^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264101941 10000000000 5321665894783 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88546393/400000000 : ℝ), (1348669469/2500000000 : ℝ), (5264101941/10000000000 : ℝ)] ![(1344224306173/10000000000000 : ℝ), (43984429765899/100000000000000 : ℝ), (5321665894783/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88546393/400000000 : ℝ)|^8239 ≤ (1344224306173/10000000000000 : ℝ)^6191
        have hw : |(-88546393/400000000 : ℝ)|=(88546393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348669469/2500000000 : ℝ)|^8239 ≤ (43984429765899/100000000000000 : ℝ)^6191
        have hw : |(1348669469/2500000000 : ℝ)|=(1348669469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264101941/10000000000 : ℝ)|^8239 ≤ (5321665894783/12500000000000 : ℝ)^6191
        have hw : |(5264101941/10000000000 : ℝ)|=(5264101941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s9_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069002723/2000000000 : ℝ)*x 0 + (-142494691/625000000 : ℝ)*x 1 + (2632051123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069002723/2000000000 : ℝ)^8239 ≤ (8689274636297/20000000000000 : ℝ)^6191 := by
    have hnat : (1069002723 : ℕ)^8239*20000000000000^6191 ≤ 8689274636297^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069002723 2000000000 8689274636297 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142494691/625000000 : ℝ)^8239 ≤ (13980296352161/100000000000000 : ℝ)^6191 := by
    have hnat : (142494691 : ℕ)^8239*100000000000000^6191 ≤ 13980296352161^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142494691 625000000 13980296352161 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632051123/5000000000 : ℝ)^8239 ≤ (42573330440931/100000000000000 : ℝ)^6191 := by
    have hnat : (2632051123 : ℕ)^8239*100000000000000^6191 ≤ 42573330440931^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632051123 5000000000 42573330440931 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069002723/2000000000 : ℝ), (-142494691/625000000 : ℝ), (2632051123/5000000000 : ℝ)] ![(8689274636297/20000000000000 : ℝ), (13980296352161/100000000000000 : ℝ), (42573330440931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069002723/2000000000 : ℝ)|^8239 ≤ (8689274636297/20000000000000 : ℝ)^6191
        have hw : |(1069002723/2000000000 : ℝ)|=(1069002723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142494691/625000000 : ℝ)|^8239 ≤ (13980296352161/100000000000000 : ℝ)^6191
        have hw : |(-142494691/625000000 : ℝ)|=(142494691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632051123/5000000000 : ℝ)|^8239 ≤ (42573330440931/100000000000000 : ℝ)^6191
        have hw : |(2632051123/5000000000 : ℝ)|=(2632051123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s9_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672506991/5000000000 : ℝ)*x 0 + (1316025489/2500000000 : ℝ)*x 1 + (-284989369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672506991/5000000000 : ℝ)^8239 ≤ (4344637715143/10000000000000 : ℝ)^6191 := by
    have hnat : (2672506991 : ℕ)^8239*10000000000000^6191 ≤ 4344637715143^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672506991 5000000000 4344637715143 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316025489/2500000000 : ℝ)^8239 ≤ (21286663659853/50000000000000 : ℝ)^6191 := by
    have hnat : (1316025489 : ℕ)^8239*50000000000000^6191 ≤ 21286663659853^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316025489 2500000000 21286663659853 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284989369/1250000000 : ℝ)^8239 ≤ (349507387587/2500000000000 : ℝ)^6191 := by
    have hnat : (284989369 : ℕ)^8239*2500000000000^6191 ≤ 349507387587^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284989369 1250000000 349507387587 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672506991/5000000000 : ℝ), (1316025489/2500000000 : ℝ), (-284989369/1250000000 : ℝ)] ![(4344637715143/10000000000000 : ℝ), (21286663659853/50000000000000 : ℝ), (349507387587/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672506991/5000000000 : ℝ)|^8239 ≤ (4344637715143/10000000000000 : ℝ)^6191
        have hw : |(2672506991/5000000000 : ℝ)|=(2672506991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316025489/2500000000 : ℝ)|^8239 ≤ (21286663659853/50000000000000 : ℝ)^6191
        have hw : |(1316025489/2500000000 : ℝ)|=(1316025489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284989369/1250000000 : ℝ)|^8239 ≤ (349507387587/2500000000000 : ℝ)^6191
        have hw : |(-284989369/1250000000 : ℝ)|=(284989369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s9_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094594443/2500000000 : ℝ)*x 0 + (1063204687/2500000000 : ℝ)*x 1 + (4507712881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094594443/2500000000 : ℝ)^8239 ≤ (16658222353719/50000000000000 : ℝ)^6191 := by
    have hnat : (1094594443 : ℕ)^8239*50000000000000^6191 ≤ 16658222353719^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094594443 2500000000 16658222353719 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063204687/2500000000 : ℝ)^8239 ≤ (6410208381593/20000000000000 : ℝ)^6191 := by
    have hnat : (1063204687 : ℕ)^8239*20000000000000^6191 ≤ 6410208381593^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063204687 2500000000 6410208381593 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507712881/10000000000 : ℝ)^8239 ≤ (34632513372423/100000000000000 : ℝ)^6191 := by
    have hnat : (4507712881 : ℕ)^8239*100000000000000^6191 ≤ 34632513372423^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507712881 10000000000 34632513372423 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094594443/2500000000 : ℝ), (1063204687/2500000000 : ℝ), (4507712881/10000000000 : ℝ)] ![(16658222353719/50000000000000 : ℝ), (6410208381593/20000000000000 : ℝ), (34632513372423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094594443/2500000000 : ℝ)|^8239 ≤ (16658222353719/50000000000000 : ℝ)^6191
        have hw : |(1094594443/2500000000 : ℝ)|=(1094594443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063204687/2500000000 : ℝ)|^8239 ≤ (6410208381593/20000000000000 : ℝ)^6191
        have hw : |(1063204687/2500000000 : ℝ)|=(1063204687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507712881/10000000000 : ℝ)|^8239 ≤ (34632513372423/100000000000000 : ℝ)^6191
        have hw : |(4507712881/10000000000 : ℝ)|=(4507712881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s9_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106832447/5000000000 : ℝ)*x 0 + (2632214391/5000000000 : ℝ)*x 1 + (5394349891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106832447/5000000000 : ℝ)^8239 ≤ (6721142012613/50000000000000 : ℝ)^6191 := by
    have hnat : (1106832447 : ℕ)^8239*50000000000000^6191 ≤ 6721142012613^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106832447 5000000000 6721142012613 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632214391/5000000000 : ℝ)^8239 ≤ (42576844932717/100000000000000 : ℝ)^6191 := by
    have hnat : (2632214391 : ℕ)^8239*100000000000000^6191 ≤ 42576844932717^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632214391 5000000000 42576844932717 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394349891/10000000000 : ℝ)^8239 ≤ (21990435510891/50000000000000 : ℝ)^6191 := by
    have hnat : (5394349891 : ℕ)^8239*50000000000000^6191 ≤ 21990435510891^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394349891 10000000000 21990435510891 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106832447/5000000000 : ℝ), (2632214391/5000000000 : ℝ), (5394349891/10000000000 : ℝ)] ![(6721142012613/50000000000000 : ℝ), (42576844932717/100000000000000 : ℝ), (21990435510891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106832447/5000000000 : ℝ)|^8239 ≤ (6721142012613/50000000000000 : ℝ)^6191
        have hw : |(-1106832447/5000000000 : ℝ)|=(1106832447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632214391/5000000000 : ℝ)|^8239 ≤ (42576844932717/100000000000000 : ℝ)^6191
        have hw : |(2632214391/5000000000 : ℝ)|=(2632214391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394349891/10000000000 : ℝ)|^8239 ≤ (21990435510891/50000000000000 : ℝ)^6191
        have hw : |(5394349891/10000000000 : ℝ)|=(5394349891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s9_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378387677/10000000000 : ℝ)*x 0 + (1126768839/2500000000 : ℝ)*x 1 + (1063364659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378387677/10000000000 : ℝ)^8239 ≤ (33316545010401/100000000000000 : ℝ)^6191 := by
    have hnat : (4378387677 : ℕ)^8239*100000000000000^6191 ≤ 33316545010401^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378387677 10000000000 33316545010401 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126768839/2500000000 : ℝ)^8239 ≤ (8656498789947/25000000000000 : ℝ)^6191 := by
    have hnat : (1126768839 : ℕ)^8239*25000000000000^6191 ≤ 8656498789947^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126768839 2500000000 8656498789947 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063364659/2500000000 : ℝ)^8239 ≤ (2003591238741/6250000000000 : ℝ)^6191 := by
    have hnat : (1063364659 : ℕ)^8239*6250000000000^6191 ≤ 2003591238741^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063364659 2500000000 2003591238741 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378387677/10000000000 : ℝ), (1126768839/2500000000 : ℝ), (1063364659/2500000000 : ℝ)] ![(33316545010401/100000000000000 : ℝ), (8656498789947/25000000000000 : ℝ), (2003591238741/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378387677/10000000000 : ℝ)|^8239 ≤ (33316545010401/100000000000000 : ℝ)^6191
        have hw : |(4378387677/10000000000 : ℝ)|=(4378387677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126768839/2500000000 : ℝ)|^8239 ≤ (8656498789947/25000000000000 : ℝ)^6191
        have hw : |(1126768839/2500000000 : ℝ)|=(1126768839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063364659/2500000000 : ℝ)|^8239 ≤ (2003591238741/6250000000000 : ℝ)^6191
        have hw : |(1063364659/2500000000 : ℝ)|=(1063364659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1399/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (3776073308920651/25000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^4119 ≤ (3776073308920651/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11223 : ℕ)^4119*25000000000000000000^1024 ≤ 3776073308920651^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 3776073308920651 25000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (3776073308920651/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (4119/1024 : ℝ) ≤ (36650940456581109/100000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^4119 ≤ (36650940456581109/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4119*100000000000000000000^1024 ≤ 36650940456581109^1024*10000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 36650940456581109 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (36650940456581109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503776073308920651/12500000000000000000 : ℝ) ≤ (1000075091241607/1000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (12503776073308920651/12500000000000000000 : ℝ)^1024 ≤ (1000075091241607/1000000000000000 : ℝ)^4119 := by
      have hnat : (12503776073308920651 : ℕ)^1024*1000000000000000^4119 ≤ 1000075091241607^4119*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503776073308920651 12500000000000000000 1000075091241607 1000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000075091241607/1000000000000000 : ℝ)) (X := (12503776073308920651/12500000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051755233692263713/100000000000000000000 : ℝ) ≤ (2500321601465333/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (100051755233692263713/100000000000000000000 : ℝ)^1024 ≤ (2500321601465333/2500000000000000 : ℝ)^4119 := by
      have hnat : (100051755233692263713 : ℕ)^1024*2500000000000000^4119 ≤ 2500321601465333^4119*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051755233692263713 100000000000000000000 2500321601465333 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500321601465333/2500000000000000 : ℝ)) (X := (100051755233692263713/100000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036650940456581109/50000000000000000000 : ℝ) ≤ (5000910949653297/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50036650940456581109/50000000000000000000 : ℝ)^1024 ≤ (5000910949653297/5000000000000000 : ℝ)^4119 := by
      have hnat : (50036650940456581109 : ℕ)^1024*5000000000000000^4119 ≤ 5000910949653297^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036650940456581109 50000000000000000000 5000910949653297 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000910949653297/5000000000000000 : ℝ)) (X := (50036650940456581109/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3776073308920651/25000000000000000000 : ℝ) ≤ ((13830029044391457419/13835000000000000000 : ℝ)+2*(267746722631/138350000000000 : ℝ)*(11223/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (13830029044391457419/13835000000000000000 : ℝ)+2*(267746722631/138350000000000 : ℝ)*(11223/100000 : ℝ)=(1000075091241607/1000000000000000 : ℝ) by norm_num, show 1+2*(3776073308920651/25000000000000000000 : ℝ)=(12503776073308920651/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36650940456581109/100000000000000000000 : ℝ)+(3776073308920651/25000000000000000000 : ℝ) ≤ ((13830029044391457419/13835000000000000000 : ℝ)+(267746722631/138350000000000 : ℝ)*((1399/10000 : ℝ)+(11223/100000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (13830029044391457419/13835000000000000000 : ℝ)+(267746722631/138350000000000 : ℝ)*((1399/10000 : ℝ)+(11223/100000 : ℝ))=(2500321601465333/2500000000000000 : ℝ) by norm_num, show 1+(36650940456581109/100000000000000000000 : ℝ)+(3776073308920651/25000000000000000000 : ℝ)=(100051755233692263713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36650940456581109/100000000000000000000 : ℝ) ≤ ((13830029044391457419/13835000000000000000 : ℝ)+2*(267746722631/138350000000000 : ℝ)*(1399/10000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (13830029044391457419/13835000000000000000 : ℝ)+2*(267746722631/138350000000000 : ℝ)*(1399/10000 : ℝ)=(5000910949653297/5000000000000000 : ℝ) by norm_num, show 1+2*(36650940456581109/100000000000000000000 : ℝ)=(50036650940456581109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13830029044391457419/13835000000000000000 : ℝ)*(X 1 0+X 2 0)+(267746722631/138350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13830029044391457419/13835000000000000000 : ℝ)) (alpha := (267746722631/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13830029044391457419/13835000000000000000 : ℝ)*(X 0 1+X 2 1)+(267746722631/138350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13830029044391457419/13835000000000000000 : ℝ)) (alpha := (267746722631/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13830029044391457419/13835000000000000000 : ℝ)*(X 0 2+X 1 2)+(267746722631/138350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (13830029044391457419/13835000000000000000 : ℝ)) (alpha := (267746722631/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88546393/400000000 : ℝ)*X 0 0+(1348669469/2500000000 : ℝ)*X 0 1+(5264101941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069002723/2000000000 : ℝ)*X 1 0+(-142494691/625000000 : ℝ)*X 1 1+(2632051123/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672506991/5000000000 : ℝ)*X 2 0+(1316025489/2500000000 : ℝ)*X 2 1+(-284989369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094594443/2500000000 : ℝ)*X 0 0+(1063204687/2500000000 : ℝ)*X 0 1+(4507712881/10000000000 : ℝ)*X 0 2+(1094594443/2500000000 : ℝ)*X 1 0+(1063204687/2500000000 : ℝ)*X 1 1+(4507712881/10000000000 : ℝ)*X 1 2+(1094594443/2500000000 : ℝ)*X 2 0+(1063204687/2500000000 : ℝ)*X 2 1+(4507712881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106832447/5000000000 : ℝ)*X 0 0+(2632214391/5000000000 : ℝ)*X 0 1+(5394349891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4378387677/10000000000 : ℝ)*X 0 0+(1126768839/2500000000 : ℝ)*X 0 1+(1063364659/2500000000 : ℝ)*X 0 2+(4378387677/10000000000 : ℝ)*X 1 0+(1126768839/2500000000 : ℝ)*X 1 1+(1063364659/2500000000 : ℝ)*X 1 2+(4378387677/10000000000 : ℝ)*X 2 0+(1126768839/2500000000 : ℝ)*X 2 1+(1063364659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1243908128345181725841858987/172937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (172825691/20000000000000 : ℝ)*(base19) + (64815029/5000000000000 : ℝ)*(base23) + (1001369/2000000000000 : ℝ)*(lower2) + (39420549/50000000000000 : ℝ)*(upper3) + (34034873/12500000000000 : ℝ)*(upper5) + (2895417430682609/50000000000000 : ℝ)*(major0) + (2895417430682609/50000000000000 : ℝ)*(major1) + (2895417430682609/50000000000000 : ℝ)*(major2) + (3829202973280679/50000000000000 : ℝ)*(sp0) + (7658448383229749/100000000000000 : ℝ)*(sp1) + (957305993882203/12500000000000 : ℝ)*(sp2) + (784641817891733/20000000000000 : ℝ)*(sp3) + (43300796847/100000000000000 : ℝ)*(sp4) + (5573076461/50000000000000 : ℝ)*(sp5) + (1961610117805793/50000000000000 : ℝ)*(f.failure) + (1531689849471641/20000000000000 : ℝ)*(f.sum) + (6484594469553/6917500000000000000000000000 : ℝ)*base65 + (3091670796970726171/691750000000000000000000000000000 : ℝ)*base67 + (6688992020004226171/691750000000000000000000000000000 : ℝ)*base69 + (10743282463629476171/691750000000000000000000000000000 : ℝ)*base71 + (3966941468629/864687500000000000000000000 : ℝ)*base74 + (8317781774029023829/691750000000000000000000000000000 : ℝ)*base76 + (6669105916126726171/691750000000000000000000000000000 : ℝ)*base77 + (10281480548872226171/691750000000000000000000000000000 : ℝ)*base79 + (99988041034399/13835000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5527417/1250000000000000000000 : ℝ)*base90 + (5527417/1250000000000000000000 : ℝ)*base92 + (5527417/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1046_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_box_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-520874133/2500000000 : ℝ)*x 0 + (1075527491/2000000000 : ℝ)*x 1 + (672204691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520874133/2500000000 : ℝ)^8239 ≤ (2480147655359/20000000000000 : ℝ)^6191 := by
    have hnat : (520874133 : ℕ)^8239*20000000000000^6191 ≤ 2480147655359^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520874133 2500000000 2480147655359 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075527491/2000000000 : ℝ)^8239 ≤ (43799630455551/100000000000000 : ℝ)^6191 := by
    have hnat : (1075527491 : ℕ)^8239*100000000000000^6191 ≤ 43799630455551^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075527491 2000000000 43799630455551 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672204691/1250000000 : ℝ)^8239 ≤ (10949907811701/25000000000000 : ℝ)^6191 := by
    have hnat : (672204691 : ℕ)^8239*25000000000000^6191 ≤ 10949907811701^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672204691 1250000000 10949907811701 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-520874133/2500000000 : ℝ), (1075527491/2000000000 : ℝ), (672204691/1250000000 : ℝ)] ![(2480147655359/20000000000000 : ℝ), (43799630455551/100000000000000 : ℝ), (10949907811701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-520874133/2500000000 : ℝ)|^8239 ≤ (2480147655359/20000000000000 : ℝ)^6191
        have hw : |(-520874133/2500000000 : ℝ)|=(520874133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075527491/2000000000 : ℝ)|^8239 ≤ (43799630455551/100000000000000 : ℝ)^6191
        have hw : |(1075527491/2000000000 : ℝ)|=(1075527491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672204691/1250000000 : ℝ)|^8239 ≤ (10949907811701/25000000000000 : ℝ)^6191
        have hw : |(672204691/1250000000 : ℝ)|=(672204691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (13237429/25000000 : ℝ)*x 0 + (-548837297/2500000000 : ℝ)*x 1 + (5377637533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13237429/25000000 : ℝ)^8239 ≤ (42905894286467/100000000000000 : ℝ)^6191 := by
    have hnat : (13237429 : ℕ)^8239*100000000000000^6191 ≤ 42905894286467^6191*25000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13237429 25000000 42905894286467 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548837297/2500000000 : ℝ)^8239 ≤ (13294474404511/100000000000000 : ℝ)^6191 := by
    have hnat : (548837297 : ℕ)^8239*100000000000000^6191 ≤ 13294474404511^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548837297 2500000000 13294474404511 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377637533/10000000000 : ℝ)^8239 ≤ (43799631300999/100000000000000 : ℝ)^6191 := by
    have hnat : (5377637533 : ℕ)^8239*100000000000000^6191 ≤ 43799631300999^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377637533 10000000000 43799631300999 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13237429/25000000 : ℝ), (-548837297/2500000000 : ℝ), (5377637533/10000000000 : ℝ)] ![(42905894286467/100000000000000 : ℝ), (13294474404511/100000000000000 : ℝ), (43799631300999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13237429/25000000 : ℝ)|^8239 ≤ (42905894286467/100000000000000 : ℝ)^6191
        have hw : |(13237429/25000000 : ℝ)|=(13237429/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548837297/2500000000 : ℝ)|^8239 ≤ (13294474404511/100000000000000 : ℝ)^6191
        have hw : |(-548837297/2500000000 : ℝ)|=(548837297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377637533/10000000000 : ℝ)|^8239 ≤ (43799631300999/100000000000000 : ℝ)^6191
        have hw : |(5377637533/10000000000 : ℝ)|=(5377637533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294971693/10000000000 : ℝ)*x 0 + (2688818751/5000000000 : ℝ)*x 1 + (-137209319/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294971693/10000000000 : ℝ)^8239 ≤ (858117905787/2000000000000 : ℝ)^6191 := by
    have hnat : (5294971693 : ℕ)^8239*2000000000000^6191 ≤ 858117905787^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294971693 10000000000 858117905787 2000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688818751/5000000000 : ℝ)^8239 ≤ (10949907741247/25000000000000 : ℝ)^6191 := by
    have hnat : (2688818751 : ℕ)^8239*25000000000000^6191 ≤ 10949907741247^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688818751 5000000000 10949907741247 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137209319/625000000 : ℝ)^8239 ≤ (6647236863777/50000000000000 : ℝ)^6191 := by
    have hnat : (137209319 : ℕ)^8239*50000000000000^6191 ≤ 6647236863777^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137209319 625000000 6647236863777 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294971693/10000000000 : ℝ), (2688818751/5000000000 : ℝ), (-137209319/625000000 : ℝ)] ![(858117905787/2000000000000 : ℝ), (10949907741247/25000000000000 : ℝ), (6647236863777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294971693/10000000000 : ℝ)|^8239 ≤ (858117905787/2000000000000 : ℝ)^6191
        have hw : |(5294971693/10000000000 : ℝ)|=(5294971693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688818751/5000000000 : ℝ)|^8239 ≤ (10949907741247/25000000000000 : ℝ)^6191
        have hw : |(2688818751/5000000000 : ℝ)|=(2688818751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137209319/625000000 : ℝ)|^8239 ≤ (6647236863777/50000000000000 : ℝ)^6191
        have hw : |(-137209319/625000000 : ℝ)|=(137209319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4486997659/10000000000 : ℝ)*x 0 + (8449697/19531250 : ℝ)*x 1 + (4326244939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486997659/10000000000 : ℝ)^8239 ≤ (34420872042423/100000000000000 : ℝ)^6191 := by
    have hnat : (4486997659 : ℕ)^8239*100000000000000^6191 ≤ 34420872042423^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486997659 10000000000 34420872042423 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8449697/19531250 : ℝ)^8239 ≤ (32789563593621/100000000000000 : ℝ)^6191 := by
    have hnat : (8449697 : ℕ)^8239*100000000000000^6191 ≤ 32789563593621^6191*19531250^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8449697 19531250 32789563593621 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326244939/10000000000 : ℝ)^8239 ≤ (4098695543763/12500000000000 : ℝ)^6191 := by
    have hnat : (4326244939 : ℕ)^8239*12500000000000^6191 ≤ 4098695543763^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326244939 10000000000 4098695543763 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486997659/10000000000 : ℝ), (8449697/19531250 : ℝ), (4326244939/10000000000 : ℝ)] ![(34420872042423/100000000000000 : ℝ), (32789563593621/100000000000000 : ℝ), (4098695543763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486997659/10000000000 : ℝ)|^8239 ≤ (34420872042423/100000000000000 : ℝ)^6191
        have hw : |(4486997659/10000000000 : ℝ)|=(4486997659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8449697/19531250 : ℝ)|^8239 ≤ (32789563593621/100000000000000 : ℝ)^6191
        have hw : |(8449697/19531250 : ℝ)|=(8449697/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326244939/10000000000 : ℝ)|^8239 ≤ (4098695543763/12500000000000 : ℝ)^6191
        have hw : |(4326244939/10000000000 : ℝ)|=(4326244939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2345202773/10000000000 : ℝ)*x 0 + (2639892893/5000000000 : ℝ)*x 1 + (659973179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2345202773/10000000000 : ℝ)^8239 ≤ (7257788856889/50000000000000 : ℝ)^6191 := by
    have hnat : (2345202773 : ℕ)^8239*50000000000000^6191 ≤ 7257788856889^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345202773 10000000000 7257788856889 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639892893/5000000000 : ℝ)^8239 ≤ (21371106523901/50000000000000 : ℝ)^6191 := by
    have hnat : (2639892893 : ℕ)^8239*50000000000000^6191 ≤ 21371106523901^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639892893 5000000000 21371106523901 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659973179/1250000000 : ℝ)^8239 ≤ (10685552308501/25000000000000 : ℝ)^6191 := by
    have hnat : (659973179 : ℕ)^8239*25000000000000^6191 ≤ 10685552308501^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659973179 1250000000 10685552308501 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2345202773/10000000000 : ℝ), (2639892893/5000000000 : ℝ), (659973179/1250000000 : ℝ)] ![(7257788856889/50000000000000 : ℝ), (21371106523901/50000000000000 : ℝ), (10685552308501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2345202773/10000000000 : ℝ)|^8239 ≤ (7257788856889/50000000000000 : ℝ)^6191
        have hw : |(-2345202773/10000000000 : ℝ)|=(2345202773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639892893/5000000000 : ℝ)|^8239 ≤ (21371106523901/50000000000000 : ℝ)^6191
        have hw : |(2639892893/5000000000 : ℝ)|=(2639892893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659973179/1250000000 : ℝ)|^8239 ≤ (10685552308501/25000000000000 : ℝ)^6191
        have hw : |(659973179/1250000000 : ℝ)|=(659973179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364255303/10000000000 : ℝ)*x 0 + (-558385453/2500000000 : ℝ)*x 1 + (5279785407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364255303/10000000000 : ℝ)^8239 ≤ (43654639907119/100000000000000 : ℝ)^6191 := by
    have hnat : (5364255303 : ℕ)^8239*100000000000000^6191 ≤ 43654639907119^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364255303 10000000000 43654639907119 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558385453/2500000000 : ℝ)^8239 ≤ (6801575551431/50000000000000 : ℝ)^6191 := by
    have hnat : (558385453 : ℕ)^8239*50000000000000^6191 ≤ 6801575551431^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558385453 2500000000 6801575551431 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279785407/10000000000 : ℝ)^8239 ≤ (10685552241167/25000000000000 : ℝ)^6191 := by
    have hnat : (5279785407 : ℕ)^8239*25000000000000^6191 ≤ 10685552241167^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279785407 10000000000 10685552241167 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364255303/10000000000 : ℝ), (-558385453/2500000000 : ℝ), (5279785407/10000000000 : ℝ)] ![(43654639907119/100000000000000 : ℝ), (6801575551431/50000000000000 : ℝ), (10685552241167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364255303/10000000000 : ℝ)|^8239 ≤ (43654639907119/100000000000000 : ℝ)^6191
        have hw : |(5364255303/10000000000 : ℝ)|=(5364255303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558385453/2500000000 : ℝ)|^8239 ≤ (6801575551431/50000000000000 : ℝ)^6191
        have hw : |(-558385453/2500000000 : ℝ)|=(558385453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279785407/10000000000 : ℝ)|^8239 ≤ (10685552241167/25000000000000 : ℝ)^6191
        have hw : |(5279785407/10000000000 : ℝ)|=(5279785407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072850959/2000000000 : ℝ)*x 0 + (5279785887/10000000000 : ℝ)*x 1 + (-1116770927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072850959/2000000000 : ℝ)^8239 ≤ (218273172027/500000000000 : ℝ)^6191 := by
    have hnat : (1072850959 : ℕ)^8239*500000000000^6191 ≤ 218273172027^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072850959 2000000000 218273172027 500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279785887/10000000000 : ℝ)^8239 ≤ (42742214135919/100000000000000 : ℝ)^6191 := by
    have hnat : (5279785887 : ℕ)^8239*100000000000000^6191 ≤ 42742214135919^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279785887 10000000000 42742214135919 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116770927/5000000000 : ℝ)^8239 ≤ (3400787860819/25000000000000 : ℝ)^6191 := by
    have hnat : (1116770927 : ℕ)^8239*25000000000000^6191 ≤ 3400787860819^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116770927 5000000000 3400787860819 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072850959/2000000000 : ℝ), (5279785887/10000000000 : ℝ), (-1116770927/5000000000 : ℝ)] ![(218273172027/500000000000 : ℝ), (42742214135919/100000000000000 : ℝ), (3400787860819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072850959/2000000000 : ℝ)|^8239 ≤ (218273172027/500000000000 : ℝ)^6191
        have hw : |(1072850959/2000000000 : ℝ)|=(1072850959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279785887/10000000000 : ℝ)|^8239 ≤ (42742214135919/100000000000000 : ℝ)^6191
        have hw : |(5279785887/10000000000 : ℝ)|=(5279785887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1116770927/5000000000 : ℝ)|^8239 ≤ (3400787860819/25000000000000 : ℝ)^6191
        have hw : |(-1116770927/5000000000 : ℝ)|=(1116770927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4269437037/10000000000 : ℝ)*x 0 + (277187733/625000000 : ℝ)*x 1 + (4435003429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269437037/10000000000 : ℝ)^8239 ≤ (32217822550799/100000000000000 : ℝ)^6191 := by
    have hnat : (4269437037 : ℕ)^8239*100000000000000^6191 ≤ 32217822550799^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269437037 10000000000 32217822550799 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277187733/625000000 : ℝ)^8239 ≤ (8472772560171/25000000000000 : ℝ)^6191 := by
    have hnat : (277187733 : ℕ)^8239*25000000000000^6191 ≤ 8472772560171^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277187733 625000000 8472772560171 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435003429/10000000000 : ℝ)^8239 ≤ (8472771799991/25000000000000 : ℝ)^6191 := by
    have hnat : (4435003429 : ℕ)^8239*25000000000000^6191 ≤ 8472771799991^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435003429 10000000000 8472771799991 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269437037/10000000000 : ℝ), (277187733/625000000 : ℝ), (4435003429/10000000000 : ℝ)] ![(32217822550799/100000000000000 : ℝ), (8472772560171/25000000000000 : ℝ), (8472771799991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269437037/10000000000 : ℝ)|^8239 ≤ (32217822550799/100000000000000 : ℝ)^6191
        have hw : |(4269437037/10000000000 : ℝ)|=(4269437037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277187733/625000000 : ℝ)|^8239 ≤ (8472772560171/25000000000000 : ℝ)^6191
        have hw : |(277187733/625000000 : ℝ)|=(277187733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435003429/10000000000 : ℝ)|^8239 ≤ (8472771799991/25000000000000 : ℝ)^6191
        have hw : |(4435003429/10000000000 : ℝ)|=(4435003429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_8 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2290595001/10000000000 : ℝ)*x 0 + (325839169/625000000 : ℝ)*x 1 + (5387235549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2290595001/10000000000 : ℝ)^8239 ≤ (7033758211633/50000000000000 : ℝ)^6191 := by
    have hnat : (2290595001 : ℕ)^8239*50000000000000^6191 ≤ 7033758211633^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290595001 10000000000 7033758211633 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325839169/625000000 : ℝ)^8239 ≤ (42028787844457/100000000000000 : ℝ)^6191 := by
    have hnat : (325839169 : ℕ)^8239*100000000000000^6191 ≤ 42028787844457^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325839169 625000000 42028787844457 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387235549/10000000000 : ℝ)^8239 ≤ (43903695712941/100000000000000 : ℝ)^6191 := by
    have hnat : (5387235549 : ℕ)^8239*100000000000000^6191 ≤ 43903695712941^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387235549 10000000000 43903695712941 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2290595001/10000000000 : ℝ), (325839169/625000000 : ℝ), (5387235549/10000000000 : ℝ)] ![(7033758211633/50000000000000 : ℝ), (42028787844457/100000000000000 : ℝ), (43903695712941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2290595001/10000000000 : ℝ)|^8239 ≤ (7033758211633/50000000000000 : ℝ)^6191
        have hw : |(-2290595001/10000000000 : ℝ)|=(2290595001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325839169/625000000 : ℝ)|^8239 ≤ (42028787844457/100000000000000 : ℝ)^6191
        have hw : |(325839169/625000000 : ℝ)|=(325839169/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387235549/10000000000 : ℝ)|^8239 ≤ (43903695712941/100000000000000 : ℝ)^6191
        have hw : |(5387235549/10000000000 : ℝ)|=(5387235549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_9 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288172607/10000000000 : ℝ)*x 0 + (-2191531219/10000000000 : ℝ)*x 1 + (1346808849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288172607/10000000000 : ℝ)^8239 ≤ (42832591692537/100000000000000 : ℝ)^6191 := by
    have hnat : (5288172607 : ℕ)^8239*100000000000000^6191 ≤ 42832591692537^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288172607 10000000000 42832591692537 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191531219/10000000000 : ℝ)^8239 ≤ (13263714238963/100000000000000 : ℝ)^6191 := by
    have hnat : (2191531219 : ℕ)^8239*100000000000000^6191 ≤ 13263714238963^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191531219 10000000000 13263714238963 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346808849/2500000000 : ℝ)^8239 ≤ (43903694053583/100000000000000 : ℝ)^6191 := by
    have hnat : (1346808849 : ℕ)^8239*100000000000000^6191 ≤ 43903694053583^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346808849 2500000000 43903694053583 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288172607/10000000000 : ℝ), (-2191531219/10000000000 : ℝ), (1346808849/2500000000 : ℝ)] ![(42832591692537/100000000000000 : ℝ), (13263714238963/100000000000000 : ℝ), (43903694053583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288172607/10000000000 : ℝ)|^8239 ≤ (42832591692537/100000000000000 : ℝ)^6191
        have hw : |(5288172607/10000000000 : ℝ)|=(5288172607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191531219/10000000000 : ℝ)|^8239 ≤ (13263714238963/100000000000000 : ℝ)^6191
        have hw : |(-2191531219/10000000000 : ℝ)|=(2191531219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346808849/2500000000 : ℝ)|^8239 ≤ (43903694053583/100000000000000 : ℝ)^6191
        have hw : |(1346808849/2500000000 : ℝ)|=(1346808849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_10 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288172513/10000000000 : ℝ)*x 0 + (53872351/100000000 : ℝ)*x 1 + (-438306349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288172513/10000000000 : ℝ)^8239 ≤ (21416295339651/50000000000000 : ℝ)^6191 := by
    have hnat : (5288172513 : ℕ)^8239*50000000000000^6191 ≤ 21416295339651^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288172513 10000000000 21416295339651 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53872351/100000000 : ℝ)^8239 ≤ (43903690843321/100000000000000 : ℝ)^6191 := by
    have hnat : (53872351 : ℕ)^8239*100000000000000^6191 ≤ 43903690843321^6191*100000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53872351 100000000 43903690843321 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438306349/2000000000 : ℝ)^8239 ≤ (6631859237779/50000000000000 : ℝ)^6191 := by
    have hnat : (438306349 : ℕ)^8239*50000000000000^6191 ≤ 6631859237779^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438306349 2000000000 6631859237779 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288172513/10000000000 : ℝ), (53872351/100000000 : ℝ), (-438306349/2000000000 : ℝ)] ![(21416295339651/50000000000000 : ℝ), (43903690843321/100000000000000 : ℝ), (6631859237779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288172513/10000000000 : ℝ)|^8239 ≤ (21416295339651/50000000000000 : ℝ)^6191
        have hw : |(5288172513/10000000000 : ℝ)|=(5288172513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53872351/100000000 : ℝ)|^8239 ≤ (43903690843321/100000000000000 : ℝ)^6191
        have hw : |(53872351/100000000 : ℝ)|=(53872351/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438306349/2000000000 : ℝ)|^8239 ≤ (6631859237779/50000000000000 : ℝ)^6191
        have hw : |(-438306349/2000000000 : ℝ)|=(438306349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_11 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (901612813/2000000000 : ℝ)*x 0 + (2157785437/5000000000 : ℝ)*x 1 + (1078892869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901612813/2000000000 : ℝ)^8239 ≤ (34636104094409/100000000000000 : ℝ)^6191 := by
    have hnat : (901612813 : ℕ)^8239*100000000000000^6191 ≤ 34636104094409^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901612813 2000000000 34636104094409 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157785437/5000000000 : ℝ)^8239 ≤ (16340972456223/50000000000000 : ℝ)^6191 := by
    have hnat : (2157785437 : ℕ)^8239*50000000000000^6191 ≤ 16340972456223^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157785437 5000000000 16340972456223 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078892869/2500000000 : ℝ)^8239 ≤ (4085243872441/12500000000000 : ℝ)^6191 := by
    have hnat : (1078892869 : ℕ)^8239*12500000000000^6191 ≤ 4085243872441^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078892869 2500000000 4085243872441 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(901612813/2000000000 : ℝ), (2157785437/5000000000 : ℝ), (1078892869/2500000000 : ℝ)] ![(34636104094409/100000000000000 : ℝ), (16340972456223/50000000000000 : ℝ), (4085243872441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(901612813/2000000000 : ℝ)|^8239 ≤ (34636104094409/100000000000000 : ℝ)^6191
        have hw : |(901612813/2000000000 : ℝ)|=(901612813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157785437/5000000000 : ℝ)|^8239 ≤ (16340972456223/50000000000000 : ℝ)^6191
        have hw : |(2157785437/5000000000 : ℝ)|=(2157785437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078892869/2500000000 : ℝ)|^8239 ≤ (4085243872441/12500000000000 : ℝ)^6191
        have hw : |(1078892869/2500000000 : ℝ)|=(1078892869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_12 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-213848629/1000000000 : ℝ)*x 0 + (5442644597/10000000000 : ℝ)*x 1 + (5271795861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213848629/1000000000 : ℝ)^8239 ≤ (6419095455093/50000000000000 : ℝ)^6191 := by
    have hnat : (213848629 : ℕ)^8239*50000000000000^6191 ≤ 6419095455093^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213848629 1000000000 6419095455093 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442644597/10000000000 : ℝ)^8239 ≤ (44505653460841/100000000000000 : ℝ)^6191 := by
    have hnat : (5442644597 : ℕ)^8239*100000000000000^6191 ≤ 44505653460841^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442644597 10000000000 44505653460841 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271795861/10000000000 : ℝ)^8239 ≤ (42656155622543/100000000000000 : ℝ)^6191 := by
    have hnat : (5271795861 : ℕ)^8239*100000000000000^6191 ≤ 42656155622543^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271795861 10000000000 42656155622543 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213848629/1000000000 : ℝ), (5442644597/10000000000 : ℝ), (5271795861/10000000000 : ℝ)] ![(6419095455093/50000000000000 : ℝ), (44505653460841/100000000000000 : ℝ), (42656155622543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213848629/1000000000 : ℝ)|^8239 ≤ (6419095455093/50000000000000 : ℝ)^6191
        have hw : |(-213848629/1000000000 : ℝ)|=(213848629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442644597/10000000000 : ℝ)|^8239 ≤ (44505653460841/100000000000000 : ℝ)^6191
        have hw : |(5442644597/10000000000 : ℝ)|=(5442644597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271795861/10000000000 : ℝ)|^8239 ≤ (42656155622543/100000000000000 : ℝ)^6191
        have hw : |(5271795861/10000000000 : ℝ)|=(5271795861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_13 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369910627/10000000000 : ℝ)*x 0 + (-1118300359/5000000000 : ℝ)*x 1 + (5271795513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369910627/10000000000 : ℝ)^8239 ≤ (8743179723993/20000000000000 : ℝ)^6191 := by
    have hnat : (5369910627 : ℕ)^8239*20000000000000^6191 ≤ 8743179723993^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369910627 10000000000 8743179723993 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118300359/5000000000 : ℝ)^8239 ≤ (3406987374871/25000000000000 : ℝ)^6191 := by
    have hnat : (1118300359 : ℕ)^8239*25000000000000^6191 ≤ 3406987374871^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118300359 5000000000 3406987374871 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271795513/10000000000 : ℝ)^8239 ≤ (42656151875263/100000000000000 : ℝ)^6191 := by
    have hnat : (5271795513 : ℕ)^8239*100000000000000^6191 ≤ 42656151875263^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271795513 10000000000 42656151875263 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369910627/10000000000 : ℝ), (-1118300359/5000000000 : ℝ), (5271795513/10000000000 : ℝ)] ![(8743179723993/20000000000000 : ℝ), (3406987374871/25000000000000 : ℝ), (42656151875263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369910627/10000000000 : ℝ)|^8239 ≤ (8743179723993/20000000000000 : ℝ)^6191
        have hw : |(5369910627/10000000000 : ℝ)|=(5369910627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118300359/5000000000 : ℝ)|^8239 ≤ (3406987374871/25000000000000 : ℝ)^6191
        have hw : |(-1118300359/5000000000 : ℝ)|=(1118300359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271795513/10000000000 : ℝ)|^8239 ≤ (42656151875263/100000000000000 : ℝ)^6191
        have hw : |(5271795513/10000000000 : ℝ)|=(5271795513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_14 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167809689/312500000 : ℝ)*x 0 + (2635897849/5000000000 : ℝ)*x 1 + (-1118300623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167809689/312500000 : ℝ)^8239 ≤ (43715892347119/100000000000000 : ℝ)^6191 := by
    have hnat : (167809689 : ℕ)^8239*100000000000000^6191 ≤ 43715892347119^6191*312500000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167809689 312500000 43715892347119 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635897849/5000000000 : ℝ)^8239 ≤ (42656153867351/100000000000000 : ℝ)^6191 := by
    have hnat : (2635897849 : ℕ)^8239*100000000000000^6191 ≤ 42656153867351^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635897849 5000000000 42656153867351 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118300623/5000000000 : ℝ)^8239 ≤ (6813976890461/50000000000000 : ℝ)^6191 := by
    have hnat : (1118300623 : ℕ)^8239*50000000000000^6191 ≤ 6813976890461^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118300623 5000000000 6813976890461 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167809689/312500000 : ℝ), (2635897849/5000000000 : ℝ), (-1118300623/5000000000 : ℝ)] ![(43715892347119/100000000000000 : ℝ), (42656153867351/100000000000000 : ℝ), (6813976890461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167809689/312500000 : ℝ)|^8239 ≤ (43715892347119/100000000000000 : ℝ)^6191
        have hw : |(167809689/312500000 : ℝ)|=(167809689/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635897849/5000000000 : ℝ)|^8239 ≤ (42656153867351/100000000000000 : ℝ)^6191
        have hw : |(2635897849/5000000000 : ℝ)|=(2635897849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1118300623/5000000000 : ℝ)|^8239 ≤ (6813976890461/50000000000000 : ℝ)^6191
        have hw : |(-1118300623/5000000000 : ℝ)|=(1118300623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_box_15 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (850288451/2000000000 : ℝ)*x 0 + (4443878893/10000000000 : ℝ)*x 1 + (138871241/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850288451/2000000000 : ℝ)^8239 ≤ (32037237120267/100000000000000 : ℝ)^6191 := by
    have hnat : (850288451 : ℕ)^8239*100000000000000^6191 ≤ 32037237120267^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850288451 2000000000 32037237120267 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4443878893/10000000000 : ℝ)^8239 ≤ (16990688633233/50000000000000 : ℝ)^6191 := by
    have hnat : (4443878893 : ℕ)^8239*50000000000000^6191 ≤ 16990688633233^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443878893 10000000000 16990688633233 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138871241/312500000 : ℝ)^8239 ≤ (6796277120181/20000000000000 : ℝ)^6191 := by
    have hnat : (138871241 : ℕ)^8239*20000000000000^6191 ≤ 6796277120181^6191*312500000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138871241 312500000 6796277120181 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850288451/2000000000 : ℝ), (4443878893/10000000000 : ℝ), (138871241/312500000 : ℝ)] ![(32037237120267/100000000000000 : ℝ), (16990688633233/50000000000000 : ℝ), (6796277120181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850288451/2000000000 : ℝ)|^8239 ≤ (32037237120267/100000000000000 : ℝ)^6191
        have hw : |(850288451/2000000000 : ℝ)|=(850288451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4443878893/10000000000 : ℝ)|^8239 ≤ (16990688633233/50000000000000 : ℝ)^6191
        have hw : |(4443878893/10000000000 : ℝ)|=(4443878893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138871241/312500000 : ℝ)|^8239 ≤ (6796277120181/20000000000000 : ℝ)^6191
        have hw : |(138871241/312500000 : ℝ)|=(138871241/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29613/50000 : ℝ) ∧ (79509/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82907/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (4119/1024 : ℝ) ≤ (3777426882189017/25000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^4119 ≤ (3777426882189017/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1403 : ℕ)^4119*25000000000000000000^1024 ≤ 3777426882189017^1024*12500^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 3777426882189017 25000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (3777426882189017/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (4119/1024 : ℝ) ≤ (36650940456581109/100000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^4119 ≤ (36650940456581109/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4119*100000000000000000000^1024 ≤ 36650940456581109^1024*10000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 36650940456581109 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (36650940456581109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503777426882189017/12500000000000000000 : ℝ) ≤ (5000375590778993/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (12503777426882189017/12500000000000000000 : ℝ)^1024 ≤ (5000375590778993/5000000000000000 : ℝ)^4119 := by
      have hnat : (12503777426882189017 : ℕ)^1024*5000000000000000^4119 ≤ 5000375590778993^4119*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503777426882189017 12500000000000000000 5000375590778993 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375590778993/5000000000000000 : ℝ)) (X := (12503777426882189017/12500000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051760647985337177/100000000000000000000 : ℝ) ≤ (2500321635102629/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (100051760647985337177/100000000000000000000 : ℝ)^1024 ≤ (2500321635102629/2500000000000000 : ℝ)^4119 := by
      have hnat : (100051760647985337177 : ℕ)^1024*2500000000000000^4119 ≤ 2500321635102629^4119*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051760647985337177 100000000000000000000 2500321635102629 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500321635102629/2500000000000000 : ℝ)) (X := (100051760647985337177/100000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036650940456581109/50000000000000000000 : ℝ) ≤ (5000910949631523/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50036650940456581109/50000000000000000000 : ℝ)^1024 ≤ (5000910949631523/5000000000000000 : ℝ)^4119 := by
      have hnat : (50036650940456581109 : ℕ)^1024*5000000000000000^4119 ≤ 5000910949631523^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036650940456581109 50000000000000000000 5000910949631523 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000910949631523/5000000000000000 : ℝ)) (X := (50036650940456581109/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3777426882189017/25000000000000000000 : ℝ) ≤ ((6912515008166948959/6915000000000000000 : ℝ)+2*(53535885253/27660000000000 : ℝ)*(1403/12500 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (6912515008166948959/6915000000000000000 : ℝ)+2*(53535885253/27660000000000 : ℝ)*(1403/12500 : ℝ)=(5000375590778993/5000000000000000 : ℝ) by norm_num, show 1+2*(3777426882189017/25000000000000000000 : ℝ)=(12503777426882189017/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36650940456581109/100000000000000000000 : ℝ)+(3777426882189017/25000000000000000000 : ℝ) ≤ ((6912515008166948959/6915000000000000000 : ℝ)+(53535885253/27660000000000 : ℝ)*((1399/10000 : ℝ)+(1403/12500 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (6912515008166948959/6915000000000000000 : ℝ)+(53535885253/27660000000000 : ℝ)*((1399/10000 : ℝ)+(1403/12500 : ℝ))=(2500321635102629/2500000000000000 : ℝ) by norm_num, show 1+(36650940456581109/100000000000000000000 : ℝ)+(3777426882189017/25000000000000000000 : ℝ)=(100051760647985337177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36650940456581109/100000000000000000000 : ℝ) ≤ ((6912515008166948959/6915000000000000000 : ℝ)+2*(53535885253/27660000000000 : ℝ)*(1399/10000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (6912515008166948959/6915000000000000000 : ℝ)+2*(53535885253/27660000000000 : ℝ)*(1399/10000 : ℝ)=(5000910949631523/5000000000000000 : ℝ) by norm_num, show 1+2*(36650940456581109/100000000000000000000 : ℝ)=(50036650940456581109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6912515008166948959/6915000000000000000 : ℝ)*(X 1 0+X 2 0)+(53535885253/27660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6912515008166948959/6915000000000000000 : ℝ)) (alpha := (53535885253/27660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6912515008166948959/6915000000000000000 : ℝ)*(X 0 1+X 2 1)+(53535885253/27660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6912515008166948959/6915000000000000000 : ℝ)) (alpha := (53535885253/27660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6912515008166948959/6915000000000000000 : ℝ)*(X 0 2+X 1 2)+(53535885253/27660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6912515008166948959/6915000000000000000 : ℝ)) (alpha := (53535885253/27660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-520874133/2500000000 : ℝ)*X 0 0+(1075527491/2000000000 : ℝ)*X 0 1+(672204691/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((13237429/25000000 : ℝ)*X 1 0+(-548837297/2500000000 : ℝ)*X 1 1+(5377637533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294971693/10000000000 : ℝ)*X 2 0+(2688818751/5000000000 : ℝ)*X 2 1+(-137209319/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4486997659/10000000000 : ℝ)*X 0 0+(8449697/19531250 : ℝ)*X 0 1+(4326244939/10000000000 : ℝ)*X 0 2+(4486997659/10000000000 : ℝ)*X 1 0+(8449697/19531250 : ℝ)*X 1 1+(4326244939/10000000000 : ℝ)*X 1 2+(4486997659/10000000000 : ℝ)*X 2 0+(8449697/19531250 : ℝ)*X 2 1+(4326244939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2345202773/10000000000 : ℝ)*X 0 0+(2639892893/5000000000 : ℝ)*X 0 1+(659973179/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364255303/10000000000 : ℝ)*X 1 0+(-558385453/2500000000 : ℝ)*X 1 1+(5279785407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072850959/2000000000 : ℝ)*X 2 0+(5279785887/10000000000 : ℝ)*X 2 1+(-1116770927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269437037/10000000000 : ℝ)*X 0 0+(277187733/625000000 : ℝ)*X 0 1+(4435003429/10000000000 : ℝ)*X 0 2+(4269437037/10000000000 : ℝ)*X 1 0+(277187733/625000000 : ℝ)*X 1 1+(4435003429/10000000000 : ℝ)*X 1 2+(4269437037/10000000000 : ℝ)*X 2 0+(277187733/625000000 : ℝ)*X 2 1+(4435003429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2290595001/10000000000 : ℝ)*X 0 0+(325839169/625000000 : ℝ)*X 0 1+(5387235549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288172607/10000000000 : ℝ)*X 1 0+(-2191531219/10000000000 : ℝ)*X 1 1+(1346808849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288172513/10000000000 : ℝ)*X 2 0+(53872351/100000000 : ℝ)*X 2 1+(-438306349/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((901612813/2000000000 : ℝ)*X 0 0+(2157785437/5000000000 : ℝ)*X 0 1+(1078892869/2500000000 : ℝ)*X 0 2+(901612813/2000000000 : ℝ)*X 1 0+(2157785437/5000000000 : ℝ)*X 1 1+(1078892869/2500000000 : ℝ)*X 1 2+(901612813/2000000000 : ℝ)*X 2 0+(2157785437/5000000000 : ℝ)*X 2 1+(1078892869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-213848629/1000000000 : ℝ)*X 0 0+(5442644597/10000000000 : ℝ)*X 0 1+(5271795861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369910627/10000000000 : ℝ)*X 1 0+(-1118300359/5000000000 : ℝ)*X 1 1+(5271795513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((167809689/312500000 : ℝ)*X 2 0+(2635897849/5000000000 : ℝ)*X 2 1+(-1118300623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((850288451/2000000000 : ℝ)*X 0 0+(4443878893/10000000000 : ℝ)*X 0 1+(138871241/312500000 : ℝ)*X 0 2+(850288451/2000000000 : ℝ)*X 1 0+(4443878893/10000000000 : ℝ)*X 1 1+(138871241/312500000 : ℝ)*X 1 2+(850288451/2000000000 : ℝ)*X 2 0+(4443878893/10000000000 : ℝ)*X 2 1+(138871241/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-22409335120990481331535081803/36015625000000000000000000000 : ℝ) := by norm_num
    linear_combination (67756221/50000000000000 : ℝ)*(upper0) + (127328361/100000000000000 : ℝ)*(upper1) + (12965939/25000000000000 : ℝ)*(upper2) + (44041369/20000000000000 : ℝ)*(upper3) + (9598973454087/250000000000 : ℝ)*(major0) + (9598973454087/250000000000 : ℝ)*(major1) + (9598973454087/250000000000 : ℝ)*(major2) + (2698589667/25000000000000 : ℝ)*(sp1) + (62911429/390625000000 : ℝ)*(sp3) + (5098644006817307/100000000000000 : ℝ)*(sp4) + (5098633212458639/100000000000000 : ℝ)*(sp5) + (2549204979426507/50000000000000 : ℝ)*(sp6) + (162578689599727/6250000000000 : ℝ)*(sp7) + (234047964293/100000000000000 : ℝ)*(sp14) + (2601275138921457/100000000000000 : ℝ)*(f.failure) + (5098644006817307/100000000000000 : ℝ)*(f.sum) + (1158897857771/461000000000000000000000000 : ℝ)*base65 + (6134200542264311/576250000000000000000000000000 : ℝ)*base67 + (6572141233521811/576250000000000000000000000000 : ℝ)*base69 + (3844340080185561/576250000000000000000000000000 : ℝ)*base71 + (80816658971/23050000000000000000000000 : ℝ)*base73 + (4094326455680561/576250000000000000000000000000 : ℝ)*base75 + (5701088587439311/576250000000000000000000000000 : ℝ)*base77 + (9060267446726811/576250000000000000000000000000 : ℝ)*base79 + (296906334317/46100000000000000000000000 : ℝ)*base81 + (8677833/2500000000000000000000 : ℝ)*base90 + (8677833/2500000000000000000000 : ℝ)*base92 + (8677833/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29613/50000 : ℝ) ≤ (68260725552900228100787316244309/115250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19650949/100000000000000 : ℝ)*(upper0) + (8143337/5000000000000 : ℝ)*(upper2) + (46591597/100000000000000 : ℝ)*(upper3) + (104093763/50000000000000 : ℝ)*(upper4) + (22836503/25000000000000 : ℝ)*(upper5) + (3902145614041349/100000000000000 : ℝ)*(major0) + (3902145614041349/100000000000000 : ℝ)*(major1) + (3902145614041349/100000000000000 : ℝ)*(major2) + (5140892203602177/100000000000000 : ℝ)*(sp0) + (5140846338027061/100000000000000 : ℝ)*(sp1) + (5140842677800793/100000000000000 : ℝ)*(sp2) + (2643656226055953/100000000000000 : ℝ)*(sp3) + (11466393779/25000000000000 : ℝ)*(sp9) + (6190725173/12500000000000 : ℝ)*(sp10) + (2643656226055953/100000000000000 : ℝ)*(f.failure) + (5140892203602177/100000000000000 : ℝ)*(f.sum) + (294261424529/172875000000000000000000000 : ℝ)*base66 + (3511974479447744309/691500000000000000000000000000000 : ℝ)*base68 + (2284071064218255691/691500000000000000000000000000000 : ℝ)*base69 + (3481224412104255691/691500000000000000000000000000000 : ℝ)*base71 + (73473606008863/1383000000000000000000000000 : ℝ)*base74 + (4083638967058755691/691500000000000000000000000000000 : ℝ)*base75 + (2903410103800755691/691500000000000000000000000000000 : ℝ)*base77 + (28323532432564244309/691500000000000000000000000000000 : ℝ)*base80 + (1774251934913/345750000000000000000000000 : ℝ)*base81 + (4387543/2500000000000000000000 : ℝ)*base89 + (4387543/2500000000000000000000 : ℝ)*base91 + (4387543/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79509/100000 : ℝ) ≤ (22909251994047110310211893715143/28812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48157711/12500000000000 : ℝ)*(upper0) + (3421697/100000000000000 : ℝ)*(lower1) + (14564461/20000000000000 : ℝ)*(upper2) + (3684491/3125000000000 : ℝ)*(lower3) + (310224229/50000000000000 : ℝ)*(lower5) + (2185200318749277/50000000000000 : ℝ)*(major0) + (2185200318749277/50000000000000 : ℝ)*(major1) + (2185200318749277/50000000000000 : ℝ)*(major2) + (1102534247/4000000000000 : ℝ)*(sp1) + (7995893919/25000000000000 : ℝ)*(sp3) + (57534041272583/1000000000000 : ℝ)*(sp8) + (46027012511217/800000000000 : ℝ)*(sp9) + (57534041272583/1000000000000 : ℝ)*(sp10) + (1480430664803733/50000000000000 : ℝ)*(sp11) + (1480446656591571/50000000000000 : ℝ)*(f.failure) + (57534041272583/1000000000000 : ℝ)*(f.sum) + (67308945827/23050000000000000000000000 : ℝ)*base65 + (257348202508800881/115250000000000000000000000000000 : ℝ)*base67 + (311633410104199119/115250000000000000000000000000000 : ℝ)*base70 + (1091521097881449119/115250000000000000000000000000000 : ℝ)*base72 + (1734339257401/461000000000000000000000000 : ℝ)*base73 + (558455815247949119/115250000000000000000000000000000 : ℝ)*base76 + (670557567762699119/115250000000000000000000000000000 : ℝ)*base78 + (318980951191199119/115250000000000000000000000000000 : ℝ)*base80 + (1405130580587/230500000000000000000000000 : ℝ)*base81 + (9190299/1250000000000000000000 : ℝ)*base90 + (9190299/1250000000000000000000 : ℝ)*base92 + (9190299/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82907/100000 : ℝ) ≤ (-11943386867357066962991937/14406250000000000000000000 : ℝ) := by norm_num
    linear_combination (19325751/25000000000000 : ℝ)*(lower0) + (111992817/100000000000000 : ℝ)*(lower3) + (522546439/100000000000000 : ℝ)*(lower4) + (2202441456302061/50000000000000 : ℝ)*(major0) + (2202441456302061/50000000000000 : ℝ)*(major1) + (2202441456302061/50000000000000 : ℝ)*(major2) + (2335806083/50000000000000 : ℝ)*(sp4) + (23887445141/20000000000000 : ℝ)*(sp5) + (13880618537/3125000000000 : ℝ)*(sp6) + (284633825973/100000000000000 : ℝ)*(sp7) + (2926570626375261/50000000000000 : ℝ)*(sp12) + (2926513243568491/50000000000000 : ℝ)*(sp13) + (182896929517797/3125000000000 : ℝ)*(sp14) + (1491985000818367/50000000000000 : ℝ)*(sp15) + (1492127317731353/50000000000000 : ℝ)*(f.failure) + (91455405068167/1562500000000 : ℝ)*(f.sum) + (1201306177431/461000000000000000000000000 : ℝ)*base66 + (185354824008415167/115250000000000000000000000000000 : ℝ)*base68 + (669586027319165167/115250000000000000000000000000000 : ℝ)*base70 + (543250652935584833/115250000000000000000000000000000 : ℝ)*base71 + (16426330607/7203125000000000000000000 : ℝ)*base74 + (1750399641389084833/115250000000000000000000000000000 : ℝ)*base75 + (176326799045165167/115250000000000000000000000000000 : ℝ)*base78 + (4677332427169084833/115250000000000000000000000000000 : ℝ)*base79 + (3366807315583/461000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (18275057/1250000000000000000000 : ℝ)*base90 + (18275057/1250000000000000000000 : ℝ)*base92 + (18275057/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1046_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29613/50000 : ℝ) else (79509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82907/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1046_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1046_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29613/50000 : ℝ) else (79509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82907/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1046_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1046_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29613/50000 : ℝ) else (79509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82907/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

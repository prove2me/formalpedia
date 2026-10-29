-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:45.429636+00:00
-- url     : https://prove2.me/submissions/95c81795-0606-47a9-b3ae-8e0c5acad8da

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
theorem support_rectangle_w1491_s3_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898852781/10000000000 : ℝ)*x 0 + (1088027839/2000000000 : ℝ)*x 1 + (2606382649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898852781/10000000000 : ℝ)^4479 ≤ (2901276170439/25000000000000 : ℝ)^3455 := by
    have hnat : (1898852781 : ℕ)^4479*25000000000000^3455 ≤ 2901276170439^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898852781 10000000000 2901276170439 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088027839/2000000000 : ℝ)^4479 ≤ (11355063642729/25000000000000 : ℝ)^3455 := by
    have hnat : (1088027839 : ℕ)^4479*25000000000000^3455 ≤ 11355063642729^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088027839 2000000000 11355063642729 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606382649/5000000000 : ℝ)^4479 ≤ (21487320368883/50000000000000 : ℝ)^3455 := by
    have hnat : (2606382649 : ℕ)^4479*50000000000000^3455 ≤ 21487320368883^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606382649 5000000000 21487320368883 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898852781/10000000000 : ℝ), (1088027839/2000000000 : ℝ), (2606382649/5000000000 : ℝ)] ![(2901276170439/25000000000000 : ℝ), (11355063642729/25000000000000 : ℝ), (21487320368883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898852781/10000000000 : ℝ)|^4479 ≤ (2901276170439/25000000000000 : ℝ)^3455
        have hw : |(-1898852781/10000000000 : ℝ)|=(1898852781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088027839/2000000000 : ℝ)|^4479 ≤ (11355063642729/25000000000000 : ℝ)^3455
        have hw : |(1088027839/2000000000 : ℝ)|=(1088027839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606382649/5000000000 : ℝ)|^4479 ≤ (21487320368883/50000000000000 : ℝ)^3455
        have hw : |(2606382649/5000000000 : ℝ)|=(2606382649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353816199/10000000000 : ℝ)*x 0 + (-2015453899/10000000000 : ℝ)*x 1 + (5212765329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353816199/10000000000 : ℝ)^4479 ≤ (22244066239079/50000000000000 : ℝ)^3455 := by
    have hnat : (5353816199 : ℕ)^4479*50000000000000^3455 ≤ 22244066239079^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353816199 10000000000 22244066239079 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015453899/10000000000 : ℝ)^4479 ≤ (6268613220799/50000000000000 : ℝ)^3455 := by
    have hnat : (2015453899 : ℕ)^4479*50000000000000^3455 ≤ 6268613220799^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015453899 10000000000 6268613220799 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212765329/10000000000 : ℝ)^4479 ≤ (42974641069079/100000000000000 : ℝ)^3455 := by
    have hnat : (5212765329 : ℕ)^4479*100000000000000^3455 ≤ 42974641069079^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212765329 10000000000 42974641069079 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353816199/10000000000 : ℝ), (-2015453899/10000000000 : ℝ), (5212765329/10000000000 : ℝ)] ![(22244066239079/50000000000000 : ℝ), (6268613220799/50000000000000 : ℝ), (42974641069079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353816199/10000000000 : ℝ)|^4479 ≤ (22244066239079/50000000000000 : ℝ)^3455
        have hw : |(5353816199/10000000000 : ℝ)|=(5353816199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015453899/10000000000 : ℝ)|^4479 ≤ (6268613220799/50000000000000 : ℝ)^3455
        have hw : |(-2015453899/10000000000 : ℝ)|=(2015453899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212765329/10000000000 : ℝ)|^4479 ≤ (42974641069079/100000000000000 : ℝ)^3455
        have hw : |(5212765329/10000000000 : ℝ)|=(5212765329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353816307/10000000000 : ℝ)*x 0 + (2606382651/5000000000 : ℝ)*x 1 + (-201545379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353816307/10000000000 : ℝ)^4479 ≤ (44488133641581/100000000000000 : ℝ)^3455 := by
    have hnat : (5353816307 : ℕ)^4479*100000000000000^3455 ≤ 44488133641581^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353816307 10000000000 44488133641581 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606382651/5000000000 : ℝ)^4479 ≤ (10743660195129/25000000000000 : ℝ)^3455 := by
    have hnat : (2606382651 : ℕ)^4479*25000000000000^3455 ≤ 10743660195129^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606382651 5000000000 10743660195129 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201545379/1000000000 : ℝ)^4479 ≤ (62686127813/500000000000 : ℝ)^3455 := by
    have hnat : (201545379 : ℕ)^4479*500000000000^3455 ≤ 62686127813^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201545379 1000000000 62686127813 500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353816307/10000000000 : ℝ), (2606382651/5000000000 : ℝ), (-201545379/1000000000 : ℝ)] ![(44488133641581/100000000000000 : ℝ), (10743660195129/25000000000000 : ℝ), (62686127813/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353816307/10000000000 : ℝ)|^4479 ≤ (44488133641581/100000000000000 : ℝ)^3455
        have hw : |(5353816307/10000000000 : ℝ)|=(5353816307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606382651/5000000000 : ℝ)|^4479 ≤ (10743660195129/25000000000000 : ℝ)^3455
        have hw : |(2606382651/5000000000 : ℝ)|=(2606382651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201545379/1000000000 : ℝ)|^4479 ≤ (62686127813/500000000000 : ℝ)^3455
        have hw : |(-201545379/1000000000 : ℝ)|=(201545379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855851091/2000000000 : ℝ)*x 0 + (4031782501/10000000000 : ℝ)*x 1 + (4539751209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855851091/2000000000 : ℝ)^4479 ≤ (16637281724197/50000000000000 : ℝ)^3455 := by
    have hnat : (855851091 : ℕ)^4479*50000000000000^3455 ≤ 16637281724197^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855851091 2000000000 16637281724197 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031782501/10000000000 : ℝ)^4479 ≤ (30801616836283/100000000000000 : ℝ)^3455 := by
    have hnat : (4031782501 : ℕ)^4479*100000000000000^3455 ≤ 30801616836283^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031782501 10000000000 30801616836283 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4539751209/10000000000 : ℝ)^4479 ≤ (17961909850207/50000000000000 : ℝ)^3455 := by
    have hnat : (4539751209 : ℕ)^4479*50000000000000^3455 ≤ 17961909850207^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539751209 10000000000 17961909850207 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855851091/2000000000 : ℝ), (4031782501/10000000000 : ℝ), (4539751209/10000000000 : ℝ)] ![(16637281724197/50000000000000 : ℝ), (30801616836283/100000000000000 : ℝ), (17961909850207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855851091/2000000000 : ℝ)|^4479 ≤ (16637281724197/50000000000000 : ℝ)^3455
        have hw : |(855851091/2000000000 : ℝ)|=(855851091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031782501/10000000000 : ℝ)|^4479 ≤ (30801616836283/100000000000000 : ℝ)^3455
        have hw : |(4031782501/10000000000 : ℝ)|=(4031782501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4539751209/10000000000 : ℝ)|^4479 ≤ (17961909850207/50000000000000 : ℝ)^3455
        have hw : |(4539751209/10000000000 : ℝ)|=(4539751209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-474721369/2500000000 : ℝ)*x 0 + (5213972797/10000000000 : ℝ)*x 1 + (339932679/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474721369/2500000000 : ℝ)^4479 ≤ (11605363725571/100000000000000 : ℝ)^3455 := by
    have hnat : (474721369 : ℕ)^4479*100000000000000^3455 ≤ 11605363725571^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474721369 2500000000 11605363725571 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213972797/10000000000 : ℝ)^4479 ≤ (42987546355017/100000000000000 : ℝ)^3455 := by
    have hnat : (5213972797 : ℕ)^4479*100000000000000^3455 ≤ 42987546355017^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213972797 10000000000 42987546355017 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339932679/625000000 : ℝ)^4479 ≤ (22703544950903/50000000000000 : ℝ)^3455 := by
    have hnat : (339932679 : ℕ)^4479*50000000000000^3455 ≤ 22703544950903^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339932679 625000000 22703544950903 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474721369/2500000000 : ℝ), (5213972797/10000000000 : ℝ), (339932679/625000000 : ℝ)] ![(11605363725571/100000000000000 : ℝ), (42987546355017/100000000000000 : ℝ), (22703544950903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474721369/2500000000 : ℝ)|^4479 ≤ (11605363725571/100000000000000 : ℝ)^3455
        have hw : |(-474721369/2500000000 : ℝ)|=(474721369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213972797/10000000000 : ℝ)|^4479 ≤ (42987546355017/100000000000000 : ℝ)^3455
        have hw : |(5213972797/10000000000 : ℝ)|=(5213972797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339932679/625000000 : ℝ)|^4479 ≤ (22703544950903/50000000000000 : ℝ)^3455
        have hw : |(339932679/625000000 : ℝ)|=(339932679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661790303/1250000000 : ℝ)*x 0 + (-1789296477/10000000000 : ℝ)*x 1 + (339932677/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661790303/1250000000 : ℝ)^4479 ≤ (10962074510007/25000000000000 : ℝ)^3455 := by
    have hnat : (661790303 : ℕ)^4479*25000000000000^3455 ≤ 10962074510007^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661790303 1250000000 10962074510007 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789296477/10000000000 : ℝ)^4479 ≤ (5372306197381/50000000000000 : ℝ)^3455 := by
    have hnat : (1789296477 : ℕ)^4479*50000000000000^3455 ≤ 5372306197381^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789296477 10000000000 5372306197381 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339932677/625000000 : ℝ)^4479 ≤ (45407089555473/100000000000000 : ℝ)^3455 := by
    have hnat : (339932677 : ℕ)^4479*100000000000000^3455 ≤ 45407089555473^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339932677 625000000 45407089555473 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661790303/1250000000 : ℝ), (-1789296477/10000000000 : ℝ), (339932677/625000000 : ℝ)] ![(10962074510007/25000000000000 : ℝ), (5372306197381/50000000000000 : ℝ), (45407089555473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661790303/1250000000 : ℝ)|^4479 ≤ (10962074510007/25000000000000 : ℝ)^3455
        have hw : |(661790303/1250000000 : ℝ)|=(661790303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1789296477/10000000000 : ℝ)|^4479 ≤ (5372306197381/50000000000000 : ℝ)^3455
        have hw : |(-1789296477/10000000000 : ℝ)|=(1789296477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339932677/625000000 : ℝ)|^4479 ≤ (45407089555473/100000000000000 : ℝ)^3455
        have hw : |(339932677/625000000 : ℝ)|=(339932677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211772893/400000000 : ℝ)*x 0 + (2719461453/5000000000 : ℝ)*x 1 + (-1789296509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211772893/400000000 : ℝ)^4479 ≤ (10962074244271/25000000000000 : ℝ)^3455 := by
    have hnat : (211772893 : ℕ)^4479*25000000000000^3455 ≤ 10962074244271^3455*400000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211772893 400000000 10962074244271 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719461453/5000000000 : ℝ)^4479 ≤ (45407090356367/100000000000000 : ℝ)^3455 := by
    have hnat : (2719461453 : ℕ)^4479*100000000000000^3455 ≤ 45407090356367^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719461453 5000000000 45407090356367 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789296509/10000000000 : ℝ)^4479 ≤ (335769145121/3125000000000 : ℝ)^3455 := by
    have hnat : (1789296509 : ℕ)^4479*3125000000000^3455 ≤ 335769145121^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789296509 10000000000 335769145121 3125000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211772893/400000000 : ℝ), (2719461453/5000000000 : ℝ), (-1789296509/10000000000 : ℝ)] ![(10962074244271/25000000000000 : ℝ), (45407090356367/100000000000000 : ℝ), (335769145121/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211772893/400000000 : ℝ)|^4479 ≤ (10962074244271/25000000000000 : ℝ)^3455
        have hw : |(211772893/400000000 : ℝ)|=(211772893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719461453/5000000000 : ℝ)|^4479 ≤ (45407090356367/100000000000000 : ℝ)^3455
        have hw : |(2719461453/5000000000 : ℝ)|=(2719461453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789296509/10000000000 : ℝ)|^4479 ≤ (335769145121/3125000000000 : ℝ)^3455
        have hw : |(-1789296509/10000000000 : ℝ)|=(1789296509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s3_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279329477/10000000000 : ℝ)*x 0 + (907410887/2000000000 : ℝ)*x 1 + (80689999/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279329477/10000000000 : ℝ)^4479 ≤ (16637654810321/50000000000000 : ℝ)^3455 := by
    have hnat : (4279329477 : ℕ)^4479*50000000000000^3455 ≤ 16637654810321^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279329477 10000000000 16637654810321 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907410887/2000000000 : ℝ)^4479 ≤ (35896157305319/100000000000000 : ℝ)^3455 := by
    have hnat : (907410887 : ℕ)^4479*100000000000000^3455 ≤ 35896157305319^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907410887 2000000000 35896157305319 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80689999/200000000 : ℝ)^4479 ≤ (30828533064409/100000000000000 : ℝ)^3455 := by
    have hnat : (80689999 : ℕ)^4479*100000000000000^3455 ≤ 30828533064409^3455*200000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80689999 200000000 30828533064409 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279329477/10000000000 : ℝ), (907410887/2000000000 : ℝ), (80689999/200000000 : ℝ)] ![(16637654810321/50000000000000 : ℝ), (35896157305319/100000000000000 : ℝ), (30828533064409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279329477/10000000000 : ℝ)|^4479 ≤ (16637654810321/50000000000000 : ℝ)^3455
        have hw : |(4279329477/10000000000 : ℝ)|=(4279329477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907410887/2000000000 : ℝ)|^4479 ≤ (35896157305319/100000000000000 : ℝ)^3455
        have hw : |(907410887/2000000000 : ℝ)|=(907410887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80689999/200000000 : ℝ)|^4479 ≤ (30828533064409/100000000000000 : ℝ)^3455
        have hw : |(80689999/200000000 : ℝ)|=(80689999/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (336/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3113/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5139/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5139/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5139/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5139/50000 : ℝ) ^ (4477/1024 : ℝ) ≤ (2393122812554101/50000000000000000000 : ℝ) := by
    have hpowers : (5139/50000 : ℝ)^4477 ≤ (2393122812554101/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5139 : ℕ)^4477*50000000000000000000^1024 ≤ 2393122812554101^1024*50000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5139 50000 2393122812554101 50000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5139/50000 : ℝ)) (X := (2393122812554101/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8041/50000 : ℝ) ^ (4477/1024 : ℝ) ≤ (33889325753538121/100000000000000000000 : ℝ) := by
    have hpowers : (8041/50000 : ℝ)^4477 ≤ (33889325753538121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8041 : ℕ)^4477*100000000000000000000^1024 ≤ 33889325753538121^1024*50000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8041 50000 33889325753538121 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8041/50000 : ℝ)) (X := (33889325753538121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002393122812554101/25000000000000000000 : ℝ) ≤ (10000218938333929/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (25002393122812554101/25000000000000000000 : ℝ)^1024 ≤ (10000218938333929/10000000000000000 : ℝ)^4477 := by
      have hnat : (25002393122812554101 : ℕ)^1024*10000000000000000^4477 ≤ 10000218938333929^4477*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002393122812554101 25000000000000000000 10000218938333929 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000218938333929/10000000000000000 : ℝ)) (X := (25002393122812554101/25000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038675571378646323/100000000000000000000 : ℝ) ≤ (10000884473523147/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (100038675571378646323/100000000000000000000 : ℝ)^1024 ≤ (10000884473523147/10000000000000000 : ℝ)^4477 := by
      have hnat : (100038675571378646323 : ℕ)^1024*10000000000000000^4477 ≤ 10000884473523147^4477*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038675571378646323 100000000000000000000 10000884473523147 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000884473523147/10000000000000000 : ℝ)) (X := (100038675571378646323/100000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033889325753538121/50000000000000000000 : ℝ) ≤ (2000310001742473/2000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50033889325753538121/50000000000000000000 : ℝ)^1024 ≤ (2000310001742473/2000000000000000 : ℝ)^4477 := by
      have hnat : (50033889325753538121 : ℕ)^1024*2000000000000000^4477 ≤ 2000310001742473^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033889325753538121 50000000000000000000 2000310001742473 2000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000310001742473/2000000000000000 : ℝ)) (X := (50033889325753538121/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2393122812554101/50000000000000000000 : ℝ) ≤ ((14506897494185139677/14510000000000000000 : ℝ)+2*(332767594609/290200000000000 : ℝ)*(5139/50000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (14506897494185139677/14510000000000000000 : ℝ)+2*(332767594609/290200000000000 : ℝ)*(5139/50000 : ℝ)=(10000218938333929/10000000000000000 : ℝ) by norm_num, show 1+2*(2393122812554101/50000000000000000000 : ℝ)=(25002393122812554101/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33889325753538121/100000000000000000000 : ℝ)+(2393122812554101/50000000000000000000 : ℝ) ≤ ((14506897494185139677/14510000000000000000 : ℝ)+(332767594609/290200000000000 : ℝ)*((8041/50000 : ℝ)+(5139/50000 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (14506897494185139677/14510000000000000000 : ℝ)+(332767594609/290200000000000 : ℝ)*((8041/50000 : ℝ)+(5139/50000 : ℝ))=(10000884473523147/10000000000000000 : ℝ) by norm_num, show 1+(33889325753538121/100000000000000000000 : ℝ)+(2393122812554101/50000000000000000000 : ℝ)=(100038675571378646323/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33889325753538121/100000000000000000000 : ℝ) ≤ ((14506897494185139677/14510000000000000000 : ℝ)+2*(332767594609/290200000000000 : ℝ)*(8041/50000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (14506897494185139677/14510000000000000000 : ℝ)+2*(332767594609/290200000000000 : ℝ)*(8041/50000 : ℝ)=(2000310001742473/2000000000000000 : ℝ) by norm_num, show 1+2*(33889325753538121/100000000000000000000 : ℝ)=(50033889325753538121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14506897494185139677/14510000000000000000 : ℝ)*(X 1 0+X 2 0)+(332767594609/290200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5139/50000 : ℝ)) (hi := (8041/50000 : ℝ)) (c := (14506897494185139677/14510000000000000000 : ℝ)) (alpha := (332767594609/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14506897494185139677/14510000000000000000 : ℝ)*(X 0 1+X 2 1)+(332767594609/290200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5139/50000 : ℝ)) (hi := (8041/50000 : ℝ)) (c := (14506897494185139677/14510000000000000000 : ℝ)) (alpha := (332767594609/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14506897494185139677/14510000000000000000 : ℝ)*(X 0 2+X 1 2)+(332767594609/290200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5139/50000 : ℝ)) (hi := (8041/50000 : ℝ)) (c := (14506897494185139677/14510000000000000000 : ℝ)) (alpha := (332767594609/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1898852781/10000000000 : ℝ)*X 0 0+(1088027839/2000000000 : ℝ)*X 0 1+(2606382649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353816199/10000000000 : ℝ)*X 1 0+(-2015453899/10000000000 : ℝ)*X 1 1+(5212765329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353816307/10000000000 : ℝ)*X 2 0+(2606382651/5000000000 : ℝ)*X 2 1+(-201545379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855851091/2000000000 : ℝ)*X 0 0+(4031782501/10000000000 : ℝ)*X 0 1+(4539751209/10000000000 : ℝ)*X 0 2+(855851091/2000000000 : ℝ)*X 1 0+(4031782501/10000000000 : ℝ)*X 1 1+(4539751209/10000000000 : ℝ)*X 1 2+(855851091/2000000000 : ℝ)*X 2 0+(4031782501/10000000000 : ℝ)*X 2 1+(4539751209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-474721369/2500000000 : ℝ)*X 0 0+(5213972797/10000000000 : ℝ)*X 0 1+(339932679/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661790303/1250000000 : ℝ)*X 1 0+(-1789296477/10000000000 : ℝ)*X 1 1+(339932677/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211772893/400000000 : ℝ)*X 2 0+(2719461453/5000000000 : ℝ)*X 2 1+(-1789296509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279329477/10000000000 : ℝ)*X 0 0+(907410887/2000000000 : ℝ)*X 0 1+(80689999/200000000 : ℝ)*X 0 2+(4279329477/10000000000 : ℝ)*X 1 0+(907410887/2000000000 : ℝ)*X 1 1+(80689999/200000000 : ℝ)*X 1 2+(4279329477/10000000000 : ℝ)*X 2 0+(907410887/2000000000 : ℝ)*X 2 1+(80689999/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1978292497287990393315182277/362750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1947035211/100000000000000 : ℝ)*(base19) + (352018631/20000000000000 : ℝ)*(base23) + (270263607/100000000000000 : ℝ)*(upper3) + (147584809/100000000000000 : ℝ)*(upper4) + (189980643/100000000000000 : ℝ)*(upper5) + (1591687403728733/50000000000000 : ℝ)*(major0) + (1591687403728733/50000000000000 : ℝ)*(major1) + (1591687403728733/50000000000000 : ℝ)*(major2) + (1099517711679957/25000000000000 : ℝ)*(sp0) + (2199049383279283/50000000000000 : ℝ)*(sp1) + (2199049476750311/50000000000000 : ℝ)*(sp2) + (196863600135329/10000000000000 : ℝ)*(sp3) + (597337479/2000000000000 : ℝ)*(sp4) + (1271818127/10000000000000 : ℝ)*(sp7) + (12304054497091/625000000000 : ℝ)*(f.failure) + (2199050356796889/50000000000000 : ℝ)*(f.sum) + (45969584874037/7255000000000000000000000000 : ℝ)*base65 + (2972145935818089241/725500000000000000000000000000000 : ℝ)*base67 + (4816733773733910759/725500000000000000000000000000000 : ℝ)*base70 + (6075257420406089241/725500000000000000000000000000000 : ℝ)*base71 + (34216042072367/7255000000000000000000000000 : ℝ)*base73 + (3441792777818910759/725500000000000000000000000000000 : ℝ)*base76 + (2690631372246089241/725500000000000000000000000000000 : ℝ)*base77 + (7627954230551089241/725500000000000000000000000000000 : ℝ)*base79 + (30865986125753/7255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (368223/62500000000000000000 : ℝ)*base90 + (368223/62500000000000000000 : ℝ)*base92 + (368223/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (404825814605392131712684389/45343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379562519/25000000000000 : ℝ)*(base19) + (1577109819/100000000000000 : ℝ)*(base23) + (181106111/100000000000000 : ℝ)*(upper3) + (67265669/100000000000000 : ℝ)*(lower4) + (84016687/50000000000000 : ℝ)*(upper5) + (201101968041181/6250000000000 : ℝ)*(major0) + (201101968041181/6250000000000 : ℝ)*(major1) + (201101968041181/6250000000000 : ℝ)*(major2) + (10991324299/50000000000000 : ℝ)*(sp1) + (728484311/3125000000000 : ℝ)*(sp2) + (2222714546643743/50000000000000 : ℝ)*(sp4) + (1111351398097203/25000000000000 : ℝ)*(sp5) + (889080840935943/20000000000000 : ℝ)*(sp6) + (497458396608161/25000000000000 : ℝ)*(sp7) + (497458396608161/25000000000000 : ℝ)*(f.failure) + (2222714546643743/50000000000000 : ℝ)*(f.sum) + (6211135712393/1813750000000000000000000000 : ℝ)*base65 + (394270133898113537/90687500000000000000000000000000 : ℝ)*base67 + (428714686422011463/90687500000000000000000000000000 : ℝ)*base70 + (407300839760863537/90687500000000000000000000000000 : ℝ)*base71 + (4112092029131/3627500000000000000000000000 : ℝ)*base73 + (403552026817136463/90687500000000000000000000000000 : ℝ)*base76 + (532587312423426037/90687500000000000000000000000000 : ℝ)*base77 + (500175454188613537/90687500000000000000000000000000 : ℝ)*base79 + (11153468019343/7255000000000000000000000000 : ℝ)*base82 + (2847067/2500000000000000000000 : ℝ)*base89 + (2847067/2500000000000000000000 : ℝ)*base91 + (2847067/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1491_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3113/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1491_s4_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118713119/625000000 : ℝ)*x 0 + (1359129993/2500000000 : ℝ)*x 1 + (2608008457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118713119/625000000 : ℝ)^4479 ≤ (5804759485299/50000000000000 : ℝ)^3455 := by
    have hnat : (118713119 : ℕ)^4479*50000000000000^3455 ≤ 5804759485299^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118713119 625000000 5804759485299 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359129993/2500000000 : ℝ)^4479 ≤ (1815243413469/4000000000000 : ℝ)^3455 := by
    have hnat : (1359129993 : ℕ)^4479*4000000000000^3455 ≤ 1815243413469^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359129993 2500000000 1815243413469 4000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608008457/5000000000 : ℝ)^4479 ≤ (43009395673011/100000000000000 : ℝ)^3455 := by
    have hnat : (2608008457 : ℕ)^4479*100000000000000^3455 ≤ 43009395673011^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608008457 5000000000 43009395673011 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118713119/625000000 : ℝ), (1359129993/2500000000 : ℝ), (2608008457/5000000000 : ℝ)] ![(5804759485299/50000000000000 : ℝ), (1815243413469/4000000000000 : ℝ), (43009395673011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118713119/625000000 : ℝ)|^4479 ≤ (5804759485299/50000000000000 : ℝ)^3455
        have hw : |(-118713119/625000000 : ℝ)|=(118713119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359129993/2500000000 : ℝ)|^4479 ≤ (1815243413469/4000000000000 : ℝ)^3455
        have hw : |(1359129993/2500000000 : ℝ)|=(1359129993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608008457/5000000000 : ℝ)|^4479 ≤ (43009395673011/100000000000000 : ℝ)^3455
        have hw : |(2608008457/5000000000 : ℝ)|=(2608008457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338218387/2500000000 : ℝ)*x 0 + (-2012402391/10000000000 : ℝ)*x 1 + (5216017123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338218387/2500000000 : ℝ)^4479 ≤ (11119494525023/25000000000000 : ℝ)^3455 := by
    have hnat : (1338218387 : ℕ)^4479*25000000000000^3455 ≤ 11119494525023^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338218387 2500000000 11119494525023 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012402391/10000000000 : ℝ)^4479 ≤ (12512623975787/100000000000000 : ℝ)^3455 := by
    have hnat : (2012402391 : ℕ)^4479*100000000000000^3455 ≤ 12512623975787^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012402391 10000000000 12512623975787 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216017123/10000000000 : ℝ)^4479 ≤ (10752349476779/25000000000000 : ℝ)^3455 := by
    have hnat : (5216017123 : ℕ)^4479*25000000000000^3455 ≤ 10752349476779^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216017123 10000000000 10752349476779 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338218387/2500000000 : ℝ), (-2012402391/10000000000 : ℝ), (5216017123/10000000000 : ℝ)] ![(11119494525023/25000000000000 : ℝ), (12512623975787/100000000000000 : ℝ), (10752349476779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338218387/2500000000 : ℝ)|^4479 ≤ (11119494525023/25000000000000 : ℝ)^3455
        have hw : |(1338218387/2500000000 : ℝ)|=(1338218387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2012402391/10000000000 : ℝ)|^4479 ≤ (12512623975787/100000000000000 : ℝ)^3455
        have hw : |(-2012402391/10000000000 : ℝ)|=(2012402391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216017123/10000000000 : ℝ)|^4479 ≤ (10752349476779/25000000000000 : ℝ)^3455
        have hw : |(5216017123/10000000000 : ℝ)|=(5216017123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676436739/5000000000 : ℝ)*x 0 + (5216016769/10000000000 : ℝ)*x 1 + (-1006201477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676436739/5000000000 : ℝ)^4479 ≤ (44477977346061/100000000000000 : ℝ)^3455 := by
    have hnat : (2676436739 : ℕ)^4479*100000000000000^3455 ≤ 44477977346061^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676436739 5000000000 44477977346061 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216016769/10000000000 : ℝ)^4479 ≤ (21504697061517/50000000000000 : ℝ)^3455 := by
    have hnat : (5216016769 : ℕ)^4479*50000000000000^3455 ≤ 21504697061517^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216016769 10000000000 21504697061517 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006201477/5000000000 : ℝ)^4479 ≤ (12512628513897/100000000000000 : ℝ)^3455 := by
    have hnat : (1006201477 : ℕ)^4479*100000000000000^3455 ≤ 12512628513897^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006201477 5000000000 12512628513897 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676436739/5000000000 : ℝ), (5216016769/10000000000 : ℝ), (-1006201477/5000000000 : ℝ)] ![(44477977346061/100000000000000 : ℝ), (21504697061517/50000000000000 : ℝ), (12512628513897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676436739/5000000000 : ℝ)|^4479 ≤ (44477977346061/100000000000000 : ℝ)^3455
        have hw : |(2676436739/5000000000 : ℝ)|=(2676436739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216016769/10000000000 : ℝ)|^4479 ≤ (21504697061517/50000000000000 : ℝ)^3455
        have hw : |(5216016769/10000000000 : ℝ)|=(5216016769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006201477/5000000000 : ℝ)|^4479 ≤ (12512628513897/100000000000000 : ℝ)^3455
        have hw : |(-1006201477/5000000000 : ℝ)|=(1006201477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279601609/10000000000 : ℝ)*x 0 + (2019708799/5000000000 : ℝ)*x 1 + (453203581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279601609/10000000000 : ℝ)^4479 ≤ (3327805285617/10000000000000 : ℝ)^3455 := by
    have hnat : (4279601609 : ℕ)^4479*10000000000000^3455 ≤ 3327805285617^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279601609 10000000000 3327805285617 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019708799/5000000000 : ℝ)^4479 ≤ (3859656979883/12500000000000 : ℝ)^3455 := by
    have hnat : (2019708799 : ℕ)^4479*12500000000000^3455 ≤ 3859656979883^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019708799 5000000000 3859656979883 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453203581/1000000000 : ℝ)^4479 ≤ (17922345646937/50000000000000 : ℝ)^3455 := by
    have hnat : (453203581 : ℕ)^4479*50000000000000^3455 ≤ 17922345646937^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453203581 1000000000 17922345646937 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279601609/10000000000 : ℝ), (2019708799/5000000000 : ℝ), (453203581/1000000000 : ℝ)] ![(3327805285617/10000000000000 : ℝ), (3859656979883/12500000000000 : ℝ), (17922345646937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279601609/10000000000 : ℝ)|^4479 ≤ (3327805285617/10000000000000 : ℝ)^3455
        have hw : |(4279601609/10000000000 : ℝ)|=(4279601609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019708799/5000000000 : ℝ)|^4479 ≤ (3859656979883/12500000000000 : ℝ)^3455
        have hw : |(2019708799/5000000000 : ℝ)|=(2019708799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453203581/1000000000 : ℝ)|^4479 ≤ (17922345646937/50000000000000 : ℝ)^3455
        have hw : |(453203581/1000000000 : ℝ)|=(453203581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899440243/10000000000 : ℝ)*x 0 + (5217152703/10000000000 : ℝ)*x 1 + (21741503/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899440243/10000000000 : ℝ)^4479 ≤ (5804879684293/50000000000000 : ℝ)^3455 := by
    have hnat : (1899440243 : ℕ)^4479*50000000000000^3455 ≤ 5804879684293^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899440243 10000000000 5804879684293 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217152703/10000000000 : ℝ)^4479 ≤ (43021537080397/100000000000000 : ℝ)^3455 := by
    have hnat : (5217152703 : ℕ)^4479*100000000000000^3455 ≤ 43021537080397^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217152703 10000000000 43021537080397 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21741503/40000000 : ℝ)^4479 ≤ (45368703540607/100000000000000 : ℝ)^3455 := by
    have hnat : (21741503 : ℕ)^4479*100000000000000^3455 ≤ 45368703540607^3455*40000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21741503 40000000 45368703540607 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899440243/10000000000 : ℝ), (5217152703/10000000000 : ℝ), (21741503/40000000 : ℝ)] ![(5804879684293/50000000000000 : ℝ), (43021537080397/100000000000000 : ℝ), (45368703540607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899440243/10000000000 : ℝ)|^4479 ≤ (5804879684293/50000000000000 : ℝ)^3455
        have hw : |(-1899440243/10000000000 : ℝ)|=(1899440243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217152703/10000000000 : ℝ)|^4479 ≤ (43021537080397/100000000000000 : ℝ)^3455
        have hw : |(5217152703/10000000000 : ℝ)|=(5217152703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21741503/40000000 : ℝ)|^4479 ≤ (45368703540607/100000000000000 : ℝ)^3455
        have hw : |(21741503/40000000 : ℝ)|=(21741503/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295179627/10000000000 : ℝ)*x 0 + (-1793043981/10000000000 : ℝ)*x 1 + (1087075149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295179627/10000000000 : ℝ)^4479 ≤ (43857501888659/100000000000000 : ℝ)^3455 := by
    have hnat : (5295179627 : ℕ)^4479*100000000000000^3455 ≤ 43857501888659^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295179627 10000000000 43857501888659 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793043981/10000000000 : ℝ)^4479 ≤ (2693448652691/25000000000000 : ℝ)^3455 := by
    have hnat : (1793043981 : ℕ)^4479*25000000000000^3455 ≤ 2693448652691^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793043981 10000000000 2693448652691 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087075149/2000000000 : ℝ)^4479 ≤ (45368703486503/100000000000000 : ℝ)^3455 := by
    have hnat : (1087075149 : ℕ)^4479*100000000000000^3455 ≤ 45368703486503^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087075149 2000000000 45368703486503 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295179627/10000000000 : ℝ), (-1793043981/10000000000 : ℝ), (1087075149/2000000000 : ℝ)] ![(43857501888659/100000000000000 : ℝ), (2693448652691/25000000000000 : ℝ), (45368703486503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295179627/10000000000 : ℝ)|^4479 ≤ (43857501888659/100000000000000 : ℝ)^3455
        have hw : |(5295179627/10000000000 : ℝ)|=(5295179627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793043981/10000000000 : ℝ)|^4479 ≤ (2693448652691/25000000000000 : ℝ)^3455
        have hw : |(-1793043981/10000000000 : ℝ)|=(1793043981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087075149/2000000000 : ℝ)|^4479 ≤ (45368703486503/100000000000000 : ℝ)^3455
        have hw : |(1087075149/2000000000 : ℝ)|=(1087075149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661897453/1250000000 : ℝ)*x 0 + (1358843937/2500000000 : ℝ)*x 1 + (-896521991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661897453/1250000000 : ℝ)^4479 ≤ (43857501856447/100000000000000 : ℝ)^3455 := by
    have hnat : (661897453 : ℕ)^4479*100000000000000^3455 ≤ 43857501856447^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661897453 1250000000 43857501856447 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358843937/2500000000 : ℝ)^4479 ≤ (22684351759483/50000000000000 : ℝ)^3455 := by
    have hnat : (1358843937 : ℕ)^4479*50000000000000^3455 ≤ 22684351759483^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358843937 2500000000 22684351759483 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896521991/5000000000 : ℝ)^4479 ≤ (5386897309277/50000000000000 : ℝ)^3455 := by
    have hnat : (896521991 : ℕ)^4479*50000000000000^3455 ≤ 5386897309277^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896521991 5000000000 5386897309277 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661897453/1250000000 : ℝ), (1358843937/2500000000 : ℝ), (-896521991/5000000000 : ℝ)] ![(43857501856447/100000000000000 : ℝ), (22684351759483/50000000000000 : ℝ), (5386897309277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661897453/1250000000 : ℝ)|^4479 ≤ (43857501856447/100000000000000 : ℝ)^3455
        have hw : |(661897453/1250000000 : ℝ)|=(661897453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358843937/2500000000 : ℝ)|^4479 ≤ (22684351759483/50000000000000 : ℝ)^3455
        have hw : |(1358843937/2500000000 : ℝ)|=(1358843937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896521991/5000000000 : ℝ)|^4479 ≤ (5386897309277/50000000000000 : ℝ)^3455
        have hw : |(-896521991/5000000000 : ℝ)|=(896521991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s4_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2139834877/5000000000 : ℝ)*x 0 + (2264749351/5000000000 : ℝ)*x 1 + (4041972947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139834877/5000000000 : ℝ)^4479 ≤ (16639369901083/50000000000000 : ℝ)^3455 := by
    have hnat : (2139834877 : ℕ)^4479*50000000000000^3455 ≤ 16639369901083^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139834877 5000000000 16639369901083 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264749351/5000000000 : ℝ)^4479 ≤ (17909339835707/50000000000000 : ℝ)^3455 := by
    have hnat : (2264749351 : ℕ)^4479*50000000000000^3455 ≤ 17909339835707^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264749351 5000000000 17909339835707 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041972947/10000000000 : ℝ)^4479 ≤ (30902580514151/100000000000000 : ℝ)^3455 := by
    have hnat : (4041972947 : ℕ)^4479*100000000000000^3455 ≤ 30902580514151^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041972947 10000000000 30902580514151 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139834877/5000000000 : ℝ), (2264749351/5000000000 : ℝ), (4041972947/10000000000 : ℝ)] ![(16639369901083/50000000000000 : ℝ), (17909339835707/50000000000000 : ℝ), (30902580514151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139834877/5000000000 : ℝ)|^4479 ≤ (16639369901083/50000000000000 : ℝ)^3455
        have hw : |(2139834877/5000000000 : ℝ)|=(2139834877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264749351/5000000000 : ℝ)|^4479 ≤ (17909339835707/50000000000000 : ℝ)^3455
        have hw : |(2264749351/5000000000 : ℝ)|=(2264749351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041972947/10000000000 : ℝ)|^4479 ≤ (30902580514151/100000000000000 : ℝ)^3455
        have hw : |(4041972947/10000000000 : ℝ)|=(4041972947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3113/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5411/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3113/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3113/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3113/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3113/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3113/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3113/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (336/3125 : ℝ) ^ (4477/1024 : ℝ) ≤ (5829119082258723/100000000000000000000 : ℝ) := by
    have hpowers : (336/3125 : ℝ)^4477 ≤ (5829119082258723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (336 : ℕ)^4477*100000000000000000000^1024 ≤ 5829119082258723^1024*3125^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        336 3125 5829119082258723 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (336/3125 : ℝ)) (X := (5829119082258723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3113/20000 : ℝ) ^ (4477/1024 : ℝ) ≤ (29377793416733391/100000000000000000000 : ℝ) := by
    have hpowers : (3113/20000 : ℝ)^4477 ≤ (29377793416733391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3113 : ℕ)^4477*100000000000000000000^1024 ≤ 29377793416733391^1024*20000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3113 20000 29377793416733391 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3113/20000 : ℝ)) (X := (29377793416733391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005829119082258723/50000000000000000000 : ℝ) ≤ (2500066660147423/2500000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50005829119082258723/50000000000000000000 : ℝ)^1024 ≤ (2500066660147423/2500000000000000 : ℝ)^4477 := by
      have hnat : (50005829119082258723 : ℕ)^1024*2500000000000000^4477 ≤ 2500066660147423^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005829119082258723 50000000000000000000 2500066660147423 2500000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500066660147423/2500000000000000 : ℝ)) (X := (50005829119082258723/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017603456249496057/50000000000000000000 : ℝ) ≤ (10000805159361447/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50017603456249496057/50000000000000000000 : ℝ)^1024 ≤ (10000805159361447/10000000000000000 : ℝ)^4477 := by
      have hnat : (50017603456249496057 : ℕ)^1024*10000000000000000^4477 ≤ 10000805159361447^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017603456249496057 50000000000000000000 10000805159361447 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805159361447/10000000000000000 : ℝ)) (X := (50017603456249496057/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029377793416733391/50000000000000000000 : ℝ) ≤ (5000671839066601/5000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50029377793416733391/50000000000000000000 : ℝ)^1024 ≤ (5000671839066601/5000000000000000 : ℝ)^4477 := by
      have hnat : (50029377793416733391 : ℕ)^1024*5000000000000000^4477 ≤ 5000671839066601^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029377793416733391 50000000000000000000 5000671839066601 5000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000671839066601/5000000000000000 : ℝ)) (X := (50029377793416733391/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5829119082258723/100000000000000000000 : ℝ) ≤ ((12029925758372592019/12032500000000000000 : ℝ)+2*(107703754351/96260000000000 : ℝ)*(336/3125 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (12029925758372592019/12032500000000000000 : ℝ)+2*(107703754351/96260000000000 : ℝ)*(336/3125 : ℝ)=(2500066660147423/2500000000000000 : ℝ) by norm_num, show 1+2*(5829119082258723/100000000000000000000 : ℝ)=(50005829119082258723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29377793416733391/100000000000000000000 : ℝ)+(5829119082258723/100000000000000000000 : ℝ) ≤ ((12029925758372592019/12032500000000000000 : ℝ)+(107703754351/96260000000000 : ℝ)*((3113/20000 : ℝ)+(336/3125 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (12029925758372592019/12032500000000000000 : ℝ)+(107703754351/96260000000000 : ℝ)*((3113/20000 : ℝ)+(336/3125 : ℝ))=(10000805159361447/10000000000000000 : ℝ) by norm_num, show 1+(29377793416733391/100000000000000000000 : ℝ)+(5829119082258723/100000000000000000000 : ℝ)=(50017603456249496057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29377793416733391/100000000000000000000 : ℝ) ≤ ((12029925758372592019/12032500000000000000 : ℝ)+2*(107703754351/96260000000000 : ℝ)*(3113/20000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (12029925758372592019/12032500000000000000 : ℝ)+2*(107703754351/96260000000000 : ℝ)*(3113/20000 : ℝ)=(5000671839066601/5000000000000000 : ℝ) by norm_num, show 1+2*(29377793416733391/100000000000000000000 : ℝ)=(50029377793416733391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12029925758372592019/12032500000000000000 : ℝ)*(X 1 0+X 2 0)+(107703754351/96260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (3113/20000 : ℝ)) (c := (12029925758372592019/12032500000000000000 : ℝ)) (alpha := (107703754351/96260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12029925758372592019/12032500000000000000 : ℝ)*(X 0 1+X 2 1)+(107703754351/96260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (3113/20000 : ℝ)) (c := (12029925758372592019/12032500000000000000 : ℝ)) (alpha := (107703754351/96260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12029925758372592019/12032500000000000000 : ℝ)*(X 0 2+X 1 2)+(107703754351/96260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (3113/20000 : ℝ)) (c := (12029925758372592019/12032500000000000000 : ℝ)) (alpha := (107703754351/96260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-118713119/625000000 : ℝ)*X 0 0+(1359129993/2500000000 : ℝ)*X 0 1+(2608008457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338218387/2500000000 : ℝ)*X 1 0+(-2012402391/10000000000 : ℝ)*X 1 1+(5216017123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676436739/5000000000 : ℝ)*X 2 0+(5216016769/10000000000 : ℝ)*X 2 1+(-1006201477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4279601609/10000000000 : ℝ)*X 0 0+(2019708799/5000000000 : ℝ)*X 0 1+(453203581/1000000000 : ℝ)*X 0 2+(4279601609/10000000000 : ℝ)*X 1 0+(2019708799/5000000000 : ℝ)*X 1 1+(453203581/1000000000 : ℝ)*X 1 2+(4279601609/10000000000 : ℝ)*X 2 0+(2019708799/5000000000 : ℝ)*X 2 1+(453203581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1899440243/10000000000 : ℝ)*X 0 0+(5217152703/10000000000 : ℝ)*X 0 1+(21741503/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295179627/10000000000 : ℝ)*X 1 0+(-1793043981/10000000000 : ℝ)*X 1 1+(1087075149/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661897453/1250000000 : ℝ)*X 2 0+(1358843937/2500000000 : ℝ)*X 2 1+(-896521991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2139834877/5000000000 : ℝ)*X 0 0+(2264749351/5000000000 : ℝ)*X 0 1+(4041972947/10000000000 : ℝ)*X 0 2+(2139834877/5000000000 : ℝ)*X 1 0+(2264749351/5000000000 : ℝ)*X 1 1+(4041972947/10000000000 : ℝ)*X 1 2+(2139834877/5000000000 : ℝ)*X 2 0+(2264749351/5000000000 : ℝ)*X 2 1+(4041972947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1195807114975668179476200993/300812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321761649/50000000000000 : ℝ)*(base19) + (280591831/50000000000000 : ℝ)*(base23) + (9439739/20000000000000 : ℝ)*(upper2) + (31398449/100000000000000 : ℝ)*(upper3) + (3282550819845649/100000000000000 : ℝ)*(major0) + (3282550819845649/100000000000000 : ℝ)*(major1) + (3282550819845649/100000000000000 : ℝ)*(major2) + (2267551933935191/50000000000000 : ℝ)*(sp0) + (566890018561193/12500000000000 : ℝ)*(sp1) + (2267554956440479/50000000000000 : ℝ)*(sp2) + (1014987639286669/50000000000000 : ℝ)*(sp3) + (846207123/5000000000000 : ℝ)*(sp4) + (5158974111/50000000000000 : ℝ)*(sp6) + (5436596533/100000000000000 : ℝ)*(sp7) + (2029980715169871/100000000000000 : ℝ)*(f.failure) + (2267560396006421/50000000000000 : ℝ)*(f.sum) + (11378322037991/4813000000000000000000000000 : ℝ)*base65 + (1279971918236349669/1203250000000000000000000000000000 : ℝ)*base68 + (5173534547277599669/1203250000000000000000000000000000 : ℝ)*base70 + (89361893437849669/1203250000000000000000000000000000 : ℝ)*base72 + (10293857022381/4813000000000000000000000000 : ℝ)*base73 + (9733221260310599669/1203250000000000000000000000000000 : ℝ)*base76 + (5880348393957150331/1203250000000000000000000000000000 : ℝ)*base77 + (89916846776849669/1203250000000000000000000000000000 : ℝ)*base80 + (1784608022867/601625000000000000000000000 : ℝ)*base82 + (51767563/10000000000000000000000 : ℝ)*base90 + (51767563/10000000000000000000000 : ℝ)*base92 + (51767563/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8138557476675784515273/2406500000000000000000000000 : ℝ) := by norm_num
    linear_combination (138402431/25000000000000 : ℝ)*(base19) + (601691001/100000000000000 : ℝ)*(base23) + (68231781/100000000000000 : ℝ)*(upper3) + (4655743/20000000000000 : ℝ)*(lower4) + (705303/1000000000000 : ℝ)*(upper5) + (1658410175883631/50000000000000 : ℝ)*(major0) + (1658410175883631/50000000000000 : ℝ)*(major1) + (1658410175883631/50000000000000 : ℝ)*(major2) + (4152538447/50000000000000 : ℝ)*(sp1) + (8921430281/100000000000000 : ℝ)*(sp2) + (4582467061650207/100000000000000 : ℝ)*(sp4) + (4582458202963589/100000000000000 : ℝ)*(sp5) + (183298301541157/4000000000000 : ℝ)*(sp6) + (1025586764577051/50000000000000 : ℝ)*(sp7) + (1025586764577051/50000000000000 : ℝ)*(f.failure) + (4582467061650207/100000000000000 : ℝ)*(f.sum) + (20298512614529/4813000000000000000000000000 : ℝ)*base66 + (3575844159165340989/601625000000000000000000000000000 : ℝ)*base67 + (6336122473278034011/601625000000000000000000000000000 : ℝ)*base70 + (1832577365243590989/601625000000000000000000000000000 : ℝ)*base71 + (12167272615029/4813000000000000000000000000 : ℝ)*base73 + (9701687635818159011/601625000000000000000000000000000 : ℝ)*base76 + (2980832641701215989/601625000000000000000000000000000 : ℝ)*base77 + (1604949338520159011/601625000000000000000000000000000 : ℝ)*base80 + (2666722749781/601625000000000000000000000 : ℝ)*base82 + (1499897/5000000000000000000000 : ℝ)*base89 + (1499897/5000000000000000000000 : ℝ)*base91 + (1499897/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1491_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3113/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1491_s5_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899483729/10000000000 : ℝ)*x 0 + (2718019371/5000000000 : ℝ)*x 1 + (104328987/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899483729/10000000000 : ℝ)^4479 ≤ (2902525985453/25000000000000 : ℝ)^3455 := by
    have hnat : (1899483729 : ℕ)^4479*25000000000000^3455 ≤ 2902525985453^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899483729 10000000000 2902525985453 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718019371/5000000000 : ℝ)^4479 ≤ (45375877781339/100000000000000 : ℝ)^3455 := by
    have hnat : (2718019371 : ℕ)^4479*100000000000000^3455 ≤ 45375877781339^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718019371 5000000000 45375877781339 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104328987/200000000 : ℝ)^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455 := by
    have hnat : (104328987 : ℕ)^4479*100000000000000^3455 ≤ 43014018254087^3455*200000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104328987 200000000 43014018254087 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899483729/10000000000 : ℝ), (2718019371/5000000000 : ℝ), (104328987/200000000 : ℝ)] ![(2902525985453/25000000000000 : ℝ), (45375877781339/100000000000000 : ℝ), (43014018254087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899483729/10000000000 : ℝ)|^4479 ≤ (2902525985453/25000000000000 : ℝ)^3455
        have hw : |(-1899483729/10000000000 : ℝ)|=(1899483729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718019371/5000000000 : ℝ)|^4479 ≤ (45375877781339/100000000000000 : ℝ)^3455
        have hw : |(2718019371/5000000000 : ℝ)|=(2718019371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104328987/200000000 : ℝ)|^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455
        have hw : |(104328987/200000000 : ℝ)|=(104328987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352747871/10000000000 : ℝ)*x 0 + (-16095977/80000000 : ℝ)*x 1 + (104328987/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352747871/10000000000 : ℝ)^4479 ≤ (22238312164311/50000000000000 : ℝ)^3455 := by
    have hnat : (5352747871 : ℕ)^4479*50000000000000^3455 ≤ 22238312164311^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352747871 10000000000 22238312164311 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16095977/80000000 : ℝ)^4479 ≤ (12509357392107/100000000000000 : ℝ)^3455 := by
    have hnat : (16095977 : ℕ)^4479*100000000000000^3455 ≤ 12509357392107^3455*80000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16095977 80000000 12509357392107 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104328987/200000000 : ℝ)^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455 := by
    have hnat : (104328987 : ℕ)^4479*100000000000000^3455 ≤ 43014018254087^3455*200000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104328987 200000000 43014018254087 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352747871/10000000000 : ℝ), (-16095977/80000000 : ℝ), (104328987/200000000 : ℝ)] ![(22238312164311/50000000000000 : ℝ), (12509357392107/100000000000000 : ℝ), (43014018254087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352747871/10000000000 : ℝ)|^4479 ≤ (22238312164311/50000000000000 : ℝ)^3455
        have hw : |(5352747871/10000000000 : ℝ)|=(5352747871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16095977/80000000 : ℝ)|^4479 ≤ (12509357392107/100000000000000 : ℝ)^3455
        have hw : |(-16095977/80000000 : ℝ)|=(16095977/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104328987/200000000 : ℝ)|^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455
        have hw : |(104328987/200000000 : ℝ)|=(104328987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352747871/10000000000 : ℝ)*x 0 + (104328987/200000000 : ℝ)*x 1 + (-16095977/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352747871/10000000000 : ℝ)^4479 ≤ (22238312164311/50000000000000 : ℝ)^3455 := by
    have hnat : (5352747871 : ℕ)^4479*50000000000000^3455 ≤ 22238312164311^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352747871 10000000000 22238312164311 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104328987/200000000 : ℝ)^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455 := by
    have hnat : (104328987 : ℕ)^4479*100000000000000^3455 ≤ 43014018254087^3455*200000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104328987 200000000 43014018254087 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16095977/80000000 : ℝ)^4479 ≤ (12509357392107/100000000000000 : ℝ)^3455 := by
    have hnat : (16095977 : ℕ)^4479*100000000000000^3455 ≤ 12509357392107^3455*80000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16095977 80000000 12509357392107 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352747871/10000000000 : ℝ), (104328987/200000000 : ℝ), (-16095977/80000000 : ℝ)] ![(22238312164311/50000000000000 : ℝ), (43014018254087/100000000000000 : ℝ), (12509357392107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352747871/10000000000 : ℝ)|^4479 ≤ (22238312164311/50000000000000 : ℝ)^3455
        have hw : |(5352747871/10000000000 : ℝ)|=(5352747871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104328987/200000000 : ℝ)|^4479 ≤ (43014018254087/100000000000000 : ℝ)^3455
        have hw : |(104328987/200000000 : ℝ)|=(104328987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16095977/80000000 : ℝ)|^4479 ≤ (12509357392107/100000000000000 : ℝ)^3455
        have hw : |(-16095977/80000000 : ℝ)|=(16095977/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2139823699/5000000000 : ℝ)*x 0 + (4040432027/10000000000 : ℝ)*x 1 + (2265505153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139823699/5000000000 : ℝ)^4479 ≤ (8319628609691/25000000000000 : ℝ)^3455 := by
    have hnat : (2139823699 : ℕ)^4479*25000000000000^3455 ≤ 8319628609691^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139823699 5000000000 8319628609691 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4040432027/10000000000 : ℝ)^4479 ≤ (30887308725377/100000000000000 : ℝ)^3455 := by
    have hnat : (4040432027 : ℕ)^4479*100000000000000^3455 ≤ 30887308725377^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040432027 10000000000 30887308725377 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265505153/5000000000 : ℝ)^4479 ≤ (8958544206387/25000000000000 : ℝ)^3455 := by
    have hnat : (2265505153 : ℕ)^4479*25000000000000^3455 ≤ 8958544206387^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265505153 5000000000 8958544206387 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139823699/5000000000 : ℝ), (4040432027/10000000000 : ℝ), (2265505153/5000000000 : ℝ)] ![(8319628609691/25000000000000 : ℝ), (30887308725377/100000000000000 : ℝ), (8958544206387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139823699/5000000000 : ℝ)|^4479 ≤ (8319628609691/25000000000000 : ℝ)^3455
        have hw : |(2139823699/5000000000 : ℝ)|=(2139823699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4040432027/10000000000 : ℝ)|^4479 ≤ (30887308725377/100000000000000 : ℝ)^3455
        have hw : |(4040432027/10000000000 : ℝ)|=(4040432027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265505153/5000000000 : ℝ)|^4479 ≤ (8958544206387/25000000000000 : ℝ)^3455
        have hw : |(2265505153/5000000000 : ℝ)|=(2265505153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899513617/10000000000 : ℝ)*x 0 + (2608787811/5000000000 : ℝ)*x 1 + (1086980839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899513617/10000000000 : ℝ)^4479 ≤ (5805170384459/50000000000000 : ℝ)^3455 := by
    have hnat : (1899513617 : ℕ)^4479*50000000000000^3455 ≤ 5805170384459^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899513617 10000000000 5805170384459 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608787811/5000000000 : ℝ)^4479 ≤ (21513029109383/50000000000000 : ℝ)^3455 := by
    have hnat : (2608787811 : ℕ)^4479*50000000000000^3455 ≤ 21513029109383^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608787811 5000000000 21513029109383 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086980839/2000000000 : ℝ)^4479 ≤ (4536360099873/10000000000000 : ℝ)^3455 := by
    have hnat : (1086980839 : ℕ)^4479*10000000000000^3455 ≤ 4536360099873^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086980839 2000000000 4536360099873 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899513617/10000000000 : ℝ), (2608787811/5000000000 : ℝ), (1086980839/2000000000 : ℝ)] ![(5805170384459/50000000000000 : ℝ), (21513029109383/50000000000000 : ℝ), (4536360099873/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899513617/10000000000 : ℝ)|^4479 ≤ (5805170384459/50000000000000 : ℝ)^3455
        have hw : |(-1899513617/10000000000 : ℝ)|=(1899513617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608787811/5000000000 : ℝ)|^4479 ≤ (21513029109383/50000000000000 : ℝ)^3455
        have hw : |(2608787811/5000000000 : ℝ)|=(2608787811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086980839/2000000000 : ℝ)|^4479 ≤ (4536360099873/10000000000000 : ℝ)^3455
        have hw : |(1086980839/2000000000 : ℝ)|=(1086980839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295293337/10000000000 : ℝ)*x 0 + (-1793542303/10000000000 : ℝ)*x 1 + (2717452083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295293337/10000000000 : ℝ)^4479 ≤ (43858722834067/100000000000000 : ℝ)^3455 := by
    have hnat : (5295293337 : ℕ)^4479*100000000000000^3455 ≤ 43858722834067^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295293337 10000000000 43858722834067 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793542303/10000000000 : ℝ)^4479 ≤ (1347209557547/12500000000000 : ℝ)^3455 := by
    have hnat : (1793542303 : ℕ)^4479*12500000000000^3455 ≤ 1347209557547^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793542303 10000000000 1347209557547 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717452083/5000000000 : ℝ)^4479 ≤ (22681800342467/50000000000000 : ℝ)^3455 := by
    have hnat : (2717452083 : ℕ)^4479*50000000000000^3455 ≤ 22681800342467^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717452083 5000000000 22681800342467 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295293337/10000000000 : ℝ), (-1793542303/10000000000 : ℝ), (2717452083/5000000000 : ℝ)] ![(43858722834067/100000000000000 : ℝ), (1347209557547/12500000000000 : ℝ), (22681800342467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295293337/10000000000 : ℝ)|^4479 ≤ (43858722834067/100000000000000 : ℝ)^3455
        have hw : |(5295293337/10000000000 : ℝ)|=(5295293337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793542303/10000000000 : ℝ)|^4479 ≤ (1347209557547/12500000000000 : ℝ)^3455
        have hw : |(-1793542303/10000000000 : ℝ)|=(1793542303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717452083/5000000000 : ℝ)|^4479 ≤ (22681800342467/50000000000000 : ℝ)^3455
        have hw : |(2717452083/5000000000 : ℝ)|=(2717452083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295293319/10000000000 : ℝ)*x 0 + (5434904173/10000000000 : ℝ)*x 1 + (-1793542319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295293319/10000000000 : ℝ)^4479 ≤ (21929361320397/50000000000000 : ℝ)^3455 := by
    have hnat : (5295293319 : ℕ)^4479*50000000000000^3455 ≤ 21929361320397^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295293319 10000000000 21929361320397 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434904173/10000000000 : ℝ)^4479 ≤ (22681800380339/50000000000000 : ℝ)^3455 := by
    have hnat : (5434904173 : ℕ)^4479*50000000000000^3455 ≤ 22681800380339^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434904173 10000000000 22681800380339 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793542319/10000000000 : ℝ)^4479 ≤ (10777676585019/100000000000000 : ℝ)^3455 := by
    have hnat : (1793542319 : ℕ)^4479*100000000000000^3455 ≤ 10777676585019^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793542319 10000000000 10777676585019 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295293319/10000000000 : ℝ), (5434904173/10000000000 : ℝ), (-1793542319/10000000000 : ℝ)] ![(21929361320397/50000000000000 : ℝ), (22681800380339/50000000000000 : ℝ), (10777676585019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295293319/10000000000 : ℝ)|^4479 ≤ (21929361320397/50000000000000 : ℝ)^3455
        have hw : |(5295293319/10000000000 : ℝ)|=(5295293319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434904173/10000000000 : ℝ)|^4479 ≤ (22681800380339/50000000000000 : ℝ)^3455
        have hw : |(5434904173/10000000000 : ℝ)|=(5434904173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793542319/10000000000 : ℝ)|^4479 ≤ (10777676585019/100000000000000 : ℝ)^3455
        have hw : |(-1793542319/10000000000 : ℝ)|=(1793542319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s5_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069928557/2500000000 : ℝ)*x 0 + (4528494117/10000000000 : ℝ)*x 1 + (4042966713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069928557/2500000000 : ℝ)^4479 ≤ (33279188130809/100000000000000 : ℝ)^3455 := by
    have hnat : (1069928557 : ℕ)^4479*100000000000000^3455 ≤ 33279188130809^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069928557 2500000000 33279188130809 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528494117/10000000000 : ℝ)^4479 ≤ (35808381387551/100000000000000 : ℝ)^3455 := by
    have hnat : (4528494117 : ℕ)^4479*100000000000000^3455 ≤ 35808381387551^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528494117 10000000000 35808381387551 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4042966713/10000000000 : ℝ)^4479 ≤ (3864053808827/12500000000000 : ℝ)^3455 := by
    have hnat : (4042966713 : ℕ)^4479*12500000000000^3455 ≤ 3864053808827^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042966713 10000000000 3864053808827 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069928557/2500000000 : ℝ), (4528494117/10000000000 : ℝ), (4042966713/10000000000 : ℝ)] ![(33279188130809/100000000000000 : ℝ), (35808381387551/100000000000000 : ℝ), (3864053808827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069928557/2500000000 : ℝ)|^4479 ≤ (33279188130809/100000000000000 : ℝ)^3455
        have hw : |(1069928557/2500000000 : ℝ)|=(1069928557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528494117/10000000000 : ℝ)|^4479 ≤ (35808381387551/100000000000000 : ℝ)^3455
        have hw : |(4528494117/10000000000 : ℝ)|=(4528494117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4042966713/10000000000 : ℝ)|^4479 ≤ (3864053808827/12500000000000 : ℝ)^3455
        have hw : |(4042966713/10000000000 : ℝ)|=(4042966713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5411/50000 : ℝ) ^ (4477/1024 : ℝ) ≤ (5996869790522457/100000000000000000000 : ℝ) := by
    have hpowers : (5411/50000 : ℝ)^4477 ≤ (5996869790522457/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5411 : ℕ)^4477*100000000000000000000^1024 ≤ 5996869790522457^1024*50000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5411 50000 5996869790522457 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5411/50000 : ℝ)) (X := (5996869790522457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (28755787451333103/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4477 ≤ (28755787451333103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4477*100000000000000000000^1024 ≤ 28755787451333103^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 28755787451333103 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (28755787451333103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005996869790522457/50000000000000000000 : ℝ) ≤ (10000274313632309/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50005996869790522457/50000000000000000000 : ℝ)^1024 ≤ (10000274313632309/10000000000000000 : ℝ)^4477 := by
      have hnat : (50005996869790522457 : ℕ)^1024*10000000000000000^4477 ≤ 10000274313632309^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005996869790522457 50000000000000000000 10000274313632309 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000274313632309/10000000000000000 : ℝ)) (X := (50005996869790522457/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500868816431046389/2500000000000000000 : ℝ) ≤ (10000794772228833/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (2500868816431046389/2500000000000000000 : ℝ)^1024 ≤ (10000794772228833/10000000000000000 : ℝ)^4477 := by
      have hnat : (2500868816431046389 : ℕ)^1024*10000000000000000^4477 ≤ 10000794772228833^4477*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500868816431046389 2500000000000000000 10000794772228833 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000794772228833/10000000000000000 : ℝ)) (X := (2500868816431046389/2500000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028755787451333103/50000000000000000000 : ℝ) ≤ (10001315230825357/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50028755787451333103/50000000000000000000 : ℝ)^1024 ≤ (10001315230825357/10000000000000000 : ℝ)^4477 := by
      have hnat : (50028755787451333103 : ℕ)^1024*10000000000000000^4477 ≤ 10001315230825357^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028755787451333103 50000000000000000000 10001315230825357 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001315230825357/10000000000000000 : ℝ)) (X := (50028755787451333103/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5996869790522457/100000000000000000000 : ℝ) ≤ ((46660015415858820647/46670000000000000000 : ℝ)+2*(130114649131/116675000000000 : ℝ)*(5411/50000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (46660015415858820647/46670000000000000000 : ℝ)+2*(130114649131/116675000000000 : ℝ)*(5411/50000 : ℝ)=(10000274313632309/10000000000000000 : ℝ) by norm_num, show 1+2*(5996869790522457/100000000000000000000 : ℝ)=(50005996869790522457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28755787451333103/100000000000000000000 : ℝ)+(5996869790522457/100000000000000000000 : ℝ) ≤ ((46660015415858820647/46670000000000000000 : ℝ)+(130114649131/116675000000000 : ℝ)*((15489/100000 : ℝ)+(5411/50000 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (46660015415858820647/46670000000000000000 : ℝ)+(130114649131/116675000000000 : ℝ)*((15489/100000 : ℝ)+(5411/50000 : ℝ))=(10000794772228833/10000000000000000 : ℝ) by norm_num, show 1+(28755787451333103/100000000000000000000 : ℝ)+(5996869790522457/100000000000000000000 : ℝ)=(2500868816431046389/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28755787451333103/100000000000000000000 : ℝ) ≤ ((46660015415858820647/46670000000000000000 : ℝ)+2*(130114649131/116675000000000 : ℝ)*(15489/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (46660015415858820647/46670000000000000000 : ℝ)+2*(130114649131/116675000000000 : ℝ)*(15489/100000 : ℝ)=(10001315230825357/10000000000000000 : ℝ) by norm_num, show 1+2*(28755787451333103/100000000000000000000 : ℝ)=(50028755787451333103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46660015415858820647/46670000000000000000 : ℝ)*(X 1 0+X 2 0)+(130114649131/116675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (46660015415858820647/46670000000000000000 : ℝ)) (alpha := (130114649131/116675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46660015415858820647/46670000000000000000 : ℝ)*(X 0 1+X 2 1)+(130114649131/116675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (46660015415858820647/46670000000000000000 : ℝ)) (alpha := (130114649131/116675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46660015415858820647/46670000000000000000 : ℝ)*(X 0 2+X 1 2)+(130114649131/116675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (46660015415858820647/46670000000000000000 : ℝ)) (alpha := (130114649131/116675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1899483729/10000000000 : ℝ)*X 0 0+(2718019371/5000000000 : ℝ)*X 0 1+(104328987/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352747871/10000000000 : ℝ)*X 1 0+(-16095977/80000000 : ℝ)*X 1 1+(104328987/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352747871/10000000000 : ℝ)*X 2 0+(104328987/200000000 : ℝ)*X 2 1+(-16095977/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2139823699/5000000000 : ℝ)*X 0 0+(4040432027/10000000000 : ℝ)*X 0 1+(2265505153/5000000000 : ℝ)*X 0 2+(2139823699/5000000000 : ℝ)*X 1 0+(4040432027/10000000000 : ℝ)*X 1 1+(2265505153/5000000000 : ℝ)*X 1 2+(2139823699/5000000000 : ℝ)*X 2 0+(4040432027/10000000000 : ℝ)*X 2 1+(2265505153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1899513617/10000000000 : ℝ)*X 0 0+(2608787811/5000000000 : ℝ)*X 0 1+(1086980839/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295293337/10000000000 : ℝ)*X 1 0+(-1793542303/10000000000 : ℝ)*X 1 1+(2717452083/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295293319/10000000000 : ℝ)*X 2 0+(5434904173/10000000000 : ℝ)*X 2 1+(-1793542319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1069928557/2500000000 : ℝ)*X 0 0+(4528494117/10000000000 : ℝ)*X 0 1+(4042966713/10000000000 : ℝ)*X 0 2+(1069928557/2500000000 : ℝ)*X 1 0+(4528494117/10000000000 : ℝ)*X 1 1+(4042966713/10000000000 : ℝ)*X 1 2+(1069928557/2500000000 : ℝ)*X 2 0+(4528494117/10000000000 : ℝ)*X 2 1+(4042966713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7441338885700195510316188743/1166750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71032999/6250000000000 : ℝ)*(base19) + (265053357/25000000000000 : ℝ)*(base23) + (40849257/100000000000000 : ℝ)*(lower2) + (159841731/100000000000000 : ℝ)*(upper3) + (51853979/50000000000000 : ℝ)*(upper5) + (1648104231379877/50000000000000 : ℝ)*(major0) + (1648104231379877/50000000000000 : ℝ)*(major1) + (1648104231379877/50000000000000 : ℝ)*(major2) + (455397232811963/10000000000000 : ℝ)*(sp0) + (569248595181923/12500000000000 : ℝ)*(sp1) + (227699441888497/5000000000000 : ℝ)*(sp2) + (2038418284579881/100000000000000 : ℝ)*(sp3) + (8784931869/50000000000000 : ℝ)*(sp4) + (2132590439/25000000000000 : ℝ)*(sp7) + (1019213407470819/50000000000000 : ℝ)*(f.failure) + (569248737247921/12500000000000 : ℝ)*(f.sum) + (18893751994723/11667500000000000000000000000 : ℝ)*base65 + (6840184554699779581/2333500000000000000000000000000000 : ℝ)*base68 + (881916976918720419/2333500000000000000000000000000000 : ℝ)*base69 + (21461173778177720419/2333500000000000000000000000000000 : ℝ)*base71 + (33786164526969/23335000000000000000000000000 : ℝ)*base74 + (15570375746246279581/2333500000000000000000000000000000 : ℝ)*base76 + (4764257249131720419/2333500000000000000000000000000000 : ℝ)*base77 + (9444755396216220419/2333500000000000000000000000000000 : ℝ)*base79 + (48213996034953/11667500000000000000000000000 : ℝ)*base81 + (31294993/5000000000000000000000 : ℝ)*base89 + (31294993/5000000000000000000000 : ℝ)*base91 + (31294993/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2167950579203299912003920489/583375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (593336697/100000000000000 : ℝ)*(base19) + (650765259/100000000000000 : ℝ)*(base23) + (187134077/100000000000000 : ℝ)*(lower1) + (35192997/50000000000000 : ℝ)*(upper3) + (35961459/100000000000000 : ℝ)*(lower4) + (79516101/100000000000000 : ℝ)*(upper5) + (1665232654853771/50000000000000 : ℝ)*(major0) + (1665232654853771/50000000000000 : ℝ)*(major1) + (1665232654853771/50000000000000 : ℝ)*(major2) + (475335341/100000000000000 : ℝ)*(sp2) + (4601318711201161/100000000000000 : ℝ)*(sp4) + (287582382366529/6250000000000 : ℝ)*(sp5) + (2300658792550281/50000000000000 : ℝ)*(sp6) + (1029805892169929/50000000000000 : ℝ)*(sp7) + (1029805892169929/50000000000000 : ℝ)*(f.failure) + (4601318711201161/100000000000000 : ℝ)*(f.sum) + (77279570436863/23335000000000000000000000000 : ℝ)*base65 + (39039784213413009837/2333500000000000000000000000000000 : ℝ)*base67 + (23813452580309509837/2333500000000000000000000000000000 : ℝ)*base69 + (62096587379830990163/2333500000000000000000000000000000 : ℝ)*base72 + (22855938633009/11667500000000000000000000000 : ℝ)*base73 + (184803515581538009837/2333500000000000000000000000000000 : ℝ)*base75 + (13596837091515509837/2333500000000000000000000000000000 : ℝ)*base77 + (35170312829674009837/2333500000000000000000000000000000 : ℝ)*base79 + (144293523645923/23335000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (53961837/5000000000000000000000 : ℝ)*base90 + (53961837/5000000000000000000000 : ℝ)*base92 + (53961837/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1491_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1491_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1491_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1491_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1491_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

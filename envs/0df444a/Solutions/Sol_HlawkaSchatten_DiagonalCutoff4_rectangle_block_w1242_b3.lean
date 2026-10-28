-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:02.398122+00:00
-- url     : https://prove2.me/submissions/1b346424-f5b3-45a5-a6d9-b8bd2af67454

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
theorem support_rectangle_w1242_box_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1996269521/10000000000 : ℝ)*x 0 + (5374842873/10000000000 : ℝ)*x 1 + (214993707/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1996269521/10000000000 : ℝ)^8435 ≤ (11907854762191/100000000000000 : ℝ)^6387 := by
    have hnat : (1996269521 : ℕ)^8435*100000000000000^6387 ≤ 11907854762191^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996269521 10000000000 11907854762191 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374842873/10000000000 : ℝ)^8435 ≤ (172054975333/390625000000 : ℝ)^6387 := by
    have hnat : (5374842873 : ℕ)^8435*390625000000^6387 ≤ 172054975333^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374842873 10000000000 172054975333 390625000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214993707/400000000 : ℝ)^8435 ≤ (44046071542383/100000000000000 : ℝ)^6387 := by
    have hnat : (214993707 : ℕ)^8435*100000000000000^6387 ≤ 44046071542383^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214993707 400000000 44046071542383 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1996269521/10000000000 : ℝ), (5374842873/10000000000 : ℝ), (214993707/400000000 : ℝ)] ![(11907854762191/100000000000000 : ℝ), (172054975333/390625000000 : ℝ), (44046071542383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1996269521/10000000000 : ℝ)|^8435 ≤ (11907854762191/100000000000000 : ℝ)^6387
        have hw : |(-1996269521/10000000000 : ℝ)|=(1996269521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374842873/10000000000 : ℝ)|^8435 ≤ (172054975333/390625000000 : ℝ)^6387
        have hw : |(5374842873/10000000000 : ℝ)|=(5374842873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(214993707/400000000 : ℝ)|^8435 ≤ (44046071542383/100000000000000 : ℝ)^6387
        have hw : |(214993707/400000000 : ℝ)|=(214993707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296794523/10000000000 : ℝ)*x 0 + (-525587301/2500000000 : ℝ)*x 1 + (5374843007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296794523/10000000000 : ℝ)^8435 ≤ (43203364526401/100000000000000 : ℝ)^6387 := by
    have hnat : (5296794523 : ℕ)^8435*100000000000000^6387 ≤ 43203364526401^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296794523 10000000000 43203364526401 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525587301/2500000000 : ℝ)^8435 ≤ (1593820040957/12500000000000 : ℝ)^6387 := by
    have hnat : (525587301 : ℕ)^8435*12500000000000^6387 ≤ 1593820040957^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525587301 2500000000 1593820040957 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374843007/10000000000 : ℝ)^8435 ≤ (4404607513547/10000000000000 : ℝ)^6387 := by
    have hnat : (5374843007 : ℕ)^8435*10000000000000^6387 ≤ 4404607513547^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374843007 10000000000 4404607513547 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296794523/10000000000 : ℝ), (-525587301/2500000000 : ℝ), (5374843007/10000000000 : ℝ)] ![(43203364526401/100000000000000 : ℝ), (1593820040957/12500000000000 : ℝ), (4404607513547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296794523/10000000000 : ℝ)|^8435 ≤ (43203364526401/100000000000000 : ℝ)^6387
        have hw : |(5296794523/10000000000 : ℝ)|=(5296794523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525587301/2500000000 : ℝ)|^8435 ≤ (1593820040957/12500000000000 : ℝ)^6387
        have hw : |(-525587301/2500000000 : ℝ)|=(525587301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374843007/10000000000 : ℝ)|^8435 ≤ (4404607513547/10000000000000 : ℝ)^6387
        have hw : |(5374843007/10000000000 : ℝ)|=(5374843007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296795391/10000000000 : ℝ)*x 0 + (335927671/625000000 : ℝ)*x 1 + (-1051174201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296795391/10000000000 : ℝ)^8435 ≤ (43203373876417/100000000000000 : ℝ)^6387 := by
    have hnat : (5296795391 : ℕ)^8435*100000000000000^6387 ≤ 43203373876417^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296795391 10000000000 43203373876417 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335927671/625000000 : ℝ)^8435 ≤ (44046072202559/100000000000000 : ℝ)^6387 := by
    have hnat : (335927671 : ℕ)^8435*100000000000000^6387 ≤ 44046072202559^6387*625000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335927671 625000000 44046072202559 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051174201/5000000000 : ℝ)^8435 ≤ (3187638475983/25000000000000 : ℝ)^6387 := by
    have hnat : (1051174201 : ℕ)^8435*25000000000000^6387 ≤ 3187638475983^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051174201 5000000000 3187638475983 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296795391/10000000000 : ℝ), (335927671/625000000 : ℝ), (-1051174201/5000000000 : ℝ)] ![(43203373876417/100000000000000 : ℝ), (44046072202559/100000000000000 : ℝ), (3187638475983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296795391/10000000000 : ℝ)|^8435 ≤ (43203373876417/100000000000000 : ℝ)^6387
        have hw : |(5296795391/10000000000 : ℝ)|=(5296795391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335927671/625000000 : ℝ)|^8435 ≤ (44046072202559/100000000000000 : ℝ)^6387
        have hw : |(335927671/625000000 : ℝ)|=(335927671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051174201/5000000000 : ℝ)|^8435 ≤ (3187638475983/25000000000000 : ℝ)^6387
        have hw : |(-1051174201/5000000000 : ℝ)|=(1051174201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2228652427/5000000000 : ℝ)*x 0 + (4299552253/10000000000 : ℝ)*x 1 + (2149775981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228652427/5000000000 : ℝ)^8435 ≤ (34399087270751/100000000000000 : ℝ)^6387 := by
    have hnat : (2228652427 : ℕ)^8435*100000000000000^6387 ≤ 34399087270751^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228652427 5000000000 34399087270751 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299552253/10000000000 : ℝ)^8435 ≤ (16400228909427/50000000000000 : ℝ)^6387 := by
    have hnat : (4299552253 : ℕ)^8435*50000000000000^6387 ≤ 16400228909427^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299552253 10000000000 16400228909427 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149775981/5000000000 : ℝ)^8435 ≤ (3280045488703/10000000000000 : ℝ)^6387 := by
    have hnat : (2149775981 : ℕ)^8435*10000000000000^6387 ≤ 3280045488703^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149775981 5000000000 3280045488703 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228652427/5000000000 : ℝ), (4299552253/10000000000 : ℝ), (2149775981/5000000000 : ℝ)] ![(34399087270751/100000000000000 : ℝ), (16400228909427/50000000000000 : ℝ), (3280045488703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228652427/5000000000 : ℝ)|^8435 ≤ (34399087270751/100000000000000 : ℝ)^6387
        have hw : |(2228652427/5000000000 : ℝ)|=(2228652427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4299552253/10000000000 : ℝ)|^8435 ≤ (16400228909427/50000000000000 : ℝ)^6387
        have hw : |(4299552253/10000000000 : ℝ)|=(4299552253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2149775981/5000000000 : ℝ)|^8435 ≤ (3280045488703/10000000000000 : ℝ)^6387
        have hw : |(2149775981/5000000000 : ℝ)|=(2149775981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2245041847/10000000000 : ℝ)*x 0 + (5282284847/10000000000 : ℝ)*x 1 + (2641142439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245041847/10000000000 : ℝ)^8435 ≤ (13905727003429/100000000000000 : ℝ)^6387 := by
    have hnat : (2245041847 : ℕ)^8435*100000000000000^6387 ≤ 13905727003429^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245041847 10000000000 13905727003429 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282284847/10000000000 : ℝ)^8435 ≤ (1721885452997/4000000000000 : ℝ)^6387 := by
    have hnat : (5282284847 : ℕ)^8435*4000000000000^6387 ≤ 1721885452997^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282284847 10000000000 1721885452997 4000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641142439/5000000000 : ℝ)^8435 ≤ (67261151029/156250000000 : ℝ)^6387 := by
    have hnat : (2641142439 : ℕ)^8435*156250000000^6387 ≤ 67261151029^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641142439 5000000000 67261151029 156250000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2245041847/10000000000 : ℝ), (5282284847/10000000000 : ℝ), (2641142439/5000000000 : ℝ)] ![(13905727003429/100000000000000 : ℝ), (1721885452997/4000000000000 : ℝ), (67261151029/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2245041847/10000000000 : ℝ)|^8435 ≤ (13905727003429/100000000000000 : ℝ)^6387
        have hw : |(-2245041847/10000000000 : ℝ)|=(2245041847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282284847/10000000000 : ℝ)|^8435 ≤ (1721885452997/4000000000000 : ℝ)^6387
        have hw : |(5282284847/10000000000 : ℝ)|=(5282284847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641142439/5000000000 : ℝ)|^8435 ≤ (67261151029/156250000000 : ℝ)^6387
        have hw : |(2641142439/5000000000 : ℝ)|=(2641142439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362041547/10000000000 : ℝ)*x 0 + (-1069521323/5000000000 : ℝ)*x 1 + (1320571201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362041547/10000000000 : ℝ)^8435 ≤ (21953791813137/50000000000000 : ℝ)^6387 := by
    have hnat : (5362041547 : ℕ)^8435*50000000000000^6387 ≤ 21953791813137^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362041547 10000000000 21953791813137 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069521323/5000000000 : ℝ)^8435 ≤ (13045280492523/100000000000000 : ℝ)^6387 := by
    have hnat : (1069521323 : ℕ)^8435*100000000000000^6387 ≤ 13045280492523^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069521323 5000000000 13045280492523 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320571201/2500000000 : ℝ)^8435 ≤ (2152356793107/5000000000000 : ℝ)^6387 := by
    have hnat : (1320571201 : ℕ)^8435*5000000000000^6387 ≤ 2152356793107^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320571201 2500000000 2152356793107 5000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362041547/10000000000 : ℝ), (-1069521323/5000000000 : ℝ), (1320571201/2500000000 : ℝ)] ![(21953791813137/50000000000000 : ℝ), (13045280492523/100000000000000 : ℝ), (2152356793107/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362041547/10000000000 : ℝ)|^8435 ≤ (21953791813137/50000000000000 : ℝ)^6387
        have hw : |(5362041547/10000000000 : ℝ)|=(5362041547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069521323/5000000000 : ℝ)|^8435 ≤ (13045280492523/100000000000000 : ℝ)^6387
        have hw : |(-1069521323/5000000000 : ℝ)|=(1069521323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320571201/2500000000 : ℝ)|^8435 ≤ (2152356793107/5000000000000 : ℝ)^6387
        have hw : |(1320571201/2500000000 : ℝ)|=(1320571201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681020759/5000000000 : ℝ)*x 0 + (528228491/1000000000 : ℝ)*x 1 + (-133690159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681020759/5000000000 : ℝ)^8435 ≤ (2195379165633/5000000000000 : ℝ)^6387 := by
    have hnat : (2681020759 : ℕ)^8435*5000000000000^6387 ≤ 2195379165633^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681020759 5000000000 2195379165633 5000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528228491/1000000000 : ℝ)^8435 ≤ (21523568501479/50000000000000 : ℝ)^6387 := by
    have hnat : (528228491 : ℕ)^8435*50000000000000^6387 ≤ 21523568501479^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528228491 1000000000 21523568501479 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133690159/625000000 : ℝ)^8435 ≤ (2609055934199/20000000000000 : ℝ)^6387 := by
    have hnat : (133690159 : ℕ)^8435*20000000000000^6387 ≤ 2609055934199^6387*625000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133690159 625000000 2609055934199 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681020759/5000000000 : ℝ), (528228491/1000000000 : ℝ), (-133690159/625000000 : ℝ)] ![(2195379165633/5000000000000 : ℝ), (21523568501479/50000000000000 : ℝ), (2609055934199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681020759/5000000000 : ℝ)|^8435 ≤ (2195379165633/5000000000000 : ℝ)^6387
        have hw : |(2681020759/5000000000 : ℝ)|=(2681020759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528228491/1000000000 : ℝ)|^8435 ≤ (21523568501479/50000000000000 : ℝ)^6387
        have hw : |(528228491/1000000000 : ℝ)|=(528228491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133690159/625000000 : ℝ)|^8435 ≤ (2609055934199/20000000000000 : ℝ)^6387
        have hw : |(-133690159/625000000 : ℝ)|=(133690159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (848768807/2000000000 : ℝ)*x 0 + (2203131187/5000000000 : ℝ)*x 1 + (550782809/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848768807/2000000000 : ℝ)^8435 ≤ (16120183569191/50000000000000 : ℝ)^6387 := by
    have hnat : (848768807 : ℕ)^8435*50000000000000^6387 ≤ 16120183569191^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848768807 2000000000 16120183569191 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203131187/5000000000 : ℝ)^8435 ≤ (8469953981059/25000000000000 : ℝ)^6387 := by
    have hnat : (2203131187 : ℕ)^8435*25000000000000^6387 ≤ 8469953981059^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203131187 5000000000 8469953981059 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550782809/1250000000 : ℝ)^8435 ≤ (33879816919377/100000000000000 : ℝ)^6387 := by
    have hnat : (550782809 : ℕ)^8435*100000000000000^6387 ≤ 33879816919377^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550782809 1250000000 33879816919377 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848768807/2000000000 : ℝ), (2203131187/5000000000 : ℝ), (550782809/1250000000 : ℝ)] ![(16120183569191/50000000000000 : ℝ), (8469953981059/25000000000000 : ℝ), (33879816919377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848768807/2000000000 : ℝ)|^8435 ≤ (16120183569191/50000000000000 : ℝ)^6387
        have hw : |(848768807/2000000000 : ℝ)|=(848768807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203131187/5000000000 : ℝ)|^8435 ≤ (8469953981059/25000000000000 : ℝ)^6387
        have hw : |(2203131187/5000000000 : ℝ)|=(2203131187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550782809/1250000000 : ℝ)|^8435 ≤ (33879816919377/100000000000000 : ℝ)^6387
        have hw : |(550782809/1250000000 : ℝ)|=(550782809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_8 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192911811/10000000000 : ℝ)*x 0 + (5219150291/10000000000 : ℝ)*x 1 + (673057029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192911811/10000000000 : ℝ)^8435 ≤ (2696179036349/20000000000000 : ℝ)^6387 := by
    have hnat : (2192911811 : ℕ)^8435*20000000000000^6387 ≤ 2696179036349^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192911811 10000000000 2696179036349 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219150291/10000000000 : ℝ)^8435 ≤ (42368960234737/100000000000000 : ℝ)^6387 := by
    have hnat : (5219150291 : ℕ)^8435*100000000000000^6387 ≤ 42368960234737^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219150291 10000000000 42368960234737 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673057029/1250000000 : ℝ)^8435 ≤ (11037536141391/25000000000000 : ℝ)^6387 := by
    have hnat : (673057029 : ℕ)^8435*25000000000000^6387 ≤ 11037536141391^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673057029 1250000000 11037536141391 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192911811/10000000000 : ℝ), (5219150291/10000000000 : ℝ), (673057029/1250000000 : ℝ)] ![(2696179036349/20000000000000 : ℝ), (42368960234737/100000000000000 : ℝ), (11037536141391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192911811/10000000000 : ℝ)|^8435 ≤ (2696179036349/20000000000000 : ℝ)^6387
        have hw : |(-2192911811/10000000000 : ℝ)|=(2192911811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219150291/10000000000 : ℝ)|^8435 ≤ (42368960234737/100000000000000 : ℝ)^6387
        have hw : |(5219150291/10000000000 : ℝ)|=(5219150291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673057029/1250000000 : ℝ)|^8435 ≤ (11037536141391/25000000000000 : ℝ)^6387
        have hw : |(673057029/1250000000 : ℝ)|=(673057029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_9 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322503793/2500000000 : ℝ)*x 0 + (-1049235379/5000000000 : ℝ)*x 1 + (2692228017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322503793/2500000000 : ℝ)^8435 ≤ (43130352974099/100000000000000 : ℝ)^6387 := by
    have hnat : (1322503793 : ℕ)^8435*100000000000000^6387 ≤ 43130352974099^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322503793 2500000000 43130352974099 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049235379/5000000000 : ℝ)^8435 ≤ (6359752296373/50000000000000 : ℝ)^6387 := by
    have hnat : (1049235379 : ℕ)^8435*50000000000000^6387 ≤ 6359752296373^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049235379 5000000000 6359752296373 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692228017/5000000000 : ℝ)^8435 ≤ (44150142421471/100000000000000 : ℝ)^6387 := by
    have hnat : (2692228017 : ℕ)^8435*100000000000000^6387 ≤ 44150142421471^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692228017 5000000000 44150142421471 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322503793/2500000000 : ℝ), (-1049235379/5000000000 : ℝ), (2692228017/5000000000 : ℝ)] ![(43130352974099/100000000000000 : ℝ), (6359752296373/50000000000000 : ℝ), (44150142421471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322503793/2500000000 : ℝ)|^8435 ≤ (43130352974099/100000000000000 : ℝ)^6387
        have hw : |(1322503793/2500000000 : ℝ)|=(1322503793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049235379/5000000000 : ℝ)|^8435 ≤ (6359752296373/50000000000000 : ℝ)^6387
        have hw : |(-1049235379/5000000000 : ℝ)|=(1049235379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692228017/5000000000 : ℝ)|^8435 ≤ (44150142421471/100000000000000 : ℝ)^6387
        have hw : |(2692228017/5000000000 : ℝ)|=(2692228017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_10 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290015069/10000000000 : ℝ)*x 0 + (1346114083/2500000000 : ℝ)*x 1 + (-524617623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290015069/10000000000 : ℝ)^8435 ≤ (5391293983131/12500000000000 : ℝ)^6387 := by
    have hnat : (5290015069 : ℕ)^8435*12500000000000^6387 ≤ 5391293983131^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290015069 10000000000 5391293983131 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346114083/2500000000 : ℝ)^8435 ≤ (44150145648439/100000000000000 : ℝ)^6387 := by
    have hnat : (1346114083 : ℕ)^8435*100000000000000^6387 ≤ 44150145648439^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346114083 2500000000 44150145648439 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524617623/2500000000 : ℝ)^8435 ≤ (2543900492689/20000000000000 : ℝ)^6387 := by
    have hnat : (524617623 : ℕ)^8435*20000000000000^6387 ≤ 2543900492689^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524617623 2500000000 2543900492689 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290015069/10000000000 : ℝ), (1346114083/2500000000 : ℝ), (-524617623/2500000000 : ℝ)] ![(5391293983131/12500000000000 : ℝ), (44150145648439/100000000000000 : ℝ), (2543900492689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290015069/10000000000 : ℝ)|^8435 ≤ (5391293983131/12500000000000 : ℝ)^6387
        have hw : |(5290015069/10000000000 : ℝ)|=(5290015069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346114083/2500000000 : ℝ)|^8435 ≤ (44150145648439/100000000000000 : ℝ)^6387
        have hw : |(1346114083/2500000000 : ℝ)|=(1346114083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524617623/2500000000 : ℝ)|^8435 ≤ (2543900492689/20000000000000 : ℝ)^6387
        have hw : |(-524617623/2500000000 : ℝ)|=(524617623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_11 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2239600867/5000000000 : ℝ)*x 0 + (4288463021/10000000000 : ℝ)*x 1 + (4288463243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239600867/5000000000 : ℝ)^8435 ≤ (8655609391651/25000000000000 : ℝ)^6387 := by
    have hnat : (2239600867 : ℕ)^8435*25000000000000^6387 ≤ 8655609391651^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239600867 5000000000 8655609391651 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4288463021/10000000000 : ℝ)^8435 ≤ (8172195021483/25000000000000 : ℝ)^6387 := by
    have hnat : (4288463021 : ℕ)^8435*25000000000000^6387 ≤ 8172195021483^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288463021 10000000000 8172195021483 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288463243/10000000000 : ℝ)^8435 ≤ (32688782320729/100000000000000 : ℝ)^6387 := by
    have hnat : (4288463243 : ℕ)^8435*100000000000000^6387 ≤ 32688782320729^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288463243 10000000000 32688782320729 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239600867/5000000000 : ℝ), (4288463021/10000000000 : ℝ), (4288463243/10000000000 : ℝ)] ![(8655609391651/25000000000000 : ℝ), (8172195021483/25000000000000 : ℝ), (32688782320729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239600867/5000000000 : ℝ)|^8435 ≤ (8655609391651/25000000000000 : ℝ)^6387
        have hw : |(2239600867/5000000000 : ℝ)|=(2239600867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4288463021/10000000000 : ℝ)|^8435 ≤ (8172195021483/25000000000000 : ℝ)^6387
        have hw : |(4288463021/10000000000 : ℝ)|=(4288463021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4288463243/10000000000 : ℝ)|^8435 ≤ (32688782320729/100000000000000 : ℝ)^6387
        have hw : |(4288463243/10000000000 : ℝ)|=(4288463243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_12 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048659117/10000000000 : ℝ)*x 0 + (5436768957/10000000000 : ℝ)*x 1 + (5274205099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048659117/10000000000 : ℝ)^8435 ≤ (12322293514147/100000000000000 : ℝ)^6387 := by
    have hnat : (2048659117 : ℕ)^8435*100000000000000^6387 ≤ 12322293514147^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048659117 10000000000 12322293514147 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436768957/10000000000 : ℝ)^8435 ≤ (44717506589709/100000000000000 : ℝ)^6387 := by
    have hnat : (5436768957 : ℕ)^8435*100000000000000^6387 ≤ 44717506589709^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436768957 10000000000 44717506589709 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274205099/10000000000 : ℝ)^8435 ≤ (21480099939469/50000000000000 : ℝ)^6387 := by
    have hnat : (5274205099 : ℕ)^8435*50000000000000^6387 ≤ 21480099939469^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274205099 10000000000 21480099939469 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048659117/10000000000 : ℝ), (5436768957/10000000000 : ℝ), (5274205099/10000000000 : ℝ)] ![(12322293514147/100000000000000 : ℝ), (44717506589709/100000000000000 : ℝ), (21480099939469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048659117/10000000000 : ℝ)|^8435 ≤ (12322293514147/100000000000000 : ℝ)^6387
        have hw : |(-2048659117/10000000000 : ℝ)|=(2048659117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436768957/10000000000 : ℝ)|^8435 ≤ (44717506589709/100000000000000 : ℝ)^6387
        have hw : |(5436768957/10000000000 : ℝ)|=(5436768957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274205099/10000000000 : ℝ)|^8435 ≤ (21480099939469/50000000000000 : ℝ)^6387
        have hw : |(5274205099/10000000000 : ℝ)|=(5274205099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_13 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341933917/2500000000 : ℝ)*x 0 + (-535547303/2500000000 : ℝ)*x 1 + (210968199/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341933917/2500000000 : ℝ)^8435 ≤ (21984585957817/50000000000000 : ℝ)^6387 := by
    have hnat : (1341933917 : ℕ)^8435*50000000000000^6387 ≤ 21984585957817^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341933917 2500000000 21984585957817 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535547303/2500000000 : ℝ)^8435 ≤ (261412590483/2000000000000 : ℝ)^6387 := by
    have hnat : (535547303 : ℕ)^8435*2000000000000^6387 ≤ 261412590483^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535547303 2500000000 261412590483 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210968199/400000000 : ℝ)^8435 ≤ (42960198545051/100000000000000 : ℝ)^6387 := by
    have hnat : (210968199 : ℕ)^8435*100000000000000^6387 ≤ 42960198545051^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210968199 400000000 42960198545051 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341933917/2500000000 : ℝ), (-535547303/2500000000 : ℝ), (210968199/400000000 : ℝ)] ![(21984585957817/50000000000000 : ℝ), (261412590483/2000000000000 : ℝ), (42960198545051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341933917/2500000000 : ℝ)|^8435 ≤ (21984585957817/50000000000000 : ℝ)^6387
        have hw : |(1341933917/2500000000 : ℝ)|=(1341933917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535547303/2500000000 : ℝ)|^8435 ≤ (261412590483/2000000000000 : ℝ)^6387
        have hw : |(-535547303/2500000000 : ℝ)|=(535547303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210968199/400000000 : ℝ)|^8435 ≤ (42960198545051/100000000000000 : ℝ)^6387
        have hw : |(210968199/400000000 : ℝ)|=(210968199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_14 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683867831/5000000000 : ℝ)*x 0 + (5274204943/10000000000 : ℝ)*x 1 + (-2142189263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683867831/5000000000 : ℝ)^8435 ≤ (21984585925363/50000000000000 : ℝ)^6387 := by
    have hnat : (2683867831 : ℕ)^8435*50000000000000^6387 ≤ 21984585925363^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683867831 5000000000 21984585925363 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274204943/10000000000 : ℝ)^8435 ≤ (21480099100411/50000000000000 : ℝ)^6387 := by
    have hnat : (5274204943 : ℕ)^8435*50000000000000^6387 ≤ 21480099100411^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274204943 10000000000 21480099100411 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142189263/10000000000 : ℝ)^8435 ≤ (3267657483777/25000000000000 : ℝ)^6387 := by
    have hnat : (2142189263 : ℕ)^8435*25000000000000^6387 ≤ 3267657483777^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142189263 10000000000 3267657483777 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683867831/5000000000 : ℝ), (5274204943/10000000000 : ℝ), (-2142189263/10000000000 : ℝ)] ![(21984585925363/50000000000000 : ℝ), (21480099100411/50000000000000 : ℝ), (3267657483777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683867831/5000000000 : ℝ)|^8435 ≤ (21984585925363/50000000000000 : ℝ)^6387
        have hw : |(2683867831/5000000000 : ℝ)|=(2683867831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274204943/10000000000 : ℝ)|^8435 ≤ (21480099100411/50000000000000 : ℝ)^6387
        have hw : |(5274204943/10000000000 : ℝ)|=(5274204943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142189263/10000000000 : ℝ)|^8435 ≤ (3267657483777/25000000000000 : ℝ)^6387
        have hw : |(-2142189263/10000000000 : ℝ)|=(2142189263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_box_15 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056244759/2500000000 : ℝ)*x 0 + (2207786029/5000000000 : ℝ)*x 1 + (4415572361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056244759/2500000000 : ℝ)^8435 ≤ (1602561526841/5000000000000 : ℝ)^6387 := by
    have hnat : (1056244759 : ℕ)^8435*5000000000000^6387 ≤ 1602561526841^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056244759 2500000000 1602561526841 5000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207786029/5000000000 : ℝ)^8435 ≤ (4246797898327/12500000000000 : ℝ)^6387 := by
    have hnat : (2207786029 : ℕ)^8435*12500000000000^6387 ≤ 4246797898327^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207786029 5000000000 4246797898327 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415572361/10000000000 : ℝ)^8435 ≤ (6794877253103/20000000000000 : ℝ)^6387 := by
    have hnat : (4415572361 : ℕ)^8435*20000000000000^6387 ≤ 6794877253103^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415572361 10000000000 6794877253103 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056244759/2500000000 : ℝ), (2207786029/5000000000 : ℝ), (4415572361/10000000000 : ℝ)] ![(1602561526841/5000000000000 : ℝ), (4246797898327/12500000000000 : ℝ), (6794877253103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056244759/2500000000 : ℝ)|^8435 ≤ (1602561526841/5000000000000 : ℝ)^6387
        have hw : |(1056244759/2500000000 : ℝ)|=(1056244759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207786029/5000000000 : ℝ)|^8435 ≤ (4246797898327/12500000000000 : ℝ)^6387
        have hw : |(2207786029/5000000000 : ℝ)|=(2207786029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415572361/10000000000 : ℝ)|^8435 ≤ (6794877253103/20000000000000 : ℝ)^6387
        have hw : |(4415572361/10000000000 : ℝ)|=(4415572361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62247/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59377/100000 : ℝ) ∧ (80109/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41673/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11479/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (13444066984013199/100000000000000000000 : ℝ) := by
    have hpowers : (11479/100000 : ℝ)^4217 ≤ (13444066984013199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11479 : ℕ)^4217*100000000000000000000^1024 ≤ 13444066984013199^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11479 100000 13444066984013199 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11479/100000 : ℝ)) (X := (13444066984013199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (4217/1024 : ℝ) ≤ (6278877687927449/20000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^4217 ≤ (6278877687927449/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1763 : ℕ)^4217*20000000000000000000^1024 ≤ 6278877687927449^1024*12500^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 6278877687927449 20000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (6278877687927449/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013444066984013199/50000000000000000000 : ℝ) ≤ (400026113964297/400000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50013444066984013199/50000000000000000000 : ℝ)^1024 ≤ (400026113964297/400000000000000 : ℝ)^4217 := by
      have hnat : (50013444066984013199 : ℕ)^1024*400000000000000^4217 ≤ 400026113964297^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013444066984013199 50000000000000000000 400026113964297 400000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026113964297/400000000000000 : ℝ)) (X := (50013444066984013199/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011209613855912611/25000000000000000000 : ℝ) ≤ (10001088612432761/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (25011209613855912611/25000000000000000000 : ℝ)^1024 ≤ (10001088612432761/10000000000000000 : ℝ)^4217 := by
      have hnat : (25011209613855912611 : ℕ)^1024*10000000000000000^4217 ≤ 10001088612432761^4217*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011209613855912611 25000000000000000000 10001088612432761 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001088612432761/10000000000000000 : ℝ)) (X := (25011209613855912611/25000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006278877687927449/10000000000000000000 : ℝ) ≤ (10001524375758097/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (10006278877687927449/10000000000000000000 : ℝ)^1024 ≤ (10001524375758097/10000000000000000 : ℝ)^4217 := by
      have hnat : (10006278877687927449 : ℕ)^1024*10000000000000000^4217 ≤ 10001524375758097^4217*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006278877687927449 10000000000000000000 10001524375758097 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001524375758097/10000000000000000 : ℝ)) (X := (10006278877687927449/10000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13444066984013199/100000000000000000000 : ℝ) ≤ ((26241709474483926737/26250000000000000000 : ℝ)+2*(54470415667/32812500000000 : ℝ)*(11479/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26241709474483926737/26250000000000000000 : ℝ)+2*(54470415667/32812500000000 : ℝ)*(11479/100000 : ℝ)=(400026113964297/400000000000000 : ℝ) by norm_num, show 1+2*(13444066984013199/100000000000000000000 : ℝ)=(50013444066984013199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6278877687927449/20000000000000000000 : ℝ)+(13444066984013199/100000000000000000000 : ℝ) ≤ ((26241709474483926737/26250000000000000000 : ℝ)+(54470415667/32812500000000 : ℝ)*((1763/12500 : ℝ)+(11479/100000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (26241709474483926737/26250000000000000000 : ℝ)+(54470415667/32812500000000 : ℝ)*((1763/12500 : ℝ)+(11479/100000 : ℝ))=(10001088612432761/10000000000000000 : ℝ) by norm_num, show 1+(6278877687927449/20000000000000000000 : ℝ)+(13444066984013199/100000000000000000000 : ℝ)=(25011209613855912611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6278877687927449/20000000000000000000 : ℝ) ≤ ((26241709474483926737/26250000000000000000 : ℝ)+2*(54470415667/32812500000000 : ℝ)*(1763/12500 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26241709474483926737/26250000000000000000 : ℝ)+2*(54470415667/32812500000000 : ℝ)*(1763/12500 : ℝ)=(10001524375758097/10000000000000000 : ℝ) by norm_num, show 1+2*(6278877687927449/20000000000000000000 : ℝ)=(10006278877687927449/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26241709474483926737/26250000000000000000 : ℝ)*(X 1 0+X 2 0)+(54470415667/32812500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26241709474483926737/26250000000000000000 : ℝ)) (alpha := (54470415667/32812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26241709474483926737/26250000000000000000 : ℝ)*(X 0 1+X 2 1)+(54470415667/32812500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26241709474483926737/26250000000000000000 : ℝ)) (alpha := (54470415667/32812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26241709474483926737/26250000000000000000 : ℝ)*(X 0 2+X 1 2)+(54470415667/32812500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (26241709474483926737/26250000000000000000 : ℝ)) (alpha := (54470415667/32812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1996269521/10000000000 : ℝ)*X 0 0+(5374842873/10000000000 : ℝ)*X 0 1+(214993707/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296794523/10000000000 : ℝ)*X 1 0+(-525587301/2500000000 : ℝ)*X 1 1+(5374843007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296795391/10000000000 : ℝ)*X 2 0+(335927671/625000000 : ℝ)*X 2 1+(-1051174201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228652427/5000000000 : ℝ)*X 0 0+(4299552253/10000000000 : ℝ)*X 0 1+(2149775981/5000000000 : ℝ)*X 0 2+(2228652427/5000000000 : ℝ)*X 1 0+(4299552253/10000000000 : ℝ)*X 1 1+(2149775981/5000000000 : ℝ)*X 1 2+(2228652427/5000000000 : ℝ)*X 2 0+(4299552253/10000000000 : ℝ)*X 2 1+(2149775981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2245041847/10000000000 : ℝ)*X 0 0+(5282284847/10000000000 : ℝ)*X 0 1+(2641142439/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362041547/10000000000 : ℝ)*X 1 0+(-1069521323/5000000000 : ℝ)*X 1 1+(1320571201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681020759/5000000000 : ℝ)*X 2 0+(528228491/1000000000 : ℝ)*X 2 1+(-133690159/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848768807/2000000000 : ℝ)*X 0 0+(2203131187/5000000000 : ℝ)*X 0 1+(550782809/1250000000 : ℝ)*X 0 2+(848768807/2000000000 : ℝ)*X 1 0+(2203131187/5000000000 : ℝ)*X 1 1+(550782809/1250000000 : ℝ)*X 1 2+(848768807/2000000000 : ℝ)*X 2 0+(2203131187/5000000000 : ℝ)*X 2 1+(550782809/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2192911811/10000000000 : ℝ)*X 0 0+(5219150291/10000000000 : ℝ)*X 0 1+(673057029/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322503793/2500000000 : ℝ)*X 1 0+(-1049235379/5000000000 : ℝ)*X 1 1+(2692228017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290015069/10000000000 : ℝ)*X 2 0+(1346114083/2500000000 : ℝ)*X 2 1+(-524617623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2239600867/5000000000 : ℝ)*X 0 0+(4288463021/10000000000 : ℝ)*X 0 1+(4288463243/10000000000 : ℝ)*X 0 2+(2239600867/5000000000 : ℝ)*X 1 0+(4288463021/10000000000 : ℝ)*X 1 1+(4288463243/10000000000 : ℝ)*X 1 2+(2239600867/5000000000 : ℝ)*X 2 0+(4288463021/10000000000 : ℝ)*X 2 1+(4288463243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2048659117/10000000000 : ℝ)*X 0 0+(5436768957/10000000000 : ℝ)*X 0 1+(5274205099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1341933917/2500000000 : ℝ)*X 1 0+(-535547303/2500000000 : ℝ)*X 1 1+(210968199/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683867831/5000000000 : ℝ)*X 2 0+(5274204943/10000000000 : ℝ)*X 2 1+(-2142189263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1056244759/2500000000 : ℝ)*X 0 0+(2207786029/5000000000 : ℝ)*X 0 1+(4415572361/10000000000 : ℝ)*X 0 2+(1056244759/2500000000 : ℝ)*X 1 0+(2207786029/5000000000 : ℝ)*X 1 1+(4415572361/10000000000 : ℝ)*X 1 2+(1056244759/2500000000 : ℝ)*X 2 0+(2207786029/5000000000 : ℝ)*X 2 1+(4415572361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62247/100000 : ℝ) ≤ (-68079575311460318320329884999601/109375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44914027/50000000000000 : ℝ)*(upper0) + (56073409/50000000000000 : ℝ)*(upper1) + (13559679/25000000000000 : ℝ)*(upper3) + (148595103/100000000000000 : ℝ)*(upper5) + (2001555522730527/50000000000000 : ℝ)*(major0) + (2001555522730527/50000000000000 : ℝ)*(major1) + (2001555522730527/50000000000000 : ℝ)*(major2) + (2392733803/100000000000000 : ℝ)*(sp1) + (45474131/625000000000 : ℝ)*(sp3) + (2691700771060547/50000000000000 : ℝ)*(sp4) + (336462692854857/6250000000000 : ℝ)*(sp5) + (1076681095682303/20000000000000 : ℝ)*(sp6) + (1321778698848459/50000000000000 : ℝ)*(sp7) + (196814521/5000000000000 : ℝ)*(sp8) + (1321782336778939/50000000000000 : ℝ)*(f.failure) + (1076681095682303/20000000000000 : ℝ)*(f.sum) + (63096678613/1093750000000000000000000000 : ℝ)*base66 + (280879724111600019/62500000000000000000000000000000 : ℝ)*base67 + (1544563884513399981/62500000000000000000000000000000 : ℝ)*base70 + (202211797950899981/62500000000000000000000000000000 : ℝ)*base72 + (3409638144131/546875000000000000000000000 : ℝ)*base73 + (3981703890575899981/62500000000000000000000000000000 : ℝ)*base76 + (264462944013399981/62500000000000000000000000000000 : ℝ)*base78 + (242618014138399981/62500000000000000000000000000000 : ℝ)*base80 + (2395272491753/273437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (42607147/5000000000000000000000 : ℝ)*base90 + (42607147/5000000000000000000000 : ℝ)*base92 + (42607147/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59377/100000 : ℝ) ≤ (1159761449782032400301829379967/1953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252142359/100000000000000 : ℝ)*(lower1) + (456310649/100000000000000 : ℝ)*(lower2) + (201164081/100000000000000 : ℝ)*(upper4) + (254309047177787/6250000000000 : ℝ)*(major0) + (254309047177787/6250000000000 : ℝ)*(major1) + (254309047177787/6250000000000 : ℝ)*(major2) + (5431040349857949/100000000000000 : ℝ)*(sp0) + (1086193125222313/20000000000000 : ℝ)*(sp1) + (5431037392798969/100000000000000 : ℝ)*(sp2) + (10748081790323/400000000000 : ℝ)*(sp3) + (476934957/2500000000000 : ℝ)*(sp6) + (1208114681/6250000000000 : ℝ)*(sp7) + (16120339299/100000000000000 : ℝ)*(sp8) + (90844085683/100000000000000 : ℝ)*(sp9) + (2687039777415647/100000000000000 : ℝ)*(f.failure) + (5303766084177/97656250000 : ℝ)*(f.sum) + (3650637237083/937500000000000000000000000 : ℝ)*base65 + (168611452748751283/23437500000000000000000000000000 : ℝ)*base68 + (122601835912813783/23437500000000000000000000000000 : ℝ)*base70 + (157081191993436217/23437500000000000000000000000000 : ℝ)*base71 + (79309870013/58593750000000000000000000 : ℝ)*base73 + (259856575772188783/23437500000000000000000000000000 : ℝ)*base76 + (207456306787813783/23437500000000000000000000000000 : ℝ)*base78 + (323351933170626283/23437500000000000000000000000000 : ℝ)*base80 + (2341550100833/937500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (91961969/10000000000000000000000 : ℝ)*base89 + (91961969/10000000000000000000000 : ℝ)*base91 + (91961969/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80109/100000 : ℝ) ≤ (175243485479204057147829693964251/218750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190335313/100000000000000 : ℝ)*(lower3) + (35350351/100000000000000 : ℝ)*(upper4) + (9388677/50000000000000 : ℝ)*(lower5) + (4535686730878923/100000000000000 : ℝ)*(major0) + (4535686730878923/100000000000000 : ℝ)*(major1) + (4535686730878923/100000000000000 : ℝ)*(major2) + (84829557/1250000000000 : ℝ)*(sp0) + (40092067643/50000000000000 : ℝ)*(sp1) + (7006435869/3125000000000 : ℝ)*(sp2) + (97880393393/100000000000000 : ℝ)*(sp3) + (6049397205099209/100000000000000 : ℝ)*(sp8) + (1512330951832121/25000000000000 : ℝ)*(sp9) + (6049179785515961/100000000000000 : ℝ)*(sp10) + (599033564136959/20000000000000 : ℝ)*(sp11) + (748816425269547/25000000000000 : ℝ)*(f.failure) + (604940399146377/10000000000000 : ℝ)*(f.sum) + (6283810392499/4375000000000000000000000000 : ℝ)*base66 + (226219692605368369/125000000000000000000000000000000 : ℝ)*base68 + (2457840307105368369/125000000000000000000000000000000 : ℝ)*base70 + (1316823586980368369/125000000000000000000000000000000 : ℝ)*base72 + (7493188864531/1093750000000000000000000000 : ℝ)*base74 + (1222715178355368369/125000000000000000000000000000000 : ℝ)*base76 + (855245013355368369/125000000000000000000000000000000 : ℝ)*base78 + (1063100677269631631/125000000000000000000000000000000 : ℝ)*base79 + (23518338586249/4375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5167269/2500000000000000000000 : ℝ)*base89 + (5167269/2500000000000000000000 : ℝ)*base91 + (5167269/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41673/50000 : ℝ) ≤ (-182313413971755068862310620981401/218750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30552133/100000000000000 : ℝ)*(lower0) + (52985003/50000000000000 : ℝ)*(lower1) + (31411791/100000000000000 : ℝ)*(lower4) + (4571183694229127/100000000000000 : ℝ)*(major0) + (4571183694229127/100000000000000 : ℝ)*(major1) + (4571183694229127/100000000000000 : ℝ)*(major2) + (6720290209/100000000000000 : ℝ)*(sp0) + (38657880561/12500000000000 : ℝ)*(sp5) + (178972507837/50000000000000 : ℝ)*(sp6) + (8566754619/100000000000000 : ℝ)*(sp7) + (1230286932194683/20000000000000 : ℝ)*(sp12) + (1230226423643827/20000000000000 : ℝ)*(sp13) + (123021668724959/2000000000000 : ℝ)*(sp14) + (3018698532092831/100000000000000 : ℝ)*(sp15) + (60374141976949/2000000000000 : ℝ)*(f.failure) + (6151441381263623/100000000000000 : ℝ)*(f.sum) + (857763536453/13125000000000000000000000000 : ℝ)*base66 + (6881293449739047343/375000000000000000000000000000000 : ℝ)*base68 + (6378674950864047343/375000000000000000000000000000000 : ℝ)*base70 + (1035065342614047343/375000000000000000000000000000000 : ℝ)*base72 + (168957061509793/3281250000000000000000000000 : ℝ)*base73 + (7234141757239047343/375000000000000000000000000000000 : ℝ)*base76 + (995013811114047343/375000000000000000000000000000000 : ℝ)*base78 + (22617073708510952657/375000000000000000000000000000000 : ℝ)*base79 + (21288959058953/13125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1024123/200000000000000000000 : ℝ)*base89 + (1024123/200000000000000000000 : ℝ)*base91 + (1024123/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1242_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59377/100000 : ℝ) else (80109/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41673/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1242_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1242_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59377/100000 : ℝ) else (80109/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41673/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1242_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59377/100000 : ℝ) else (80109/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41673/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

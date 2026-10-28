-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:54.838518+00:00
-- url     : https://prove2.me/submissions/293073af-f224-4ebf-9977-9d72ee0bd59c

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
theorem support_rectangle_w1128_s6_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173567927/10000000000 : ℝ)*x 0 + (2696831739/5000000000 : ℝ)*x 1 + (164536039/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173567927/10000000000 : ℝ)^8321 ≤ (13206097038219/100000000000000 : ℝ)^6273 := by
    have hnat : (2173567927 : ℕ)^8321*100000000000000^6273 ≤ 13206097038219^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173567927 10000000000 13206097038219 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696831739/5000000000 : ℝ)^8321 ≤ (44090971784707/100000000000000 : ℝ)^6273 := by
    have hnat : (2696831739 : ℕ)^8321*100000000000000^6273 ≤ 44090971784707^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696831739 5000000000 44090971784707 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164536039/312500000 : ℝ)^8321 ≤ (42702931166307/100000000000000 : ℝ)^6273 := by
    have hnat : (164536039 : ℕ)^8321*100000000000000^6273 ≤ 42702931166307^6273*312500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164536039 312500000 42702931166307 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173567927/10000000000 : ℝ), (2696831739/5000000000 : ℝ), (164536039/312500000 : ℝ)] ![(13206097038219/100000000000000 : ℝ), (44090971784707/100000000000000 : ℝ), (42702931166307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173567927/10000000000 : ℝ)|^8321 ≤ (13206097038219/100000000000000 : ℝ)^6273
        have hw : |(-2173567927/10000000000 : ℝ)|=(2173567927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696831739/5000000000 : ℝ)|^8321 ≤ (44090971784707/100000000000000 : ℝ)^6273
        have hw : |(2696831739/5000000000 : ℝ)|=(2696831739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164536039/312500000 : ℝ)|^8321 ≤ (42702931166307/100000000000000 : ℝ)^6273
        have hw : |(164536039/312500000 : ℝ)|=(164536039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672451031/5000000000 : ℝ)*x 0 + (-279844931/1250000000 : ℝ)*x 1 + (164536039/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672451031/5000000000 : ℝ)^8321 ≤ (43563013425847/100000000000000 : ℝ)^6273 := by
    have hnat : (2672451031 : ℕ)^8321*100000000000000^6273 ≤ 43563013425847^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672451031 5000000000 43563013425847 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279844931/1250000000 : ℝ)^8321 ≤ (13734055392289/100000000000000 : ℝ)^6273 := by
    have hnat : (279844931 : ℕ)^8321*100000000000000^6273 ≤ 13734055392289^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279844931 1250000000 13734055392289 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164536039/312500000 : ℝ)^8321 ≤ (42702931166307/100000000000000 : ℝ)^6273 := by
    have hnat : (164536039 : ℕ)^8321*100000000000000^6273 ≤ 42702931166307^6273*312500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164536039 312500000 42702931166307 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672451031/5000000000 : ℝ), (-279844931/1250000000 : ℝ), (164536039/312500000 : ℝ)] ![(43563013425847/100000000000000 : ℝ), (13734055392289/100000000000000 : ℝ), (42702931166307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672451031/5000000000 : ℝ)|^8321 ≤ (43563013425847/100000000000000 : ℝ)^6273
        have hw : |(2672451031/5000000000 : ℝ)|=(2672451031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279844931/1250000000 : ℝ)|^8321 ≤ (13734055392289/100000000000000 : ℝ)^6273
        have hw : |(-279844931/1250000000 : ℝ)|=(279844931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164536039/312500000 : ℝ)|^8321 ≤ (42702931166307/100000000000000 : ℝ)^6273
        have hw : |(164536039/312500000 : ℝ)|=(164536039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344902053/10000000000 : ℝ)*x 0 + (2632576629/5000000000 : ℝ)*x 1 + (-2238759447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344902053/10000000000 : ℝ)^8321 ≤ (8712602665709/20000000000000 : ℝ)^6273 := by
    have hnat : (5344902053 : ℕ)^8321*20000000000000^6273 ≤ 8712602665709^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344902053 10000000000 8712602665709 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632576629/5000000000 : ℝ)^8321 ≤ (42702931273891/100000000000000 : ℝ)^6273 := by
    have hnat : (2632576629 : ℕ)^8321*100000000000000^6273 ≤ 42702931273891^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632576629 5000000000 42702931273891 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238759447/10000000000 : ℝ)^8321 ≤ (13734055384151/100000000000000 : ℝ)^6273 := by
    have hnat : (2238759447 : ℕ)^8321*100000000000000^6273 ≤ 13734055384151^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238759447 10000000000 13734055384151 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344902053/10000000000 : ℝ), (2632576629/5000000000 : ℝ), (-2238759447/10000000000 : ℝ)] ![(8712602665709/20000000000000 : ℝ), (42702931273891/100000000000000 : ℝ), (13734055384151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344902053/10000000000 : ℝ)|^8321 ≤ (8712602665709/20000000000000 : ℝ)^6273
        have hw : |(5344902053/10000000000 : ℝ)|=(5344902053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632576629/5000000000 : ℝ)|^8321 ≤ (42702931273891/100000000000000 : ℝ)^6273
        have hw : |(2632576629/5000000000 : ℝ)|=(2632576629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238759447/10000000000 : ℝ)|^8321 ≤ (13734055384151/100000000000000 : ℝ)^6273
        have hw : |(-2238759447/10000000000 : ℝ)|=(2238759447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436663041/1000000000 : ℝ)*x 0 + (4241005319/10000000000 : ℝ)*x 1 + (4495971199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436663041/1000000000 : ℝ)^8321 ≤ (16658349362173/50000000000000 : ℝ)^6273 := by
    have hnat : (436663041 : ℕ)^8321*50000000000000^6273 ≤ 16658349362173^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436663041 1000000000 16658349362173 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241005319/10000000000 : ℝ)^8321 ≤ (16025639824113/50000000000000 : ℝ)^6273 := by
    have hnat : (4241005319 : ℕ)^8321*50000000000000^6273 ≤ 16025639824113^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241005319 10000000000 16025639824113 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495971199/10000000000 : ℝ)^8321 ≤ (6926404321759/20000000000000 : ℝ)^6273 := by
    have hnat : (4495971199 : ℕ)^8321*20000000000000^6273 ≤ 6926404321759^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495971199 10000000000 6926404321759 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436663041/1000000000 : ℝ), (4241005319/10000000000 : ℝ), (4495971199/10000000000 : ℝ)] ![(16658349362173/50000000000000 : ℝ), (16025639824113/50000000000000 : ℝ), (6926404321759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436663041/1000000000 : ℝ)|^8321 ≤ (16658349362173/50000000000000 : ℝ)^6273
        have hw : |(436663041/1000000000 : ℝ)|=(436663041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241005319/10000000000 : ℝ)|^8321 ≤ (16025639824113/50000000000000 : ℝ)^6273
        have hw : |(4241005319/10000000000 : ℝ)|=(4241005319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495971199/10000000000 : ℝ)|^8321 ≤ (6926404321759/20000000000000 : ℝ)^6273
        have hw : |(4495971199/10000000000 : ℝ)|=(4495971199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16981039/78125000 : ℝ)*x 0 + (658184719/1250000000 : ℝ)*x 1 + (1348334437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16981039/78125000 : ℝ)^8321 ≤ (6603068929491/50000000000000 : ℝ)^6273 := by
    have hnat : (16981039 : ℕ)^8321*50000000000000^6273 ≤ 6603068929491^6273*78125000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16981039 78125000 6603068929491 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658184719/1250000000 : ℝ)^8321 ≤ (42706422338971/100000000000000 : ℝ)^6273 := by
    have hnat : (658184719 : ℕ)^8321*100000000000000^6273 ≤ 42706422338971^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658184719 1250000000 42706422338971 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348334437/2500000000 : ℝ)^8321 ≤ (352699518353/800000000000 : ℝ)^6273 := by
    have hnat : (1348334437 : ℕ)^8321*800000000000^6273 ≤ 352699518353^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348334437 2500000000 352699518353 800000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16981039/78125000 : ℝ), (658184719/1250000000 : ℝ), (1348334437/2500000000 : ℝ)] ![(6603068929491/50000000000000 : ℝ), (42706422338971/100000000000000 : ℝ), (352699518353/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16981039/78125000 : ℝ)|^8321 ≤ (6603068929491/50000000000000 : ℝ)^6273
        have hw : |(-16981039/78125000 : ℝ)|=(16981039/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658184719/1250000000 : ℝ)|^8321 ≤ (42706422338971/100000000000000 : ℝ)^6273
        have hw : |(658184719/1250000000 : ℝ)|=(658184719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348334437/2500000000 : ℝ)|^8321 ≤ (352699518353/800000000000 : ℝ)^6273
        have hw : |(1348334437/2500000000 : ℝ)|=(1348334437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312377477/10000000000 : ℝ)*x 0 + (-2110574953/10000000000 : ℝ)*x 1 + (2696668871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312377477/10000000000 : ℝ)^8321 ≤ (21605864880967/50000000000000 : ℝ)^6273 := by
    have hnat : (5312377477 : ℕ)^8321*50000000000000^6273 ≤ 21605864880967^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312377477 10000000000 21605864880967 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110574953/10000000000 : ℝ)^8321 ≤ (12700830499087/100000000000000 : ℝ)^6273 := by
    have hnat : (2110574953 : ℕ)^8321*100000000000000^6273 ≤ 12700830499087^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110574953 10000000000 12700830499087 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696668871/5000000000 : ℝ)^8321 ≤ (22043719864533/50000000000000 : ℝ)^6273 := by
    have hnat : (2696668871 : ℕ)^8321*50000000000000^6273 ≤ 22043719864533^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696668871 5000000000 22043719864533 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312377477/10000000000 : ℝ), (-2110574953/10000000000 : ℝ), (2696668871/5000000000 : ℝ)] ![(21605864880967/50000000000000 : ℝ), (12700830499087/100000000000000 : ℝ), (22043719864533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312377477/10000000000 : ℝ)|^8321 ≤ (21605864880967/50000000000000 : ℝ)^6273
        have hw : |(5312377477/10000000000 : ℝ)|=(5312377477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110574953/10000000000 : ℝ)|^8321 ≤ (12700830499087/100000000000000 : ℝ)^6273
        have hw : |(-2110574953/10000000000 : ℝ)|=(2110574953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696668871/5000000000 : ℝ)|^8321 ≤ (22043719864533/50000000000000 : ℝ)^6273
        have hw : |(2696668871/5000000000 : ℝ)|=(2696668871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312377523/10000000000 : ℝ)*x 0 + (2696668821/5000000000 : ℝ)*x 1 + (-2110575027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312377523/10000000000 : ℝ)^8321 ≤ (5401466282283/12500000000000 : ℝ)^6273 := by
    have hnat : (5312377523 : ℕ)^8321*12500000000000^6273 ≤ 5401466282283^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312377523 10000000000 5401466282283 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696668821/5000000000 : ℝ)^8321 ≤ (22043719322373/50000000000000 : ℝ)^6273 := by
    have hnat : (2696668821 : ℕ)^8321*50000000000000^6273 ≤ 22043719322373^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696668821 5000000000 22043719322373 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110575027/10000000000 : ℝ)^8321 ≤ (6350415544891/50000000000000 : ℝ)^6273 := by
    have hnat : (2110575027 : ℕ)^8321*50000000000000^6273 ≤ 6350415544891^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110575027 10000000000 6350415544891 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312377523/10000000000 : ℝ), (2696668821/5000000000 : ℝ), (-2110575027/10000000000 : ℝ)] ![(5401466282283/12500000000000 : ℝ), (22043719322373/50000000000000 : ℝ), (6350415544891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312377523/10000000000 : ℝ)|^8321 ≤ (5401466282283/12500000000000 : ℝ)^6273
        have hw : |(5312377523/10000000000 : ℝ)|=(5312377523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696668821/5000000000 : ℝ)|^8321 ≤ (22043719322373/50000000000000 : ℝ)^6273
        have hw : |(2696668821/5000000000 : ℝ)|=(2696668821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110575027/10000000000 : ℝ)|^8321 ≤ (6350415544891/50000000000000 : ℝ)^6273
        have hw : |(-2110575027/10000000000 : ℝ)|=(2110575027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s6_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366640327/10000000000 : ℝ)*x 0 + (179813091/400000000 : ℝ)*x 1 + (4241651591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366640327/10000000000 : ℝ)^8321 ≤ (33316799092569/100000000000000 : ℝ)^6273 := by
    have hnat : (4366640327 : ℕ)^8321*100000000000000^6273 ≤ 33316799092569^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366640327 10000000000 33316799092569 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179813091/400000000 : ℝ)^8321 ≤ (34625442319001/100000000000000 : ℝ)^6273 := by
    have hnat : (179813091 : ℕ)^8321*100000000000000^6273 ≤ 34625442319001^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179813091 400000000 34625442319001 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241651591/10000000000 : ℝ)^8321 ≤ (16028879286473/50000000000000 : ℝ)^6273 := by
    have hnat : (4241651591 : ℕ)^8321*50000000000000^6273 ≤ 16028879286473^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241651591 10000000000 16028879286473 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366640327/10000000000 : ℝ), (179813091/400000000 : ℝ), (4241651591/10000000000 : ℝ)] ![(33316799092569/100000000000000 : ℝ), (34625442319001/100000000000000 : ℝ), (16028879286473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366640327/10000000000 : ℝ)|^8321 ≤ (33316799092569/100000000000000 : ℝ)^6273
        have hw : |(4366640327/10000000000 : ℝ)|=(4366640327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179813091/400000000 : ℝ)|^8321 ≤ (34625442319001/100000000000000 : ℝ)^6273
        have hw : |(179813091/400000000 : ℝ)|=(179813091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241651591/10000000000 : ℝ)|^8321 ≤ (16028879286473/50000000000000 : ℝ)^6273
        have hw : |(4241651591/10000000000 : ℝ)|=(4241651591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11327/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5647/50000 : ℝ) ^ (65/16 : ℝ) ≤ (14196919509171321/100000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^65 ≤ (14196919509171321/100000000000000000000 : ℝ)^16 := by
      have hnat : (5647 : ℕ)^65*100000000000000000000^16 ≤ 14196919509171321^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 14196919509171321 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (14196919509171321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (65/16 : ℝ) ≤ (34799593094342281/100000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^65 ≤ (34799593094342281/100000000000000000000 : ℝ)^16 := by
      have hnat : (14083 : ℕ)^65*100000000000000000000^16 ≤ 34799593094342281^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 34799593094342281 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (34799593094342281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014196919509171321/50000000000000000000 : ℝ) ≤ (10000698850479527/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50014196919509171321/50000000000000000000 : ℝ)^16 ≤ (10000698850479527/10000000000000000 : ℝ)^65 := by
      have hnat : (50014196919509171321 : ℕ)^16*10000000000000000^65 ≤ 10000698850479527^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014196919509171321 50000000000000000000 10000698850479527 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000698850479527/10000000000000000 : ℝ)) (X := (50014196919509171321/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024498256301756801/50000000000000000000 : ℝ) ≤ (10001205845330699/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50024498256301756801/50000000000000000000 : ℝ)^16 ≤ (10001205845330699/10000000000000000 : ℝ)^65 := by
      have hnat : (50024498256301756801 : ℕ)^16*10000000000000000^65 ≤ 10001205845330699^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024498256301756801 50000000000000000000 10001205845330699 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001205845330699/10000000000000000 : ℝ)) (X := (50024498256301756801/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034799593094342281/50000000000000000000 : ℝ) ≤ (10001712840181871/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50034799593094342281/50000000000000000000 : ℝ)^16 ≤ (10001712840181871/10000000000000000 : ℝ)^65 := by
      have hnat : (50034799593094342281 : ℕ)^16*10000000000000000^65 ≤ 10001712840181871^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034799593094342281 50000000000000000000 10001712840181871 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712840181871/10000000000000000 : ℝ)) (X := (50034799593094342281/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14196919509171321/100000000000000000000 : ℝ) ≤ ((27880497094289127667/27890000000000000000 : ℝ)+2*(126748712793/69725000000000 : ℝ)*(5647/50000 : ℝ))^(65/16 : ℝ) := by
    rw [show (27880497094289127667/27890000000000000000 : ℝ)+2*(126748712793/69725000000000 : ℝ)*(5647/50000 : ℝ)=(10000698850479527/10000000000000000 : ℝ) by norm_num, show 1+2*(14196919509171321/100000000000000000000 : ℝ)=(50014196919509171321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34799593094342281/100000000000000000000 : ℝ)+(14196919509171321/100000000000000000000 : ℝ) ≤ ((27880497094289127667/27890000000000000000 : ℝ)+(126748712793/69725000000000 : ℝ)*((14083/100000 : ℝ)+(5647/50000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (27880497094289127667/27890000000000000000 : ℝ)+(126748712793/69725000000000 : ℝ)*((14083/100000 : ℝ)+(5647/50000 : ℝ))=(10001205845330699/10000000000000000 : ℝ) by norm_num, show 1+(34799593094342281/100000000000000000000 : ℝ)+(14196919509171321/100000000000000000000 : ℝ)=(50024498256301756801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34799593094342281/100000000000000000000 : ℝ) ≤ ((27880497094289127667/27890000000000000000 : ℝ)+2*(126748712793/69725000000000 : ℝ)*(14083/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (27880497094289127667/27890000000000000000 : ℝ)+2*(126748712793/69725000000000 : ℝ)*(14083/100000 : ℝ)=(10001712840181871/10000000000000000 : ℝ) by norm_num, show 1+2*(34799593094342281/100000000000000000000 : ℝ)=(50034799593094342281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27880497094289127667/27890000000000000000 : ℝ)*(X 1 0+X 2 0)+(126748712793/69725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (27880497094289127667/27890000000000000000 : ℝ)) (alpha := (126748712793/69725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27880497094289127667/27890000000000000000 : ℝ)*(X 0 1+X 2 1)+(126748712793/69725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (27880497094289127667/27890000000000000000 : ℝ)) (alpha := (126748712793/69725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27880497094289127667/27890000000000000000 : ℝ)*(X 0 2+X 1 2)+(126748712793/69725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (27880497094289127667/27890000000000000000 : ℝ)) (alpha := (126748712793/69725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173567927/10000000000 : ℝ)*X 0 0+(2696831739/5000000000 : ℝ)*X 0 1+(164536039/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672451031/5000000000 : ℝ)*X 1 0+(-279844931/1250000000 : ℝ)*X 1 1+(164536039/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344902053/10000000000 : ℝ)*X 2 0+(2632576629/5000000000 : ℝ)*X 2 1+(-2238759447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436663041/1000000000 : ℝ)*X 0 0+(4241005319/10000000000 : ℝ)*X 0 1+(4495971199/10000000000 : ℝ)*X 0 2+(436663041/1000000000 : ℝ)*X 1 0+(4241005319/10000000000 : ℝ)*X 1 1+(4495971199/10000000000 : ℝ)*X 1 2+(436663041/1000000000 : ℝ)*X 2 0+(4241005319/10000000000 : ℝ)*X 2 1+(4495971199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16981039/78125000 : ℝ)*X 0 0+(658184719/1250000000 : ℝ)*X 0 1+(1348334437/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312377477/10000000000 : ℝ)*X 1 0+(-2110574953/10000000000 : ℝ)*X 1 1+(2696668871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312377523/10000000000 : ℝ)*X 2 0+(2696668821/5000000000 : ℝ)*X 2 1+(-2110575027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366640327/10000000000 : ℝ)*X 0 0+(179813091/400000000 : ℝ)*X 0 1+(4241651591/10000000000 : ℝ)*X 0 2+(4366640327/10000000000 : ℝ)*X 1 0+(179813091/400000000 : ℝ)*X 1 1+(4241651591/10000000000 : ℝ)*X 1 2+(4366640327/10000000000 : ℝ)*X 2 0+(179813091/400000000 : ℝ)*X 2 1+(4241651591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (715855912995607623753/108945312500000000000000000 : ℝ) := by norm_num
    linear_combination (1346035197/100000000000000 : ℝ)*(base19) + (1227871509/100000000000000 : ℝ)*(base23) + (28076967/50000000000000 : ℝ)*(lower2) + (688131/400000000000 : ℝ)*(upper3) + (9346743/10000000000000 : ℝ)*(upper5) + (2925921896412947/50000000000000 : ℝ)*(major0) + (2925921896412947/50000000000000 : ℝ)*(major1) + (2925921896412947/50000000000000 : ℝ)*(major2) + (38907600785773/500000000000 : ℝ)*(sp0) + (1556311021982847/20000000000000 : ℝ)*(sp1) + (7781555228077923/100000000000000 : ℝ)*(sp2) + (3922111077435791/100000000000000 : ℝ)*(sp3) + (2268674677/6250000000000 : ℝ)*(sp4) + (1983324049/10000000000000 : ℝ)*(sp7) + (3922130910676281/100000000000000 : ℝ)*(f.failure) + (972694556993679/12500000000000 : ℝ)*(f.sum) + (2471992579637/3486250000000000000000000000 : ℝ)*base65 + (1075562784290395351/1394500000000000000000000000000000 : ℝ)*base68 + (9121371804165604649/1394500000000000000000000000000000 : ℝ)*base69 + (8665460981528104649/1394500000000000000000000000000000 : ℝ)*base71 + (37051482624287/13945000000000000000000000000 : ℝ)*base74 + (11030026353642395351/1394500000000000000000000000000000 : ℝ)*base76 + (5050884421347604649/1394500000000000000000000000000000 : ℝ)*base77 + (1958346365605395351/1394500000000000000000000000000000 : ℝ)*base80 + (16197760355621/6972500000000000000000000000 : ℝ)*base82 + (800041/625000000000000000000 : ℝ)*base90 + (800041/625000000000000000000 : ℝ)*base92 + (800041/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34661994107186891489037/6972500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9067211/800000000000 : ℝ)*(base19) + (1179821037/100000000000000 : ℝ)*(base23) + (7436987/100000000000000 : ℝ)*(upper2) + (98975093/100000000000000 : ℝ)*(upper3) + (147709871/100000000000000 : ℝ)*(upper5) + (5881548734916647/100000000000000 : ℝ)*(major0) + (5881548734916647/100000000000000 : ℝ)*(major1) + (5881548734916647/100000000000000 : ℝ)*(major2) + (65289021/200000000000 : ℝ)*(sp1) + (13439233111/50000000000000 : ℝ)*(sp2) + (1564211399620593/20000000000000 : ℝ)*(sp4) + (7821023220191091/100000000000000 : ℝ)*(sp5) + (7821028939815707/100000000000000 : ℝ)*(sp6) + (394204030602221/10000000000000 : ℝ)*(sp7) + (394204030602221/10000000000000 : ℝ)*(f.failure) + (1564211399620593/20000000000000 : ℝ)*(f.sum) + (11383580288367/6972500000000000000000000000 : ℝ)*base65 + (21632013928344972549/2789000000000000000000000000000000 : ℝ)*base67 + (8785192439844972549/2789000000000000000000000000000000 : ℝ)*base69 + (27234776438138027451/2789000000000000000000000000000000 : ℝ)*base72 + (72471482533769/13945000000000000000000000000 : ℝ)*base73 + (20394267411033027451/2789000000000000000000000000000000 : ℝ)*base76 + (13828050983818027451/2789000000000000000000000000000000 : ℝ)*base78 + (34184021410734972549/2789000000000000000000000000000000 : ℝ)*base79 + (47953972570569/13945000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (63381/62500000000000000000 : ℝ)*base90 + (63381/62500000000000000000 : ℝ)*base92 + (63381/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1128_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s7_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-543399039/2500000000 : ℝ)*x 0 + (2696659263/5000000000 : ℝ)*x 1 + (1316369943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543399039/2500000000 : ℝ)^8321 ≤ (13206324546871/100000000000000 : ℝ)^6273 := by
    have hnat : (543399039 : ℕ)^8321*100000000000000^6273 ≤ 13206324546871^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543399039 2500000000 13206324546871 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696659263/5000000000 : ℝ)^8321 ≤ (22043615683121/50000000000000 : ℝ)^6273 := by
    have hnat : (2696659263 : ℕ)^8321*50000000000000^6273 ≤ 22043615683121^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696659263 5000000000 22043615683121 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316369943/2500000000 : ℝ)^8321 ≤ (21353222035669/50000000000000 : ℝ)^6273 := by
    have hnat : (1316369943 : ℕ)^8321*50000000000000^6273 ≤ 21353222035669^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316369943 2500000000 21353222035669 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543399039/2500000000 : ℝ), (2696659263/5000000000 : ℝ), (1316369943/2500000000 : ℝ)] ![(13206324546871/100000000000000 : ℝ), (22043615683121/50000000000000 : ℝ), (21353222035669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543399039/2500000000 : ℝ)|^8321 ≤ (13206324546871/100000000000000 : ℝ)^6273
        have hw : |(-543399039/2500000000 : ℝ)|=(543399039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696659263/5000000000 : ℝ)|^8321 ≤ (22043615683121/50000000000000 : ℝ)^6273
        have hw : |(2696659263/5000000000 : ℝ)|=(2696659263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316369943/2500000000 : ℝ)|^8321 ≤ (21353222035669/50000000000000 : ℝ)^6273
        have hw : |(1316369943/2500000000 : ℝ)|=(1316369943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336203979/2500000000 : ℝ)*x 0 + (-1119221093/5000000000 : ℝ)*x 1 + (2632739891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336203979/2500000000 : ℝ)^8321 ≤ (21781041038511/50000000000000 : ℝ)^6273 := by
    have hnat : (1336203979 : ℕ)^8321*50000000000000^6273 ≤ 21781041038511^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336203979 2500000000 21781041038511 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119221093/5000000000 : ℝ)^8321 ≤ (13731473728947/100000000000000 : ℝ)^6273 := by
    have hnat : (1119221093 : ℕ)^8321*100000000000000^6273 ≤ 13731473728947^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119221093 5000000000 13731473728947 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632739891/5000000000 : ℝ)^8321 ≤ (10676611044731/25000000000000 : ℝ)^6273 := by
    have hnat : (2632739891 : ℕ)^8321*25000000000000^6273 ≤ 10676611044731^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632739891 5000000000 10676611044731 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336203979/2500000000 : ℝ), (-1119221093/5000000000 : ℝ), (2632739891/5000000000 : ℝ)] ![(21781041038511/50000000000000 : ℝ), (13731473728947/100000000000000 : ℝ), (10676611044731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336203979/2500000000 : ℝ)|^8321 ≤ (21781041038511/50000000000000 : ℝ)^6273
        have hw : |(1336203979/2500000000 : ℝ)|=(1336203979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119221093/5000000000 : ℝ)|^8321 ≤ (13731473728947/100000000000000 : ℝ)^6273
        have hw : |(-1119221093/5000000000 : ℝ)|=(1119221093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632739891/5000000000 : ℝ)|^8321 ≤ (10676611044731/25000000000000 : ℝ)^6273
        have hw : |(2632739891/5000000000 : ℝ)|=(2632739891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66810199/125000000 : ℝ)*x 0 + (658184973/1250000000 : ℝ)*x 1 + (-1119221089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66810199/125000000 : ℝ)^8321 ≤ (43562082120267/100000000000000 : ℝ)^6273 := by
    have hnat : (66810199 : ℕ)^8321*100000000000000^6273 ≤ 43562082120267^6273*125000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66810199 125000000 43562082120267 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658184973/1250000000 : ℝ)^8321 ≤ (42706444200441/100000000000000 : ℝ)^6273 := by
    have hnat : (658184973 : ℕ)^8321*100000000000000^6273 ≤ 42706444200441^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658184973 1250000000 42706444200441 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119221089/5000000000 : ℝ)^8321 ≤ (274629473277/2000000000000 : ℝ)^6273 := by
    have hnat : (1119221089 : ℕ)^8321*2000000000000^6273 ≤ 274629473277^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119221089 5000000000 274629473277 2000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66810199/125000000 : ℝ), (658184973/1250000000 : ℝ), (-1119221089/5000000000 : ℝ)] ![(43562082120267/100000000000000 : ℝ), (42706444200441/100000000000000 : ℝ), (274629473277/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66810199/125000000 : ℝ)|^8321 ≤ (43562082120267/100000000000000 : ℝ)^6273
        have hw : |(66810199/125000000 : ℝ)|=(66810199/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658184973/1250000000 : ℝ)|^8321 ≤ (42706444200441/100000000000000 : ℝ)^6273
        have hw : |(658184973/1250000000 : ℝ)|=(658184973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119221089/5000000000 : ℝ)|^8321 ≤ (274629473277/2000000000000 : ℝ)^6273
        have hw : |(-1119221089/5000000000 : ℝ)|=(1119221089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183323761/5000000000 : ℝ)*x 0 + (530208653/1250000000 : ℝ)*x 1 + (2247651423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183323761/5000000000 : ℝ)^8321 ≤ (2082304494497/6250000000000 : ℝ)^6273 := by
    have hnat : (2183323761 : ℕ)^8321*6250000000000^6273 ≤ 2082304494497^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183323761 5000000000 2082304494497 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530208653/1250000000 : ℝ)^8321 ≤ (8014483837399/25000000000000 : ℝ)^6273 := by
    have hnat : (530208653 : ℕ)^8321*25000000000000^6273 ≤ 8014483837399^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530208653 1250000000 8014483837399 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247651423/5000000000 : ℝ)^8321 ≤ (34625192721891/100000000000000 : ℝ)^6273 := by
    have hnat : (2247651423 : ℕ)^8321*100000000000000^6273 ≤ 34625192721891^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247651423 5000000000 34625192721891 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183323761/5000000000 : ℝ), (530208653/1250000000 : ℝ), (2247651423/5000000000 : ℝ)] ![(2082304494497/6250000000000 : ℝ), (8014483837399/25000000000000 : ℝ), (34625192721891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183323761/5000000000 : ℝ)|^8321 ≤ (2082304494497/6250000000000 : ℝ)^6273
        have hw : |(2183323761/5000000000 : ℝ)|=(2183323761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530208653/1250000000 : ℝ)|^8321 ≤ (8014483837399/25000000000000 : ℝ)^6273
        have hw : |(530208653/1250000000 : ℝ)|=(530208653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247651423/5000000000 : ℝ)|^8321 ≤ (34625192721891/100000000000000 : ℝ)^6273
        have hw : |(2247651423/5000000000 : ℝ)|=(2247651423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086800443/5000000000 : ℝ)*x 0 + (5265801377/10000000000 : ℝ)*x 1 + (1348248977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086800443/5000000000 : ℝ)^8321 ≤ (6603181333951/50000000000000 : ℝ)^6273 := by
    have hnat : (1086800443 : ℕ)^8321*50000000000000^6273 ≤ 6603181333951^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086800443 5000000000 6603181333951 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265801377/10000000000 : ℝ)^8321 ≤ (21354952062441/50000000000000 : ℝ)^6273 := by
    have hnat : (5265801377 : ℕ)^8321*50000000000000^6273 ≤ 21354952062441^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265801377 10000000000 21354952062441 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348248977/2500000000 : ℝ)^8321 ≤ (44083733192751/100000000000000 : ℝ)^6273 := by
    have hnat : (1348248977 : ℕ)^8321*100000000000000^6273 ≤ 44083733192751^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348248977 2500000000 44083733192751 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086800443/5000000000 : ℝ), (5265801377/10000000000 : ℝ), (1348248977/2500000000 : ℝ)] ![(6603181333951/50000000000000 : ℝ), (21354952062441/50000000000000 : ℝ), (44083733192751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086800443/5000000000 : ℝ)|^8321 ≤ (6603181333951/50000000000000 : ℝ)^6273
        have hw : |(-1086800443/5000000000 : ℝ)|=(1086800443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265801377/10000000000 : ℝ)|^8321 ≤ (21354952062441/50000000000000 : ℝ)^6273
        have hw : |(5265801377/10000000000 : ℝ)|=(5265801377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348248977/2500000000 : ℝ)|^8321 ≤ (44083733192751/100000000000000 : ℝ)^6273
        have hw : |(1348248977/2500000000 : ℝ)|=(1348248977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656230353/5000000000 : ℝ)*x 0 + (-1055462933/5000000000 : ℝ)*x 1 + (2696498291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656230353/5000000000 : ℝ)^8321 ≤ (21606313893797/50000000000000 : ℝ)^6273 := by
    have hnat : (2656230353 : ℕ)^8321*50000000000000^6273 ≤ 21606313893797^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656230353 5000000000 21606313893797 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055462933/5000000000 : ℝ)^8321 ≤ (3175907922677/25000000000000 : ℝ)^6273 := by
    have hnat : (1055462933 : ℕ)^8321*25000000000000^6273 ≤ 3175907922677^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055462933 5000000000 3175907922677 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696498291/5000000000 : ℝ)^8321 ≤ (44083740500917/100000000000000 : ℝ)^6273 := by
    have hnat : (2696498291 : ℕ)^8321*100000000000000^6273 ≤ 44083740500917^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696498291 5000000000 44083740500917 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656230353/5000000000 : ℝ), (-1055462933/5000000000 : ℝ), (2696498291/5000000000 : ℝ)] ![(21606313893797/50000000000000 : ℝ), (3175907922677/25000000000000 : ℝ), (44083740500917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656230353/5000000000 : ℝ)|^8321 ≤ (21606313893797/50000000000000 : ℝ)^6273
        have hw : |(2656230353/5000000000 : ℝ)|=(2656230353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055462933/5000000000 : ℝ)|^8321 ≤ (3175907922677/25000000000000 : ℝ)^6273
        have hw : |(-1055462933/5000000000 : ℝ)|=(1055462933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696498291/5000000000 : ℝ)|^8321 ≤ (44083740500917/100000000000000 : ℝ)^6273
        have hw : |(2696498291/5000000000 : ℝ)|=(2696498291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062492101/2000000000 : ℝ)*x 0 + (5392996803/10000000000 : ℝ)*x 1 + (-2110925839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062492101/2000000000 : ℝ)^8321 ≤ (10803156404709/25000000000000 : ℝ)^6273 := by
    have hnat : (1062492101 : ℕ)^8321*25000000000000^6273 ≤ 10803156404709^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062492101 2000000000 10803156404709 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392996803/10000000000 : ℝ)^8321 ≤ (8816748579443/20000000000000 : ℝ)^6273 := by
    have hnat : (5392996803 : ℕ)^8321*20000000000000^6273 ≤ 8816748579443^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392996803 10000000000 8816748579443 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110925839/10000000000 : ℝ)^8321 ≤ (12703631475173/100000000000000 : ℝ)^6273 := by
    have hnat : (2110925839 : ℕ)^8321*100000000000000^6273 ≤ 12703631475173^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110925839 10000000000 12703631475173 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062492101/2000000000 : ℝ), (5392996803/10000000000 : ℝ), (-2110925839/10000000000 : ℝ)] ![(10803156404709/25000000000000 : ℝ), (8816748579443/20000000000000 : ℝ), (12703631475173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062492101/2000000000 : ℝ)|^8321 ≤ (10803156404709/25000000000000 : ℝ)^6273
        have hw : |(1062492101/2000000000 : ℝ)|=(1062492101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392996803/10000000000 : ℝ)|^8321 ≤ (8816748579443/20000000000000 : ℝ)^6273
        have hw : |(5392996803/10000000000 : ℝ)|=(5392996803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110925839/10000000000 : ℝ)|^8321 ≤ (12703631475173/100000000000000 : ℝ)^6273
        have hw : |(-2110925839/10000000000 : ℝ)|=(2110925839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s7_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873331519/2000000000 : ℝ)*x 0 + (179786613/400000000 : ℝ)*x 1 + (4242308749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873331519/2000000000 : ℝ)^8321 ≤ (6663394771831/20000000000000 : ℝ)^6273 := by
    have hnat : (873331519 : ℕ)^8321*20000000000000^6273 ≤ 6663394771831^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873331519 2000000000 6663394771831 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179786613/400000000 : ℝ)^8321 ≤ (17309339584687/50000000000000 : ℝ)^6273 := by
    have hnat : (179786613 : ℕ)^8321*50000000000000^6273 ≤ 17309339584687^6273*400000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179786613 400000000 17309339584687 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242308749/10000000000 : ℝ)^8321 ≤ (2004021685069/6250000000000 : ℝ)^6273 := by
    have hnat : (4242308749 : ℕ)^8321*6250000000000^6273 ≤ 2004021685069^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242308749 10000000000 2004021685069 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873331519/2000000000 : ℝ), (179786613/400000000 : ℝ), (4242308749/10000000000 : ℝ)] ![(6663394771831/20000000000000 : ℝ), (17309339584687/50000000000000 : ℝ), (2004021685069/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873331519/2000000000 : ℝ)|^8321 ≤ (6663394771831/20000000000000 : ℝ)^6273
        have hw : |(873331519/2000000000 : ℝ)|=(873331519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179786613/400000000 : ℝ)|^8321 ≤ (17309339584687/50000000000000 : ℝ)^6273
        have hw : |(179786613/400000000 : ℝ)|=(179786613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242308749/10000000000 : ℝ)|^8321 ≤ (2004021685069/6250000000000 : ℝ)^6273
        have hw : |(4242308749/10000000000 : ℝ)|=(4242308749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11327/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11327/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11327/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11327/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2873239173846391/20000000000000000000 : ℝ) := by
    have hpowers : (11327/100000 : ℝ)^65 ≤ (2873239173846391/20000000000000000000 : ℝ)^16 := by
      have hnat : (11327 : ℕ)^65*20000000000000000000^16 ≤ 2873239173846391^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11327 100000 2873239173846391 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11327/100000 : ℝ)) (X := (2873239173846391/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (65/16 : ℝ) ≤ (17229770497088121/50000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^65 ≤ (17229770497088121/50000000000000000000 : ℝ)^16 := by
      have hnat : (14049 : ℕ)^65*50000000000000000000^16 ≤ 17229770497088121^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 17229770497088121 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (17229770497088121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002873239173846391/10000000000000000000 : ℝ) ≤ (10000707182290987/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (10002873239173846391/10000000000000000000 : ℝ)^16 ≤ (10000707182290987/10000000000000000 : ℝ)^65 := by
      have hnat : (10002873239173846391 : ℕ)^16*10000000000000000^65 ≤ 10000707182290987^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002873239173846391 10000000000000000000 10000707182290987 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707182290987/10000000000000000 : ℝ)) (X := (10002873239173846391/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048825736863408197/100000000000000000000 : ℝ) ≤ (5000600821584739/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100048825736863408197/100000000000000000000 : ℝ)^16 ≤ (5000600821584739/5000000000000000 : ℝ)^65 := by
      have hnat : (100048825736863408197 : ℕ)^16*5000000000000000^65 ≤ 5000600821584739^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048825736863408197 100000000000000000000 5000600821584739 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000600821584739/5000000000000000 : ℝ)) (X := (100048825736863408197/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017229770497088121/25000000000000000000 : ℝ) ≤ (10001696104047969/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25017229770497088121/25000000000000000000 : ℝ)^16 ≤ (10001696104047969/10000000000000000 : ℝ)^65 := by
      have hnat : (25017229770497088121 : ℕ)^16*10000000000000000^65 ≤ 10001696104047969^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017229770497088121 25000000000000000000 10001696104047969 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001696104047969/10000000000000000 : ℝ)) (X := (25017229770497088121/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2873239173846391/20000000000000000000 : ℝ) ≤ ((54421446866909463/54440000000000000 : ℝ)+2*(494460878491/272200000000000 : ℝ)*(11327/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (54421446866909463/54440000000000000 : ℝ)+2*(494460878491/272200000000000 : ℝ)*(11327/100000 : ℝ)=(10000707182290987/10000000000000000 : ℝ) by norm_num, show 1+2*(2873239173846391/20000000000000000000 : ℝ)=(10002873239173846391/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17229770497088121/50000000000000000000 : ℝ)+(2873239173846391/20000000000000000000 : ℝ) ≤ ((54421446866909463/54440000000000000 : ℝ)+(494460878491/272200000000000 : ℝ)*((14049/100000 : ℝ)+(11327/100000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (54421446866909463/54440000000000000 : ℝ)+(494460878491/272200000000000 : ℝ)*((14049/100000 : ℝ)+(11327/100000 : ℝ))=(5000600821584739/5000000000000000 : ℝ) by norm_num, show 1+(17229770497088121/50000000000000000000 : ℝ)+(2873239173846391/20000000000000000000 : ℝ)=(100048825736863408197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17229770497088121/50000000000000000000 : ℝ) ≤ ((54421446866909463/54440000000000000 : ℝ)+2*(494460878491/272200000000000 : ℝ)*(14049/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (54421446866909463/54440000000000000 : ℝ)+2*(494460878491/272200000000000 : ℝ)*(14049/100000 : ℝ)=(10001696104047969/10000000000000000 : ℝ) by norm_num, show 1+2*(17229770497088121/50000000000000000000 : ℝ)=(25017229770497088121/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54421446866909463/54440000000000000 : ℝ)*(X 1 0+X 2 0)+(494460878491/272200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (54421446866909463/54440000000000000 : ℝ)) (alpha := (494460878491/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54421446866909463/54440000000000000 : ℝ)*(X 0 1+X 2 1)+(494460878491/272200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (54421446866909463/54440000000000000 : ℝ)) (alpha := (494460878491/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54421446866909463/54440000000000000 : ℝ)*(X 0 2+X 1 2)+(494460878491/272200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (11327/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (54421446866909463/54440000000000000 : ℝ)) (alpha := (494460878491/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-543399039/2500000000 : ℝ)*X 0 0+(2696659263/5000000000 : ℝ)*X 0 1+(1316369943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336203979/2500000000 : ℝ)*X 1 0+(-1119221093/5000000000 : ℝ)*X 1 1+(2632739891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66810199/125000000 : ℝ)*X 2 0+(658184973/1250000000 : ℝ)*X 2 1+(-1119221089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183323761/5000000000 : ℝ)*X 0 0+(530208653/1250000000 : ℝ)*X 0 1+(2247651423/5000000000 : ℝ)*X 0 2+(2183323761/5000000000 : ℝ)*X 1 0+(530208653/1250000000 : ℝ)*X 1 1+(2247651423/5000000000 : ℝ)*X 1 2+(2183323761/5000000000 : ℝ)*X 2 0+(530208653/1250000000 : ℝ)*X 2 1+(2247651423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086800443/5000000000 : ℝ)*X 0 0+(5265801377/10000000000 : ℝ)*X 0 1+(1348248977/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656230353/5000000000 : ℝ)*X 1 0+(-1055462933/5000000000 : ℝ)*X 1 1+(2696498291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062492101/2000000000 : ℝ)*X 2 0+(5392996803/10000000000 : ℝ)*X 2 1+(-2110925839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873331519/2000000000 : ℝ)*X 0 0+(179786613/400000000 : ℝ)*X 0 1+(4242308749/10000000000 : ℝ)*X 0 2+(873331519/2000000000 : ℝ)*X 1 0+(179786613/400000000 : ℝ)*X 1 1+(4242308749/10000000000 : ℝ)*X 1 2+(873331519/2000000000 : ℝ)*X 2 0+(179786613/400000000 : ℝ)*X 2 1+(4242308749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (524778270361519991996721/85062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (617680243/50000000000000 : ℝ)*(base19) + (233689853/20000000000000 : ℝ)*(base23) + (7778357/20000000000000 : ℝ)*(lower2) + (74500017/50000000000000 : ℝ)*(upper3) + (108943201/100000000000000 : ℝ)*(upper5) + (367661061436439/6250000000000 : ℝ)*(major0) + (367661061436439/6250000000000 : ℝ)*(major1) + (367661061436439/6250000000000 : ℝ)*(major2) + (1564477897356721/20000000000000 : ℝ)*(sp0) + (7822423047514251/100000000000000 : ℝ)*(sp1) + (61112680581449/781250000000 : ℝ)*(sp2) + (3942711549625737/100000000000000 : ℝ)*(sp3) + (34796091131/100000000000000 : ℝ)*(sp4) + (17927821371/100000000000000 : ℝ)*(sp7) + (985682369361777/25000000000000 : ℝ)*(f.failure) + (488901517679671/6250000000000 : ℝ)*(f.sum) + (8366396319927/6805000000000000000000000000 : ℝ)*base65 + (2484812455562057/340250000000000000000000000000 : ℝ)*base67 + (3781476561525193/340250000000000000000000000000 : ℝ)*base70 + (2497101877511693/340250000000000000000000000000 : ℝ)*base72 + (29900723794907/6805000000000000000000000000 : ℝ)*base73 + (9446823910503693/340250000000000000000000000000 : ℝ)*base76 + (2979404661502693/340250000000000000000000000000 : ℝ)*base78 + (11381669502085693/340250000000000000000000000000 : ℝ)*base80 + (19141403135433/6805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (634303/156250000000000000000 : ℝ)*base89 + (634303/156250000000000000000 : ℝ)*base91 + (634303/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6416788885367918657613477/544400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14403311/50000000000000 : ℝ)*(base19) + (117916207/20000000000000 : ℝ)*(base23) + (195492517/50000000000000 : ℝ)*(upper3) + (352438499/100000000000000 : ℝ)*(lower4) + (6056663/10000000000000 : ℝ)*(upper5) + (1182459510809807/20000000000000 : ℝ)*(major0) + (1182459510809807/20000000000000 : ℝ)*(major1) + (1182459510809807/20000000000000 : ℝ)*(major2) + (5967108013/50000000000000 : ℝ)*(sp1) + (10980325999/25000000000000 : ℝ)*(sp2) + (7861945367267651/100000000000000 : ℝ)*(sp4) + (7861933404245003/100000000000000 : ℝ)*(sp5) + (393095042819131/5000000000000 : ℝ)*(sp6) + (990662336983429/25000000000000 : ℝ)*(sp7) + (990662336983429/25000000000000 : ℝ)*(f.failure) + (7861945367267651/100000000000000 : ℝ)*(f.sum) + (6456770576289/2722000000000000000000000000 : ℝ)*base65 + (27922370926559/1088800000000000000000000000000 : ℝ)*base68 + (10889910460541441/1088800000000000000000000000000 : ℝ)*base69 + (5950632887835841/1088800000000000000000000000000 : ℝ)*base71 + (2148569591363/544400000000000000000000000 : ℝ)*base74 + (5000380066005441/1088800000000000000000000000000 : ℝ)*base75 + (2887611270920959/1088800000000000000000000000000 : ℝ)*base78 + (8358205445699841/1088800000000000000000000000000 : ℝ)*base79 + (618828755583/544400000000000000000000000 : ℝ)*base82 + (591231/156250000000000000000 : ℝ)*base89 + (591231/156250000000000000000 : ℝ)*base91 + (591231/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1128_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s8_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086800641/5000000000 : ℝ)*x 0 + (5393247619/10000000000 : ℝ)*x 1 + (1316386849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086800641/5000000000 : ℝ)^8321 ≤ (13206365859431/100000000000000 : ℝ)^6273 := by
    have hnat : (1086800641 : ℕ)^8321*100000000000000^6273 ≤ 13206365859431^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086800641 5000000000 13206365859431 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393247619/10000000000 : ℝ)^8321 ≤ (11021615627489/25000000000000 : ℝ)^6273 := by
    have hnat : (5393247619 : ℕ)^8321*25000000000000^6273 ≤ 11021615627489^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393247619 10000000000 11021615627489 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316386849/2500000000 : ℝ)^8321 ≤ (42707171612323/100000000000000 : ℝ)^6273 := by
    have hnat : (1316386849 : ℕ)^8321*100000000000000^6273 ≤ 42707171612323^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316386849 2500000000 42707171612323 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086800641/5000000000 : ℝ), (5393247619/10000000000 : ℝ), (1316386849/2500000000 : ℝ)] ![(13206365859431/100000000000000 : ℝ), (11021615627489/25000000000000 : ℝ), (42707171612323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086800641/5000000000 : ℝ)|^8321 ≤ (13206365859431/100000000000000 : ℝ)^6273
        have hw : |(-1086800641/5000000000 : ℝ)|=(1086800641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393247619/10000000000 : ℝ)|^8321 ≤ (11021615627489/25000000000000 : ℝ)^6273
        have hw : |(5393247619/10000000000 : ℝ)|=(5393247619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316386849/2500000000 : ℝ)|^8321 ≤ (42707171612323/100000000000000 : ℝ)^6273
        have hw : |(1316386849/2500000000 : ℝ)|=(1316386849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344798401/10000000000 : ℝ)*x 0 + (-139898503/625000000 : ℝ)*x 1 + (1053109481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344798401/10000000000 : ℝ)^8321 ≤ (5445236589749/12500000000000 : ℝ)^6273 := by
    have hnat : (5344798401 : ℕ)^8321*12500000000000^6273 ≤ 5445236589749^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344798401 10000000000 5445236589749 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139898503/625000000 : ℝ)^8321 ≤ (13730935557731/100000000000000 : ℝ)^6273 := by
    have hnat : (139898503 : ℕ)^8321*100000000000000^6273 ≤ 13730935557731^6273*625000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139898503 625000000 13730935557731 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053109481/2000000000 : ℝ)^8321 ≤ (42707171709151/100000000000000 : ℝ)^6273 := by
    have hnat : (1053109481 : ℕ)^8321*100000000000000^6273 ≤ 42707171709151^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053109481 2000000000 42707171709151 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344798401/10000000000 : ℝ), (-139898503/625000000 : ℝ), (1053109481/2000000000 : ℝ)] ![(5445236589749/12500000000000 : ℝ), (13730935557731/100000000000000 : ℝ), (42707171709151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344798401/10000000000 : ℝ)|^8321 ≤ (5445236589749/12500000000000 : ℝ)^6273
        have hw : |(5344798401/10000000000 : ℝ)|=(5344798401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139898503/625000000 : ℝ)|^8321 ≤ (13730935557731/100000000000000 : ℝ)^6273
        have hw : |(-139898503/625000000 : ℝ)|=(139898503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053109481/2000000000 : ℝ)|^8321 ≤ (42707171709151/100000000000000 : ℝ)^6273
        have hw : |(1053109481/2000000000 : ℝ)|=(1053109481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344798409/10000000000 : ℝ)*x 0 + (2632773699/5000000000 : ℝ)*x 1 + (-2238376047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344798409/10000000000 : ℝ)^8321 ≤ (21780946402241/50000000000000 : ℝ)^6273 := by
    have hnat : (5344798409 : ℕ)^8321*50000000000000^6273 ≤ 21780946402241^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344798409 10000000000 21780946402241 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632773699/5000000000 : ℝ)^8321 ≤ (42707171633841/100000000000000 : ℝ)^6273 := by
    have hnat : (2632773699 : ℕ)^8321*100000000000000^6273 ≤ 42707171633841^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632773699 5000000000 42707171633841 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238376047/10000000000 : ℝ)^8321 ≤ (6865467774797/50000000000000 : ℝ)^6273 := by
    have hnat : (2238376047 : ℕ)^8321*50000000000000^6273 ≤ 6865467774797^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238376047 10000000000 6865467774797 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344798409/10000000000 : ℝ), (2632773699/5000000000 : ℝ), (-2238376047/10000000000 : ℝ)] ![(21780946402241/50000000000000 : ℝ), (42707171633841/100000000000000 : ℝ), (6865467774797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344798409/10000000000 : ℝ)|^8321 ≤ (21780946402241/50000000000000 : ℝ)^6273
        have hw : |(5344798409/10000000000 : ℝ)|=(5344798409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632773699/5000000000 : ℝ)|^8321 ≤ (42707171633841/100000000000000 : ℝ)^6273
        have hw : |(2632773699/5000000000 : ℝ)|=(2632773699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238376047/10000000000 : ℝ)|^8321 ≤ (6865467774797/50000000000000 : ℝ)^6273
        have hw : |(-2238376047/10000000000 : ℝ)|=(2238376047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366651049/10000000000 : ℝ)*x 0 + (2120903081/5000000000 : ℝ)*x 1 + (899032997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366651049/10000000000 : ℝ)^8321 ≤ (1665845380407/5000000000000 : ℝ)^6273 := by
    have hnat : (4366651049 : ℕ)^8321*5000000000000^6273 ≤ 1665845380407^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366651049 10000000000 1665845380407 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120903081/5000000000 : ℝ)^8321 ≤ (8014827051611/25000000000000 : ℝ)^6273 := by
    have hnat : (2120903081 : ℕ)^8321*25000000000000^6273 ≤ 8014827051611^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120903081 5000000000 8014827051611 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899032997/2000000000 : ℝ)^8321 ≤ (8655946042599/25000000000000 : ℝ)^6273 := by
    have hnat : (899032997 : ℕ)^8321*25000000000000^6273 ≤ 8655946042599^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899032997 2000000000 8655946042599 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366651049/10000000000 : ℝ), (2120903081/5000000000 : ℝ), (899032997/2000000000 : ℝ)] ![(1665845380407/5000000000000 : ℝ), (8014827051611/25000000000000 : ℝ), (8655946042599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366651049/10000000000 : ℝ)|^8321 ≤ (1665845380407/5000000000000 : ℝ)^6273
        have hw : |(4366651049/10000000000 : ℝ)|=(4366651049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120903081/5000000000 : ℝ)|^8321 ≤ (8014827051611/25000000000000 : ℝ)^6273
        have hw : |(2120903081/5000000000 : ℝ)|=(2120903081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899032997/2000000000 : ℝ)|^8321 ≤ (8655946042599/25000000000000 : ℝ)^6273
        have hw : |(899032997/2000000000 : ℝ)|=(899032997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173606239/10000000000 : ℝ)*x 0 + (5265867847/10000000000 : ℝ)*x 1 + (2696462987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173606239/10000000000 : ℝ)^8321 ≤ (13206405809981/100000000000000 : ℝ)^6273 := by
    have hnat : (2173606239 : ℕ)^8321*100000000000000^6273 ≤ 13206405809981^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173606239 10000000000 13206405809981 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265867847/10000000000 : ℝ)^8321 ≤ (42710619264653/100000000000000 : ℝ)^6273 := by
    have hnat : (5265867847 : ℕ)^8321*100000000000000^6273 ≤ 42710619264653^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265867847 10000000000 42710619264653 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696462987/5000000000 : ℝ)^8321 ≤ (44082974901651/100000000000000 : ℝ)^6273 := by
    have hnat : (2696462987 : ℕ)^8321*100000000000000^6273 ≤ 44082974901651^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696462987 5000000000 44082974901651 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173606239/10000000000 : ℝ), (5265867847/10000000000 : ℝ), (2696462987/5000000000 : ℝ)] ![(13206405809981/100000000000000 : ℝ), (42710619264653/100000000000000 : ℝ), (44082974901651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173606239/10000000000 : ℝ)|^8321 ≤ (13206405809981/100000000000000 : ℝ)^6273
        have hw : |(-2173606239/10000000000 : ℝ)|=(2173606239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265867847/10000000000 : ℝ)|^8321 ≤ (42710619264653/100000000000000 : ℝ)^6273
        have hw : |(5265867847/10000000000 : ℝ)|=(5265867847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696462987/5000000000 : ℝ)|^8321 ≤ (44082974901651/100000000000000 : ℝ)^6273
        have hw : |(2696462987/5000000000 : ℝ)|=(2696462987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83007481/156250000 : ℝ)*x 0 + (-263874659/1250000000 : ℝ)*x 1 + (2696463011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83007481/156250000 : ℝ)^8321 ≤ (43212822846509/100000000000000 : ℝ)^6273 := by
    have hnat : (83007481 : ℕ)^8321*100000000000000^6273 ≤ 43212822846509^6273*156250000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83007481 156250000 43212822846509 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263874659/1250000000 : ℝ)^8321 ≤ (12704201713539/100000000000000 : ℝ)^6273 := by
    have hnat : (263874659 : ℕ)^8321*100000000000000^6273 ≤ 12704201713539^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263874659 1250000000 12704201713539 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696463011/5000000000 : ℝ)^8321 ≤ (1377592981941/3125000000000 : ℝ)^6273 := by
    have hnat : (2696463011 : ℕ)^8321*3125000000000^6273 ≤ 1377592981941^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696463011 5000000000 1377592981941 3125000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83007481/156250000 : ℝ), (-263874659/1250000000 : ℝ), (2696463011/5000000000 : ℝ)] ![(43212822846509/100000000000000 : ℝ), (12704201713539/100000000000000 : ℝ), (1377592981941/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83007481/156250000 : ℝ)|^8321 ≤ (43212822846509/100000000000000 : ℝ)^6273
        have hw : |(83007481/156250000 : ℝ)|=(83007481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263874659/1250000000 : ℝ)|^8321 ≤ (12704201713539/100000000000000 : ℝ)^6273
        have hw : |(-263874659/1250000000 : ℝ)|=(263874659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696463011/5000000000 : ℝ)|^8321 ≤ (1377592981941/3125000000000 : ℝ)^6273
        have hw : |(2696463011/5000000000 : ℝ)|=(2696463011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656239243/5000000000 : ℝ)*x 0 + (5392926041/10000000000 : ℝ)*x 1 + (-42219953/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656239243/5000000000 : ℝ)^8321 ≤ (10803204907783/25000000000000 : ℝ)^6273 := by
    have hnat : (2656239243 : ℕ)^8321*25000000000000^6273 ≤ 10803204907783^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656239243 5000000000 10803204907783 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392926041/10000000000 : ℝ)^8321 ≤ (44082975628127/100000000000000 : ℝ)^6273 := by
    have hnat : (5392926041 : ℕ)^8321*100000000000000^6273 ≤ 44082975628127^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392926041 10000000000 44082975628127 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42219953/200000000 : ℝ)^8321 ≤ (1270420473107/10000000000000 : ℝ)^6273 := by
    have hnat : (42219953 : ℕ)^8321*10000000000000^6273 ≤ 1270420473107^6273*200000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42219953 200000000 1270420473107 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656239243/5000000000 : ℝ), (5392926041/10000000000 : ℝ), (-42219953/200000000 : ℝ)] ![(10803204907783/25000000000000 : ℝ), (44082975628127/100000000000000 : ℝ), (1270420473107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656239243/5000000000 : ℝ)|^8321 ≤ (10803204907783/25000000000000 : ℝ)^6273
        have hw : |(2656239243/5000000000 : ℝ)|=(2656239243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392926041/10000000000 : ℝ)|^8321 ≤ (44082975628127/100000000000000 : ℝ)^6273
        have hw : |(5392926041/10000000000 : ℝ)|=(5392926041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42219953/200000000 : ℝ)|^8321 ≤ (1270420473107/10000000000000 : ℝ)^6273
        have hw : |(-42219953/200000000 : ℝ)|=(42219953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s8_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366660593/10000000000 : ℝ)*x 0 + (4494529149/10000000000 : ℝ)*x 1 + (424244449/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366660593/10000000000 : ℝ)^8321 ≤ (33317004201443/100000000000000 : ℝ)^6273 := by
    have hnat : (4366660593 : ℕ)^8321*100000000000000^6273 ≤ 33317004201443^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366660593 10000000000 33317004201443 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494529149/10000000000 : ℝ)^8321 ≤ (34617287898177/100000000000000 : ℝ)^6273 := by
    have hnat : (4494529149 : ℕ)^8321*100000000000000^6273 ≤ 34617287898177^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494529149 10000000000 34617287898177 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424244449/1000000000 : ℝ)^8321 ≤ (100205337139/312500000000 : ℝ)^6273 := by
    have hnat : (424244449 : ℕ)^8321*312500000000^6273 ≤ 100205337139^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424244449 1000000000 100205337139 312500000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366660593/10000000000 : ℝ), (4494529149/10000000000 : ℝ), (424244449/1000000000 : ℝ)] ![(33317004201443/100000000000000 : ℝ), (34617287898177/100000000000000 : ℝ), (100205337139/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366660593/10000000000 : ℝ)|^8321 ≤ (33317004201443/100000000000000 : ℝ)^6273
        have hw : |(4366660593/10000000000 : ℝ)|=(4366660593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494529149/10000000000 : ℝ)|^8321 ≤ (34617287898177/100000000000000 : ℝ)^6273
        have hw : |(4494529149/10000000000 : ℝ)|=(4494529149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424244449/1000000000 : ℝ)|^8321 ≤ (100205337139/312500000000 : ℝ)^6273
        have hw : |(424244449/1000000000 : ℝ)|=(424244449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2267/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (65/16 : ℝ) ≤ (14402297702006503/100000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^65 ≤ (14402297702006503/100000000000000000000 : ℝ)^16 := by
      have hnat : (5667 : ℕ)^65*100000000000000000000^16 ≤ 14402297702006503^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 14402297702006503 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (14402297702006503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (7021/50000 : ℝ) ^ (65/16 : ℝ) ≤ (34389842382113487/100000000000000000000 : ℝ) := by
    have hpowers : (7021/50000 : ℝ)^65 ≤ (34389842382113487/100000000000000000000 : ℝ)^16 := by
      have hnat : (7021 : ℕ)^65*100000000000000000000^16 ≤ 34389842382113487^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7021 50000 34389842382113487 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7021/50000 : ℝ)) (X := (34389842382113487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014402297702006503/50000000000000000000 : ℝ) ≤ (5000354479613317/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50014402297702006503/50000000000000000000 : ℝ)^16 ≤ (5000354479613317/5000000000000000 : ℝ)^65 := by
      have hnat : (50014402297702006503 : ℕ)^16*5000000000000000^65 ≤ 5000354479613317^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014402297702006503 50000000000000000000 5000354479613317 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354479613317/5000000000000000 : ℝ)) (X := (50014402297702006503/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004879214008411999/10000000000000000000 : ℝ) ≤ (10001200816475993/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (10004879214008411999/10000000000000000000 : ℝ)^16 ≤ (10001200816475993/10000000000000000 : ℝ)^65 := by
      have hnat : (10004879214008411999 : ℕ)^16*10000000000000000^65 ≤ 10001200816475993^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004879214008411999 10000000000000000000 10001200816475993 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001200816475993/10000000000000000 : ℝ)) (X := (10004879214008411999/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034389842382113487/50000000000000000000 : ℝ) ≤ (1250211584215669/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50034389842382113487/50000000000000000000 : ℝ)^16 ≤ (1250211584215669/1250000000000000 : ℝ)^65 := by
      have hnat : (50034389842382113487 : ℕ)^16*1250000000000000^65 ≤ 1250211584215669^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034389842382113487 50000000000000000000 1250211584215669 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250211584215669/1250000000000000 : ℝ)) (X := (50034389842382113487/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14402297702006503/100000000000000000000 : ℝ) ≤ ((1353538522072862753/1354000000000000000 : ℝ)+2*(491857249359/270800000000000 : ℝ)*(5667/50000 : ℝ))^(65/16 : ℝ) := by
    rw [show (1353538522072862753/1354000000000000000 : ℝ)+2*(491857249359/270800000000000 : ℝ)*(5667/50000 : ℝ)=(5000354479613317/5000000000000000 : ℝ) by norm_num, show 1+2*(14402297702006503/100000000000000000000 : ℝ)=(50014402297702006503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34389842382113487/100000000000000000000 : ℝ)+(14402297702006503/100000000000000000000 : ℝ) ≤ ((1353538522072862753/1354000000000000000 : ℝ)+(491857249359/270800000000000 : ℝ)*((7021/50000 : ℝ)+(5667/50000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (1353538522072862753/1354000000000000000 : ℝ)+(491857249359/270800000000000 : ℝ)*((7021/50000 : ℝ)+(5667/50000 : ℝ))=(10001200816475993/10000000000000000 : ℝ) by norm_num, show 1+(34389842382113487/100000000000000000000 : ℝ)+(14402297702006503/100000000000000000000 : ℝ)=(10004879214008411999/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34389842382113487/100000000000000000000 : ℝ) ≤ ((1353538522072862753/1354000000000000000 : ℝ)+2*(491857249359/270800000000000 : ℝ)*(7021/50000 : ℝ))^(65/16 : ℝ) := by
    rw [show (1353538522072862753/1354000000000000000 : ℝ)+2*(491857249359/270800000000000 : ℝ)*(7021/50000 : ℝ)=(1250211584215669/1250000000000000 : ℝ) by norm_num, show 1+2*(34389842382113487/100000000000000000000 : ℝ)=(50034389842382113487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1353538522072862753/1354000000000000000 : ℝ)*(X 1 0+X 2 0)+(491857249359/270800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1353538522072862753/1354000000000000000 : ℝ)) (alpha := (491857249359/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1353538522072862753/1354000000000000000 : ℝ)*(X 0 1+X 2 1)+(491857249359/270800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1353538522072862753/1354000000000000000 : ℝ)) (alpha := (491857249359/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1353538522072862753/1354000000000000000 : ℝ)*(X 0 2+X 1 2)+(491857249359/270800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1353538522072862753/1354000000000000000 : ℝ)) (alpha := (491857249359/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1086800641/5000000000 : ℝ)*X 0 0+(5393247619/10000000000 : ℝ)*X 0 1+(1316386849/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344798401/10000000000 : ℝ)*X 1 0+(-139898503/625000000 : ℝ)*X 1 1+(1053109481/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344798409/10000000000 : ℝ)*X 2 0+(2632773699/5000000000 : ℝ)*X 2 1+(-2238376047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366651049/10000000000 : ℝ)*X 0 0+(2120903081/5000000000 : ℝ)*X 0 1+(899032997/2000000000 : ℝ)*X 0 2+(4366651049/10000000000 : ℝ)*X 1 0+(2120903081/5000000000 : ℝ)*X 1 1+(899032997/2000000000 : ℝ)*X 1 2+(4366651049/10000000000 : ℝ)*X 2 0+(2120903081/5000000000 : ℝ)*X 2 1+(899032997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2173606239/10000000000 : ℝ)*X 0 0+(5265867847/10000000000 : ℝ)*X 0 1+(2696462987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((83007481/156250000 : ℝ)*X 1 0+(-263874659/1250000000 : ℝ)*X 1 1+(2696463011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656239243/5000000000 : ℝ)*X 2 0+(5392926041/10000000000 : ℝ)*X 2 1+(-42219953/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366660593/10000000000 : ℝ)*X 0 0+(4494529149/10000000000 : ℝ)*X 0 1+(424244449/1000000000 : ℝ)*X 0 2+(4366660593/10000000000 : ℝ)*X 1 0+(4494529149/10000000000 : ℝ)*X 1 1+(424244449/1000000000 : ℝ)*X 1 2+(4366660593/10000000000 : ℝ)*X 2 0+(4494529149/10000000000 : ℝ)*X 2 1+(424244449/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13908167459818416587322303/1354000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127671227/6250000000000 : ℝ)*(base19) + (238788201/12500000000000 : ℝ)*(base23) + (38524039/50000000000000 : ℝ)*(lower2) + (261773293/100000000000000 : ℝ)*(upper3) + (9939823/6250000000000 : ℝ)*(upper5) + (117779833675961/2000000000000 : ℝ)*(major0) + (117779833675961/2000000000000 : ℝ)*(major1) + (117779833675961/2000000000000 : ℝ)*(major2) + (7830898240635707/100000000000000 : ℝ)*(sp0) + (313238085026581/4000000000000 : ℝ)*(sp1) + (156619045161971/2000000000000 : ℝ)*(sp2) + (246687408646963/6250000000000 : ℝ)*(sp3) + (1118555369/2000000000000 : ℝ)*(sp4) + (15159221743/50000000000000 : ℝ)*(sp7) + (246689303549681/6250000000000 : ℝ)*(f.failure) + (3915477084202079/50000000000000 : ℝ)*(f.sum) + (5132207017169/1354000000000000000000000000 : ℝ)*base66 + (18697933365931633/2708000000000000000000000000000 : ℝ)*base67 + (46500909792639633/2708000000000000000000000000000 : ℝ)*base69 + (25350702903155633/2708000000000000000000000000000 : ℝ)*base71 + (127010086549/270800000000000000000000000 : ℝ)*base74 + (64717305292715633/2708000000000000000000000000000 : ℝ)*base75 + (16894208096255633/2708000000000000000000000000000 : ℝ)*base77 + (37004245937095633/2708000000000000000000000000000 : ℝ)*base79 + (341458515763/270800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (481309/39062500000000000000 : ℝ)*base89 + (481309/39062500000000000000 : ℝ)*base91 + (481309/39062500000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26991627122354327212174443/8462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129355069/20000000000000 : ℝ)*(base19) + (42871499/20000000000000 : ℝ)*(base23) + (543063/25000000000000 : ℝ)*(lower1) + (89591893/100000000000000 : ℝ)*(upper2) + (48048089/50000000000000 : ℝ)*(upper5) + (739832782808423/12500000000000 : ℝ)*(major0) + (739832782808423/12500000000000 : ℝ)*(major1) + (739832782808423/12500000000000 : ℝ)*(major2) + (657311/1562500000000 : ℝ)*(sp0) + (26230128739/100000000000000 : ℝ)*(sp1) + (3935204578047461/50000000000000 : ℝ)*(sp4) + (3935191160629371/50000000000000 : ℝ)*(sp5) + (1967602245951333/25000000000000 : ℝ)*(sp6) + (991728805113339/25000000000000 : ℝ)*(sp7) + (991728805113339/25000000000000 : ℝ)*(f.failure) + (7870409198162827/100000000000000 : ℝ)*(f.sum) + (5623724759811/846250000000000000000000000 : ℝ)*base65 + (133382090674203519/16925000000000000000000000000000 : ℝ)*base67 + (139611795625553519/16925000000000000000000000000000 : ℝ)*base69 + (156618277263778519/16925000000000000000000000000000 : ℝ)*base71 + (7192642769867/1692500000000000000000000000 : ℝ)*base73 + (35705387097921481/16925000000000000000000000000000 : ℝ)*base76 + (200941276265153519/16925000000000000000000000000000 : ℝ)*base77 + (125457978277146481/16925000000000000000000000000000 : ℝ)*base80 + (8343441402657/1692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1904779/156250000000000000000 : ℝ)*base90 + (1904779/156250000000000000000 : ℝ)*base92 + (1904779/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1128_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1128_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1128_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1128_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1128_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

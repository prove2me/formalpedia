-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:45.456488+00:00
-- url     : https://prove2.me/submissions/07bfcffc-a133-4dba-9d3e-8ce3c50f339a

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
theorem support_rectangle_w1378_s0_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-894027009/5000000000 : ℝ)*x 0 + (2990756549/5000000000 : ℝ)*x 1 + (4819425317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894027009/5000000000 : ℝ)^2169 ≤ (5252210467417/50000000000000 : ℝ)^1657 := by
    have hnat : (894027009 : ℕ)^2169*50000000000000^1657 ≤ 5252210467417^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894027009 5000000000 5252210467417 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2990756549/5000000000 : ℝ)^2169 ≤ (51032568365287/100000000000000 : ℝ)^1657 := by
    have hnat : (2990756549 : ℕ)^2169*100000000000000^1657 ≤ 51032568365287^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990756549 5000000000 51032568365287 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819425317/10000000000 : ℝ)^2169 ≤ (1201969083753/3125000000000 : ℝ)^1657 := by
    have hnat : (4819425317 : ℕ)^2169*3125000000000^1657 ≤ 1201969083753^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819425317 10000000000 1201969083753 3125000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894027009/5000000000 : ℝ), (2990756549/5000000000 : ℝ), (4819425317/10000000000 : ℝ)] ![(5252210467417/50000000000000 : ℝ), (51032568365287/100000000000000 : ℝ), (1201969083753/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894027009/5000000000 : ℝ)|^2169 ≤ (5252210467417/50000000000000 : ℝ)^1657
        have hw : |(-894027009/5000000000 : ℝ)|=(894027009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2990756549/5000000000 : ℝ)|^2169 ≤ (51032568365287/100000000000000 : ℝ)^1657
        have hw : |(2990756549/5000000000 : ℝ)|=(2990756549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819425317/10000000000 : ℝ)|^2169 ≤ (1201969083753/3125000000000 : ℝ)^1657
        have hw : |(4819425317/10000000000 : ℝ)|=(4819425317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2748892863/5000000000 : ℝ)*x 0 + (-244686993/1000000000 : ℝ)*x 1 + (4819425963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748892863/5000000000 : ℝ)^2169 ≤ (45699124591377/100000000000000 : ℝ)^1657 := by
    have hnat : (2748892863 : ℕ)^2169*100000000000000^1657 ≤ 45699124591377^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748892863 5000000000 45699124591377 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244686993/1000000000 : ℝ)^2169 ≤ (15837857956673/100000000000000 : ℝ)^1657 := by
    have hnat : (244686993 : ℕ)^2169*100000000000000^1657 ≤ 15837857956673^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244686993 1000000000 15837857956673 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819425963/10000000000 : ℝ)^2169 ≤ (38463017428757/100000000000000 : ℝ)^1657 := by
    have hnat : (4819425963 : ℕ)^2169*100000000000000^1657 ≤ 38463017428757^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819425963 10000000000 38463017428757 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748892863/5000000000 : ℝ), (-244686993/1000000000 : ℝ), (4819425963/10000000000 : ℝ)] ![(45699124591377/100000000000000 : ℝ), (15837857956673/100000000000000 : ℝ), (38463017428757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748892863/5000000000 : ℝ)|^2169 ≤ (45699124591377/100000000000000 : ℝ)^1657
        have hw : |(2748892863/5000000000 : ℝ)|=(2748892863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244686993/1000000000 : ℝ)|^2169 ≤ (15837857956673/100000000000000 : ℝ)^1657
        have hw : |(-244686993/1000000000 : ℝ)|=(244686993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819425963/10000000000 : ℝ)|^2169 ≤ (38463017428757/100000000000000 : ℝ)^1657
        have hw : |(4819425963/10000000000 : ℝ)|=(4819425963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5497785603/10000000000 : ℝ)*x 0 + (4819425219/10000000000 : ℝ)*x 1 + (-1223435503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497785603/10000000000 : ℝ)^2169 ≤ (913982465061/2000000000000 : ℝ)^1657 := by
    have hnat : (5497785603 : ℕ)^2169*2000000000000^1657 ≤ 913982465061^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497785603 10000000000 913982465061 2000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819425219/10000000000 : ℝ)^2169 ≤ (7692601931261/20000000000000 : ℝ)^1657 := by
    have hnat : (4819425219 : ℕ)^2169*20000000000000^1657 ≤ 7692601931261^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819425219 10000000000 7692601931261 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223435503/5000000000 : ℝ)^2169 ≤ (3167573414663/20000000000000 : ℝ)^1657 := by
    have hnat : (1223435503 : ℕ)^2169*20000000000000^1657 ≤ 3167573414663^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223435503 5000000000 3167573414663 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497785603/10000000000 : ℝ), (4819425219/10000000000 : ℝ), (-1223435503/5000000000 : ℝ)] ![(913982465061/2000000000000 : ℝ), (7692601931261/20000000000000 : ℝ), (3167573414663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497785603/10000000000 : ℝ)|^2169 ≤ (913982465061/2000000000000 : ℝ)^1657
        have hw : |(5497785603/10000000000 : ℝ)|=(5497785603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819425219/10000000000 : ℝ)|^2169 ≤ (7692601931261/20000000000000 : ℝ)^1657
        have hw : |(4819425219/10000000000 : ℝ)|=(4819425219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1223435503/5000000000 : ℝ)|^2169 ≤ (3167573414663/20000000000000 : ℝ)^1657
        have hw : |(-1223435503/5000000000 : ℝ)|=(1223435503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4173407119/10000000000 : ℝ)*x 0 + (776243239/2500000000 : ℝ)*x 1 + (1114411739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173407119/10000000000 : ℝ)^2169 ≤ (31858503560043/100000000000000 : ℝ)^1657 := by
    have hnat : (4173407119 : ℕ)^2169*100000000000000^1657 ≤ 31858503560043^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173407119 10000000000 31858503560043 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776243239/2500000000 : ℝ)^2169 ≤ (21632547893047/100000000000000 : ℝ)^1657 := by
    have hnat : (776243239 : ℕ)^2169*100000000000000^1657 ≤ 21632547893047^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776243239 2500000000 21632547893047 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114411739/2000000000 : ℝ)^2169 ≤ (11627237131459/25000000000000 : ℝ)^1657 := by
    have hnat : (1114411739 : ℕ)^2169*25000000000000^1657 ≤ 11627237131459^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114411739 2000000000 11627237131459 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173407119/10000000000 : ℝ), (776243239/2500000000 : ℝ), (1114411739/2000000000 : ℝ)] ![(31858503560043/100000000000000 : ℝ), (21632547893047/100000000000000 : ℝ), (11627237131459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173407119/10000000000 : ℝ)|^2169 ≤ (31858503560043/100000000000000 : ℝ)^1657
        have hw : |(4173407119/10000000000 : ℝ)|=(4173407119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776243239/2500000000 : ℝ)|^2169 ≤ (21632547893047/100000000000000 : ℝ)^1657
        have hw : |(776243239/2500000000 : ℝ)|=(776243239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1114411739/2000000000 : ℝ)|^2169 ≤ (11627237131459/25000000000000 : ℝ)^1657
        have hw : |(1114411739/2000000000 : ℝ)|=(1114411739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792325409/10000000000 : ℝ)*x 0 + (4849266881/10000000000 : ℝ)*x 1 + (2975302363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792325409/10000000000 : ℝ)^2169 ≤ (10537280213081/100000000000000 : ℝ)^1657 := by
    have hnat : (1792325409 : ℕ)^2169*100000000000000^1657 ≤ 10537280213081^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792325409 10000000000 10537280213081 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4849266881/10000000000 : ℝ)^2169 ≤ (38775058616637/100000000000000 : ℝ)^1657 := by
    have hnat : (4849266881 : ℕ)^2169*100000000000000^1657 ≤ 38775058616637^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849266881 10000000000 38775058616637 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2975302363/5000000000 : ℝ)^2169 ≤ (50687661150217/100000000000000 : ℝ)^1657 := by
    have hnat : (2975302363 : ℕ)^2169*100000000000000^1657 ≤ 50687661150217^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975302363 5000000000 50687661150217 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792325409/10000000000 : ℝ), (4849266881/10000000000 : ℝ), (2975302363/5000000000 : ℝ)] ![(10537280213081/100000000000000 : ℝ), (38775058616637/100000000000000 : ℝ), (50687661150217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792325409/10000000000 : ℝ)|^2169 ≤ (10537280213081/100000000000000 : ℝ)^1657
        have hw : |(-1792325409/10000000000 : ℝ)|=(1792325409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4849266881/10000000000 : ℝ)|^2169 ≤ (38775058616637/100000000000000 : ℝ)^1657
        have hw : |(4849266881/10000000000 : ℝ)|=(4849266881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2975302363/5000000000 : ℝ)|^2169 ≤ (50687661150217/100000000000000 : ℝ)^1657
        have hw : |(2975302363/5000000000 : ℝ)|=(2975302363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2590433211/5000000000 : ℝ)*x 0 + (-1315693729/10000000000 : ℝ)*x 1 + (2975301631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590433211/5000000000 : ℝ)^2169 ≤ (42281946831313/100000000000000 : ℝ)^1657 := by
    have hnat : (2590433211 : ℕ)^2169*100000000000000^1657 ≤ 42281946831313^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590433211 5000000000 42281946831313 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315693729/10000000000 : ℝ)^2169 ≤ (3515204166861/50000000000000 : ℝ)^1657 := by
    have hnat : (1315693729 : ℕ)^2169*50000000000000^1657 ≤ 3515204166861^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315693729 10000000000 3515204166861 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2975301631/5000000000 : ℝ)^2169 ≤ (12671911206623/25000000000000 : ℝ)^1657 := by
    have hnat : (2975301631 : ℕ)^2169*25000000000000^1657 ≤ 12671911206623^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975301631 5000000000 12671911206623 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590433211/5000000000 : ℝ), (-1315693729/10000000000 : ℝ), (2975301631/5000000000 : ℝ)] ![(42281946831313/100000000000000 : ℝ), (3515204166861/50000000000000 : ℝ), (12671911206623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590433211/5000000000 : ℝ)|^2169 ≤ (42281946831313/100000000000000 : ℝ)^1657
        have hw : |(2590433211/5000000000 : ℝ)|=(2590433211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315693729/10000000000 : ℝ)|^2169 ≤ (3515204166861/50000000000000 : ℝ)^1657
        have hw : |(-1315693729/10000000000 : ℝ)|=(1315693729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2975301631/5000000000 : ℝ)|^2169 ≤ (12671911206623/25000000000000 : ℝ)^1657
        have hw : |(2975301631/5000000000 : ℝ)|=(2975301631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5180864639/10000000000 : ℝ)*x 0 + (743825821/1250000000 : ℝ)*x 1 + (-1315691181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180864639/10000000000 : ℝ)^2169 ≤ (42281927783683/100000000000000 : ℝ)^1657 := by
    have hnat : (5180864639 : ℕ)^2169*100000000000000^1657 ≤ 42281927783683^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180864639 10000000000 42281927783683 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743825821/1250000000 : ℝ)^2169 ≤ (2027507267547/4000000000000 : ℝ)^1657 := by
    have hnat : (743825821 : ℕ)^2169*4000000000000^1657 ≤ 2027507267547^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743825821 1250000000 2027507267547 4000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315691181/10000000000 : ℝ)^2169 ≤ (703039051149/10000000000000 : ℝ)^1657 := by
    have hnat : (1315691181 : ℕ)^2169*10000000000000^1657 ≤ 703039051149^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315691181 10000000000 703039051149 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180864639/10000000000 : ℝ), (743825821/1250000000 : ℝ), (-1315691181/10000000000 : ℝ)] ![(42281927783683/100000000000000 : ℝ), (2027507267547/4000000000000 : ℝ), (703039051149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180864639/10000000000 : ℝ)|^2169 ≤ (42281927783683/100000000000000 : ℝ)^1657
        have hw : |(5180864639/10000000000 : ℝ)|=(5180864639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(743825821/1250000000 : ℝ)|^2169 ≤ (2027507267547/4000000000000 : ℝ)^1657
        have hw : |(743825821/1250000000 : ℝ)|=(743825821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1315691181/10000000000 : ℝ)|^2169 ≤ (703039051149/10000000000000 : ℝ)^1657
        have hw : |(-1315691181/10000000000 : ℝ)|=(1315691181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s0_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (418246561/1000000000 : ℝ)*x 0 + (5508709051/10000000000 : ℝ)*x 1 + (792648217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418246561/1000000000 : ℝ)^2169 ≤ (15974525175059/50000000000000 : ℝ)^1657 := by
    have hnat : (418246561 : ℕ)^2169*50000000000000^1657 ≤ 15974525175059^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418246561 1000000000 15974525175059 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508709051/10000000000 : ℝ)^2169 ≤ (45818014556833/100000000000000 : ℝ)^1657 := by
    have hnat : (5508709051 : ℕ)^2169*100000000000000^1657 ≤ 45818014556833^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508709051 10000000000 45818014556833 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792648217/2500000000 : ℝ)^2169 ≤ (43423701343/195312500000 : ℝ)^1657 := by
    have hnat : (792648217 : ℕ)^2169*195312500000^1657 ≤ 43423701343^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792648217 2500000000 43423701343 195312500000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418246561/1000000000 : ℝ), (5508709051/10000000000 : ℝ), (792648217/2500000000 : ℝ)] ![(15974525175059/50000000000000 : ℝ), (45818014556833/100000000000000 : ℝ), (43423701343/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418246561/1000000000 : ℝ)|^2169 ≤ (15974525175059/50000000000000 : ℝ)^1657
        have hw : |(418246561/1000000000 : ℝ)|=(418246561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508709051/10000000000 : ℝ)|^2169 ≤ (45818014556833/100000000000000 : ℝ)^1657
        have hw : |(5508709051/10000000000 : ℝ)|=(5508709051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792648217/2500000000 : ℝ)|^2169 ≤ (43423701343/195312500000 : ℝ)^1657
        have hw : |(792648217/2500000000 : ℝ)|=(792648217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1681/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13307/50000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4337/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4337 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4337*1^1024 ≤ 0^1024*1^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4337/1024 : ℝ) ≤ (2063403498201529663/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4337 ≤ (2063403498201529663/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4337*100000000000000000000^1024 ≤ 2063403498201529663^1024*5^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2063403498201529663 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2063403498201529663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4337 := by
      have hnat : (1 : ℕ)^1024*1^4337 ≤ 1^4337*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102063403498201529663/100000000000000000000 : ℝ) ≤ (10048339225764409/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (102063403498201529663/100000000000000000000 : ℝ)^1024 ≤ (10048339225764409/10000000000000000 : ℝ)^4337 := by
      have hnat : (102063403498201529663 : ℕ)^1024*10000000000000000^4337 ≤ 10048339225764409^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102063403498201529663 100000000000000000000 10048339225764409 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048339225764409/10000000000000000 : ℝ)) (X := (102063403498201529663/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52063403498201529663/50000000000000000000 : ℝ) ≤ (5048339225764409/5000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (52063403498201529663/50000000000000000000 : ℝ)^1024 ≤ (5048339225764409/5000000000000000 : ℝ)^4337 := by
      have hnat : (52063403498201529663 : ℕ)^1024*5000000000000000^4337 ≤ 5048339225764409^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52063403498201529663 50000000000000000000 5048339225764409 5000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048339225764409/5000000000000000 : ℝ)) (X := (52063403498201529663/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48339225764409/4000000000000000 : ℝ)*(0 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48339225764409/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2063403498201529663/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48339225764409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48339225764409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048339225764409/10000000000000000 : ℝ) by norm_num, show 1+(2063403498201529663/100000000000000000000 : ℝ)+(0 : ℝ)=(102063403498201529663/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2063403498201529663/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48339225764409/4000000000000000 : ℝ)*(2/5 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48339225764409/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048339225764409/5000000000000000 : ℝ) by norm_num, show 1+2*(2063403498201529663/100000000000000000000 : ℝ)=(52063403498201529663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48339225764409/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48339225764409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48339225764409/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48339225764409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48339225764409/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48339225764409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894027009/5000000000 : ℝ)*X 0 0+(2990756549/5000000000 : ℝ)*X 0 1+(4819425317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2748892863/5000000000 : ℝ)*X 1 0+(-244686993/1000000000 : ℝ)*X 1 1+(4819425963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5497785603/10000000000 : ℝ)*X 2 0+(4819425219/10000000000 : ℝ)*X 2 1+(-1223435503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173407119/10000000000 : ℝ)*X 0 0+(776243239/2500000000 : ℝ)*X 0 1+(1114411739/2000000000 : ℝ)*X 0 2+(4173407119/10000000000 : ℝ)*X 1 0+(776243239/2500000000 : ℝ)*X 1 1+(1114411739/2000000000 : ℝ)*X 1 2+(4173407119/10000000000 : ℝ)*X 2 0+(776243239/2500000000 : ℝ)*X 2 1+(1114411739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1792325409/10000000000 : ℝ)*X 0 0+(4849266881/10000000000 : ℝ)*X 0 1+(2975302363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2590433211/5000000000 : ℝ)*X 1 0+(-1315693729/10000000000 : ℝ)*X 1 1+(2975301631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5180864639/10000000000 : ℝ)*X 2 0+(743825821/1250000000 : ℝ)*X 2 1+(-1315691181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418246561/1000000000 : ℝ)*X 0 0+(5508709051/10000000000 : ℝ)*X 0 1+(792648217/2500000000 : ℝ)*X 0 2+(418246561/1000000000 : ℝ)*X 1 0+(5508709051/10000000000 : ℝ)*X 1 1+(792648217/2500000000 : ℝ)*X 1 2+(418246561/1000000000 : ℝ)*X 2 0+(5508709051/10000000000 : ℝ)*X 2 1+(792648217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3199268760055024279263/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229750549/100000000000000 : ℝ)*(base1) + (21884367/100000000000000 : ℝ)*(base16) + (116935051/10000000000000 : ℝ)*(base19) + (1171982641/100000000000000 : ℝ)*(base23) + (212552499/100000000000000 : ℝ)*(upper3) + (1977916982627/312500000000 : ℝ)*(major0) + (1977916982627/312500000000 : ℝ)*(major1) + (1977916982627/312500000000 : ℝ)*(major2) + (860524316565799/100000000000000 : ℝ)*(sp0) + (172105158254381/20000000000000 : ℝ)*(sp1) + (430262905262071/50000000000000 : ℝ)*(sp2) + (101334422158421/25000000000000 : ℝ)*(sp3) + (723922883/25000000000000 : ℝ)*(sp4) + (449340647/25000000000000 : ℝ)*(sp7) + (405339715746821/100000000000000 : ℝ)*(f.failure) + (430263491253391/50000000000000 : ℝ)*(f.sum) + (379607143807/625000000000000000000000000 : ℝ)*base66 + (6846696814943/1250000000000000000000000000 : ℝ)*base67 + (10337825073693/1250000000000000000000000000 : ℝ)*base69 + (2820319039943/1250000000000000000000000000 : ℝ)*base71 + (776399646193/625000000000000000000000000 : ℝ)*base73 + (12593880073693/1250000000000000000000000000 : ℝ)*base75 + (3973194544943/1250000000000000000000000000 : ℝ)*base77 + (1585865815057/1250000000000000000000000000 : ℝ)*base80 + (1685549227443/625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (52897939/5000000000000000000000 : ℝ)*base90 + (52897939/5000000000000000000000 : ℝ)*base92 + (52897939/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168598382217296290229949/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (328268959/100000000000000 : ℝ)*(base19) + (456865969/100000000000000 : ℝ)*(base23) + (7533013/25000000000000 : ℝ)*(base39) + (25548011/12500000000000 : ℝ)*(upper2) + (31170249/50000000000000 : ℝ)*(upper4) + (31194327/100000000000000 : ℝ)*(upper5) + (133568056509687/20000000000000 : ℝ)*(major0) + (133568056509687/20000000000000 : ℝ)*(major1) + (667840252416383/100000000000000 : ℝ)*(major2) + (112374591/5000000000000 : ℝ)*(sp2) + (907985828873029/100000000000000 : ℝ)*(sp4) + (907985500604069/100000000000000 : ℝ)*(sp5) + (907983154647291/100000000000000 : ℝ)*(sp6) + (213847282796567/50000000000000 : ℝ)*(sp7) + (213847282796567/50000000000000 : ℝ)*(f.failure) + (22699646475127/2500000000000 : ℝ)*(f.sum) + (164093409981281/200000000000000000000000000000 : ℝ)*base65 + (1182210823287353/400000000000000000000000000000 : ℝ)*base68 + (298639180950017/80000000000000000000000000000 : ℝ)*base70 + (1828715386712647/400000000000000000000000000000 : ℝ)*base71 + (767595520818719/200000000000000000000000000000 : ℝ)*base74 + (314117777129983/80000000000000000000000000000 : ℝ)*base75 + (222713483590017/80000000000000000000000000000 : ℝ)*base78 + (314963352169983/80000000000000000000000000000 : ℝ)*base79 + (34349180510017/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (10244047/2500000000000000000000 : ℝ)*base89 + (10244047/2500000000000000000000 : ℝ)*base91 + (10244047/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1378_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1681/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13307/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_s1_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967690897/10000000000 : ℝ)*x 0 + (5626347473/10000000000 : ℝ)*x 1 + (1264877049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967690897/10000000000 : ℝ)^2169 ≤ (2976700217853/25000000000000 : ℝ)^1657 := by
    have hnat : (1967690897 : ℕ)^2169*25000000000000^1657 ≤ 2976700217853^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967690897 10000000000 2976700217853 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5626347473/10000000000 : ℝ)^2169 ≤ (9420598809021/20000000000000 : ℝ)^1657 := by
    have hnat : (5626347473 : ℕ)^2169*20000000000000^1657 ≤ 9420598809021^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5626347473 10000000000 9420598809021 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264877049/2500000000 : ℝ)^2169 ≤ (20495102534847/50000000000000 : ℝ)^1657 := by
    have hnat : (1264877049 : ℕ)^2169*50000000000000^1657 ≤ 20495102534847^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264877049 2500000000 20495102534847 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967690897/10000000000 : ℝ), (5626347473/10000000000 : ℝ), (1264877049/2500000000 : ℝ)] ![(2976700217853/25000000000000 : ℝ), (9420598809021/20000000000000 : ℝ), (20495102534847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967690897/10000000000 : ℝ)|^2169 ≤ (2976700217853/25000000000000 : ℝ)^1657
        have hw : |(-1967690897/10000000000 : ℝ)|=(1967690897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5626347473/10000000000 : ℝ)|^2169 ≤ (9420598809021/20000000000000 : ℝ)^1657
        have hw : |(5626347473/10000000000 : ℝ)|=(5626347473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1264877049/2500000000 : ℝ)|^2169 ≤ (20495102534847/50000000000000 : ℝ)^1657
        have hw : |(1264877049/2500000000 : ℝ)|=(1264877049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2700993843/5000000000 : ℝ)*x 0 + (-113463011/500000000 : ℝ)*x 1 + (5059509603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700993843/5000000000 : ℝ)^2169 ≤ (1395612237943/3125000000000 : ℝ)^1657 := by
    have hnat : (2700993843 : ℕ)^2169*3125000000000^1657 ≤ 1395612237943^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700993843 5000000000 1395612237943 3125000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113463011/500000000 : ℝ)^2169 ≤ (14350188377397/100000000000000 : ℝ)^1657 := by
    have hnat : (113463011 : ℕ)^2169*100000000000000^1657 ≤ 14350188377397^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113463011 500000000 14350188377397 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5059509603/10000000000 : ℝ)^2169 ≤ (20495109995433/50000000000000 : ℝ)^1657 := by
    have hnat : (5059509603 : ℕ)^2169*50000000000000^1657 ≤ 20495109995433^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059509603 10000000000 20495109995433 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700993843/5000000000 : ℝ), (-113463011/500000000 : ℝ), (5059509603/10000000000 : ℝ)] ![(1395612237943/3125000000000 : ℝ), (14350188377397/100000000000000 : ℝ), (20495109995433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700993843/5000000000 : ℝ)|^2169 ≤ (1395612237943/3125000000000 : ℝ)^1657
        have hw : |(2700993843/5000000000 : ℝ)|=(2700993843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113463011/500000000 : ℝ)|^2169 ≤ (14350188377397/100000000000000 : ℝ)^1657
        have hw : |(-113463011/500000000 : ℝ)|=(113463011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5059509603/10000000000 : ℝ)|^2169 ≤ (20495109995433/50000000000000 : ℝ)^1657
        have hw : |(5059509603/10000000000 : ℝ)|=(5059509603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5401988311/10000000000 : ℝ)*x 0 + (1011901677/2000000000 : ℝ)*x 1 + (-2269260963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401988311/10000000000 : ℝ)^2169 ≤ (44659598377781/100000000000000 : ℝ)^1657 := by
    have hnat : (5401988311 : ℕ)^2169*100000000000000^1657 ≤ 44659598377781^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401988311 10000000000 44659598377781 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011901677/2000000000 : ℝ)^2169 ≤ (4099020707403/10000000000000 : ℝ)^1657 := by
    have hnat : (1011901677 : ℕ)^2169*10000000000000^1657 ≤ 4099020707403^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011901677 2000000000 4099020707403 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269260963/10000000000 : ℝ)^2169 ≤ (7175097263869/50000000000000 : ℝ)^1657 := by
    have hnat : (2269260963 : ℕ)^2169*50000000000000^1657 ≤ 7175097263869^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269260963 10000000000 7175097263869 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401988311/10000000000 : ℝ), (1011901677/2000000000 : ℝ), (-2269260963/10000000000 : ℝ)] ![(44659598377781/100000000000000 : ℝ), (4099020707403/10000000000000 : ℝ), (7175097263869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401988311/10000000000 : ℝ)|^2169 ≤ (44659598377781/100000000000000 : ℝ)^1657
        have hw : |(5401988311/10000000000 : ℝ)|=(5401988311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011901677/2000000000 : ℝ)|^2169 ≤ (4099020707403/10000000000000 : ℝ)^1657
        have hw : |(1011901677/2000000000 : ℝ)|=(1011901677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2269260963/10000000000 : ℝ)|^2169 ≤ (7175097263869/50000000000000 : ℝ)^1657
        have hw : |(-2269260963/10000000000 : ℝ)|=(2269260963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (857172721/2000000000 : ℝ)*x 0 + (3722708073/10000000000 : ℝ)*x 1 + (1231522553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857172721/2000000000 : ℝ)^2169 ≤ (32986867913101/100000000000000 : ℝ)^1657 := by
    have hnat : (857172721 : ℕ)^2169*100000000000000^1657 ≤ 32986867913101^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857172721 2000000000 32986867913101 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3722708073/10000000000 : ℝ)^2169 ≤ (27432019010181/100000000000000 : ℝ)^1657 := by
    have hnat : (3722708073 : ℕ)^2169*100000000000000^1657 ≤ 27432019010181^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722708073 10000000000 27432019010181 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231522553/2500000000 : ℝ)^2169 ≤ (39581113060193/100000000000000 : ℝ)^1657 := by
    have hnat : (1231522553 : ℕ)^2169*100000000000000^1657 ≤ 39581113060193^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231522553 2500000000 39581113060193 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857172721/2000000000 : ℝ), (3722708073/10000000000 : ℝ), (1231522553/2500000000 : ℝ)] ![(32986867913101/100000000000000 : ℝ), (27432019010181/100000000000000 : ℝ), (39581113060193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857172721/2000000000 : ℝ)|^2169 ≤ (32986867913101/100000000000000 : ℝ)^1657
        have hw : |(857172721/2000000000 : ℝ)|=(857172721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3722708073/10000000000 : ℝ)|^2169 ≤ (27432019010181/100000000000000 : ℝ)^1657
        have hw : |(3722708073/10000000000 : ℝ)|=(3722708073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231522553/2500000000 : ℝ)|^2169 ≤ (39581113060193/100000000000000 : ℝ)^1657
        have hw : |(1231522553/2500000000 : ℝ)|=(1231522553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968165193/10000000000 : ℝ)*x 0 + (633303229/1250000000 : ℝ)*x 1 + (561930753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968165193/10000000000 : ℝ)^2169 ≤ (11910557868787/100000000000000 : ℝ)^1657 := by
    have hnat : (1968165193 : ℕ)^2169*100000000000000^1657 ≤ 11910557868787^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968165193 10000000000 11910557868787 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633303229/1250000000 : ℝ)^2169 ≤ (2053179088997/5000000000000 : ℝ)^1657 := by
    have hnat : (633303229 : ℕ)^2169*5000000000000^1657 ≤ 2053179088997^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633303229 1250000000 2053179088997 5000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561930753/1000000000 : ℝ)^2169 ≤ (9405172069069/20000000000000 : ℝ)^1657 := by
    have hnat : (561930753 : ℕ)^2169*20000000000000^1657 ≤ 9405172069069^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561930753 1000000000 9405172069069 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968165193/10000000000 : ℝ), (633303229/1250000000 : ℝ), (561930753/1000000000 : ℝ)] ![(11910557868787/100000000000000 : ℝ), (2053179088997/5000000000000 : ℝ), (9405172069069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968165193/10000000000 : ℝ)|^2169 ≤ (11910557868787/100000000000000 : ℝ)^1657
        have hw : |(-1968165193/10000000000 : ℝ)|=(1968165193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(633303229/1250000000 : ℝ)|^2169 ≤ (2053179088997/5000000000000 : ℝ)^1657
        have hw : |(633303229/1250000000 : ℝ)|=(633303229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561930753/1000000000 : ℝ)|^2169 ≤ (9405172069069/20000000000000 : ℝ)^1657
        have hw : |(561930753/1000000000 : ℝ)|=(561930753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5254468007/10000000000 : ℝ)*x 0 + (-427365519/2500000000 : ℝ)*x 1 + (5619307633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254468007/10000000000 : ℝ)^2169 ≤ (8613989235967/20000000000000 : ℝ)^1657 := by
    have hnat : (5254468007 : ℕ)^2169*20000000000000^1657 ≤ 8613989235967^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254468007 10000000000 8613989235967 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427365519/2500000000 : ℝ)^2169 ≤ (9904192333959/100000000000000 : ℝ)^1657 := by
    have hnat : (427365519 : ℕ)^2169*100000000000000^1657 ≤ 9904192333959^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427365519 2500000000 9904192333959 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5619307633/10000000000 : ℝ)^2169 ≤ (9405172294731/20000000000000 : ℝ)^1657 := by
    have hnat : (5619307633 : ℕ)^2169*20000000000000^1657 ≤ 9405172294731^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5619307633 10000000000 9405172294731 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254468007/10000000000 : ℝ), (-427365519/2500000000 : ℝ), (5619307633/10000000000 : ℝ)] ![(8613989235967/20000000000000 : ℝ), (9904192333959/100000000000000 : ℝ), (9405172294731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254468007/10000000000 : ℝ)|^2169 ≤ (8613989235967/20000000000000 : ℝ)^1657
        have hw : |(5254468007/10000000000 : ℝ)|=(5254468007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427365519/2500000000 : ℝ)|^2169 ≤ (9904192333959/100000000000000 : ℝ)^1657
        have hw : |(-427365519/2500000000 : ℝ)|=(427365519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5619307633/10000000000 : ℝ)|^2169 ≤ (9405172294731/20000000000000 : ℝ)^1657
        have hw : |(5619307633/10000000000 : ℝ)|=(5619307633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1050893581/2000000000 : ℝ)*x 0 + (1123861549/2000000000 : ℝ)*x 1 + (-1709462059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050893581/2000000000 : ℝ)^2169 ≤ (21534972542709/50000000000000 : ℝ)^1657 := by
    have hnat : (1050893581 : ℕ)^2169*50000000000000^1657 ≤ 21534972542709^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050893581 2000000000 21534972542709 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123861549/2000000000 : ℝ)^2169 ≤ (23512931350277/50000000000000 : ℝ)^1657 := by
    have hnat : (1123861549 : ℕ)^2169*50000000000000^1657 ≤ 23512931350277^1657*2000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123861549 2000000000 23512931350277 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709462059/10000000000 : ℝ)^2169 ≤ (9904192205031/100000000000000 : ℝ)^1657 := by
    have hnat : (1709462059 : ℕ)^2169*100000000000000^1657 ≤ 9904192205031^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709462059 10000000000 9904192205031 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050893581/2000000000 : ℝ), (1123861549/2000000000 : ℝ), (-1709462059/10000000000 : ℝ)] ![(21534972542709/50000000000000 : ℝ), (23512931350277/50000000000000 : ℝ), (9904192205031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050893581/2000000000 : ℝ)|^2169 ≤ (21534972542709/50000000000000 : ℝ)^1657
        have hw : |(1050893581/2000000000 : ℝ)|=(1050893581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123861549/2000000000 : ℝ)|^2169 ≤ (23512931350277/50000000000000 : ℝ)^1657
        have hw : |(1123861549/2000000000 : ℝ)|=(1123861549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1709462059/10000000000 : ℝ)|^2169 ≤ (9904192205031/100000000000000 : ℝ)^1657
        have hw : |(-1709462059/10000000000 : ℝ)|=(1709462059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s1_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1071717813/2500000000 : ℝ)*x 0 + (76740721/156250000 : ℝ)*x 1 + (3737650467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071717813/2500000000 : ℝ)^2169 ≤ (32997020202039/100000000000000 : ℝ)^1657 := by
    have hnat : (1071717813 : ℕ)^2169*100000000000000^1657 ≤ 32997020202039^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071717813 2500000000 32997020202039 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76740721/156250000 : ℝ)^2169 ≤ (19713370467737/50000000000000 : ℝ)^1657 := by
    have hnat : (76740721 : ℕ)^2169*50000000000000^1657 ≤ 19713370467737^1657*156250000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76740721 156250000 19713370467737 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3737650467/10000000000 : ℝ)^2169 ≤ (27576238848339/100000000000000 : ℝ)^1657 := by
    have hnat : (3737650467 : ℕ)^2169*100000000000000^1657 ≤ 27576238848339^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3737650467 10000000000 27576238848339 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071717813/2500000000 : ℝ), (76740721/156250000 : ℝ), (3737650467/10000000000 : ℝ)] ![(32997020202039/100000000000000 : ℝ), (19713370467737/50000000000000 : ℝ), (27576238848339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071717813/2500000000 : ℝ)|^2169 ≤ (32997020202039/100000000000000 : ℝ)^1657
        have hw : |(1071717813/2500000000 : ℝ)|=(1071717813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76740721/156250000 : ℝ)|^2169 ≤ (19713370467737/50000000000000 : ℝ)^1657
        have hw : |(76740721/156250000 : ℝ)|=(76740721/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3737650467/10000000000 : ℝ)|^2169 ≤ (27576238848339/100000000000000 : ℝ)^1657
        have hw : |(3737650467/10000000000 : ℝ)|=(3737650467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13307/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (451/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9599/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13307/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13307/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13307/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13307/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13307/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13307/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1681/100000 : ℝ) ^ (4337/1024 : ℝ) ≤ (3052498383051/100000000000000000000 : ℝ) := by
    have hpowers : (1681/100000 : ℝ)^4337 ≤ (3052498383051/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1681 : ℕ)^4337*100000000000000000000^1024 ≤ 3052498383051^1024*100000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1681 100000 3052498383051 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1681/100000 : ℝ)) (X := (3052498383051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13307/50000 : ℝ) ^ (4337/1024 : ℝ) ≤ (45925024780650403/12500000000000000000 : ℝ) := by
    have hpowers : (13307/50000 : ℝ)^4337 ≤ (45925024780650403/12500000000000000000 : ℝ)^1024 := by
      have hnat : (13307 : ℕ)^4337*12500000000000000000^1024 ≤ 45925024780650403^1024*50000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13307 50000 45925024780650403 12500000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13307/50000 : ℝ)) (X := (45925024780650403/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003052498383051/50000000000000000000 : ℝ) ≤ (10000000144143799/10000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50000003052498383051/50000000000000000000 : ℝ)^1024 ≤ (10000000144143799/10000000000000000 : ℝ)^4337 := by
      have hnat : (50000003052498383051 : ℕ)^1024*10000000000000000^4337 ≤ 10000000144143799^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003052498383051 50000000000000000000 10000000144143799 10000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000144143799/10000000000000000 : ℝ)) (X := (50000003052498383051/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4014696130029743451/4000000000000000000 : ℝ) ≤ (5004331267260901/5000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (4014696130029743451/4000000000000000000 : ℝ)^1024 ≤ (5004331267260901/5000000000000000 : ℝ)^4337 := by
      have hnat : (4014696130029743451 : ℕ)^1024*5000000000000000^4337 ≤ 5004331267260901^4337*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4014696130029743451 4000000000000000000 5004331267260901 5000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004331267260901/5000000000000000 : ℝ)) (X := (4014696130029743451/4000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6295925024780650403/6250000000000000000 : ℝ) ≤ (2003464984979961/2000000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (6295925024780650403/6250000000000000000 : ℝ)^1024 ≤ (2003464984979961/2000000000000000 : ℝ)^4337 := by
      have hnat : (6295925024780650403 : ℕ)^1024*2000000000000000^4337 ≤ 2003464984979961^4337*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6295925024780650403 6250000000000000000 2003464984979961 2000000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003464984979961/2000000000000000 : ℝ)) (X := (6295925024780650403/6250000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3052498383051/100000000000000000000 : ℝ) ≤ ((249300880637486494381/249330000000000000000 : ℝ)+2*(8662390378003/2493300000000000 : ℝ)*(1681/100000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (249300880637486494381/249330000000000000000 : ℝ)+2*(8662390378003/2493300000000000 : ℝ)*(1681/100000 : ℝ)=(10000000144143799/10000000000000000 : ℝ) by norm_num, show 1+2*(3052498383051/100000000000000000000 : ℝ)=(50000003052498383051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45925024780650403/12500000000000000000 : ℝ)+(3052498383051/100000000000000000000 : ℝ) ≤ ((249300880637486494381/249330000000000000000 : ℝ)+(8662390378003/2493300000000000 : ℝ)*((13307/50000 : ℝ)+(1681/100000 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (249300880637486494381/249330000000000000000 : ℝ)+(8662390378003/2493300000000000 : ℝ)*((13307/50000 : ℝ)+(1681/100000 : ℝ))=(5004331267260901/5000000000000000 : ℝ) by norm_num, show 1+(45925024780650403/12500000000000000000 : ℝ)+(3052498383051/100000000000000000000 : ℝ)=(4014696130029743451/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45925024780650403/12500000000000000000 : ℝ) ≤ ((249300880637486494381/249330000000000000000 : ℝ)+2*(8662390378003/2493300000000000 : ℝ)*(13307/50000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (249300880637486494381/249330000000000000000 : ℝ)+2*(8662390378003/2493300000000000 : ℝ)*(13307/50000 : ℝ)=(2003464984979961/2000000000000000 : ℝ) by norm_num, show 1+2*(45925024780650403/12500000000000000000 : ℝ)=(6295925024780650403/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (249300880637486494381/249330000000000000000 : ℝ)*(X 1 0+X 2 0)+(8662390378003/2493300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1681/100000 : ℝ)) (hi := (13307/50000 : ℝ)) (c := (249300880637486494381/249330000000000000000 : ℝ)) (alpha := (8662390378003/2493300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (249300880637486494381/249330000000000000000 : ℝ)*(X 0 1+X 2 1)+(8662390378003/2493300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1681/100000 : ℝ)) (hi := (13307/50000 : ℝ)) (c := (249300880637486494381/249330000000000000000 : ℝ)) (alpha := (8662390378003/2493300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (249300880637486494381/249330000000000000000 : ℝ)*(X 0 2+X 1 2)+(8662390378003/2493300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (1681/100000 : ℝ)) (hi := (13307/50000 : ℝ)) (c := (249300880637486494381/249330000000000000000 : ℝ)) (alpha := (8662390378003/2493300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1967690897/10000000000 : ℝ)*X 0 0+(5626347473/10000000000 : ℝ)*X 0 1+(1264877049/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2700993843/5000000000 : ℝ)*X 1 0+(-113463011/500000000 : ℝ)*X 1 1+(5059509603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5401988311/10000000000 : ℝ)*X 2 0+(1011901677/2000000000 : ℝ)*X 2 1+(-2269260963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857172721/2000000000 : ℝ)*X 0 0+(3722708073/10000000000 : ℝ)*X 0 1+(1231522553/2500000000 : ℝ)*X 0 2+(857172721/2000000000 : ℝ)*X 1 0+(3722708073/10000000000 : ℝ)*X 1 1+(1231522553/2500000000 : ℝ)*X 1 2+(857172721/2000000000 : ℝ)*X 2 0+(3722708073/10000000000 : ℝ)*X 2 1+(1231522553/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1968165193/10000000000 : ℝ)*X 0 0+(633303229/1250000000 : ℝ)*X 0 1+(561930753/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254468007/10000000000 : ℝ)*X 1 0+(-427365519/2500000000 : ℝ)*X 1 1+(5619307633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050893581/2000000000 : ℝ)*X 2 0+(1123861549/2000000000 : ℝ)*X 2 1+(-1709462059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071717813/2500000000 : ℝ)*X 0 0+(76740721/156250000 : ℝ)*X 0 1+(3737650467/10000000000 : ℝ)*X 0 2+(1071717813/2500000000 : ℝ)*X 1 0+(76740721/156250000 : ℝ)*X 1 1+(3737650467/10000000000 : ℝ)*X 1 2+(1071717813/2500000000 : ℝ)*X 2 0+(76740721/156250000 : ℝ)*X 2 1+(3737650467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10178537267257129239074851559/1038875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92219/5000000000000 : ℝ)*(base1) + (1660906679/100000000000000 : ℝ)*(base19) + (466255239/25000000000000 : ℝ)*(base23) + (300117429/100000000000000 : ℝ)*(upper3) + (29224303/100000000000000 : ℝ)*(upper5) + (648800174965261/50000000000000 : ℝ)*(major0) + (648800174965261/50000000000000 : ℝ)*(major1) + (648800174965261/50000000000000 : ℝ)*(major2) + (70567385972211/4000000000000 : ℝ)*(sp0) + (1102622938211/62500000000 : ℝ)*(sp1) + (1764196497023323/100000000000000 : ℝ)*(sp2) + (25968617746613/3125000000000 : ℝ)*(sp3) + (2742916677/20000000000000 : ℝ)*(sp4) + (3120746157/50000000000000 : ℝ)*(sp7) + (831002011228311/100000000000000 : ℝ)*(f.failure) + (1764198362044279/100000000000000 : ℝ)*(f.sum) + (28142213852473/62332500000000000000000000000 : ℝ)*base65 + (5834652420378501559/12466500000000000000000000000000000 : ℝ)*base68 + (18632329850754998441/12466500000000000000000000000000000 : ℝ)*base69 + (67314134173392998441/12466500000000000000000000000000000 : ℝ)*base71 + (229567041647897/62332500000000000000000000000 : ℝ)*base74 + (49643373795729998441/12466500000000000000000000000000000 : ℝ)*base75 + (70445920269968498441/12466500000000000000000000000000000 : ℝ)*base77 + (16913693685281498441/12466500000000000000000000000000000 : ℝ)*base79 + (75091345598201/124665000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4699151/5000000000000000000000 : ℝ)*base89 + (4699151/5000000000000000000000 : ℝ)*base91 + (4699151/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19287538840418510151492882531/2077750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18601507/20000000000000 : ℝ)*(base1) + (371156839/20000000000000 : ℝ)*(base19) + (1824275129/100000000000000 : ℝ)*(base23) + (110894953/50000000000000 : ℝ)*(upper3) + (51967133/25000000000000 : ℝ)*(upper5) + (665167841248849/50000000000000 : ℝ)*(major0) + (665167841248849/50000000000000 : ℝ)*(major1) + (665167841248849/50000000000000 : ℝ)*(major2) + (2489906611/25000000000000 : ℝ)*(sp1) + (1008786011/10000000000000 : ℝ)*(sp2) + (5652202991949/312500000000 : ℝ)*(sp4) + (904346524502753/50000000000000 : ℝ)*(sp5) + (904346476140453/50000000000000 : ℝ)*(sp6) + (425983049070909/50000000000000 : ℝ)*(sp7) + (851966191149353/100000000000000 : ℝ)*(f.failure) + (361740972883229/20000000000000 : ℝ)*(f.sum) + (191332598856127/62332500000000000000000000000 : ℝ)*base65 + (41898522901907917469/12466500000000000000000000000000000 : ℝ)*base67 + (65797175209983082531/12466500000000000000000000000000000 : ℝ)*base70 + (4157711082807082531/12466500000000000000000000000000000 : ℝ)*base72 + (304538656345927/62332500000000000000000000000 : ℝ)*base73 + (6368169079121917469/12466500000000000000000000000000000 : ℝ)*base75 + (92424241056161917469/12466500000000000000000000000000000 : ℝ)*base77 + (26528106810167917469/12466500000000000000000000000000000 : ℝ)*base79 + (1527550459673/3895781250000000000000000000 : ℝ)*base82 + (17013327/5000000000000000000000 : ℝ)*base90 + (17013327/5000000000000000000000 : ℝ)*base92 + (17013327/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1378_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13307/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9599/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1378_s2_0 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-100240193/500000000 : ℝ)*x 0 + (5470297553/10000000000 : ℝ)*x 1 + (519173687/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100240193/500000000 : ℝ)^2169 ≤ (1525202794749/12500000000000 : ℝ)^1657 := by
    have hnat : (100240193 : ℕ)^2169*12500000000000^1657 ≤ 1525202794749^1657*500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100240193 500000000 1525202794749 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470297553/10000000000 : ℝ)^2169 ≤ (22700132568703/50000000000000 : ℝ)^1657 := by
    have hnat : (5470297553 : ℕ)^2169*50000000000000^1657 ≤ 22700132568703^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470297553 10000000000 22700132568703 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519173687/1000000000 : ℝ)^2169 ≤ (5299764061217/12500000000000 : ℝ)^1657 := by
    have hnat : (519173687 : ℕ)^2169*12500000000000^1657 ≤ 5299764061217^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519173687 1000000000 5299764061217 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100240193/500000000 : ℝ), (5470297553/10000000000 : ℝ), (519173687/1000000000 : ℝ)] ![(1525202794749/12500000000000 : ℝ), (22700132568703/50000000000000 : ℝ), (5299764061217/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100240193/500000000 : ℝ)|^2169 ≤ (1525202794749/12500000000000 : ℝ)^1657
        have hw : |(-100240193/500000000 : ℝ)|=(100240193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470297553/10000000000 : ℝ)|^2169 ≤ (22700132568703/50000000000000 : ℝ)^1657
        have hw : |(5470297553/10000000000 : ℝ)|=(5470297553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519173687/1000000000 : ℝ)|^2169 ≤ (5299764061217/12500000000000 : ℝ)^1657
        have hw : |(519173687/1000000000 : ℝ)|=(519173687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_1 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681737139/5000000000 : ℝ)*x 0 + (-537116621/2500000000 : ℝ)*x 1 + (5191736913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681737139/5000000000 : ℝ)^2169 ≤ (11060817074717/25000000000000 : ℝ)^1657 := by
    have hnat : (2681737139 : ℕ)^2169*25000000000000^1657 ≤ 11060817074717^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681737139 5000000000 11060817074717 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537116621/2500000000 : ℝ)^2169 ≤ (6679309369361/50000000000000 : ℝ)^1657 := by
    have hnat : (537116621 : ℕ)^2169*50000000000000^1657 ≤ 6679309369361^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537116621 2500000000 6679309369361 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191736913/10000000000 : ℝ)^2169 ≤ (42398112949399/100000000000000 : ℝ)^1657 := by
    have hnat : (5191736913 : ℕ)^2169*100000000000000^1657 ≤ 42398112949399^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191736913 10000000000 42398112949399 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681737139/5000000000 : ℝ), (-537116621/2500000000 : ℝ), (5191736913/10000000000 : ℝ)] ![(11060817074717/25000000000000 : ℝ), (6679309369361/50000000000000 : ℝ), (42398112949399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681737139/5000000000 : ℝ)|^2169 ≤ (11060817074717/25000000000000 : ℝ)^1657
        have hw : |(2681737139/5000000000 : ℝ)|=(2681737139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537116621/2500000000 : ℝ)|^2169 ≤ (6679309369361/50000000000000 : ℝ)^1657
        have hw : |(-537116621/2500000000 : ℝ)|=(537116621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5191736913/10000000000 : ℝ)|^2169 ≤ (42398112949399/100000000000000 : ℝ)^1657
        have hw : |(5191736913/10000000000 : ℝ)|=(5191736913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_2 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681737099/5000000000 : ℝ)*x 0 + (5191736983/10000000000 : ℝ)*x 1 + (-1074233249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681737099/5000000000 : ℝ)^2169 ≤ (22121633717519/50000000000000 : ℝ)^1657 := by
    have hnat : (2681737099 : ℕ)^2169*50000000000000^1657 ≤ 22121633717519^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681737099 5000000000 22121633717519 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191736983/10000000000 : ℝ)^2169 ≤ (42398113697687/100000000000000 : ℝ)^1657 := by
    have hnat : (5191736983 : ℕ)^2169*100000000000000^1657 ≤ 42398113697687^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191736983 10000000000 42398113697687 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074233249/5000000000 : ℝ)^2169 ≤ (3339654713167/25000000000000 : ℝ)^1657 := by
    have hnat : (1074233249 : ℕ)^2169*25000000000000^1657 ≤ 3339654713167^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074233249 5000000000 3339654713167 25000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681737099/5000000000 : ℝ), (5191736983/10000000000 : ℝ), (-1074233249/5000000000 : ℝ)] ![(22121633717519/50000000000000 : ℝ), (42398113697687/100000000000000 : ℝ), (3339654713167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681737099/5000000000 : ℝ)|^2169 ≤ (22121633717519/50000000000000 : ℝ)^1657
        have hw : |(2681737099/5000000000 : ℝ)|=(2681737099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191736983/10000000000 : ℝ)|^2169 ≤ (42398113697687/100000000000000 : ℝ)^1657
        have hw : |(5191736983/10000000000 : ℝ)|=(5191736983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074233249/5000000000 : ℝ)|^2169 ≤ (3339654713167/25000000000000 : ℝ)^1657
        have hw : |(-1074233249/5000000000 : ℝ)|=(1074233249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_3 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538990249/1250000000 : ℝ)*x 0 + (1006384121/2500000000 : ℝ)*x 1 + (4616914409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538990249/1250000000 : ℝ)^2169 ≤ (2078103077523/6250000000000 : ℝ)^1657 := by
    have hnat : (538990249 : ℕ)^2169*6250000000000^1657 ≤ 2078103077523^1657*1250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538990249 1250000000 2078103077523 6250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006384121/2500000000 : ℝ)^2169 ≤ (30389070134781/100000000000000 : ℝ)^1657 := by
    have hnat : (1006384121 : ℕ)^2169*100000000000000^1657 ≤ 30389070134781^1657*2500000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006384121 2500000000 30389070134781 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4616914409/10000000000 : ℝ)^2169 ≤ (18180640302189/50000000000000 : ℝ)^1657 := by
    have hnat : (4616914409 : ℕ)^2169*50000000000000^1657 ≤ 18180640302189^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616914409 10000000000 18180640302189 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538990249/1250000000 : ℝ), (1006384121/2500000000 : ℝ), (4616914409/10000000000 : ℝ)] ![(2078103077523/6250000000000 : ℝ), (30389070134781/100000000000000 : ℝ), (18180640302189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538990249/1250000000 : ℝ)|^2169 ≤ (2078103077523/6250000000000 : ℝ)^1657
        have hw : |(538990249/1250000000 : ℝ)|=(538990249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006384121/2500000000 : ℝ)|^2169 ≤ (30389070134781/100000000000000 : ℝ)^1657
        have hw : |(1006384121/2500000000 : ℝ)|=(1006384121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4616914409/10000000000 : ℝ)|^2169 ≤ (18180640302189/50000000000000 : ℝ)^1657
        have hw : |(4616914409/10000000000 : ℝ)|=(4616914409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_4 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-125303749/625000000 : ℝ)*x 0 + (5193417301/10000000000 : ℝ)*x 1 + (5468602721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125303749/625000000 : ℝ)^2169 ≤ (12202069487393/100000000000000 : ℝ)^1657 := by
    have hnat : (125303749 : ℕ)^2169*100000000000000^1657 ≤ 12202069487393^1657*625000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125303749 625000000 12202069487393 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193417301/10000000000 : ℝ)^2169 ≤ (42416076913583/100000000000000 : ℝ)^1657 := by
    have hnat : (5193417301 : ℕ)^2169*100000000000000^1657 ≤ 42416076913583^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193417301 10000000000 42416076913583 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468602721/10000000000 : ℝ)^2169 ≤ (1815274143503/4000000000000 : ℝ)^1657 := by
    have hnat : (5468602721 : ℕ)^2169*4000000000000^1657 ≤ 1815274143503^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468602721 10000000000 1815274143503 4000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125303749/625000000 : ℝ), (5193417301/10000000000 : ℝ), (5468602721/10000000000 : ℝ)] ![(12202069487393/100000000000000 : ℝ), (42416076913583/100000000000000 : ℝ), (1815274143503/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125303749/625000000 : ℝ)|^2169 ≤ (12202069487393/100000000000000 : ℝ)^1657
        have hw : |(-125303749/625000000 : ℝ)|=(125303749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193417301/10000000000 : ℝ)|^2169 ≤ (42416076913583/100000000000000 : ℝ)^1657
        have hw : |(5193417301/10000000000 : ℝ)|=(5193417301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468602721/10000000000 : ℝ)|^2169 ≤ (1815274143503/4000000000000 : ℝ)^1657
        have hw : |(5468602721/10000000000 : ℝ)|=(5468602721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_5 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132285041/250000000 : ℝ)*x 0 + (-187160127/1000000000 : ℝ)*x 1 + (5468602419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132285041/250000000 : ℝ)^2169 ≤ (43466658106013/100000000000000 : ℝ)^1657 := by
    have hnat : (132285041 : ℕ)^2169*100000000000000^1657 ≤ 43466658106013^1657*250000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132285041 250000000 43466658106013 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187160127/1000000000 : ℝ)^2169 ≤ (1115149157001/10000000000000 : ℝ)^1657 := by
    have hnat : (187160127 : ℕ)^2169*10000000000000^1657 ≤ 1115149157001^1657*1000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187160127 1000000000 1115149157001 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468602419/10000000000 : ℝ)^2169 ≤ (45381850307001/100000000000000 : ℝ)^1657 := by
    have hnat : (5468602419 : ℕ)^2169*100000000000000^1657 ≤ 45381850307001^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468602419 10000000000 45381850307001 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132285041/250000000 : ℝ), (-187160127/1000000000 : ℝ), (5468602419/10000000000 : ℝ)] ![(43466658106013/100000000000000 : ℝ), (1115149157001/10000000000000 : ℝ), (45381850307001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132285041/250000000 : ℝ)|^2169 ≤ (43466658106013/100000000000000 : ℝ)^1657
        have hw : |(132285041/250000000 : ℝ)|=(132285041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187160127/1000000000 : ℝ)|^2169 ≤ (1115149157001/10000000000000 : ℝ)^1657
        have hw : |(-187160127/1000000000 : ℝ)|=(187160127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468602419/10000000000 : ℝ)|^2169 ≤ (45381850307001/100000000000000 : ℝ)^1657
        have hw : |(5468602419/10000000000 : ℝ)|=(5468602419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_6 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291403127/10000000000 : ℝ)*x 0 + (5468602519/10000000000 : ℝ)*x 1 + (-935799541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291403127/10000000000 : ℝ)^2169 ≤ (5433334261933/12500000000000 : ℝ)^1657 := by
    have hnat : (5291403127 : ℕ)^2169*12500000000000^1657 ≤ 5433334261933^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291403127 10000000000 5433334261933 12500000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468602519/10000000000 : ℝ)^2169 ≤ (45381851393283/100000000000000 : ℝ)^1657 := by
    have hnat : (5468602519 : ℕ)^2169*100000000000000^1657 ≤ 45381851393283^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468602519 10000000000 45381851393283 100000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935799541/5000000000 : ℝ)^2169 ≤ (696967156569/6250000000000 : ℝ)^1657 := by
    have hnat : (935799541 : ℕ)^2169*6250000000000^1657 ≤ 696967156569^1657*5000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935799541 5000000000 696967156569 6250000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291403127/10000000000 : ℝ), (5468602519/10000000000 : ℝ), (-935799541/5000000000 : ℝ)] ![(5433334261933/12500000000000 : ℝ), (45381851393283/100000000000000 : ℝ), (696967156569/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291403127/10000000000 : ℝ)|^2169 ≤ (5433334261933/12500000000000 : ℝ)^1657
        have hw : |(5291403127/10000000000 : ℝ)|=(5291403127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468602519/10000000000 : ℝ)|^2169 ≤ (45381851393283/100000000000000 : ℝ)^1657
        have hw : |(5468602519/10000000000 : ℝ)|=(5468602519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-935799541/5000000000 : ℝ)|^2169 ≤ (696967156569/6250000000000 : ℝ)^1657
        have hw : |(-935799541/5000000000 : ℝ)|=(935799541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1378_s2_7 (p : ℝ) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312042821/10000000000 : ℝ)*x 0 + (4613347593/10000000000 : ℝ)*x 1 + (4029133247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312042821/10000000000 : ℝ)^2169 ≤ (6650173773051/20000000000000 : ℝ)^1657 := by
    have hnat : (4312042821 : ℕ)^2169*20000000000000^1657 ≤ 6650173773051^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312042821 10000000000 6650173773051 20000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4613347593/10000000000 : ℝ)^2169 ≤ (3632451402317/10000000000000 : ℝ)^1657 := by
    have hnat : (4613347593 : ℕ)^2169*10000000000000^1657 ≤ 3632451402317^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4613347593 10000000000 3632451402317 10000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029133247/10000000000 : ℝ)^2169 ≤ (15212308546493/50000000000000 : ℝ)^1657 := by
    have hnat : (4029133247 : ℕ)^2169*50000000000000^1657 ≤ 15212308546493^1657*10000000000^2169 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029133247 10000000000 15212308546493 50000000000000 2169 1657 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2169/512 : ℝ)) 2169 1657 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312042821/10000000000 : ℝ), (4613347593/10000000000 : ℝ), (4029133247/10000000000 : ℝ)] ![(6650173773051/20000000000000 : ℝ), (3632451402317/10000000000000 : ℝ), (15212308546493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312042821/10000000000 : ℝ)|^2169 ≤ (6650173773051/20000000000000 : ℝ)^1657
        have hw : |(4312042821/10000000000 : ℝ)|=(4312042821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4613347593/10000000000 : ℝ)|^2169 ≤ (3632451402317/10000000000000 : ℝ)^1657
        have hw : |(4613347593/10000000000 : ℝ)|=(4613347593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029133247/10000000000 : ℝ)|^2169 ≤ (15212308546493/50000000000000 : ℝ)^1657
        have hw : |(4029133247/10000000000 : ℝ)|=(4029133247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1378_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9599/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5039/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15969/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9599/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (451/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9599/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (451/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9599/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (451/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9599/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (451/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9599/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (451/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9599/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (451/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (451/6250 : ℝ) ^ (4337/1024 : ℝ) ≤ (1460442293214733/100000000000000000000 : ℝ) := by
    have hpowers : (451/6250 : ℝ)^4337 ≤ (1460442293214733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (451 : ℕ)^4337*100000000000000000000^1024 ≤ 1460442293214733^1024*6250^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        451 6250 1460442293214733 100000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (451/6250 : ℝ)) (X := (1460442293214733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9599/50000 : ℝ) ^ (4337/1024 : ℝ) ≤ (46058217933151837/50000000000000000000 : ℝ) := by
    have hpowers : (9599/50000 : ℝ)^4337 ≤ (46058217933151837/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9599 : ℕ)^4337*50000000000000000000^1024 ≤ 46058217933151837^1024*50000^4337 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9599 50000 46058217933151837 50000000000000000000 4337 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9599/50000 : ℝ)) (X := (46058217933151837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001460442293214733/50000000000000000000 : ℝ) ≤ (2500017240906439/2500000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (50001460442293214733/50000000000000000000 : ℝ)^1024 ≤ (2500017240906439/2500000000000000 : ℝ)^4337 := by
      have hnat : (50001460442293214733 : ℕ)^1024*2500000000000000^4337 ≤ 2500017240906439^4337*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001460442293214733 50000000000000000000 2500017240906439 2500000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500017240906439/2500000000000000 : ℝ)) (X := (50001460442293214733/50000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100093576878159518407/100000000000000000000 : ℝ) ≤ (2500552158714329/2500000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (100093576878159518407/100000000000000000000 : ℝ)^1024 ≤ (2500552158714329/2500000000000000 : ℝ)^4337 := by
      have hnat : (100093576878159518407 : ℕ)^1024*2500000000000000^4337 ≤ 2500552158714329^4337*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100093576878159518407 100000000000000000000 2500552158714329 2500000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500552158714329/2500000000000000 : ℝ)) (X := (100093576878159518407/100000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25046058217933151837/25000000000000000000 : ℝ) ≤ (2501087076522219/2500000000000000 : ℝ) ^ (4337/1024 : ℝ) := by
    have hpowers : (25046058217933151837/25000000000000000000 : ℝ)^1024 ≤ (2501087076522219/2500000000000000 : ℝ)^4337 := by
      have hnat : (25046058217933151837 : ℕ)^1024*2500000000000000^4337 ≤ 2501087076522219^4337*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25046058217933151837 25000000000000000000 2501087076522219 2500000000000000 1024 4337 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501087076522219/2500000000000000 : ℝ)) (X := (25046058217933151837/25000000000000000000 : ℝ)) (by norm_num) 4337 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1460442293214733/100000000000000000000 : ℝ) ≤ ((14973743323368741809/14977500000000000000 : ℝ)+2*(53491780789/29955000000000 : ℝ)*(451/6250 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (14973743323368741809/14977500000000000000 : ℝ)+2*(53491780789/29955000000000 : ℝ)*(451/6250 : ℝ)=(2500017240906439/2500000000000000 : ℝ) by norm_num, show 1+2*(1460442293214733/100000000000000000000 : ℝ)=(50001460442293214733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46058217933151837/50000000000000000000 : ℝ)+(1460442293214733/100000000000000000000 : ℝ) ≤ ((14973743323368741809/14977500000000000000 : ℝ)+(53491780789/29955000000000 : ℝ)*((9599/50000 : ℝ)+(451/6250 : ℝ)))^(4337/1024 : ℝ) := by
    rw [show (14973743323368741809/14977500000000000000 : ℝ)+(53491780789/29955000000000 : ℝ)*((9599/50000 : ℝ)+(451/6250 : ℝ))=(2500552158714329/2500000000000000 : ℝ) by norm_num, show 1+(46058217933151837/50000000000000000000 : ℝ)+(1460442293214733/100000000000000000000 : ℝ)=(100093576878159518407/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46058217933151837/50000000000000000000 : ℝ) ≤ ((14973743323368741809/14977500000000000000 : ℝ)+2*(53491780789/29955000000000 : ℝ)*(9599/50000 : ℝ))^(4337/1024 : ℝ) := by
    rw [show (14973743323368741809/14977500000000000000 : ℝ)+2*(53491780789/29955000000000 : ℝ)*(9599/50000 : ℝ)=(2501087076522219/2500000000000000 : ℝ) by norm_num, show 1+2*(46058217933151837/50000000000000000000 : ℝ)=(25046058217933151837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14973743323368741809/14977500000000000000 : ℝ)*(X 1 0+X 2 0)+(53491780789/29955000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (451/6250 : ℝ)) (hi := (9599/50000 : ℝ)) (c := (14973743323368741809/14977500000000000000 : ℝ)) (alpha := (53491780789/29955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14973743323368741809/14977500000000000000 : ℝ)*(X 0 1+X 2 1)+(53491780789/29955000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (451/6250 : ℝ)) (hi := (9599/50000 : ℝ)) (c := (14973743323368741809/14977500000000000000 : ℝ)) (alpha := (53491780789/29955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14973743323368741809/14977500000000000000 : ℝ)*(X 0 2+X 1 2)+(53491780789/29955000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4337/1024 : ℝ)) (lo := (451/6250 : ℝ)) (hi := (9599/50000 : ℝ)) (c := (14973743323368741809/14977500000000000000 : ℝ)) (alpha := (53491780789/29955000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100240193/500000000 : ℝ)*X 0 0+(5470297553/10000000000 : ℝ)*X 0 1+(519173687/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681737139/5000000000 : ℝ)*X 1 0+(-537116621/2500000000 : ℝ)*X 1 1+(5191736913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681737099/5000000000 : ℝ)*X 2 0+(5191736983/10000000000 : ℝ)*X 2 1+(-1074233249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538990249/1250000000 : ℝ)*X 0 0+(1006384121/2500000000 : ℝ)*X 0 1+(4616914409/10000000000 : ℝ)*X 0 2+(538990249/1250000000 : ℝ)*X 1 0+(1006384121/2500000000 : ℝ)*X 1 1+(4616914409/10000000000 : ℝ)*X 1 2+(538990249/1250000000 : ℝ)*X 2 0+(1006384121/2500000000 : ℝ)*X 2 1+(4616914409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-125303749/625000000 : ℝ)*X 0 0+(5193417301/10000000000 : ℝ)*X 0 1+(5468602721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132285041/250000000 : ℝ)*X 1 0+(-187160127/1000000000 : ℝ)*X 1 1+(5468602419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291403127/10000000000 : ℝ)*X 2 0+(5468602519/10000000000 : ℝ)*X 2 1+(-935799541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312042821/10000000000 : ℝ)*X 0 0+(4613347593/10000000000 : ℝ)*X 0 1+(4029133247/10000000000 : ℝ)*X 0 2+(4312042821/10000000000 : ℝ)*X 1 0+(4613347593/10000000000 : ℝ)*X 1 1+(4029133247/10000000000 : ℝ)*X 1 2+(4312042821/10000000000 : ℝ)*X 2 0+(4613347593/10000000000 : ℝ)*X 2 1+(4029133247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1378_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171247615401439138720024353/31203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (925932343/100000000000000 : ℝ)*(base19) + (99425749/12500000000000 : ℝ)*(base23) + (5161029/12500000000000 : ℝ)*(lower2) + (76877197/50000000000000 : ℝ)*(upper3) + (13988713/20000000000000 : ℝ)*(upper5) + (165027585724479/6250000000000 : ℝ)*(major0) + (165027585724479/6250000000000 : ℝ)*(major1) + (165027585724479/6250000000000 : ℝ)*(major2) + (358989467339151/10000000000000 : ℝ)*(sp0) + (3589904832063131/100000000000000 : ℝ)*(sp1) + (1794952481294741/50000000000000 : ℝ)*(sp2) + (1690970966930703/100000000000000 : ℝ)*(sp3) + (2216920793/20000000000000 : ℝ)*(sp4) + (5835318617/100000000000000 : ℝ)*(sp7) + (42274420056233/2500000000000 : ℝ)*(f.failure) + (1794952878997737/50000000000000 : ℝ)*(f.sum) + (3453532294153/1997000000000000000000000000 : ℝ)*base66 + (35270060088618337/31203125000000000000000000000000 : ℝ)*base67 + (1396391859683019/15601562500000000000000000000000 : ℝ)*base70 + (58364738655004481/15601562500000000000000000000000 : ℝ)*base71 + (989588529943/399400000000000000000000000 : ℝ)*base73 + (5342772739012839/3900390625000000000000000000000 : ℝ)*base75 + (5306078059133509/975097656250000000000000000000 : ℝ)*base78 + (61037963606285731/15601562500000000000000000000000 : ℝ)*base79 + (869085717401/998500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (40753/125000000000000000000 : ℝ)*base89 + (40753/125000000000000000000 : ℝ)*base91 + (40753/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1064474193478451959911/124812500000000000000000000 : ℝ) := by norm_num
    linear_combination (1571605789/100000000000000 : ℝ)*(base19) + (965349709/25000000000000 : ℝ)*(base23) + (22307439/6250000000000 : ℝ)*(upper3) + (69810379/20000000000000 : ℝ)*(lower4) + (21093291/20000000000000 : ℝ)*(upper5) + (2672807568488651/100000000000000 : ℝ)*(major0) + (2672807568488651/100000000000000 : ℝ)*(major1) + (2672807568488651/100000000000000 : ℝ)*(major2) + (8866902803/100000000000000 : ℝ)*(sp1) + (53574033593/100000000000000 : ℝ)*(sp2) + (908477567584253/25000000000000 : ℝ)*(sp4) + (3633899831828421/100000000000000 : ℝ)*(sp5) + (3633852834904583/100000000000000 : ℝ)*(sp6) + (1711704582354071/100000000000000 : ℝ)*(sp7) + (1711704582354071/100000000000000 : ℝ)*(f.failure) + (908477567584253/25000000000000 : ℝ)*(f.sum) + (29554928877097/5991000000000000000000000000 : ℝ)*base66 + (2297837912743959659/1497750000000000000000000000000000 : ℝ)*base67 + (7004873042310459659/1497750000000000000000000000000000 : ℝ)*base69 + (11125656971693540341/1497750000000000000000000000000000 : ℝ)*base72 + (3325276523483/1198200000000000000000000000 : ℝ)*base74 + (2239619831053959659/1497750000000000000000000000000000 : ℝ)*base75 + (1508533499436290341/1497750000000000000000000000000000 : ℝ)*base78 + (15314908106017040341/1497750000000000000000000000000000 : ℝ)*base80 + (11711885253691/5991000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7399311/5000000000000000000000 : ℝ)*base89 + (7399311/5000000000000000000000 : ℝ)*base91 + (7399311/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1378_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9599/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1378_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1378_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1378_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1378_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1378_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4337/1024 : ℝ) ≤ p) (hpb : p ≤ (2169/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78074441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5039/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15969/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1378_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

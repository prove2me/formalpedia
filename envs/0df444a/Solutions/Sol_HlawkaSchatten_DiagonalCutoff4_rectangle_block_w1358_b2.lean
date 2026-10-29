-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:10:30.207309+00:00
-- url     : https://prove2.me/submissions/89acbaaf-4c4d-459f-b438-91c40764888d

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
theorem support_rectangle_w1358_s6_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015113297/5000000000 : ℝ)*x 0 + (2705946083/5000000000 : ℝ)*x 1 + (5245077193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015113297/5000000000 : ℝ)^2159 ≤ (12367504866053/100000000000000 : ℝ)^1647 := by
    have hnat : (1015113297 : ℕ)^2159*100000000000000^1647 ≤ 12367504866053^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015113297 5000000000 12367504866053 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705946083/5000000000 : ℝ)^2159 ≤ (44715269013557/100000000000000 : ℝ)^1647 := by
    have hnat : (2705946083 : ℕ)^2159*100000000000000^1647 ≤ 44715269013557^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705946083 5000000000 44715269013557 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245077193/10000000000 : ℝ)^2159 ≤ (268232663153/625000000000 : ℝ)^1647 := by
    have hnat : (5245077193 : ℕ)^2159*625000000000^1647 ≤ 268232663153^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245077193 10000000000 268232663153 625000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015113297/5000000000 : ℝ), (2705946083/5000000000 : ℝ), (5245077193/10000000000 : ℝ)] ![(12367504866053/100000000000000 : ℝ), (44715269013557/100000000000000 : ℝ), (268232663153/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015113297/5000000000 : ℝ)|^2159 ≤ (12367504866053/100000000000000 : ℝ)^1647
        have hw : |(-1015113297/5000000000 : ℝ)|=(1015113297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705946083/5000000000 : ℝ)|^2159 ≤ (44715269013557/100000000000000 : ℝ)^1647
        have hw : |(2705946083/5000000000 : ℝ)|=(2705946083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245077193/10000000000 : ℝ)|^2159 ≤ (268232663153/625000000000 : ℝ)^1647
        have hw : |(5245077193/10000000000 : ℝ)|=(5245077193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348718857/10000000000 : ℝ)*x 0 + (-2115207621/10000000000 : ℝ)*x 1 + (2622538601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348718857/10000000000 : ℝ)^2159 ≤ (44032288112347/100000000000000 : ℝ)^1647 := by
    have hnat : (5348718857 : ℕ)^2159*100000000000000^1647 ≤ 44032288112347^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348718857 10000000000 44032288112347 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115207621/10000000000 : ℝ)^2159 ≤ (1631310709297/12500000000000 : ℝ)^1647 := by
    have hnat : (2115207621 : ℕ)^2159*12500000000000^1647 ≤ 1631310709297^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115207621 10000000000 1631310709297 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622538601/5000000000 : ℝ)^2159 ≤ (21458613100507/50000000000000 : ℝ)^1647 := by
    have hnat : (2622538601 : ℕ)^2159*50000000000000^1647 ≤ 21458613100507^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622538601 5000000000 21458613100507 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348718857/10000000000 : ℝ), (-2115207621/10000000000 : ℝ), (2622538601/5000000000 : ℝ)] ![(44032288112347/100000000000000 : ℝ), (1631310709297/12500000000000 : ℝ), (21458613100507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348718857/10000000000 : ℝ)|^2159 ≤ (44032288112347/100000000000000 : ℝ)^1647
        have hw : |(5348718857/10000000000 : ℝ)|=(5348718857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115207621/10000000000 : ℝ)|^2159 ≤ (1631310709297/12500000000000 : ℝ)^1647
        have hw : |(-2115207621/10000000000 : ℝ)|=(2115207621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622538601/5000000000 : ℝ)|^2159 ≤ (21458613100507/50000000000000 : ℝ)^1647
        have hw : |(2622538601/5000000000 : ℝ)|=(2622538601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348718857/10000000000 : ℝ)*x 0 + (2622538597/5000000000 : ℝ)*x 1 + (-2115207631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348718857/10000000000 : ℝ)^2159 ≤ (44032288112347/100000000000000 : ℝ)^1647 := by
    have hnat : (5348718857 : ℕ)^2159*100000000000000^1647 ≤ 44032288112347^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348718857 10000000000 44032288112347 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622538597/5000000000 : ℝ)^2159 ≤ (21458613057603/50000000000000 : ℝ)^1647 := by
    have hnat : (2622538597 : ℕ)^2159*50000000000000^1647 ≤ 21458613057603^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622538597 5000000000 21458613057603 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115207631/10000000000 : ℝ)^2159 ≤ (6525242877627/50000000000000 : ℝ)^1647 := by
    have hnat : (2115207631 : ℕ)^2159*50000000000000^1647 ≤ 6525242877627^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115207631 10000000000 6525242877627 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348718857/10000000000 : ℝ), (2622538597/5000000000 : ℝ), (-2115207631/10000000000 : ℝ)] ![(44032288112347/100000000000000 : ℝ), (21458613057603/50000000000000 : ℝ), (6525242877627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348718857/10000000000 : ℝ)|^2159 ≤ (44032288112347/100000000000000 : ℝ)^1647
        have hw : |(5348718857/10000000000 : ℝ)|=(5348718857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622538597/5000000000 : ℝ)|^2159 ≤ (21458613057603/50000000000000 : ℝ)^1647
        have hw : |(2622538597/5000000000 : ℝ)|=(2622538597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115207631/10000000000 : ℝ)|^2159 ≤ (6525242877627/50000000000000 : ℝ)^1647
        have hw : |(-2115207631/10000000000 : ℝ)|=(2115207631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322451891/10000000000 : ℝ)*x 0 + (1037503089/2500000000 : ℝ)*x 1 + (900304587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322451891/10000000000 : ℝ)^2159 ≤ (16651764078599/50000000000000 : ℝ)^1647 := by
    have hnat : (4322451891 : ℕ)^2159*50000000000000^1647 ≤ 16651764078599^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322451891 10000000000 16651764078599 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037503089/2500000000 : ℝ)^2159 ≤ (6314559639693/20000000000000 : ℝ)^1647 := by
    have hnat : (1037503089 : ℕ)^2159*20000000000000^1647 ≤ 6314559639693^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037503089 2500000000 6314559639693 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900304587/2000000000 : ℝ)^2159 ≤ (35123673628689/100000000000000 : ℝ)^1647 := by
    have hnat : (900304587 : ℕ)^2159*100000000000000^1647 ≤ 35123673628689^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900304587 2000000000 35123673628689 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322451891/10000000000 : ℝ), (1037503089/2500000000 : ℝ), (900304587/2000000000 : ℝ)] ![(16651764078599/50000000000000 : ℝ), (6314559639693/20000000000000 : ℝ), (35123673628689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322451891/10000000000 : ℝ)|^2159 ≤ (16651764078599/50000000000000 : ℝ)^1647
        have hw : |(4322451891/10000000000 : ℝ)|=(4322451891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037503089/2500000000 : ℝ)|^2159 ≤ (6314559639693/20000000000000 : ℝ)^1647
        have hw : |(1037503089/2500000000 : ℝ)|=(1037503089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900304587/2000000000 : ℝ)|^2159 ≤ (35123673628689/100000000000000 : ℝ)^1647
        have hw : |(900304587/2000000000 : ℝ)|=(900304587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030238639/10000000000 : ℝ)*x 0 + (2622837629/5000000000 : ℝ)*x 1 + (5411290993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030238639/10000000000 : ℝ)^2159 ≤ (12367601050273/100000000000000 : ℝ)^1647 := by
    have hnat : (2030238639 : ℕ)^2159*100000000000000^1647 ≤ 12367601050273^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030238639 10000000000 12367601050273 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622837629/5000000000 : ℝ)^2159 ≤ (8584728215657/20000000000000 : ℝ)^1647 := by
    have hnat : (2622837629 : ℕ)^2159*20000000000000^1647 ≤ 8584728215657^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622837629 5000000000 8584728215657 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411290993/10000000000 : ℝ)^2159 ≤ (5588594732899/12500000000000 : ℝ)^1647 := by
    have hnat : (5411290993 : ℕ)^2159*12500000000000^1647 ≤ 5588594732899^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411290993 10000000000 5588594732899 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030238639/10000000000 : ℝ), (2622837629/5000000000 : ℝ), (5411290993/10000000000 : ℝ)] ![(12367601050273/100000000000000 : ℝ), (8584728215657/20000000000000 : ℝ), (5588594732899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030238639/10000000000 : ℝ)|^2159 ≤ (12367601050273/100000000000000 : ℝ)^1647
        have hw : |(-2030238639/10000000000 : ℝ)|=(2030238639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622837629/5000000000 : ℝ)|^2159 ≤ (8584728215657/20000000000000 : ℝ)^1647
        have hw : |(2622837629/5000000000 : ℝ)|=(2622837629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411290993/10000000000 : ℝ)|^2159 ≤ (5588594732899/12500000000000 : ℝ)^1647
        have hw : |(5411290993/10000000000 : ℝ)|=(5411290993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305672867/10000000000 : ℝ)*x 0 + (-1948993799/10000000000 : ℝ)*x 1 + (270564553/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305672867/10000000000 : ℝ)^2159 ≤ (2178417042827/5000000000000 : ℝ)^1647 := by
    have hnat : (5305672867 : ℕ)^2159*5000000000000^1647 ≤ 2178417042827^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305672867 10000000000 2178417042827 5000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948993799/10000000000 : ℝ)^2159 ≤ (5861450270823/50000000000000 : ℝ)^1647 := by
    have hnat : (1948993799 : ℕ)^2159*50000000000000^1647 ≤ 5861450270823^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948993799 10000000000 5861450270823 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270564553/500000000 : ℝ)^2159 ≤ (44708758588839/100000000000000 : ℝ)^1647 := by
    have hnat : (270564553 : ℕ)^2159*100000000000000^1647 ≤ 44708758588839^1647*500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270564553 500000000 44708758588839 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305672867/10000000000 : ℝ), (-1948993799/10000000000 : ℝ), (270564553/500000000 : ℝ)] ![(2178417042827/5000000000000 : ℝ), (5861450270823/50000000000000 : ℝ), (44708758588839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305672867/10000000000 : ℝ)|^2159 ≤ (2178417042827/5000000000000 : ℝ)^1647
        have hw : |(5305672867/10000000000 : ℝ)|=(5305672867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948993799/10000000000 : ℝ)|^2159 ≤ (5861450270823/50000000000000 : ℝ)^1647
        have hw : |(-1948993799/10000000000 : ℝ)|=(1948993799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270564553/500000000 : ℝ)|^2159 ≤ (44708758588839/100000000000000 : ℝ)^1647
        have hw : |(270564553/500000000 : ℝ)|=(270564553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305672921/10000000000 : ℝ)*x 0 + (5411290997/10000000000 : ℝ)*x 1 + (-487248453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305672921/10000000000 : ℝ)^2159 ≤ (21784170718909/50000000000000 : ℝ)^1647 := by
    have hnat : (5305672921 : ℕ)^2159*50000000000000^1647 ≤ 21784170718909^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305672921 10000000000 21784170718909 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411290997/10000000000 : ℝ)^2159 ≤ (22354378953257/50000000000000 : ℝ)^1647 := by
    have hnat : (5411290997 : ℕ)^2159*50000000000000^1647 ≤ 22354378953257^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411290997 10000000000 22354378953257 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487248453/2500000000 : ℝ)^2159 ≤ (11722900644147/100000000000000 : ℝ)^1647 := by
    have hnat : (487248453 : ℕ)^2159*100000000000000^1647 ≤ 11722900644147^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487248453 2500000000 11722900644147 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305672921/10000000000 : ℝ), (5411290997/10000000000 : ℝ), (-487248453/2500000000 : ℝ)] ![(21784170718909/50000000000000 : ℝ), (22354378953257/50000000000000 : ℝ), (11722900644147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305672921/10000000000 : ℝ)|^2159 ≤ (21784170718909/50000000000000 : ℝ)^1647
        have hw : |(5305672921/10000000000 : ℝ)|=(5305672921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411290997/10000000000 : ℝ)|^2159 ≤ (22354378953257/50000000000000 : ℝ)^1647
        have hw : |(5411290997/10000000000 : ℝ)|=(5411290997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487248453/2500000000 : ℝ)|^2159 ≤ (11722900644147/100000000000000 : ℝ)^1647
        have hw : |(-487248453/2500000000 : ℝ)|=(487248453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s6_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322477191/10000000000 : ℝ)*x 0 + (1125065661/2500000000 : ℝ)*x 1 + (4151279167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322477191/10000000000 : ℝ)^2159 ≤ (4162972960763/12500000000000 : ℝ)^1647 := by
    have hnat : (4322477191 : ℕ)^2159*12500000000000^1647 ≤ 4162972960763^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322477191 10000000000 4162972960763 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125065661/2500000000 : ℝ)^2159 ≤ (7022156734489/20000000000000 : ℝ)^1647 := by
    have hnat : (1125065661 : ℕ)^2159*20000000000000^1647 ≤ 7022156734489^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125065661 2500000000 7022156734489 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151279167/10000000000 : ℝ)^2159 ≤ (31585432614019/100000000000000 : ℝ)^1647 := by
    have hnat : (4151279167 : ℕ)^2159*100000000000000^1647 ≤ 31585432614019^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151279167 10000000000 31585432614019 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322477191/10000000000 : ℝ), (1125065661/2500000000 : ℝ), (4151279167/10000000000 : ℝ)] ![(4162972960763/12500000000000 : ℝ), (7022156734489/20000000000000 : ℝ), (31585432614019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322477191/10000000000 : ℝ)|^2159 ≤ (4162972960763/12500000000000 : ℝ)^1647
        have hw : |(4322477191/10000000000 : ℝ)|=(4322477191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125065661/2500000000 : ℝ)|^2159 ≤ (7022156734489/20000000000000 : ℝ)^1647
        have hw : |(1125065661/2500000000 : ℝ)|=(1125065661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151279167/10000000000 : ℝ)|^2159 ≤ (31585432614019/100000000000000 : ℝ)^1647
        have hw : |(4151279167/10000000000 : ℝ)|=(4151279167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11179/100000 : ℝ) ^ (4317/1024 : ℝ) ≤ (2433200303186973/25000000000000000000 : ℝ) := by
    have hpowers : (11179/100000 : ℝ)^4317 ≤ (2433200303186973/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11179 : ℕ)^4317*25000000000000000000^1024 ≤ 2433200303186973^1024*100000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11179 100000 2433200303186973 25000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11179/100000 : ℝ)) (X := (2433200303186973/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (4317/1024 : ℝ) ≤ (15542336573569757/50000000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^4317 ≤ (15542336573569757/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3681 : ℕ)^4317*50000000000000000000^1024 ≤ 15542336573569757^1024*25000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 15542336573569757 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (15542336573569757/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502433200303186973/12500000000000000000 : ℝ) ≤ (10000461693240931/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (12502433200303186973/12500000000000000000 : ℝ)^1024 ≤ (10000461693240931/10000000000000000 : ℝ)^4317 := by
      have hnat : (12502433200303186973 : ℕ)^1024*10000000000000000^4317 ≤ 10000461693240931^4317*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502433200303186973 12500000000000000000 10000461693240931 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000461693240931/10000000000000000 : ℝ)) (X := (12502433200303186973/12500000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020408737179943703/50000000000000000000 : ℝ) ≤ (10000968046987217/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50020408737179943703/50000000000000000000 : ℝ)^1024 ≤ (10000968046987217/10000000000000000 : ℝ)^4317 := by
      have hnat : (50020408737179943703 : ℕ)^1024*10000000000000000^4317 ≤ 10000968046987217^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020408737179943703 50000000000000000000 10000968046987217 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000968046987217/10000000000000000 : ℝ)) (X := (50020408737179943703/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015542336573569757/25000000000000000000 : ℝ) ≤ (10001474400733503/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25015542336573569757/25000000000000000000 : ℝ)^1024 ≤ (10001474400733503/10000000000000000 : ℝ)^4317 := by
      have hnat : (25015542336573569757 : ℕ)^1024*10000000000000000^4317 ≤ 10001474400733503^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015542336573569757 25000000000000000000 10001474400733503 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001474400733503/10000000000000000 : ℝ)) (X := (25015542336573569757/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2433200303186973/25000000000000000000 : ℝ) ≤ ((35440315645479638007/35450000000000000000 : ℝ)+2*(253176873143/177250000000000 : ℝ)*(11179/100000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (35440315645479638007/35450000000000000000 : ℝ)+2*(253176873143/177250000000000 : ℝ)*(11179/100000 : ℝ)=(10000461693240931/10000000000000000 : ℝ) by norm_num, show 1+2*(2433200303186973/25000000000000000000 : ℝ)=(12502433200303186973/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15542336573569757/50000000000000000000 : ℝ)+(2433200303186973/25000000000000000000 : ℝ) ≤ ((35440315645479638007/35450000000000000000 : ℝ)+(253176873143/177250000000000 : ℝ)*((3681/25000 : ℝ)+(11179/100000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (35440315645479638007/35450000000000000000 : ℝ)+(253176873143/177250000000000 : ℝ)*((3681/25000 : ℝ)+(11179/100000 : ℝ))=(10000968046987217/10000000000000000 : ℝ) by norm_num, show 1+(15542336573569757/50000000000000000000 : ℝ)+(2433200303186973/25000000000000000000 : ℝ)=(50020408737179943703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15542336573569757/50000000000000000000 : ℝ) ≤ ((35440315645479638007/35450000000000000000 : ℝ)+2*(253176873143/177250000000000 : ℝ)*(3681/25000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (35440315645479638007/35450000000000000000 : ℝ)+2*(253176873143/177250000000000 : ℝ)*(3681/25000 : ℝ)=(10001474400733503/10000000000000000 : ℝ) by norm_num, show 1+2*(15542336573569757/50000000000000000000 : ℝ)=(25015542336573569757/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35440315645479638007/35450000000000000000 : ℝ)*(X 1 0+X 2 0)+(253176873143/177250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (35440315645479638007/35450000000000000000 : ℝ)) (alpha := (253176873143/177250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35440315645479638007/35450000000000000000 : ℝ)*(X 0 1+X 2 1)+(253176873143/177250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (35440315645479638007/35450000000000000000 : ℝ)) (alpha := (253176873143/177250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35440315645479638007/35450000000000000000 : ℝ)*(X 0 2+X 1 2)+(253176873143/177250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (35440315645479638007/35450000000000000000 : ℝ)) (alpha := (253176873143/177250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1015113297/5000000000 : ℝ)*X 0 0+(2705946083/5000000000 : ℝ)*X 0 1+(5245077193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348718857/10000000000 : ℝ)*X 1 0+(-2115207621/10000000000 : ℝ)*X 1 1+(2622538601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348718857/10000000000 : ℝ)*X 2 0+(2622538597/5000000000 : ℝ)*X 2 1+(-2115207631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322451891/10000000000 : ℝ)*X 0 0+(1037503089/2500000000 : ℝ)*X 0 1+(900304587/2000000000 : ℝ)*X 0 2+(4322451891/10000000000 : ℝ)*X 1 0+(1037503089/2500000000 : ℝ)*X 1 1+(900304587/2000000000 : ℝ)*X 1 2+(4322451891/10000000000 : ℝ)*X 2 0+(1037503089/2500000000 : ℝ)*X 2 1+(900304587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2030238639/10000000000 : ℝ)*X 0 0+(2622837629/5000000000 : ℝ)*X 0 1+(5411290993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305672867/10000000000 : ℝ)*X 1 0+(-1948993799/10000000000 : ℝ)*X 1 1+(270564553/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305672921/10000000000 : ℝ)*X 2 0+(5411290997/10000000000 : ℝ)*X 2 1+(-487248453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322477191/10000000000 : ℝ)*X 0 0+(1125065661/2500000000 : ℝ)*X 0 1+(4151279167/10000000000 : ℝ)*X 0 2+(4322477191/10000000000 : ℝ)*X 1 0+(1125065661/2500000000 : ℝ)*X 1 1+(4151279167/10000000000 : ℝ)*X 1 2+(4322477191/10000000000 : ℝ)*X 2 0+(1125065661/2500000000 : ℝ)*X 2 1+(4151279167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1807564343734458253669469739/443125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (388779733/50000000000000 : ℝ)*(base19) + (141606891/20000000000000 : ℝ)*(base23) + (1487479/4000000000000 : ℝ)*(lower2) + (113168993/100000000000000 : ℝ)*(upper3) + (49378577/100000000000000 : ℝ)*(upper5) + (2209894771142559/50000000000000 : ℝ)*(major0) + (2209894771142559/50000000000000 : ℝ)*(major1) + (2209894771142559/50000000000000 : ℝ)*(major2) + (2997341459968083/50000000000000 : ℝ)*(sp0) + (5994697902184811/100000000000000 : ℝ)*(sp1) + (2997348985854911/50000000000000 : ℝ)*(sp2) + (2844871787143849/100000000000000 : ℝ)*(sp3) + (15759808111/100000000000000 : ℝ)*(sp4) + (1696342223/20000000000000 : ℝ)*(sp7) + (711220067213741/25000000000000 : ℝ)*(f.failure) + (5994698679744277/100000000000000 : ℝ)*(f.sum) + (53392103071227/17725000000000000000000000000 : ℝ)*base66 + (8475016038505960087/1772500000000000000000000000000000 : ℝ)*base68 + (14733970166373460087/1772500000000000000000000000000000 : ℝ)*base70 + (20605559285198460087/1772500000000000000000000000000000 : ℝ)*base72 + (108056151917823/17725000000000000000000000000 : ℝ)*base73 + (8355934780745960087/1772500000000000000000000000000000 : ℝ)*base76 + (1783185237944039913/1772500000000000000000000000000000 : ℝ)*base77 + (15320599409170960087/1772500000000000000000000000000000 : ℝ)*base80 + (38688072634651/8862500000000000000000000000 : ℝ)*base82 + (1108851/1250000000000000000000 : ℝ)*base89 + (1108851/1250000000000000000000 : ℝ)*base91 + (1108851/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1871225736523226265581494581/886250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185125747/50000000000000 : ℝ)*(base19) + (426560447/100000000000000 : ℝ)*(base23) + (7478441/20000000000000 : ℝ)*(upper3) + (702867/100000000000000 : ℝ)*(lower4) + (57743629/100000000000000 : ℝ)*(upper5) + (2225884978357787/50000000000000 : ℝ)*(major0) + (2225884978357787/50000000000000 : ℝ)*(major1) + (2225884978357787/50000000000000 : ℝ)*(major2) + (2081180623/20000000000000 : ℝ)*(sp1) + (9608447147/100000000000000 : ℝ)*(sp2) + (3019037390918117/50000000000000 : ℝ)*(sp4) + (48304512045453/800000000000 : ℝ)*(sp5) + (6038064746828639/100000000000000 : ℝ)*(sp6) + (2865465061215003/100000000000000 : ℝ)*(sp7) + (2865465061215003/100000000000000 : ℝ)*(f.failure) + (3019037390918117/50000000000000 : ℝ)*(f.sum) + (51498741050089/17725000000000000000000000000 : ℝ)*base65 + (5271235898842189491/1772500000000000000000000000000000 : ℝ)*base68 + (7528933949669689491/1772500000000000000000000000000000 : ℝ)*base70 + (17714289942819689491/1772500000000000000000000000000000 : ℝ)*base72 + (29764844358107/8862500000000000000000000000 : ℝ)*base73 + (4393055961949689491/1772500000000000000000000000000000 : ℝ)*base76 + (9379688420849689491/1772500000000000000000000000000000 : ℝ)*base78 + (2621047479744689491/1772500000000000000000000000000000 : ℝ)*base80 + (4709420444129/1107812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (41904133/5000000000000000000000 : ℝ)*base89 + (41904133/5000000000000000000000 : ℝ)*base91 + (41904133/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1358_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_s7_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015116027/5000000000 : ℝ)*x 0 + (1352958943/2500000000 : ℝ)*x 1 + (5245130073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015116027/5000000000 : ℝ)^2159 ≤ (247350969327/2000000000000 : ℝ)^1647 := by
    have hnat : (1015116027 : ℕ)^2159*2000000000000^1647 ≤ 247350969327^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015116027 5000000000 247350969327 2000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352958943/2500000000 : ℝ)^2159 ≤ (4471465821507/10000000000000 : ℝ)^1647 := by
    have hnat : (1352958943 : ℕ)^2159*10000000000000^1647 ≤ 4471465821507^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352958943 2500000000 4471465821507 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245130073/10000000000 : ℝ)^2159 ≤ (1341181040549/3125000000000 : ℝ)^1647 := by
    have hnat : (5245130073 : ℕ)^2159*3125000000000^1647 ≤ 1341181040549^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245130073 10000000000 1341181040549 3125000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015116027/5000000000 : ℝ), (1352958943/2500000000 : ℝ), (5245130073/10000000000 : ℝ)] ![(247350969327/2000000000000 : ℝ), (4471465821507/10000000000000 : ℝ), (1341181040549/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015116027/5000000000 : ℝ)|^2159 ≤ (247350969327/2000000000000 : ℝ)^1647
        have hw : |(-1015116027/5000000000 : ℝ)|=(1015116027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352958943/2500000000 : ℝ)|^2159 ≤ (4471465821507/10000000000000 : ℝ)^1647
        have hw : |(1352958943/2500000000 : ℝ)|=(1352958943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245130073/10000000000 : ℝ)|^2159 ≤ (1341181040549/3125000000000 : ℝ)^1647
        have hw : |(5245130073/10000000000 : ℝ)|=(5245130073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674352349/5000000000 : ℝ)*x 0 + (-423031279/2000000000 : ℝ)*x 1 + (5245130073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674352349/5000000000 : ℝ)^2159 ≤ (8806427063203/20000000000000 : ℝ)^1647 := by
    have hnat : (2674352349 : ℕ)^2159*20000000000000^1647 ≤ 8806427063203^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674352349 5000000000 8806427063203 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423031279/2000000000 : ℝ)^2159 ≤ (13050071368087/100000000000000 : ℝ)^1647 := by
    have hnat : (423031279 : ℕ)^2159*100000000000000^1647 ≤ 13050071368087^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423031279 2000000000 13050071368087 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245130073/10000000000 : ℝ)^2159 ≤ (1341181040549/3125000000000 : ℝ)^1647 := by
    have hnat : (5245130073 : ℕ)^2159*3125000000000^1647 ≤ 1341181040549^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245130073 10000000000 1341181040549 3125000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674352349/5000000000 : ℝ), (-423031279/2000000000 : ℝ), (5245130073/10000000000 : ℝ)] ![(8806427063203/20000000000000 : ℝ), (13050071368087/100000000000000 : ℝ), (1341181040549/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674352349/5000000000 : ℝ)|^2159 ≤ (8806427063203/20000000000000 : ℝ)^1647
        have hw : |(2674352349/5000000000 : ℝ)|=(2674352349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423031279/2000000000 : ℝ)|^2159 ≤ (13050071368087/100000000000000 : ℝ)^1647
        have hw : |(-423031279/2000000000 : ℝ)|=(423031279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245130073/10000000000 : ℝ)|^2159 ≤ (1341181040549/3125000000000 : ℝ)^1647
        have hw : |(5245130073/10000000000 : ℝ)|=(5245130073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674352349/5000000000 : ℝ)*x 0 + (2622565037/5000000000 : ℝ)*x 1 + (-423031279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674352349/5000000000 : ℝ)^2159 ≤ (8806427063203/20000000000000 : ℝ)^1647 := by
    have hnat : (2674352349 : ℕ)^2159*20000000000000^1647 ≤ 8806427063203^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674352349 5000000000 8806427063203 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622565037/5000000000 : ℝ)^2159 ≤ (8583558661659/20000000000000 : ℝ)^1647 := by
    have hnat : (2622565037 : ℕ)^2159*20000000000000^1647 ≤ 8583558661659^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622565037 5000000000 8583558661659 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423031279/2000000000 : ℝ)^2159 ≤ (13050071368087/100000000000000 : ℝ)^1647 := by
    have hnat : (423031279 : ℕ)^2159*100000000000000^1647 ≤ 13050071368087^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423031279 2000000000 13050071368087 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674352349/5000000000 : ℝ), (2622565037/5000000000 : ℝ), (-423031279/2000000000 : ℝ)] ![(8806427063203/20000000000000 : ℝ), (8583558661659/20000000000000 : ℝ), (13050071368087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674352349/5000000000 : ℝ)|^2159 ≤ (8806427063203/20000000000000 : ℝ)^1647
        have hw : |(2674352349/5000000000 : ℝ)|=(2674352349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622565037/5000000000 : ℝ)|^2159 ≤ (8583558661659/20000000000000 : ℝ)^1647
        have hw : |(2622565037/5000000000 : ℝ)|=(2622565037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423031279/2000000000 : ℝ)|^2159 ≤ (13050071368087/100000000000000 : ℝ)^1647
        have hw : |(-423031279/2000000000 : ℝ)|=(423031279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67538371/156250000 : ℝ)*x 0 + (4150127013/10000000000 : ℝ)*x 1 + (2250703667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67538371/156250000 : ℝ)^2159 ≤ (33303567072301/100000000000000 : ℝ)^1647 := by
    have hnat : (67538371 : ℕ)^2159*100000000000000^1647 ≤ 33303567072301^1647*156250000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67538371 156250000 33303567072301 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150127013/10000000000 : ℝ)^2159 ≤ (3946742708687/12500000000000 : ℝ)^1647 := by
    have hnat : (4150127013 : ℕ)^2159*12500000000000^1647 ≤ 3946742708687^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150127013 10000000000 3946742708687 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250703667/5000000000 : ℝ)^2159 ≤ (702449824849/2000000000000 : ℝ)^1647 := by
    have hnat : (2250703667 : ℕ)^2159*2000000000000^1647 ≤ 702449824849^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250703667 5000000000 702449824849 2000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67538371/156250000 : ℝ), (4150127013/10000000000 : ℝ), (2250703667/5000000000 : ℝ)] ![(33303567072301/100000000000000 : ℝ), (3946742708687/12500000000000 : ℝ), (702449824849/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67538371/156250000 : ℝ)|^2159 ≤ (33303567072301/100000000000000 : ℝ)^1647
        have hw : |(67538371/156250000 : ℝ)|=(67538371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150127013/10000000000 : ℝ)|^2159 ≤ (3946742708687/12500000000000 : ℝ)^1647
        have hw : |(4150127013/10000000000 : ℝ)|=(4150127013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250703667/5000000000 : ℝ)|^2159 ≤ (702449824849/2000000000000 : ℝ)^1647
        have hw : |(2250703667/5000000000 : ℝ)|=(2250703667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-507560993/2500000000 : ℝ)*x 0 + (5245727383/10000000000 : ℝ)*x 1 + (1352808859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507560993/2500000000 : ℝ)^2159 ≤ (12367643636501/100000000000000 : ℝ)^1647 := by
    have hnat : (507560993 : ℕ)^2159*100000000000000^1647 ≤ 12367643636501^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507560993 2500000000 12367643636501 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245727383/10000000000 : ℝ)^2159 ≤ (42924200193017/100000000000000 : ℝ)^1647 := by
    have hnat : (5245727383 : ℕ)^2159*100000000000000^1647 ≤ 42924200193017^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245727383 10000000000 42924200193017 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352808859/2500000000 : ℝ)^2159 ≤ (44708156150943/100000000000000 : ℝ)^1647 := by
    have hnat : (1352808859 : ℕ)^2159*100000000000000^1647 ≤ 44708156150943^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352808859 2500000000 44708156150943 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507560993/2500000000 : ℝ), (5245727383/10000000000 : ℝ), (1352808859/2500000000 : ℝ)] ![(12367643636501/100000000000000 : ℝ), (42924200193017/100000000000000 : ℝ), (44708156150943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507560993/2500000000 : ℝ)|^2159 ≤ (12367643636501/100000000000000 : ℝ)^1647
        have hw : |(-507560993/2500000000 : ℝ)|=(507560993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245727383/10000000000 : ℝ)|^2159 ≤ (42924200193017/100000000000000 : ℝ)^1647
        have hw : |(5245727383/10000000000 : ℝ)|=(5245727383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352808859/2500000000 : ℝ)|^2159 ≤ (44708156150943/100000000000000 : ℝ)^1647
        have hw : |(1352808859/2500000000 : ℝ)|=(1352808859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305686803/10000000000 : ℝ)*x 0 + (-487262779/2500000000 : ℝ)*x 1 + (5411235481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305686803/10000000000 : ℝ)^2159 ≤ (108921227173/250000000000 : ℝ)^1647 := by
    have hnat : (5305686803 : ℕ)^2159*250000000000^1647 ≤ 108921227173^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305686803 10000000000 108921227173 250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487262779/2500000000 : ℝ)^2159 ≤ (11723352469493/100000000000000 : ℝ)^1647 := by
    have hnat : (487262779 : ℕ)^2159*100000000000000^1647 ≤ 11723352469493^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487262779 2500000000 11723352469493 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411235481/10000000000 : ℝ)^2159 ≤ (44708156638317/100000000000000 : ℝ)^1647 := by
    have hnat : (5411235481 : ℕ)^2159*100000000000000^1647 ≤ 44708156638317^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411235481 10000000000 44708156638317 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305686803/10000000000 : ℝ), (-487262779/2500000000 : ℝ), (5411235481/10000000000 : ℝ)] ![(108921227173/250000000000 : ℝ), (11723352469493/100000000000000 : ℝ), (44708156638317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305686803/10000000000 : ℝ)|^2159 ≤ (108921227173/250000000000 : ℝ)^1647
        have hw : |(5305686803/10000000000 : ℝ)|=(5305686803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487262779/2500000000 : ℝ)|^2159 ≤ (11723352469493/100000000000000 : ℝ)^1647
        have hw : |(-487262779/2500000000 : ℝ)|=(487262779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411235481/10000000000 : ℝ)|^2159 ≤ (44708156638317/100000000000000 : ℝ)^1647
        have hw : |(5411235481/10000000000 : ℝ)|=(5411235481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305686977/10000000000 : ℝ)*x 0 + (2705617723/5000000000 : ℝ)*x 1 + (-121815683/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305686977/10000000000 : ℝ)^2159 ≤ (21784246371103/50000000000000 : ℝ)^1647 := by
    have hnat : (5305686977 : ℕ)^2159*50000000000000^1647 ≤ 21784246371103^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305686977 10000000000 21784246371103 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705617723/5000000000 : ℝ)^2159 ≤ (44708156259249/100000000000000 : ℝ)^1647 := by
    have hnat : (2705617723 : ℕ)^2159*100000000000000^1647 ≤ 44708156259249^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705617723 5000000000 44708156259249 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121815683/625000000 : ℝ)^2159 ≤ (11723350987161/100000000000000 : ℝ)^1647 := by
    have hnat : (121815683 : ℕ)^2159*100000000000000^1647 ≤ 11723350987161^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121815683 625000000 11723350987161 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305686977/10000000000 : ℝ), (2705617723/5000000000 : ℝ), (-121815683/625000000 : ℝ)] ![(21784246371103/50000000000000 : ℝ), (44708156259249/100000000000000 : ℝ), (11723350987161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305686977/10000000000 : ℝ)|^2159 ≤ (21784246371103/50000000000000 : ℝ)^1647
        have hw : |(5305686977/10000000000 : ℝ)|=(5305686977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705617723/5000000000 : ℝ)|^2159 ≤ (44708156259249/100000000000000 : ℝ)^1647
        have hw : |(2705617723/5000000000 : ℝ)|=(2705617723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121815683/625000000 : ℝ)|^2159 ≤ (11723350987161/100000000000000 : ℝ)^1647
        have hw : |(-121815683/625000000 : ℝ)|=(121815683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_s7_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322481123/10000000000 : ℝ)*x 0 + (2250074299/5000000000 : ℝ)*x 1 + (415139213/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322481123/10000000000 : ℝ)^2159 ≤ (4162977924897/12500000000000 : ℝ)^1647 := by
    have hnat : (4322481123 : ℕ)^2159*12500000000000^1647 ≤ 4162977924897^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322481123 10000000000 4162977924897 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250074299/5000000000 : ℝ)^2159 ≤ (35109617292477/100000000000000 : ℝ)^1647 := by
    have hnat : (2250074299 : ℕ)^2159*100000000000000^1647 ≤ 35109617292477^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250074299 5000000000 35109617292477 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415139213/1000000000 : ℝ)^2159 ≤ (3948319912207/12500000000000 : ℝ)^1647 := by
    have hnat : (415139213 : ℕ)^2159*12500000000000^1647 ≤ 3948319912207^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415139213 1000000000 3948319912207 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322481123/10000000000 : ℝ), (2250074299/5000000000 : ℝ), (415139213/1000000000 : ℝ)] ![(4162977924897/12500000000000 : ℝ), (35109617292477/100000000000000 : ℝ), (3948319912207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322481123/10000000000 : ℝ)|^2159 ≤ (4162977924897/12500000000000 : ℝ)^1647
        have hw : |(4322481123/10000000000 : ℝ)|=(4322481123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250074299/5000000000 : ℝ)|^2159 ≤ (35109617292477/100000000000000 : ℝ)^1647
        have hw : |(2250074299/5000000000 : ℝ)|=(2250074299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415139213/1000000000 : ℝ)|^2159 ≤ (3948319912207/12500000000000 : ℝ)^1647
        have hw : |(415139213/1000000000 : ℝ)|=(415139213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11187/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3679/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5593/50000 : ℝ) ^ (4317/1024 : ℝ) ≤ (2439630026451903/25000000000000000000 : ℝ) := by
    have hpowers : (5593/50000 : ℝ)^4317 ≤ (2439630026451903/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5593 : ℕ)^4317*25000000000000000000^1024 ≤ 2439630026451903^1024*50000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5593 50000 2439630026451903 25000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5593/50000 : ℝ)) (X := (2439630026451903/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (4317/1024 : ℝ) ≤ (15511209475244189/50000000000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^4317 ≤ (15511209475244189/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14717 : ℕ)^4317*50000000000000000000^1024 ≤ 15511209475244189^1024*100000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 15511209475244189 50000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (15511209475244189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502439630026451903/12500000000000000000 : ℝ) ≤ (10000462913172899/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (12502439630026451903/12500000000000000000 : ℝ)^1024 ≤ (10000462913172899/10000000000000000 : ℝ)^4317 := by
      have hnat : (12502439630026451903 : ℕ)^1024*10000000000000000^4317 ≤ 10000462913172899^4317*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502439630026451903 12500000000000000000 10000462913172899 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000462913172899/10000000000000000 : ℝ)) (X := (12502439630026451903/12500000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004078093905629599/10000000000000000000 : ℝ) ≤ (5000483590316497/5000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (10004078093905629599/10000000000000000000 : ℝ)^1024 ≤ (5000483590316497/5000000000000000 : ℝ)^4317 := by
      have hnat : (10004078093905629599 : ℕ)^1024*5000000000000000^4317 ≤ 5000483590316497^4317*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004078093905629599 10000000000000000000 5000483590316497 5000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000483590316497/5000000000000000 : ℝ)) (X := (10004078093905629599/10000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015511209475244189/25000000000000000000 : ℝ) ≤ (10001471448093089/10000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (25015511209475244189/25000000000000000000 : ℝ)^1024 ≤ (10001471448093089/10000000000000000 : ℝ)^4317 := by
      have hnat : (25015511209475244189 : ℕ)^1024*10000000000000000^4317 ≤ 10001471448093089^4317*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015511209475244189 25000000000000000000 10001471448093089 10000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001471448093089/10000000000000000 : ℝ)) (X := (25015511209475244189/25000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2439630026451903/25000000000000000000 : ℝ) ≤ ((11766784358265420343/11770000000000000000 : ℝ)+2*(33617830673/23540000000000 : ℝ)*(5593/50000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (11766784358265420343/11770000000000000000 : ℝ)+2*(33617830673/23540000000000 : ℝ)*(5593/50000 : ℝ)=(10000462913172899/10000000000000000 : ℝ) by norm_num, show 1+2*(2439630026451903/25000000000000000000 : ℝ)=(12502439630026451903/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15511209475244189/50000000000000000000 : ℝ)+(2439630026451903/25000000000000000000 : ℝ) ≤ ((11766784358265420343/11770000000000000000 : ℝ)+(33617830673/23540000000000 : ℝ)*((14717/100000 : ℝ)+(5593/50000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (11766784358265420343/11770000000000000000 : ℝ)+(33617830673/23540000000000 : ℝ)*((14717/100000 : ℝ)+(5593/50000 : ℝ))=(5000483590316497/5000000000000000 : ℝ) by norm_num, show 1+(15511209475244189/50000000000000000000 : ℝ)+(2439630026451903/25000000000000000000 : ℝ)=(10004078093905629599/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15511209475244189/50000000000000000000 : ℝ) ≤ ((11766784358265420343/11770000000000000000 : ℝ)+2*(33617830673/23540000000000 : ℝ)*(14717/100000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (11766784358265420343/11770000000000000000 : ℝ)+2*(33617830673/23540000000000 : ℝ)*(14717/100000 : ℝ)=(10001471448093089/10000000000000000 : ℝ) by norm_num, show 1+2*(15511209475244189/50000000000000000000 : ℝ)=(25015511209475244189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11766784358265420343/11770000000000000000 : ℝ)*(X 1 0+X 2 0)+(33617830673/23540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (11766784358265420343/11770000000000000000 : ℝ)) (alpha := (33617830673/23540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11766784358265420343/11770000000000000000 : ℝ)*(X 0 1+X 2 1)+(33617830673/23540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (11766784358265420343/11770000000000000000 : ℝ)) (alpha := (33617830673/23540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11766784358265420343/11770000000000000000 : ℝ)*(X 0 2+X 1 2)+(33617830673/23540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (11766784358265420343/11770000000000000000 : ℝ)) (alpha := (33617830673/23540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1015116027/5000000000 : ℝ)*X 0 0+(1352958943/2500000000 : ℝ)*X 0 1+(5245130073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674352349/5000000000 : ℝ)*X 1 0+(-423031279/2000000000 : ℝ)*X 1 1+(5245130073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674352349/5000000000 : ℝ)*X 2 0+(2622565037/5000000000 : ℝ)*X 2 1+(-423031279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67538371/156250000 : ℝ)*X 0 0+(4150127013/10000000000 : ℝ)*X 0 1+(2250703667/5000000000 : ℝ)*X 0 2+(67538371/156250000 : ℝ)*X 1 0+(4150127013/10000000000 : ℝ)*X 1 1+(2250703667/5000000000 : ℝ)*X 1 2+(67538371/156250000 : ℝ)*X 2 0+(4150127013/10000000000 : ℝ)*X 2 1+(2250703667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-507560993/2500000000 : ℝ)*X 0 0+(5245727383/10000000000 : ℝ)*X 0 1+(1352808859/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305686803/10000000000 : ℝ)*X 1 0+(-487262779/2500000000 : ℝ)*X 1 1+(5411235481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305686977/10000000000 : ℝ)*X 2 0+(2705617723/5000000000 : ℝ)*X 2 1+(-121815683/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322481123/10000000000 : ℝ)*X 0 0+(2250074299/5000000000 : ℝ)*X 0 1+(415139213/1000000000 : ℝ)*X 0 2+(4322481123/10000000000 : ℝ)*X 1 0+(2250074299/5000000000 : ℝ)*X 1 1+(415139213/1000000000 : ℝ)*X 1 2+(4322481123/10000000000 : ℝ)*X 2 0+(2250074299/5000000000 : ℝ)*X 2 1+(415139213/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (391410884561651810354850753/73562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498435921/50000000000000 : ℝ)*(base19) + (232335019/25000000000000 : ℝ)*(base23) + (36120747/100000000000000 : ℝ)*(lower2) + (33390483/25000000000000 : ℝ)*(upper3) + (5287649/6250000000000 : ℝ)*(upper5) + (1105673317487457/25000000000000 : ℝ)*(major0) + (1105673317487457/25000000000000 : ℝ)*(major1) + (1105673317487457/25000000000000 : ℝ)*(major2) + (74982706996713/1250000000000 : ℝ)*(sp0) + (5998636058149461/100000000000000 : ℝ)*(sp1) + (5998636125681227/100000000000000 : ℝ)*(sp2) + (1138695519053/40000000000 : ℝ)*(sp3) + (20495284263/100000000000000 : ℝ)*(sp4) + (2101977211/20000000000000 : ℝ)*(sp7) + (569349861503711/20000000000000 : ℝ)*(f.failure) + (5998637055021303/100000000000000 : ℝ)*(f.sum) + (152968668269/1177000000000000000000000000 : ℝ)*base66 + (4063906886690112249/294250000000000000000000000000000 : ℝ)*base68 + (2226156076390862249/294250000000000000000000000000000 : ℝ)*base70 + (3708863525512112249/294250000000000000000000000000000 : ℝ)*base72 + (3568085162971/1177000000000000000000000000 : ℝ)*base74 + (626570289232887751/294250000000000000000000000000000 : ℝ)*base75 + (4906001015071112249/294250000000000000000000000000000 : ℝ)*base78 + (3681809193303362249/294250000000000000000000000000000 : ℝ)*base80 + (5500423018399/1177000000000000000000000000 : ℝ)*base81 + (15907521/1000000000000000000000 : ℝ)*base89 + (15907521/1000000000000000000000 : ℝ)*base91 + (15907521/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30069052929301381671921537/7356250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210806021/50000000000000 : ℝ)*(base19) + (900213591/100000000000000 : ℝ)*(base23) + (85030207/50000000000000 : ℝ)*(lower1) + (12649099/25000000000000 : ℝ)*(upper3) + (25977281/25000000000000 : ℝ)*(lower4) + (21151009/20000000000000 : ℝ)*(upper5) + (55683241190697/1250000000000 : ℝ)*(major0) + (55683241190697/1250000000000 : ℝ)*(major1) + (55683241190697/1250000000000 : ℝ)*(major2) + (2087103073/20000000000000 : ℝ)*(sp2) + (6041993616210517/100000000000000 : ℝ)*(sp4) + (1510498298649619/25000000000000 : ℝ)*(sp5) + (6041982280481561/100000000000000 : ℝ)*(sp6) + (358415604756157/12500000000000 : ℝ)*(sp7) + (358415604756157/12500000000000 : ℝ)*(f.failure) + (6041993616210517/100000000000000 : ℝ)*(f.sum) + (1089490852963/294250000000000000000000000 : ℝ)*base65 + (220527545764888429/14712500000000000000000000000000 : ℝ)*base68 + (165715220698099071/14712500000000000000000000000000 : ℝ)*base69 + (1940266777007499071/14712500000000000000000000000000 : ℝ)*base71 + (24945056929/73562500000000000000000000 : ℝ)*base74 + (206123888419499071/14712500000000000000000000000000 : ℝ)*base75 + (21143455281288429/14712500000000000000000000000000 : ℝ)*base78 + (165473853131549071/14712500000000000000000000000000 : ℝ)*base79 + (2909265997489/1177000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1230627/625000000000000000000 : ℝ)*base89 + (1230627/625000000000000000000 : ℝ)*base91 + (1230627/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1358_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1358_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1358_box_0 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-466060259/2500000000 : ℝ)*x 0 + (1347317029/2500000000 : ℝ)*x 1 + (5389268739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466060259/2500000000 : ℝ)^2159 ≤ (5529607740279/50000000000000 : ℝ)^1647 := by
    have hnat : (466060259 : ℕ)^2159*50000000000000^1647 ≤ 5529607740279^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466060259 2500000000 5529607740279 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347317029/2500000000 : ℝ)^2159 ≤ (5558798610357/12500000000000 : ℝ)^1647 := by
    have hnat : (1347317029 : ℕ)^2159*12500000000000^1647 ≤ 5558798610357^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347317029 2500000000 5558798610357 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389268739/10000000000 : ℝ)^2159 ≤ (2779399726359/6250000000000 : ℝ)^1647 := by
    have hnat : (5389268739 : ℕ)^2159*6250000000000^1647 ≤ 2779399726359^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389268739 10000000000 2779399726359 6250000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466060259/2500000000 : ℝ), (1347317029/2500000000 : ℝ), (5389268739/10000000000 : ℝ)] ![(5529607740279/50000000000000 : ℝ), (5558798610357/12500000000000 : ℝ), (2779399726359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466060259/2500000000 : ℝ)|^2159 ≤ (5529607740279/50000000000000 : ℝ)^1647
        have hw : |(-466060259/2500000000 : ℝ)|=(466060259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347317029/2500000000 : ℝ)|^2159 ≤ (5558798610357/12500000000000 : ℝ)^1647
        have hw : |(1347317029/2500000000 : ℝ)|=(1347317029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389268739/10000000000 : ℝ)|^2159 ≤ (2779399726359/6250000000000 : ℝ)^1647
        have hw : |(5389268739/10000000000 : ℝ)|=(5389268739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_1 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285375291/10000000000 : ℝ)*x 0 + (-2006656893/10000000000 : ℝ)*x 1 + (5389268059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285375291/10000000000 : ℝ)^2159 ≤ (10837494945689/25000000000000 : ℝ)^1647 := by
    have hnat : (5285375291 : ℕ)^2159*25000000000000^1647 ≤ 10837494945689^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285375291 10000000000 10837494945689 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006656893/10000000000 : ℝ)^2159 ≤ (12179631940031/100000000000000 : ℝ)^1647 := by
    have hnat : (2006656893 : ℕ)^2159*100000000000000^1647 ≤ 12179631940031^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006656893 10000000000 12179631940031 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389268059/10000000000 : ℝ)^2159 ≤ (5558798533287/12500000000000 : ℝ)^1647 := by
    have hnat : (5389268059 : ℕ)^2159*12500000000000^1647 ≤ 5558798533287^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389268059 10000000000 5558798533287 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285375291/10000000000 : ℝ), (-2006656893/10000000000 : ℝ), (5389268059/10000000000 : ℝ)] ![(10837494945689/25000000000000 : ℝ), (12179631940031/100000000000000 : ℝ), (5558798533287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285375291/10000000000 : ℝ)|^2159 ≤ (10837494945689/25000000000000 : ℝ)^1647
        have hw : |(5285375291/10000000000 : ℝ)|=(5285375291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006656893/10000000000 : ℝ)|^2159 ≤ (12179631940031/100000000000000 : ℝ)^1647
        have hw : |(-2006656893/10000000000 : ℝ)|=(2006656893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389268059/10000000000 : ℝ)|^2159 ≤ (5558798533287/12500000000000 : ℝ)^1647
        have hw : |(5389268059/10000000000 : ℝ)|=(5389268059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_2 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285375101/10000000000 : ℝ)*x 0 + (2694634121/5000000000 : ℝ)*x 1 + (-2006656899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285375101/10000000000 : ℝ)^2159 ≤ (43349977739957/100000000000000 : ℝ)^1647 := by
    have hnat : (5285375101 : ℕ)^2159*100000000000000^1647 ≤ 43349977739957^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285375101 10000000000 43349977739957 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694634121/5000000000 : ℝ)^2159 ≤ (44470390245777/100000000000000 : ℝ)^1647 := by
    have hnat : (2694634121 : ℕ)^2159*100000000000000^1647 ≤ 44470390245777^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694634121 5000000000 44470390245777 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006656899/10000000000 : ℝ)^2159 ≤ (1217963198777/10000000000000 : ℝ)^1647 := by
    have hnat : (2006656899 : ℕ)^2159*10000000000000^1647 ≤ 1217963198777^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006656899 10000000000 1217963198777 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285375101/10000000000 : ℝ), (2694634121/5000000000 : ℝ), (-2006656899/10000000000 : ℝ)] ![(43349977739957/100000000000000 : ℝ), (44470390245777/100000000000000 : ℝ), (1217963198777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285375101/10000000000 : ℝ)|^2159 ≤ (43349977739957/100000000000000 : ℝ)^1647
        have hw : |(5285375101/10000000000 : ℝ)|=(5285375101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694634121/5000000000 : ℝ)|^2159 ≤ (44470390245777/100000000000000 : ℝ)^1647
        have hw : |(2694634121/5000000000 : ℝ)|=(2694634121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006656899/10000000000 : ℝ)|^2159 ≤ (1217963198777/10000000000000 : ℝ)^1647
        have hw : |(-2006656899/10000000000 : ℝ)|=(2006656899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_3 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1117567789/2500000000 : ℝ)*x 0 + (4252401729/10000000000 : ℝ)*x 1 + (4252401969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117567789/2500000000 : ℝ)^2159 ≤ (34804369449417/100000000000000 : ℝ)^1647 := by
    have hnat : (1117567789 : ℕ)^2159*100000000000000^1647 ≤ 34804369449417^1647*2500000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117567789 2500000000 34804369449417 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252401729/10000000000 : ℝ)^2159 ≤ (32597814061763/100000000000000 : ℝ)^1647 := by
    have hnat : (4252401729 : ℕ)^2159*100000000000000^1647 ≤ 32597814061763^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252401729 10000000000 32597814061763 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252401969/10000000000 : ℝ)^2159 ≤ (3259781647347/10000000000000 : ℝ)^1647 := by
    have hnat : (4252401969 : ℕ)^2159*10000000000000^1647 ≤ 3259781647347^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252401969 10000000000 3259781647347 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1117567789/2500000000 : ℝ), (4252401729/10000000000 : ℝ), (4252401969/10000000000 : ℝ)] ![(34804369449417/100000000000000 : ℝ), (32597814061763/100000000000000 : ℝ), (3259781647347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1117567789/2500000000 : ℝ)|^2159 ≤ (34804369449417/100000000000000 : ℝ)^1647
        have hw : |(1117567789/2500000000 : ℝ)|=(1117567789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252401729/10000000000 : ℝ)|^2159 ≤ (32597814061763/100000000000000 : ℝ)^1647
        have hw : |(4252401729/10000000000 : ℝ)|=(4252401729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252401969/10000000000 : ℝ)|^2159 ≤ (3259781647347/10000000000000 : ℝ)^1647
        have hw : |(4252401969/10000000000 : ℝ)|=(4252401969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_4 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-219897137/1000000000 : ℝ)*x 0 + (2632635381/5000000000 : ℝ)*x 1 + (5265271589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219897137/1000000000 : ℝ)^2159 ≤ (13732086438727/100000000000000 : ℝ)^1647 := by
    have hnat : (219897137 : ℕ)^2159*100000000000000^1647 ≤ 13732086438727^1647*1000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219897137 1000000000 13732086438727 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632635381/5000000000 : ℝ)^2159 ≤ (43133952331361/100000000000000 : ℝ)^1647 := by
    have hnat : (2632635381 : ℕ)^2159*100000000000000^1647 ≤ 43133952331361^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632635381 5000000000 43133952331361 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265271589/10000000000 : ℝ)^2159 ≤ (21566980606193/50000000000000 : ℝ)^1647 := by
    have hnat : (5265271589 : ℕ)^2159*50000000000000^1647 ≤ 21566980606193^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265271589 10000000000 21566980606193 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219897137/1000000000 : ℝ), (2632635381/5000000000 : ℝ), (5265271589/10000000000 : ℝ)] ![(13732086438727/100000000000000 : ℝ), (43133952331361/100000000000000 : ℝ), (21566980606193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219897137/1000000000 : ℝ)|^2159 ≤ (13732086438727/100000000000000 : ℝ)^1647
        have hw : |(-219897137/1000000000 : ℝ)|=(219897137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632635381/5000000000 : ℝ)|^2159 ≤ (43133952331361/100000000000000 : ℝ)^1647
        have hw : |(2632635381/5000000000 : ℝ)|=(2632635381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265271589/10000000000 : ℝ)|^2159 ≤ (21566980606193/50000000000000 : ℝ)^1647
        have hw : |(5265271589/10000000000 : ℝ)|=(5265271589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_5 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686204611/5000000000 : ℝ)*x 0 + (-20565241/100000000 : ℝ)*x 1 + (5265271453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686204611/5000000000 : ℝ)^2159 ≤ (5536014719007/12500000000000 : ℝ)^1647 := by
    have hnat : (2686204611 : ℕ)^2159*12500000000000^1647 ≤ 5536014719007^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686204611 5000000000 5536014719007 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20565241/100000000 : ℝ)^2159 ≤ (12577922485681/100000000000000 : ℝ)^1647 := by
    have hnat : (20565241 : ℕ)^2159*100000000000000^1647 ≤ 12577922485681^1647*100000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20565241 100000000 12577922485681 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265271453/10000000000 : ℝ)^2159 ≤ (43133959751903/100000000000000 : ℝ)^1647 := by
    have hnat : (5265271453 : ℕ)^2159*100000000000000^1647 ≤ 43133959751903^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265271453 10000000000 43133959751903 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686204611/5000000000 : ℝ), (-20565241/100000000 : ℝ), (5265271453/10000000000 : ℝ)] ![(5536014719007/12500000000000 : ℝ), (12577922485681/100000000000000 : ℝ), (43133959751903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686204611/5000000000 : ℝ)|^2159 ≤ (5536014719007/12500000000000 : ℝ)^1647
        have hw : |(2686204611/5000000000 : ℝ)|=(2686204611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20565241/100000000 : ℝ)|^2159 ≤ (12577922485681/100000000000000 : ℝ)^1647
        have hw : |(-20565241/100000000 : ℝ)|=(20565241/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265271453/10000000000 : ℝ)|^2159 ≤ (43133959751903/100000000000000 : ℝ)^1647
        have hw : |(5265271453/10000000000 : ℝ)|=(5265271453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_6 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074481733/2000000000 : ℝ)*x 0 + (329079497/625000000 : ℝ)*x 1 + (-2056524183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074481733/2000000000 : ℝ)^2159 ≤ (8857622346589/20000000000000 : ℝ)^1647 := by
    have hnat : (1074481733 : ℕ)^2159*20000000000000^1647 ≤ 8857622346589^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074481733 2000000000 8857622346589 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329079497/625000000 : ℝ)^2159 ≤ (43133965110587/100000000000000 : ℝ)^1647 := by
    have hnat : (329079497 : ℕ)^2159*100000000000000^1647 ≤ 43133965110587^1647*625000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329079497 625000000 43133965110587 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056524183/10000000000 : ℝ)^2159 ≤ (6288961575563/50000000000000 : ℝ)^1647 := by
    have hnat : (2056524183 : ℕ)^2159*50000000000000^1647 ≤ 6288961575563^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056524183 10000000000 6288961575563 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074481733/2000000000 : ℝ), (329079497/625000000 : ℝ), (-2056524183/10000000000 : ℝ)] ![(8857622346589/20000000000000 : ℝ), (43133965110587/100000000000000 : ℝ), (6288961575563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074481733/2000000000 : ℝ)|^2159 ≤ (8857622346589/20000000000000 : ℝ)^1647
        have hw : |(1074481733/2000000000 : ℝ)|=(1074481733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329079497/625000000 : ℝ)|^2159 ≤ (43133965110587/100000000000000 : ℝ)^1647
        have hw : |(329079497/625000000 : ℝ)|=(329079497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056524183/10000000000 : ℝ)|^2159 ≤ (6288961575563/50000000000000 : ℝ)^1647
        have hw : |(-2056524183/10000000000 : ℝ)|=(2056524183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_7 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (834738341/2000000000 : ℝ)*x 0 + (2200319169/5000000000 : ℝ)*x 1 + (2200319349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834738341/2000000000 : ℝ)^2159 ≤ (31809159830747/100000000000000 : ℝ)^1647 := by
    have hnat : (834738341 : ℕ)^2159*100000000000000^1647 ≤ 31809159830747^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834738341 2000000000 31809159830747 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200319169/5000000000 : ℝ)^2159 ≤ (34095418249447/100000000000000 : ℝ)^1647 := by
    have hnat : (2200319169 : ℕ)^2159*100000000000000^1647 ≤ 34095418249447^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200319169 5000000000 34095418249447 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200319349/5000000000 : ℝ)^2159 ≤ (34095421905747/100000000000000 : ℝ)^1647 := by
    have hnat : (2200319349 : ℕ)^2159*100000000000000^1647 ≤ 34095421905747^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200319349 5000000000 34095421905747 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834738341/2000000000 : ℝ), (2200319169/5000000000 : ℝ), (2200319349/5000000000 : ℝ)] ![(31809159830747/100000000000000 : ℝ), (34095418249447/100000000000000 : ℝ), (34095421905747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834738341/2000000000 : ℝ)|^2159 ≤ (31809159830747/100000000000000 : ℝ)^1647
        have hw : |(834738341/2000000000 : ℝ)|=(834738341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200319169/5000000000 : ℝ)|^2159 ≤ (34095418249447/100000000000000 : ℝ)^1647
        have hw : |(2200319169/5000000000 : ℝ)|=(2200319169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200319349/5000000000 : ℝ)|^2159 ≤ (34095421905747/100000000000000 : ℝ)^1647
        have hw : |(2200319349/5000000000 : ℝ)|=(2200319349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_8 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128636967/10000000000 : ℝ)*x 0 + (2589916461/5000000000 : ℝ)*x 1 + (5403280659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128636967/10000000000 : ℝ)^2159 ≤ (13159207146623/100000000000000 : ℝ)^1647 := by
    have hnat : (2128636967 : ℕ)^2159*100000000000000^1647 ≤ 13159207146623^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128636967 10000000000 13159207146623 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589916461/5000000000 : ℝ)^2159 ≤ (4221877137519/10000000000000 : ℝ)^1647 := by
    have hnat : (2589916461 : ℕ)^2159*10000000000000^1647 ≤ 4221877137519^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589916461 5000000000 4221877137519 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403280659/10000000000 : ℝ)^2159 ≤ (11155505364869/25000000000000 : ℝ)^1647 := by
    have hnat : (5403280659 : ℕ)^2159*25000000000000^1647 ≤ 11155505364869^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403280659 10000000000 11155505364869 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128636967/10000000000 : ℝ), (2589916461/5000000000 : ℝ), (5403280659/10000000000 : ℝ)] ![(13159207146623/100000000000000 : ℝ), (4221877137519/10000000000000 : ℝ), (11155505364869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128636967/10000000000 : ℝ)|^2159 ≤ (13159207146623/100000000000000 : ℝ)^1647
        have hw : |(-2128636967/10000000000 : ℝ)|=(2128636967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589916461/5000000000 : ℝ)|^2159 ≤ (4221877137519/10000000000000 : ℝ)^1647
        have hw : |(2589916461/5000000000 : ℝ)|=(2589916461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403280659/10000000000 : ℝ)|^2159 ≤ (11155505364869/25000000000000 : ℝ)^1647
        have hw : |(5403280659/10000000000 : ℝ)|=(5403280659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_9 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (211021353/400000000 : ℝ)*x 0 + (-2000890979/10000000000 : ℝ)*x 1 + (1080656191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211021353/400000000 : ℝ)^2159 ≤ (43244199154331/100000000000000 : ℝ)^1647 := by
    have hnat : (211021353 : ℕ)^2159*100000000000000^1647 ≤ 43244199154331^1647*400000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211021353 400000000 43244199154331 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000890979/10000000000 : ℝ)^2159 ≤ (12133776157489/100000000000000 : ℝ)^1647 := by
    have hnat : (2000890979 : ℕ)^2159*100000000000000^1647 ≤ 12133776157489^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000890979 10000000000 12133776157489 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080656191/2000000000 : ℝ)^2159 ≤ (8924404932769/20000000000000 : ℝ)^1647 := by
    have hnat : (1080656191 : ℕ)^2159*20000000000000^1647 ≤ 8924404932769^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080656191 2000000000 8924404932769 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211021353/400000000 : ℝ), (-2000890979/10000000000 : ℝ), (1080656191/2000000000 : ℝ)] ![(43244199154331/100000000000000 : ℝ), (12133776157489/100000000000000 : ℝ), (8924404932769/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211021353/400000000 : ℝ)|^2159 ≤ (43244199154331/100000000000000 : ℝ)^1647
        have hw : |(211021353/400000000 : ℝ)|=(211021353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000890979/10000000000 : ℝ)|^2159 ≤ (12133776157489/100000000000000 : ℝ)^1647
        have hw : |(-2000890979/10000000000 : ℝ)|=(2000890979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080656191/2000000000 : ℝ)|^2159 ≤ (8924404932769/20000000000000 : ℝ)^1647
        have hw : |(1080656191/2000000000 : ℝ)|=(1080656191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_10 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275534893/10000000000 : ℝ)*x 0 + (2701640379/5000000000 : ℝ)*x 1 + (-400177961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275534893/10000000000 : ℝ)^2159 ≤ (43244210630363/100000000000000 : ℝ)^1647 := by
    have hnat : (5275534893 : ℕ)^2159*100000000000000^1647 ≤ 43244210630363^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275534893 10000000000 43244210630363 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701640379/5000000000 : ℝ)^2159 ≤ (5577752816401/12500000000000 : ℝ)^1647 := by
    have hnat : (2701640379 : ℕ)^2159*12500000000000^1647 ≤ 5577752816401^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701640379 5000000000 5577752816401 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400177961/2000000000 : ℝ)^2159 ≤ (6066883412477/50000000000000 : ℝ)^1647 := by
    have hnat : (400177961 : ℕ)^2159*50000000000000^1647 ≤ 6066883412477^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400177961 2000000000 6066883412477 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275534893/10000000000 : ℝ), (2701640379/5000000000 : ℝ), (-400177961/2000000000 : ℝ)] ![(43244210630363/100000000000000 : ℝ), (5577752816401/12500000000000 : ℝ), (6066883412477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275534893/10000000000 : ℝ)|^2159 ≤ (43244210630363/100000000000000 : ℝ)^1647
        have hw : |(5275534893/10000000000 : ℝ)|=(5275534893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701640379/5000000000 : ℝ)|^2159 ≤ (5577752816401/12500000000000 : ℝ)^1647
        have hw : |(2701640379/5000000000 : ℝ)|=(2701640379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400177961/2000000000 : ℝ)|^2159 ≤ (6066883412477/50000000000000 : ℝ)^1647
        have hw : |(-400177961/2000000000 : ℝ)|=(400177961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_11 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (56290333/125000000 : ℝ)*x 0 + (2117818379/5000000000 : ℝ)*x 1 + (4235636721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56290333/125000000 : ℝ)^2159 ≤ (35141100501137/100000000000000 : ℝ)^1647 := by
    have hnat : (56290333 : ℕ)^2159*100000000000000^1647 ≤ 35141100501137^1647*125000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56290333 125000000 35141100501137 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117818379/5000000000 : ℝ)^2159 ≤ (16214724962997/50000000000000 : ℝ)^1647 := by
    have hnat : (2117818379 : ℕ)^2159*50000000000000^1647 ≤ 16214724962997^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117818379 5000000000 16214724962997 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235636721/10000000000 : ℝ)^2159 ≤ (16214724777323/50000000000000 : ℝ)^1647 := by
    have hnat : (4235636721 : ℕ)^2159*50000000000000^1647 ≤ 16214724777323^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235636721 10000000000 16214724777323 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56290333/125000000 : ℝ), (2117818379/5000000000 : ℝ), (4235636721/10000000000 : ℝ)] ![(35141100501137/100000000000000 : ℝ), (16214724962997/50000000000000 : ℝ), (16214724777323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56290333/125000000 : ℝ)|^2159 ≤ (35141100501137/100000000000000 : ℝ)^1647
        have hw : |(56290333/125000000 : ℝ)|=(56290333/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117818379/5000000000 : ℝ)|^2159 ≤ (16214724962997/50000000000000 : ℝ)^1647
        have hw : |(2117818379/5000000000 : ℝ)|=(2117818379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235636721/10000000000 : ℝ)|^2159 ≤ (16214724777323/50000000000000 : ℝ)^1647
        have hw : |(4235636721/10000000000 : ℝ)|=(4235636721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_12 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934882019/10000000000 : ℝ)*x 0 + (2736268627/5000000000 : ℝ)*x 1 + (5254189183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1934882019/10000000000 : ℝ)^2159 ≤ (2322351841553/20000000000000 : ℝ)^1647 := by
    have hnat : (1934882019 : ℕ)^2159*20000000000000^1647 ≤ 2322351841553^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934882019 10000000000 2322351841553 20000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736268627/5000000000 : ℝ)^2159 ≤ (45373252871099/100000000000000 : ℝ)^1647 := by
    have hnat : (2736268627 : ℕ)^2159*100000000000000^1647 ≤ 45373252871099^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736268627 5000000000 45373252871099 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254189183/10000000000 : ℝ)^2159 ≤ (21507493958673/50000000000000 : ℝ)^1647 := by
    have hnat : (5254189183 : ℕ)^2159*50000000000000^1647 ≤ 21507493958673^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254189183 10000000000 21507493958673 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1934882019/10000000000 : ℝ), (2736268627/5000000000 : ℝ), (5254189183/10000000000 : ℝ)] ![(2322351841553/20000000000000 : ℝ), (45373252871099/100000000000000 : ℝ), (21507493958673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1934882019/10000000000 : ℝ)|^2159 ≤ (2322351841553/20000000000000 : ℝ)^1647
        have hw : |(-1934882019/10000000000 : ℝ)|=(1934882019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736268627/5000000000 : ℝ)|^2159 ≤ (45373252871099/100000000000000 : ℝ)^1647
        have hw : |(2736268627/5000000000 : ℝ)|=(2736268627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254189183/10000000000 : ℝ)|^2159 ≤ (21507493958673/50000000000000 : ℝ)^1647
        have hw : |(5254189183/10000000000 : ℝ)|=(5254189183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_13 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076037021/2000000000 : ℝ)*x 0 + (-2060878119/10000000000 : ℝ)*x 1 + (2627094821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076037021/2000000000 : ℝ)^2159 ≤ (22186082602631/50000000000000 : ℝ)^1647 := by
    have hnat : (1076037021 : ℕ)^2159*50000000000000^1647 ≤ 22186082602631^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076037021 2000000000 22186082602631 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060878119/10000000000 : ℝ)^2159 ≤ (6306420963987/50000000000000 : ℝ)^1647 := by
    have hnat : (2060878119 : ℕ)^2159*50000000000000^1647 ≤ 6306420963987^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060878119 10000000000 6306420963987 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627094821/5000000000 : ℝ)^2159 ≤ (43014992843249/100000000000000 : ℝ)^1647 := by
    have hnat : (2627094821 : ℕ)^2159*100000000000000^1647 ≤ 43014992843249^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627094821 5000000000 43014992843249 100000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076037021/2000000000 : ℝ), (-2060878119/10000000000 : ℝ), (2627094821/5000000000 : ℝ)] ![(22186082602631/50000000000000 : ℝ), (6306420963987/50000000000000 : ℝ), (43014992843249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076037021/2000000000 : ℝ)|^2159 ≤ (22186082602631/50000000000000 : ℝ)^1647
        have hw : |(1076037021/2000000000 : ℝ)|=(1076037021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060878119/10000000000 : ℝ)|^2159 ≤ (6306420963987/50000000000000 : ℝ)^1647
        have hw : |(-2060878119/10000000000 : ℝ)|=(2060878119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627094821/5000000000 : ℝ)|^2159 ≤ (43014992843249/100000000000000 : ℝ)^1647
        have hw : |(2627094821/5000000000 : ℝ)|=(2627094821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_14 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5380185701/10000000000 : ℝ)*x 0 + (1050837863/2000000000 : ℝ)*x 1 + (-2060877753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380185701/10000000000 : ℝ)^2159 ≤ (11093042912179/25000000000000 : ℝ)^1647 := by
    have hnat : (5380185701 : ℕ)^2159*25000000000000^1647 ≤ 11093042912179^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380185701 10000000000 11093042912179 25000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050837863/2000000000 : ℝ)^2159 ≤ (21507494666973/50000000000000 : ℝ)^1647 := by
    have hnat : (1050837863 : ℕ)^2159*50000000000000^1647 ≤ 21507494666973^1647*2000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050837863 2000000000 21507494666973 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060877753/10000000000 : ℝ)^2159 ≤ (1576604873959/12500000000000 : ℝ)^1647 := by
    have hnat : (2060877753 : ℕ)^2159*12500000000000^1647 ≤ 1576604873959^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060877753 10000000000 1576604873959 12500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380185701/10000000000 : ℝ), (1050837863/2000000000 : ℝ), (-2060877753/10000000000 : ℝ)] ![(11093042912179/25000000000000 : ℝ), (21507494666973/50000000000000 : ℝ), (1576604873959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380185701/10000000000 : ℝ)|^2159 ≤ (11093042912179/25000000000000 : ℝ)^1647
        have hw : |(5380185701/10000000000 : ℝ)|=(5380185701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050837863/2000000000 : ℝ)|^2159 ≤ (21507494666973/50000000000000 : ℝ)^1647
        have hw : |(1050837863/2000000000 : ℝ)|=(1050837863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060877753/10000000000 : ℝ)|^2159 ≤ (1576604873959/12500000000000 : ℝ)^1647
        have hw : |(-2060877753/10000000000 : ℝ)|=(2060877753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1358_box_15 (p : ℝ) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2073368899/5000000000 : ℝ)*x 0 + (4413875763/10000000000 : ℝ)*x 1 + (35311009/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073368899/5000000000 : ℝ)^2159 ≤ (788503631749/2500000000000 : ℝ)^1647 := by
    have hnat : (2073368899 : ℕ)^2159*2500000000000^1647 ≤ 788503631749^1647*5000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073368899 5000000000 788503631749 2500000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413875763/10000000000 : ℝ)^2159 ≤ (17114962761511/50000000000000 : ℝ)^1647 := by
    have hnat : (4413875763 : ℕ)^2159*50000000000000^1647 ≤ 17114962761511^1647*10000000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413875763 10000000000 17114962761511 50000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35311009/80000000 : ℝ)^2159 ≤ (3422992920307/10000000000000 : ℝ)^1647 := by
    have hnat : (35311009 : ℕ)^2159*10000000000000^1647 ≤ 3422992920307^1647*80000000^2159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35311009 80000000 3422992920307 10000000000000 2159 1647 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2159/512 : ℝ)) 2159 1647 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073368899/5000000000 : ℝ), (4413875763/10000000000 : ℝ), (35311009/80000000 : ℝ)] ![(788503631749/2500000000000 : ℝ), (17114962761511/50000000000000 : ℝ), (3422992920307/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073368899/5000000000 : ℝ)|^2159 ≤ (788503631749/2500000000000 : ℝ)^1647
        have hw : |(2073368899/5000000000 : ℝ)|=(2073368899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413875763/10000000000 : ℝ)|^2159 ≤ (17114962761511/50000000000000 : ℝ)^1647
        have hw : |(4413875763/10000000000 : ℝ)|=(4413875763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35311009/80000000 : ℝ)|^2159 ≤ (3422992920307/10000000000000 : ℝ)^1647
        have hw : |(35311009/80000000 : ℝ)|=(35311009/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1358_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31431/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14743/25000 : ℝ) ∧ (5003/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42207/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11187/100000 : ℝ) ^ (4317/1024 : ℝ) ≤ (9762198461009389/100000000000000000000 : ℝ) := by
    have hpowers : (11187/100000 : ℝ)^4317 ≤ (9762198461009389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11187 : ℕ)^4317*100000000000000000000^1024 ≤ 9762198461009389^1024*100000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11187 100000 9762198461009389 100000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11187/100000 : ℝ)) (X := (9762198461009389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (4317/1024 : ℝ) ≤ (1240541330539141/4000000000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^4317 ≤ (1240541330539141/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3679 : ℕ)^4317*4000000000000000000^1024 ≤ 1240541330539141^1024*25000^4317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 1240541330539141 4000000000000000000 4317 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (1240541330539141/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009762198461009389/50000000000000000000 : ℝ) ≤ (2000092617529877/2000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50009762198461009389/50000000000000000000 : ℝ)^1024 ≤ (2000092617529877/2000000000000000 : ℝ)^4317 := by
      have hnat : (50009762198461009389 : ℕ)^1024*2000000000000000^4317 ≤ 2000092617529877^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009762198461009389 50000000000000000000 2000092617529877 2000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092617529877/2000000000000000 : ℝ)) (X := (50009762198461009389/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020387865862243957/50000000000000000000 : ℝ) ≤ (400038682286103/400000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (50020387865862243957/50000000000000000000 : ℝ)^1024 ≤ (400038682286103/400000000000000 : ℝ)^4317 := by
      have hnat : (50020387865862243957 : ℕ)^1024*400000000000000^4317 ≤ 400038682286103^4317*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020387865862243957 50000000000000000000 400038682286103 400000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400038682286103/400000000000000 : ℝ)) (X := (50020387865862243957/50000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001240541330539141/2000000000000000000 : ℝ) ≤ (2000294205331153/2000000000000000 : ℝ) ^ (4317/1024 : ℝ) := by
    have hpowers : (2001240541330539141/2000000000000000000 : ℝ)^1024 ≤ (2000294205331153/2000000000000000 : ℝ)^4317 := by
      have hnat : (2001240541330539141 : ℕ)^1024*2000000000000000^4317 ≤ 2000294205331153^4317*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001240541330539141 2000000000000000000 2000294205331153 2000000000000000 1024 4317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000294205331153/2000000000000000 : ℝ)) (X := (2001240541330539141/2000000000000000000 : ℝ)) (by norm_num) 4317 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9762198461009389/100000000000000000000 : ℝ) ≤ ((7056071684530061321/7058000000000000000 : ℝ)+2*(50396950319/35290000000000 : ℝ)*(11187/100000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (7056071684530061321/7058000000000000000 : ℝ)+2*(50396950319/35290000000000 : ℝ)*(11187/100000 : ℝ)=(2000092617529877/2000000000000000 : ℝ) by norm_num, show 1+2*(9762198461009389/100000000000000000000 : ℝ)=(50009762198461009389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1240541330539141/4000000000000000000 : ℝ)+(9762198461009389/100000000000000000000 : ℝ) ≤ ((7056071684530061321/7058000000000000000 : ℝ)+(50396950319/35290000000000 : ℝ)*((3679/25000 : ℝ)+(11187/100000 : ℝ)))^(4317/1024 : ℝ) := by
    rw [show (7056071684530061321/7058000000000000000 : ℝ)+(50396950319/35290000000000 : ℝ)*((3679/25000 : ℝ)+(11187/100000 : ℝ))=(400038682286103/400000000000000 : ℝ) by norm_num, show 1+(1240541330539141/4000000000000000000 : ℝ)+(9762198461009389/100000000000000000000 : ℝ)=(50020387865862243957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1240541330539141/4000000000000000000 : ℝ) ≤ ((7056071684530061321/7058000000000000000 : ℝ)+2*(50396950319/35290000000000 : ℝ)*(3679/25000 : ℝ))^(4317/1024 : ℝ) := by
    rw [show (7056071684530061321/7058000000000000000 : ℝ)+2*(50396950319/35290000000000 : ℝ)*(3679/25000 : ℝ)=(2000294205331153/2000000000000000 : ℝ) by norm_num, show 1+2*(1240541330539141/4000000000000000000 : ℝ)=(2001240541330539141/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7056071684530061321/7058000000000000000 : ℝ)*(X 1 0+X 2 0)+(50396950319/35290000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (7056071684530061321/7058000000000000000 : ℝ)) (alpha := (50396950319/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7056071684530061321/7058000000000000000 : ℝ)*(X 0 1+X 2 1)+(50396950319/35290000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (7056071684530061321/7058000000000000000 : ℝ)) (alpha := (50396950319/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7056071684530061321/7058000000000000000 : ℝ)*(X 0 2+X 1 2)+(50396950319/35290000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4317/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (7056071684530061321/7058000000000000000 : ℝ)) (alpha := (50396950319/35290000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-466060259/2500000000 : ℝ)*X 0 0+(1347317029/2500000000 : ℝ)*X 0 1+(5389268739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285375291/10000000000 : ℝ)*X 1 0+(-2006656893/10000000000 : ℝ)*X 1 1+(5389268059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285375101/10000000000 : ℝ)*X 2 0+(2694634121/5000000000 : ℝ)*X 2 1+(-2006656899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1117567789/2500000000 : ℝ)*X 0 0+(4252401729/10000000000 : ℝ)*X 0 1+(4252401969/10000000000 : ℝ)*X 0 2+(1117567789/2500000000 : ℝ)*X 1 0+(4252401729/10000000000 : ℝ)*X 1 1+(4252401969/10000000000 : ℝ)*X 1 2+(1117567789/2500000000 : ℝ)*X 2 0+(4252401729/10000000000 : ℝ)*X 2 1+(4252401969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219897137/1000000000 : ℝ)*X 0 0+(2632635381/5000000000 : ℝ)*X 0 1+(5265271589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686204611/5000000000 : ℝ)*X 1 0+(-20565241/100000000 : ℝ)*X 1 1+(5265271453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074481733/2000000000 : ℝ)*X 2 0+(329079497/625000000 : ℝ)*X 2 1+(-2056524183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((834738341/2000000000 : ℝ)*X 0 0+(2200319169/5000000000 : ℝ)*X 0 1+(2200319349/5000000000 : ℝ)*X 0 2+(834738341/2000000000 : ℝ)*X 1 0+(2200319169/5000000000 : ℝ)*X 1 1+(2200319349/5000000000 : ℝ)*X 1 2+(834738341/2000000000 : ℝ)*X 2 0+(2200319169/5000000000 : ℝ)*X 2 1+(2200319349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2128636967/10000000000 : ℝ)*X 0 0+(2589916461/5000000000 : ℝ)*X 0 1+(5403280659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((211021353/400000000 : ℝ)*X 1 0+(-2000890979/10000000000 : ℝ)*X 1 1+(1080656191/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275534893/10000000000 : ℝ)*X 2 0+(2701640379/5000000000 : ℝ)*X 2 1+(-400177961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((56290333/125000000 : ℝ)*X 0 0+(2117818379/5000000000 : ℝ)*X 0 1+(4235636721/10000000000 : ℝ)*X 0 2+(56290333/125000000 : ℝ)*X 1 0+(2117818379/5000000000 : ℝ)*X 1 1+(4235636721/10000000000 : ℝ)*X 1 2+(56290333/125000000 : ℝ)*X 2 0+(2117818379/5000000000 : ℝ)*X 2 1+(4235636721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1934882019/10000000000 : ℝ)*X 0 0+(2736268627/5000000000 : ℝ)*X 0 1+(5254189183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1076037021/2000000000 : ℝ)*X 1 0+(-2060878119/10000000000 : ℝ)*X 1 1+(2627094821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380185701/10000000000 : ℝ)*X 2 0+(1050837863/2000000000 : ℝ)*X 2 1+(-2060877753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2073368899/5000000000 : ℝ)*X 0 0+(4413875763/10000000000 : ℝ)*X 0 1+(35311009/80000000 : ℝ)*X 0 2+(2073368899/5000000000 : ℝ)*X 1 0+(4413875763/10000000000 : ℝ)*X 1 1+(35311009/80000000 : ℝ)*X 1 2+(2073368899/5000000000 : ℝ)*X 2 0+(4413875763/10000000000 : ℝ)*X 2 1+(35311009/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1358_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31431/50000 : ℝ) ≤ (-55457712715543722024477833835147/88225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62502181/50000000000000 : ℝ)*(upper1) + (219302741/100000000000000 : ℝ)*(lower4) + (78842531/50000000000000 : ℝ)*(upper5) + (734648491900969/25000000000000 : ℝ)*(major0) + (734648491900969/25000000000000 : ℝ)*(major1) + (734648491900969/25000000000000 : ℝ)*(major2) + (318205187/4000000000000 : ℝ)*(sp3) + (100166223153799/2500000000000 : ℝ)*(sp4) + (801317059070857/20000000000000 : ℝ)*(sp5) + (4006580332532657/100000000000000 : ℝ)*(sp6) + (1891473056948161/100000000000000 : ℝ)*(sp7) + (11132980803/100000000000000 : ℝ)*(sp12) + (74763778477/100000000000000 : ℝ)*(sp13) + (15945320021/20000000000000 : ℝ)*(sp14) + (472870253019459/25000000000000 : ℝ)*(f.failure) + (2003330029566381/50000000000000 : ℝ)*(f.sum) + (6457020819199/882250000000000000000000000 : ℝ)*base65 + (315630089812770049/176450000000000000000000000000000 : ℝ)*base67 + (1089361834219379951/176450000000000000000000000000000 : ℝ)*base70 + (701327348019520049/176450000000000000000000000000000 : ℝ)*base71 + (5600896911109/1764500000000000000000000000 : ℝ)*base73 + (597726777746879951/176450000000000000000000000000000 : ℝ)*base76 + (319812424169770049/176450000000000000000000000000000 : ℝ)*base77 + (253222185055120049/176450000000000000000000000000000 : ℝ)*base79 + (542228718967/705800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2496349/1250000000000000000000 : ℝ)*base89 + (2496349/1250000000000000000000 : ℝ)*base91 + (2496349/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14743/25000 : ℝ) ≤ (26015300213104238634255268980621/44112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3727847/50000000000000 : ℝ)*(lower0) + (24983761/25000000000000 : ℝ)*(lower1) + (16541813/100000000000000 : ℝ)*(lower3) + (110186177/100000000000000 : ℝ)*(lower5) + (751955371825267/25000000000000 : ℝ)*(major0) + (751955371825267/25000000000000 : ℝ)*(major1) + (751955371825267/25000000000000 : ℝ)*(major2) + (1014981398765431/25000000000000 : ℝ)*(sp0) + (811973138808071/20000000000000 : ℝ)*(sp1) + (31718313090559/781250000000 : ℝ)*(sp2) + (1936031855148981/100000000000000 : ℝ)*(sp3) + (8745788031/100000000000000 : ℝ)*(sp7) + (78381551197/100000000000000 : ℝ)*(sp9) + (18480529829/100000000000000 : ℝ)*(sp12) + (484010150234253/25000000000000 : ℝ)*(f.failure) + (31718313090559/781250000000 : ℝ)*(f.sum) + (117498820859/176450000000000000000000000 : ℝ)*base65 + (2710802358889852293/176450000000000000000000000000000 : ℝ)*base68 + (986813654314702293/176450000000000000000000000000000 : ℝ)*base70 + (288341402428652293/176450000000000000000000000000000 : ℝ)*base72 + (54647353140837/3529000000000000000000000000 : ℝ)*base74 + (1409726956378352293/176450000000000000000000000000000 : ℝ)*base76 + (281567408334447707/176450000000000000000000000000000 : ℝ)*base77 + (856515782389152293/176450000000000000000000000000000 : ℝ)*base80 + (4808691494507/3529000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5340883/1250000000000000000000 : ℝ)*base89 + (5340883/1250000000000000000000 : ℝ)*base91 + (5340883/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5003/6250 : ℝ) ≤ (35312071306279784785290445908069/44112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21067713/100000000000000 : ℝ)*(upper0) + (195762117/100000000000000 : ℝ)*(lower1) + (195646363/100000000000000 : ℝ)*(lower3) + (32856977/5000000000000 : ℝ)*(upper4) + (414907594478137/12500000000000 : ℝ)*(major0) + (414907594478137/12500000000000 : ℝ)*(major1) + (414907594478137/12500000000000 : ℝ)*(major2) + (18890331919/20000000000000 : ℝ)*(sp1) + (138273583139/50000000000000 : ℝ)*(sp2) + (158859759237/100000000000000 : ℝ)*(sp3) + (2237666925636401/50000000000000 : ℝ)*(sp8) + (4475239399613207/100000000000000 : ℝ)*(sp9) + (1118764326026631/25000000000000 : ℝ)*(sp10) + (534086363976907/25000000000000 : ℝ)*(sp11) + (133531519729179/6250000000000 : ℝ)*(f.failure) + (2237666925636401/50000000000000 : ℝ)*(f.sum) + (16697222013067/1764500000000000000000000000 : ℝ)*base66 + (760232018067786023/88225000000000000000000000000000 : ℝ)*base68 + (713294545911663977/88225000000000000000000000000000 : ℝ)*base69 + (376459758869261023/88225000000000000000000000000000 : ℝ)*base72 + (19505734391713/3529000000000000000000000000 : ℝ)*base74 + (974033628214463977/88225000000000000000000000000000 : ℝ)*base75 + (100158856490488977/88225000000000000000000000000000 : ℝ)*base77 + (13728762089813977/88225000000000000000000000000000 : ℝ)*base79 + (15592401200523/3529000000000000000000000000 : ℝ)*base82 + (2012731/312500000000000000000 : ℝ)*base90 + (2012731/312500000000000000000 : ℝ)*base92 + (2012731/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-42207/50000 : ℝ) ≤ (-37236105177615724547546743669341/44112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63498993/100000000000000 : ℝ)*(lower1) + (196218907/100000000000000 : ℝ)*(lower2) + (225273307/100000000000000 : ℝ)*(upper5) + (838974802615707/25000000000000 : ℝ)*(major0) + (838974802615707/25000000000000 : ℝ)*(major1) + (838974802615707/25000000000000 : ℝ)*(major2) + (14037624321/100000000000000 : ℝ)*(sp0) + (4839412317/12500000000000 : ℝ)*(sp5) + (137384750907/100000000000000 : ℝ)*(sp6) + (5298307601/12500000000000 : ℝ)*(sp7) + (91596685386327/2000000000000 : ℝ)*(sp12) + (915961918328427/20000000000000 : ℝ)*(sp13) + (1144927730547441/25000000000000 : ℝ)*(sp14) + (1080022478167533/50000000000000 : ℝ)*(sp15) + (1080043671397937/50000000000000 : ℝ)*(f.failure) + (4579848306940671/100000000000000 : ℝ)*(f.sum) + (4340791975347/1764500000000000000000000000 : ℝ)*base66 + (148029985197268947/176450000000000000000000000000000 : ℝ)*base67 + (252880826760018947/176450000000000000000000000000000 : ℝ)*base69 + (831613893200618947/176450000000000000000000000000000 : ℝ)*base71 + (27986363328349/3529000000000000000000000000 : ℝ)*base74 + (363779316868031053/176450000000000000000000000000000 : ℝ)*base76 + (1006674252050218947/176450000000000000000000000000000 : ℝ)*base77 + (940805721314668947/176450000000000000000000000000000 : ℝ)*base79 + (4361587785021/705800000000000000000000000 : ℝ)*base82 + (12156207/2500000000000000000000 : ℝ)*base89 + (12156207/2500000000000000000000 : ℝ)*base91 + (12156207/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1358_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14743/25000 : ℝ) else (5003/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42207/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1358_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1358_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14743/25000 : ℝ) else (5003/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42207/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1358_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1358_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1358_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4317/1024 : ℝ) ≤ p) (hpb : p ≤ (2159/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77679711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31431/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14743/25000 : ℝ) else (5003/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42207/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1358_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
